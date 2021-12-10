/// Authored by Kofi Otuo <otuokofi@outlook.com>
///
use crossterm::event::*;
use crossterm::style::*;
use crossterm::terminal::ClearType;
use crossterm::{cursor, event, execute, queue, style, terminal};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::io::{stdout, Write};
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::{Duration, Instant};
use std::{cmp, env, fs, io};

const TAB_STOP: usize = 4;

struct CleanUp;

impl Drop for CleanUp {
    fn drop(&mut self) {
    }
}

struct StatusMessage {
    message: Option<String>,
    set_time: Option<Instant>,
}

impl StatusMessage {
    fn new(initial_message: String) -> Self {
        Self {
            message: Some(initial_message),
            set_time: Some(Instant::now()),
        }
    }

    fn set_message(&mut self, message: String) {
        self.message = Some(message);
        self.set_time = Some(Instant::now())
    }

    fn message(&mut self) -> Option<&String> {
        self.set_time.and_then(|time| {
            if time.elapsed() > Duration::from_secs(5) {
                self.message = None;
                self.set_time = None;
                None
            } else {
                Some(self.message.as_ref().unwrap())
            }
        })
    }
}

struct Row {
    offset: usize,
    row_content: String,
    render: RenderBuf,
    column_offsets: Vec<usize>,
}

#[derive(serde::Deserialize)]
#[derive(Eq, PartialEq, Hash)]
struct EncodedFrame {
    addr: Option<u64>,
    name: Option<std::string::String>,
    filename: Option<std::path::PathBuf>,
    lineno: Option<u32>,
    colno: Option<u32>,
}

#[derive(serde::Deserialize)]
struct EncodedFile {
    addrs: HashMap<u64, Vec<EncodedFrame>>,
    frames: Vec<(u64, u32)>,
    ranges: Vec<(u32, usize)>,
    text: std::string::String,
}

struct Buffer {
    rows: Vec<Row>,
    cursor: CursorController,
}

#[derive(Eq, PartialEq, Hash)]
struct TracedAddr(Vec<EncodedFrame>);

#[derive(Eq, PartialEq, Hash)]
struct TracedFrame {
    height: usize,
    addr: Rc<TracedAddr>,
    parent: Option<Rc<TracedFrame>>,
}

struct TracedBuffer {
    addrs: HashMap<u64, Rc<TracedAddr>>,
    frames: Vec<Rc<TracedFrame>>,
    by_offset: Vec<Rc<TracedFrame>>,
    heights: Vec<usize>,
    min_height: usize,
    max_height: usize,
    stack_hashes: Vec<u64>,
    text: String,
}

impl TracedBuffer {
    fn from_file(file: &Path) -> Self {
        let data = fs::read_to_string(&file).expect("Unable to read file");
        let raw: EncodedFile = serde_json::from_str(&data).unwrap();

        let addrs = raw.addrs.into_iter()
            .map(|(addr, frames)| {
                (addr, Rc::new(TracedAddr(frames)))
            })
            .collect::<HashMap<_, _>>();

        let mut frames = Vec::<Rc<TracedFrame>>::new();
        for (addr, parent) in raw.frames {
            let (parent, height) = if parent == u32::MAX {
                (None, 1)
            } else {
                let parent = &frames[parent as usize];
                (Some(parent.clone()), parent.height + 1)
            };
            let frame = Rc::new(TracedFrame {
                addr: addrs[&addr].clone(),
                parent,
                height,
            });
            frames.push(frame);
        }

        let mut by_offset = Vec::with_capacity(raw.text.len());

        for (frame, count) in raw.ranges {
            let frame = &frames[frame as usize];
            for _ in 0..count {
                by_offset.push(frame.clone());
            }
        }

        let heights = by_offset.iter().map(|f| f.height).collect::<Vec<_>>();

        let min_height = heights.iter().min().copied().unwrap_or(0);
        let max_height = heights.iter().max().copied().unwrap_or(0);

        let stack_hashes = by_offset.iter().map(|f| {
            let mut hasher = DefaultHasher::new();
            f.hash(&mut hasher);
            hasher.finish()
        }).collect::<Vec<_>>();

        Self {
            addrs,
            frames,
            heights,
            min_height,
            max_height,
            stack_hashes,
            by_offset,
            text: raw.text,
        }
    }

    fn contents(&self) -> &str {
        &self.text
    }
}

struct EditorRows {
    external_files: HashMap<PathBuf, Buffer>,
    row_contents: Vec<Row>,
    filename: Option<PathBuf>,
    traced: TracedBuffer,
}

impl EditorRows {
    fn from_file(file: PathBuf) -> Self {
        let traced = TracedBuffer::from_file(&file);
        let mut row_contents = Vec::new();
        let text = traced.contents();
        let newlines = text.match_indices('\n').map(|(i, _)| i);
        let mut i = 0;
        for n in newlines {
            let line = &text[i..n];
            let mut row = Row {
                offset: i,
                row_content: line.into(),
                render: RenderBuf::new(),
                column_offsets: Vec::new(),
            };
            Self::render_row(&mut row, &traced);
            row_contents.push(row);
            i = n + 1;
        }
        Self {
            external_files: HashMap::new(),
            filename: Some(file),
            row_contents,
            traced,
        }
    }

    fn number_of_rows(&self) -> usize {
        self.row_contents.len()
    }

    fn get_row(&self, at: usize) -> &str {
        &self.row_contents[at].row_content
    }

    fn get_editor_row(&self, at: usize) -> &Row {
        &self.row_contents[at]
    }

    fn render_row(row: &mut Row, traced: &TracedBuffer) {
        let mut index = 0;
        let capacity = row
            .row_content
            .chars()
            .fold(0, |acc, next| acc + if next == '\t' { TAB_STOP } else { 1 });
        row.render.content.clear();
        row.column_offsets.clear();
        row.row_content.char_indices().for_each(|(i, c)| {
            row.column_offsets.push(row.render.content.len());
            let height = traced.heights[i + row.offset];
            let value = (height - traced.min_height + 1) as f64 / (traced.max_height - traced.min_height + 1) as f64;
            let hash = traced.stack_hashes[i + row.offset];
            queue!(
                row.render,
                // ResetColor
                SetBackgroundColor(Color::Rgb {
                    r: (value * 255.0) as u8,
                    g: (hash & 0xff) as u8,
                    b: ((hash >> 8) & 0xff) as u8,
                 })
            ).unwrap();
            index += 1;
            if c == '\t' {
                row.render.push(' ');
                while index % TAB_STOP != 0 {
                    row.render.push(' ');
                    index += 1
                }
            } else {
                row.render.push(c);
            }
        });
        row.column_offsets.push(row.render.content.len());
    }
}

#[derive(Copy, Clone)]
struct CursorController {
    cursor_x: usize,
    cursor_y: usize,
    screen_rows: usize,
    screen_columns: usize,
    row_offset: usize,
    column_offset: usize,
    render_x: usize,
}

impl CursorController {
    fn new(win_size: (usize, usize)) -> CursorController {
        Self {
            cursor_x: 0,
            cursor_y: 0,
            screen_columns: win_size.0,
            screen_rows: win_size.1,
            row_offset: 0,
            column_offset: 0,
            render_x: 0,
        }
    }

    fn get_render_x(&self, row: &Row) -> usize {
        row.row_content
            .chars()
            .take(self.cursor_x)
            .fold(0, |render_x, c| {
                if c == '\t' {
                    render_x + (TAB_STOP - 1) - (render_x % TAB_STOP) + 1
                } else {
                    render_x + 1
                }
            })
    }

    fn scroll(&mut self, editor_rows: &EditorRows) {
        self.render_x = 0;
        if self.cursor_y < editor_rows.number_of_rows() {
            self.render_x = self.get_render_x(editor_rows.get_editor_row(self.cursor_y));
        }
        self.row_offset = cmp::min(self.row_offset, self.cursor_y);
        if self.cursor_y >= self.row_offset + self.screen_rows {
            self.row_offset = self.cursor_y - self.screen_rows + 1;
        }
        self.column_offset = cmp::min(self.column_offset, self.render_x);
        if self.render_x >= self.column_offset + self.screen_columns {
            self.column_offset = self.render_x - self.screen_columns + 1;
        }
    }

    fn move_cursor(&mut self, direction: KeyCode, editor_rows: &EditorRows) {
        let number_of_rows = editor_rows.number_of_rows();

        match direction {
            KeyCode::Up => {
                self.cursor_y = self.cursor_y.saturating_sub(1);
            }
            KeyCode::Left => {
                if self.cursor_x != 0 {
                    self.cursor_x -= 1;
                } else if self.cursor_y > 0 {
                    self.cursor_y -= 1;
                    self.cursor_x = editor_rows.get_row(self.cursor_y).len();
                }
            }
            KeyCode::Down => {
                if self.cursor_y < number_of_rows {
                    self.cursor_y += 1;
                }
            }
            KeyCode::Right => {
                if self.cursor_y < number_of_rows {
                    match self.cursor_x.cmp(&editor_rows.get_row(self.cursor_y).len()) {
                        Ordering::Less => self.cursor_x += 1,
                        Ordering::Equal => {
                            self.cursor_y += 1;
                            self.cursor_x = 0
                        }
                        _ => {}
                    }
                }
            }
            KeyCode::End => {
                if self.cursor_y < number_of_rows {
                    self.cursor_x = editor_rows.get_row(self.cursor_y).len();
                }
            }
            KeyCode::Home => self.cursor_x = 0,
            _ => unimplemented!(),
        }
        let row_len = if self.cursor_y < number_of_rows {
            editor_rows.get_row(self.cursor_y).len()
        } else {
            0
        };
        self.cursor_x = cmp::min(self.cursor_x, row_len);
    }
}

struct RenderBuf {
    content: String,
}

impl RenderBuf {
    fn new() -> Self {
        Self {
            content: String::new(),
        }
    }

    fn push(&mut self, ch: char) {
        self.content.push(ch)
    }

    fn push_str(&mut self, string: &str) {
        self.content.push_str(string)
    }

    fn flush_to_screen(&mut self) -> io::Result<()> {
        let out = write!(stdout(), "{}", self.content);
        stdout().flush()?;
        self.content.clear();
        out
    }
}

impl io::Write for RenderBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match std::str::from_utf8(buf) {
            Ok(s) => {
                self.content.push_str(s);
                Ok(s.len())
            }
            Err(_) => Err(io::ErrorKind::WriteZero.into()),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

struct Output {
    win_size: (usize, usize),
    editor_contents: RenderBuf,
    cursor_controller: CursorController,
    editor_rows: EditorRows,
    status_message: StatusMessage,
}

impl Output {
    fn from_file(path: PathBuf) -> Self {
        let win_size = terminal::size()
            .map(|(x, y)| (x as usize, y as usize - 2))
            .unwrap();
        Self {
            win_size,
            editor_contents: RenderBuf::new(),
            cursor_controller: CursorController::new(win_size),
            editor_rows: EditorRows::from_file(path),
            status_message: StatusMessage::new(
                "HELP: Ctrl-Q = Quit".into(),
            ),
        }
    }

    fn clear_screen() -> crossterm::Result<()> {
        execute!(stdout(), terminal::Clear(ClearType::All))?;
        execute!(stdout(), cursor::MoveTo(0, 0))
    }

    fn draw_message_bar(&mut self) {
        queue!(
            self.editor_contents,
            terminal::Clear(ClearType::UntilNewLine)
        )
        .unwrap();
        if let Some(msg) = self.status_message.message() {
            self.editor_contents
                .push_str(&msg[..cmp::min(self.win_size.0, msg.len())]);
        }
    }

    fn draw_status_bar(&mut self) {
        self.editor_contents
            .push_str(&style::Attribute::Reverse.to_string());
        let info = format!(
            "{} -- {} lines",
            self.editor_rows
                .filename
                .as_ref()
                .and_then(|path| path.file_name())
                .and_then(|name| name.to_str())
                .unwrap_or("[No Name]"),
            self.editor_rows.number_of_rows()
        );
        let info_len = cmp::min(info.len(), self.win_size.0);
        /* modify the following */
        let line_info = format!(
            "{} | {}/{}",
            "no ft",
            self.cursor_controller.cursor_y + 1,
            self.editor_rows.number_of_rows()
        );
        self.editor_contents.push_str(&info[..info_len]);
        for i in info_len..self.win_size.0 {
            if self.win_size.0 - i == line_info.len() {
                self.editor_contents.push_str(&line_info);
                break;
            } else {
                self.editor_contents.push(' ')
            }
        }
        self.editor_contents
            .push_str(&style::Attribute::Reset.to_string());
        self.editor_contents.push_str("\r\n");
    }

    fn draw_rows(&mut self) {
        let screen_rows = self.win_size.1;
        let screen_columns = self.win_size.0;
        for i in 0..screen_rows {
            let file_row = i + self.cursor_controller.row_offset;
            if file_row >= self.editor_rows.number_of_rows() {
                if self.editor_rows.number_of_rows() == 0 && i == screen_rows / 3 {
                    let mut welcome = format!("debug buf viewer");
                    if welcome.len() > screen_columns {
                        welcome.truncate(screen_columns)
                    }
                    let mut padding = (screen_columns - welcome.len()) / 2;
                    if padding != 0 {
                        self.editor_contents.push('~');
                        padding -= 1
                    }
                    (0..padding).for_each(|_| self.editor_contents.push(' '));
                    self.editor_contents.push_str(&welcome);
                } else {
                    self.editor_contents.push('~');
                }
            } else {
                let row = self.editor_rows.get_editor_row(file_row);
                let render = &row.render;
                let column_offsets = &row.column_offsets;
                let column_offset = self.cursor_controller.column_offset;
                let len = cmp::min(column_offsets.len().saturating_sub(column_offset + 1), screen_columns);
                let start = if len == 0 { 0 } else { column_offset };
                let render = render.content[column_offsets[start] .. column_offsets[start + len]].to_string();
                self.editor_contents.push_str(&render);
            }
            queue!(
                self.editor_contents,
                ResetColor,
                terminal::Clear(ClearType::UntilNewLine)
            )
            .unwrap();
            self.editor_contents.push_str("\r\n");
        }
    }

    fn draw_stacks(&mut self) {
        let screen_rows = self.win_size.1;
        let screen_columns = self.win_size.0;

        let offset = self.editor_rows.row_contents[self.cursor_controller.cursor_y].offset + self.cursor_controller.cursor_x;

        let mut frame = &self.editor_rows.traced.by_offset[offset];
        let mut i = 0;
        loop {
            queue!(
                self.editor_contents,
                cursor::MoveTo(screen_columns as u16 / 2, i),
                terminal::Clear(ClearType::UntilNewLine),
            ).unwrap();

            let line = frame.addr.0[0].name.as_ref().map(|s| s.as_str()).unwrap_or("<unknown>");

            self.editor_contents.push_str(&line[..cmp::min(line.len(), screen_columns / 2)]);

            i += 1;
            if let Some(parent) = &frame.parent {
                frame = parent;
            } else {
                break;
            }
        }
    }

    fn move_cursor(&mut self, direction: KeyCode) {
        self.cursor_controller
            .move_cursor(direction, &self.editor_rows);
    }

    fn refresh_screen(&mut self) -> crossterm::Result<()> {
        self.cursor_controller.scroll(&self.editor_rows);
        queue!(self.editor_contents, cursor::Hide, cursor::MoveTo(0, 0))?;
        self.draw_rows();
        self.draw_status_bar();
        self.draw_message_bar();
        self.draw_stacks();
        let cursor_x = self.cursor_controller.render_x - self.cursor_controller.column_offset;
        let cursor_y = self.cursor_controller.cursor_y - self.cursor_controller.row_offset;
        queue!(
            self.editor_contents,
            cursor::MoveTo(cursor_x as u16, cursor_y as u16),
            cursor::Show
        )?;
        self.editor_contents.flush_to_screen()
    }
}

struct Reader;

impl Reader {
    fn read_key(&self) -> crossterm::Result<KeyEvent> {
        loop {
            if event::poll(Duration::from_millis(500))? {
                if let Event::Key(event) = event::read()? {
                    return Ok(event);
                }
            }
        }
    }
}

struct Editor {
    reader: Reader,
    output: Output,
}

impl Editor {
    fn from_file(path: PathBuf) -> Self {
        Self {
            reader: Reader,
            output: Output::from_file(path),
        }
    }

    fn process_keypress(&mut self) -> crossterm::Result<bool> {
        match self.reader.read_key()? {
            KeyEvent {
                code: KeyCode::Char('q'),
                modifiers: KeyModifiers::CONTROL,
            } => {
                return Ok(false);
            }
            KeyEvent {
                code: KeyCode::Char('w'),
                modifiers: KeyModifiers::NONE,
            } => {
                todo!();
            }
            KeyEvent {
                code: KeyCode::Char('a'),
                modifiers: KeyModifiers::NONE,
            } => {
                todo!();
            }
            KeyEvent {
                code: KeyCode::Char('s'),
                modifiers: KeyModifiers::NONE,
            } => {
                todo!();
            }
            KeyEvent {
                code: KeyCode::Char('d'),
                modifiers: KeyModifiers::NONE,
            } => {
                todo!();
            }
            KeyEvent {
                code: KeyCode::Char('/'),
                modifiers: KeyModifiers::NONE,
            } => {
                todo!();
            }
            KeyEvent {
                code:
                    direction
                    @
                    (KeyCode::Up
                    | KeyCode::Down
                    | KeyCode::Left
                    | KeyCode::Right
                    | KeyCode::Home
                    | KeyCode::End),
                modifiers: KeyModifiers::NONE,
            } => self.output.move_cursor(direction),
            KeyEvent {
                code: val @ (KeyCode::PageUp | KeyCode::PageDown),
                modifiers: KeyModifiers::NONE,
            } => {
                if matches!(val, KeyCode::PageUp) {
                    self.output.cursor_controller.cursor_y =
                        self.output.cursor_controller.row_offset
                } else {
                    self.output.cursor_controller.cursor_y = cmp::min(
                        self.output.win_size.1 + self.output.cursor_controller.row_offset - 1,
                        self.output.editor_rows.number_of_rows(),
                    );
                }
                (0..self.output.win_size.1).for_each(|_| {
                    self.output.move_cursor(if matches!(val, KeyCode::PageUp) {
                        KeyCode::Up
                    } else {
                        KeyCode::Down
                    });
                })
            }
            _ => {}
        }
        Ok(true)
    }

    fn run(&mut self) -> crossterm::Result<bool> {
        self.output.refresh_screen()?;
        self.process_keypress()
    }
}

fn with_screen<T>(f: impl FnOnce() -> T) -> T {
    terminal::enable_raw_mode().unwrap();

    let hook = std::panic::take_hook();
    // TODO: unset this hook when we leave, or use catch_unwind
    std::panic::set_hook(Box::new(move |e| {
        terminal::disable_raw_mode().expect("Unable to disable raw mode");
        Output::clear_screen().expect("error");
        // println!("panicking!");
        std::io::stdout().flush().unwrap();
        hook(e);
    }));

    let res = f();

    res
}

fn main() -> crossterm::Result<()> {
    let mut args = std::env::args().skip(1).collect::<Vec<String>>();
    assert_eq!(args.len(), 1);
    let path = args.pop().unwrap().into();
    let mut editor = Editor::from_file(path);
    with_screen(|| {
        while editor.run()? {}
        Ok(())
    })
}
