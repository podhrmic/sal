//! Source positions. SAL reports places as line/column pairs
//! (`line(37), column(19)`); columns are 0-based in the oracle's output.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub line: u32,
    pub col: u32,
}

impl Pos {
    pub fn new(line: u32, col: u32) -> Self {
        Pos { line, col }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: Pos,
    pub end: Pos,
}

impl Span {
    pub fn new(start: Pos, end: Pos) -> Self {
        Span { start, end }
    }

    pub fn join(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn dummy() -> Span {
        Span::new(Pos::new(0, 0), Pos::new(0, 0))
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line({}), column({})", self.start.line, self.start.col)
    }
}
