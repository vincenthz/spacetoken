use std::{fmt, num::NonZeroUsize};

/// Mapping of lines in a UTF-8 data stream
///
/// It allow to efficiently map byte offset into line / column position
///
/// Keep the offset in bytes of all start of line
/// where newline is the '\n' character.
pub struct LineMap {
    vec: Vec<usize>, // each line represented by an element starting at line 1 (vec[0]) pointing to the raw offset
    total_len: usize,
}

impl LineMap {
    /// Create a new `LineMap`
    pub fn new(content: &str) -> LineMap {
        let mut line_map = Vec::new();
        line_map.push(0); // line 1 starts at offset 0

        let total_len = content.as_bytes().len();

        for (ofs, c) in content.as_bytes().iter().enumerate() {
            if *c == b'\n' {
                //println!("line {} at ofs={}", line_map.len(), ofs);
                line_map.push(ofs + 1);
            }
        }
        LineMap {
            vec: line_map,
            total_len,
        }
    }

    /// Return the line (start at 1) and byte offset of the start of the line
    fn find_nearest_offset_lesser_or_equal(&self, ofs: usize) -> Option<(NonZeroUsize, usize)> {
        if self.total_len < ofs {
            return None;
        }

        // TODO replace by binary search
        let mut line = self.vec.len() - 1;
        while ofs < self.vec[line] {
            line -= 1;
        }
        let start = self.vec[line];
        // note that line starts at 1, thus the + 1
        Some((NonZeroUsize::try_from(line + 1).unwrap(), start))
    }

    /// Try to resolve a byte offset into the line where it is found
    pub fn find_line(&self, ofs: usize) -> Option<NonZeroUsize> {
        self.find_nearest_offset_lesser_or_equal(ofs)
            .map(|(line, _)| line)
    }

    /// Try to resolve a byte offset into a `LineCol` through the LineMap
    pub fn find_byte(&self, ofs: usize) -> Option<LineCol> {
        if let Some((line, line_ofs)) = self.find_nearest_offset_lesser_or_equal(ofs) {
            let col = ofs - line_ofs;
            Some(LineCol { line, column: col })
        } else {
            None
        }
    }

    /// Try to resolve a byte offset into a `LineCol` through the LineMap
    pub fn span(&self, ofs: core::ops::Range<usize>) -> Option<Span> {
        // TODO optimise ..
        if let Some(start) = self.find_byte(ofs.start) {
            if let Some(end) = self.find_byte(ofs.end) {
                Some(Span { start, end })
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// A line-column position
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LineCol {
    /// the line (starts at line 1)
    pub line: NonZeroUsize,
    /// the column (in byte, starts at 0)
    pub column: usize,
}

impl PartialOrd for LineCol {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.line.partial_cmp(&other.line) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.column.partial_cmp(&other.column)
    }
}

impl Ord for LineCol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.line.cmp(&other.line) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        self.column.cmp(&other.column)
    }
}

impl Default for LineCol {
    fn default() -> Self {
        Self {
            line: NonZeroUsize::try_from(1).unwrap(),
            column: 0,
        }
    }
}

impl fmt::Debug for LineCol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl fmt::Display for LineCol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// A Span (start and end) of LineCol where end > start
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// Start location
    pub start: LineCol,
    /// End location
    pub end: LineCol,
}

impl Span {
    /// Return a `Range` from a span
    pub fn range(self) -> core::ops::Range<LineCol> {
        core::ops::Range {
            start: self.start,
            end: self.end,
        }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
