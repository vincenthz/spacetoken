//! Parse API on top of the `TokenTree`

use crate::location;

use super::token::*;
use super::tree::*;

use std::sync::Arc;

/// Type of errors
#[derive(Debug, Clone)]
pub enum ParseError {
    /// Unknown
    EndOfStream,

    /// Expecting Comment
    ExpectingComment {
        /// position of this error
        span: Position,
    },
    /// Expecting Ident
    ExpectingIdent {
        /// position of this error
        span: Position,
    },
    /// Expecting Punct
    ExpectingPunct {
        /// position of this error
        span: Position,
    },
    /// Expecting Literal
    ExpectingLiteral {
        /// position of this error
        span: Position,
    },
    /// Expecting Group
    ExpectingGroup {
        /// delimiter expected
        delim: GroupDelim,
        /// delimiter got (if a group)
        delim_got: Option<GroupDelim>,
        /// position of this error
        span: Position,
    },
    /// Error during the parsing of a group
    ErrorGroup {
        /// delimiter expected
        delim: GroupDelim,
        /// span of this group
        span: Position,
        /// parser error during the parsing of the tokens inside this group
        r: Box<ParseError>,
    },
    /// Error during the parsing of a group
    ErrorGroupUnfinished {
        /// delimiter expected
        delim: GroupDelim,
        /// remaining tokens that were left unparsed in this group
        remaining: usize,
        /// Position of the start of the remaining token
        span: Position,
    },
}

/// Multi lines
pub enum RecursiveLine {
    /// Terminal recursion line
    Simple(String),
    /// Header with multiple inner line
    Recursive(String, Box<RecursiveLine>),
}

impl ParseError {
    /// return a human printable error for this parser error
    pub fn human_print(self, linemap: &location::LineMap) -> RecursiveLine {
        match self {
            ParseError::EndOfStream => RecursiveLine::Simple(String::from("EOF")),
            ParseError::ExpectingComment { span } => {
                RecursiveLine::Simple(format!("{:?} : expecting comment", linemap.span(span)))
            }
            ParseError::ExpectingIdent { span } => {
                RecursiveLine::Simple(format!("{:?} : expecting ident", linemap.span(span)))
            }
            ParseError::ExpectingPunct { span } => {
                RecursiveLine::Simple(format!("{:?} : expecting punctuation", linemap.span(span)))
            }
            ParseError::ExpectingLiteral { span } => {
                RecursiveLine::Simple(format!("{:?} : expecting literal", linemap.span(span)))
            }
            ParseError::ExpectingGroup {
                delim,
                delim_got,
                span,
            } => {
                if let Some(got) = delim_got {
                    RecursiveLine::Simple(format!(
                        "{:?} : expecting group {delim:?} but got {got:?}",
                        linemap.span(span),
                    ))
                } else {
                    RecursiveLine::Simple(format!(
                        "{:?} : expecting group {delim:?} but got not a group",
                        linemap.span(span),
                    ))
                }
            }
            ParseError::ErrorGroup { delim, span, r } => RecursiveLine::Recursive(
                format!(
                    "{:?} : error during parsing of group {delim:?}",
                    linemap.span(span)
                ),
                Box::new(r.human_print(linemap)),
            ),
            ParseError::ErrorGroupUnfinished {
                delim,
                remaining,
                span: pos,
            } => RecursiveLine::Simple(format!(
                "{:?} : error group {delim:?} is unfinished: {remaining} tokens remaining",
                linemap.span(pos),
            )),
        }
    }
}

/// Parser Stream
///
/// it is cheap to clone, and it is the primary
/// interface to retry the parsing or evaluate
/// multiple parsing options
#[derive(Clone)]
pub struct Parser {
    trees: Arc<Vec<SpannedTree>>,
    pos: usize,
}

impl Parser {
    /// create a new parser from a stream
    pub fn new(trees: Vec<SpannedTree>) -> Self {
        Self {
            trees: Arc::new(trees),
            pos: 0,
        }
    }

    /// Get the number of remaining spanned trees
    pub fn remaining(&self) -> usize {
        self.trees.len() - self.pos
    }

    /// Check if all the elements in the parser have been consumed
    pub fn finished(&self) -> bool {
        self.remaining() == 0
    }

    /// Peek at the next available spanned tree
    pub fn peek(&self) -> Option<&SpannedTree> {
        if self.pos == self.trees.len() {
            None
        } else {
            Some(&self.trees[self.pos])
        }
    }

    /// Return the next spanned tree and advance the position
    pub fn next_opt(&mut self) -> Option<&SpannedTree> {
        if self.pos == self.trees.len() {
            None
        } else {
            let token = &self.trees[self.pos];
            self.pos += 1;
            Some(token)
        }
    }

    /// Return the next spanned tree and advance the position
    ///
    /// If no token is available, return the EndOfStream error
    pub fn next(&mut self) -> Result<&SpannedTree, ParseError> {
        self.next_opt().ok_or(ParseError::EndOfStream)
    }

    /// Try to parse, if the inner callback return nothing, then
    /// the parser is not modified and None is returned, otherwise
    /// the state is advanced as needed, and the object returned
    pub fn optional<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&mut Self) -> Result<T, ParseError>,
    {
        let mut trying = self.clone();
        match f(&mut trying) {
            Ok(t) => {
                *self = trying;
                Some(t)
            }
            Err(_) => None,
        }
    }

    /// Try to parse an Ident from the parser
    pub fn ident<F, T>(&mut self, f: F) -> Result<T, ParseError>
    where
        F: FnOnce(&String) -> Result<T, ParseError>,
    {
        match self.peek() {
            None => Err(ParseError::EndOfStream),
            Some(tt) => match &tt.token {
                TokenTree::Ident(i) => {
                    let r = f(i);
                    if let Ok(_) = r {
                        self.pos += 1;
                    }
                    r
                }
                TokenTree::Comment(_)
                | TokenTree::Group(_, _)
                | TokenTree::Punct(_, _)
                | TokenTree::Literal(_) => Err(ParseError::ExpectingIdent {
                    span: tt.span.clone(),
                }),
            },
        }
    }

    /// try to parse a literal from the parser
    pub fn literal<F, T>(&mut self, f: F) -> Result<T, ParseError>
    where
        F: FnOnce(&Literal) -> Result<T, ParseError>,
    {
        match self.peek() {
            None => Err(ParseError::EndOfStream),
            Some(tt) => match &tt.token {
                TokenTree::Literal(lit) => {
                    let r = f(lit);
                    if let Ok(_) = &r {
                        self.pos += 1;
                    }
                    r
                }
                TokenTree::Comment(_)
                | TokenTree::Ident(_)
                | TokenTree::Group(_, _)
                | TokenTree::Punct(_, _) => Err(ParseError::ExpectingLiteral {
                    span: tt.span.clone(),
                }),
            },
        }
    }

    /// try to parse a comment from the parser
    pub fn comment<F, T>(&mut self, f: F) -> Result<T, ParseError>
    where
        F: FnOnce(&String) -> Result<T, ParseError>,
    {
        match self.peek() {
            None => Err(ParseError::EndOfStream),
            Some(tt) => match &tt.token {
                TokenTree::Comment(comment) => {
                    let r = f(comment);
                    if let Ok(_) = &r {
                        self.pos += 1;
                    }
                    r
                }
                TokenTree::Literal(_)
                | TokenTree::Ident(_)
                | TokenTree::Group(_, _)
                | TokenTree::Punct(_, _) => Err(ParseError::ExpectingLiteral {
                    span: tt.span.clone(),
                }),
            },
        }
    }

    /// try to parse a literal from the parser
    pub fn group<F, T>(&mut self, delimiter: GroupDelim, f: F) -> Result<T, ParseError>
    where
        F: FnOnce(&mut Parser) -> Result<T, ParseError>,
    {
        match self.peek() {
            None => Err(ParseError::EndOfStream),
            Some(tt) => match &tt.token {
                TokenTree::Group(got_delimiter, tokens) => {
                    if *got_delimiter == delimiter {
                        let mut inner_parser = Parser::new(tokens.clone());
                        let inner = f(&mut inner_parser);
                        match inner {
                            Ok(t) => {
                                if let Some(unfinished_token) = inner_parser.peek() {
                                    Err(ParseError::ErrorGroupUnfinished {
                                        delim: delimiter,
                                        remaining: inner_parser.remaining(),
                                        span: unfinished_token.span.clone(),
                                    })
                                } else {
                                    self.pos += 1;
                                    Ok(t)
                                }
                            }
                            Err(inner_err) => {
                                return Err(ParseError::ErrorGroup {
                                    delim: delimiter,
                                    span: tt.span.clone(),
                                    r: Box::new(inner_err),
                                });
                            }
                        }
                    } else {
                        Err(ParseError::ExpectingGroup {
                            delim: delimiter,
                            delim_got: Some(*got_delimiter),
                            span: tt.span.clone(),
                        })
                    }
                }
                TokenTree::Comment(_)
                | TokenTree::Ident(_)
                | TokenTree::Literal(_)
                | TokenTree::Punct(_, _) => Err(ParseError::ExpectingGroup {
                    delim: delimiter,
                    delim_got: None,
                    span: tt.span.clone(),
                }),
            },
        }
    }

    /*
    pub fn punct<F, T>(&mut self, f: F) -> Result<T, ParseError>
    where
        F: FnOnce(char) -> Result<T, ParseError>,
    {
        match self.peek() {
            None => Err(ParseError::EndOfStream),
            Some(tt) => match &tt.token {
                TokenTree::Punct(p, _) => {
                    let (punct_tokens, s) = self.joint_punct();
                    let r = f(s);
                    if r.is_ok() {
                        self.skip(punct_tokens);
                    }
                    r
                }
                TokenTree::Comment(_)
                | TokenTree::Group(_, _)
                | TokenTree::Ident(_)
                | TokenTree::Literal(_) => Err(ParseError::ExpectingPunct),
            },
        }
    }
    */
}

/// Parsable object on top of sequence of TokenTree tokens
pub trait Parse: Sized {
    /// Try to parse the object Self against the current parser
    fn parse(parser: &mut Parser) -> Result<Self, ParseError>;
}

/// many parser combinator
pub fn many<T: Parse>(parser: &mut Parser) -> Result<Vec<T>, ParseError> {
    let mut out = Vec::new();
    loop {
        match parser.optional(|p| T::parse(p)) {
            Some(t) => out.push(t),
            None => {
                break;
            }
        }
    }
    Ok(out)
}

/// many1 parser combinator: like many but fail if there's no element being parsed
pub fn many1<T: Parse>(parser: &mut Parser) -> Result<Vec<T>, ParseError> {
    let mut out = Vec::new();
    let first = T::parse(parser)?;
    out.push(first);
    loop {
        match parser.optional(|p| T::parse(p)) {
            Some(t) => out.push(t),
            None => {
                break;
            }
        }
    }
    Ok(out)
}

/// Module
pub struct Module {
    declarations: Vec<Decl>,
}

/// Declaration
pub enum Decl {}

impl Parse for Module {
    fn parse(parser: &mut Parser) -> Result<Self, ParseError> {
        many(parser).map(|declarations| Module { declarations })
    }
}
impl Parse for Decl {
    fn parse(parser: &mut Parser) -> Result<Self, ParseError> {
        todo!()
    }
}
