use super::token::*;
use logos::Logos;

/// Literal enumeration of Number, String
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    /// Literal number
    Number(Number),
    /// Literal string
    String(String),
}

/// Indicates whether a Punct token can join with the following punctuation token
/// to form a multi-character operator
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Spacing {
    /// A Punct token is directly followed by another Punct token
    ///
    /// e.g. the '+' in `+=` will be Joint
    Joint,

    /// A Punct token is not directly followed by another Punct token.
    ///
    /// This could be because there's a spacing between Punct, or that
    /// the next token is not a Punct
    ///
    /// e.g. the '+' `in + =` will be Alone
    Alone,
}

/// Tree augmented with a position
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedTree {
    /// The start and end position in the source of this token
    pub span: Position,
    /// The Token associated with this position
    pub token: TokenTree,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Token Tree
pub enum TokenTree {
    /// Identifier
    Ident(String),
    /// Literal
    Literal(Literal),
    /// Punctuation
    Punct(char, Spacing),
    /// Comment
    Comment(String),
    /// Group of Token with group Delimiter () [] or {}
    Group(GroupDelim, Vec<SpannedTree>),
}

/// Provide access to a stream of `TokenTree` from the source lexer
#[derive(Clone)]
pub struct TreeStream<'a> {
    lex: Lexer<'a, Token>,
}

impl<'a> TreeStream<'a> {
    /// Create a new tree stream using the given logos lexer
    pub fn new(s: &'a str) -> Self {
        let lex = Token::lexer(s); //str lex: Lexer<'a, Token>
        Self { lex }
    }

    /// Create a `TreeIterator` from the stream
    pub fn into_iter(self) -> TreeIterator<'a> {
        TreeIterator {
            current_token: None,
            lex: self.lex,
            stack: vec![],
            delims: vec![],
            tokens: None,
            previous_punct: None,
        }
    }
}

type Position = core::ops::Range<usize>;
type Error = ();

/// A `TokenTree` iterator from a `TokenStream`
///
/// The only method exposed is `.next()` to get the next `TokenTree`
pub struct TreeIterator<'a> {
    current_token: Option<(Position, Result<Token, Error>)>,
    lex: Lexer<'a, Token>,
    stack: Vec<Vec<SpannedTree>>,
    delims: Vec<(Position, GroupDelim)>,
    tokens: Option<Vec<SpannedTree>>,
    previous_punct: Option<(char, Position)>,
}

macro_rules! push_or_emit {
    ($self:ident, $t:expr) => {{
        let token = $t;
        match &mut $self.tokens {
            None => return Some(Ok(token)),
            Some(toks) => toks.push(token),
        }
    }};
}

macro_rules! push_or_emit_err {
    ($self:ident, $t:expr) => {{
        let etoken = $t;
        match etoken {
            Ok(tok) => match &mut $self.tokens {
                None => return Some(Ok(tok)),
                Some(toks) => toks.push(tok),
            },
            Err(e) => return Some(Err(e)),
        }
    }};
}

impl<'a> TreeIterator<'a> {
    fn advance_err(&mut self) -> Error {
        let mut swap = None;
        std::mem::swap(&mut swap, &mut self.current_token);
        let (_, r) = swap.expect("current token is here");
        r.err().expect("current token is an error")
    }

    fn advance(&mut self) -> Token {
        let mut swap = None;
        std::mem::swap(&mut swap, &mut self.current_token);
        let (_, r) = swap.expect("current token is here");
        r.ok().expect("current token is a token")
    }

    fn push_group(&mut self, start_pos: Position, delim: GroupDelim) {
        self.delims.push((start_pos, delim));

        // if it's already in a queueing, we create a new queue and set the current queue in the stack,
        // otherwise we create our first queue
        if let Some(tokens) = &mut self.tokens {
            let mut new_vec = vec![];
            std::mem::swap(&mut new_vec, tokens);
            self.stack.push(new_vec);
        } else {
            self.tokens = Some(vec![]);
        }
    }

    fn pop_group(&mut self, end_pos: Position, delim: GroupDelim) -> Result<SpannedTree, ()> {
        match self.delims.pop() {
            None => Err(()),
            Some((start_pos, last_delim)) => {
                // check if the delimiter match the start one we have on the stack
                if last_delim != delim {
                    return Err(());
                }

                let pos = core::ops::Range {
                    start: start_pos.start,
                    end: end_pos.end,
                };

                match self.stack.pop() {
                    // level 1 of grouping
                    None => {
                        let mut swap = None;
                        std::mem::swap(&mut swap, &mut self.tokens);
                        if let Some(tokens) = swap {
                            Ok(SpannedTree {
                                span: pos,
                                token: TokenTree::Group(delim, tokens),
                            })
                        } else {
                            // it was level one, raise an error
                            Err(())
                        }
                    }
                    // level 2 and greater of grouping
                    Some(mut st) => {
                        if let Some(tokens) = &mut self.tokens {
                            std::mem::swap(&mut st, tokens);
                            Ok(SpannedTree {
                                span: pos,
                                token: TokenTree::Group(delim, st),
                            })
                        } else {
                            // internal error: we have a non-empty self.stack, but not a self.tokens
                            panic!("internal error: the unexpected has happened")
                        }
                    }
                }
            }
        }
    }
}

impl<'a> Iterator for TreeIterator<'a> {
    type Item = Result<SpannedTree, ()>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let peek = match &self.current_token {
                None => {
                    match self.lex.next() {
                        None => {
                            self.current_token = None;
                        }
                        Some(t) => {
                            let pos = self.lex.span();
                            self.current_token = Some((pos, t));
                        }
                    }
                    self.current_token.clone()
                }
                Some(_) => self.current_token.clone(),
            };

            if let Some(r) = peek {
                let (span, ertok) = r;
                match ertok {
                    Err(_) => {
                        if let Some(t) = mk_previous_punct(&mut self.previous_punct, None) {
                            push_or_emit!(self, t);
                        }
                        let ret = self.advance_err();
                        return Some(Err(ret));
                    }
                    Ok(tok) => {
                        // debug for token that get generated in the lexing iterator
                        // println!("TOKEN {:?}: {:?}", span, tok);

                        // push the previous punct, depending on what the next token is we set the
                        // correct spacing parameter (Joint or Alone)
                        if let Some(t) =
                            mk_previous_punct(&mut self.previous_punct, Some((&span, &tok)))
                        {
                            push_or_emit!(self, t);
                        }

                        let tok = self.advance();

                        // Process the element now
                        match tok {
                            Token::GroupStart(delim) => self.push_group(span, delim),
                            Token::GroupEnd(delim) => {
                                push_or_emit_err!(self, self.pop_group(span, delim))
                            }
                            Token::Comment(s) => push_or_emit!(
                                self,
                                SpannedTree {
                                    span,
                                    token: TokenTree::Comment(s)
                                }
                            ),
                            Token::Punct(c) => self.previous_punct = Some((c, span.clone())),
                            Token::Number(n) => {
                                push_or_emit!(
                                    self,
                                    SpannedTree {
                                        span,
                                        token: TokenTree::Literal(Literal::Number(n))
                                    }
                                )
                            }
                            Token::String(s) => {
                                push_or_emit!(
                                    self,
                                    SpannedTree {
                                        span,
                                        token: TokenTree::Literal(Literal::String(s))
                                    }
                                )
                            }
                            Token::Ident(id) => {
                                push_or_emit!(
                                    self,
                                    SpannedTree {
                                        span,
                                        token: TokenTree::Ident(id)
                                    }
                                )
                            }
                        };
                    }
                }
            } else {
                if let Some(t) = mk_previous_punct(&mut self.previous_punct, None) {
                    push_or_emit!(self, t);
                }
                return None;
            }
        }
    }
}

fn mk_previous_punct(
    previous_punct: &mut Option<(char, std::ops::Range<usize>)>,
    tok: Option<(&std::ops::Range<usize>, &Token)>,
) -> Option<SpannedTree> {
    if let Some((prev_punct, prev_pos)) = previous_punct.as_ref() {
        let emit = match tok {
            Some((pos, Token::Punct(_punct))) => {
                let spacing = if prev_pos.end == pos.start {
                    Spacing::Joint
                } else {
                    Spacing::Alone
                };
                TokenTree::Punct(*prev_punct, spacing)
            }
            _ => TokenTree::Punct(*prev_punct, Spacing::Alone),
        };
        let pos = prev_pos.clone();
        *previous_punct = None;
        Some(SpannedTree {
            span: pos,
            token: emit,
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spanned_tree_no_pos(tree: SpannedTree) -> TokenTree {
        match tree.token {
            TokenTree::Group(delim, st) => {
                let st2 = st
                    .into_iter()
                    .map(|st| spanned_tree_no_pos(st))
                    .map(|t| SpannedTree {
                        span: NO_POSITION,
                        token: t,
                    })
                    .collect::<Vec<_>>();
                TokenTree::Group(delim, st2)
            }
            t => t.clone(),
        }
    }

    macro_rules! test_tree {
        ($s:literal, $v:expr) => {{
            let stream = TreeStream::new($s);
            let mut it = stream.into_iter();

            let expected = $v;
            let mut exp_it = expected.into_iter();
            let mut pos = 1;
            loop {
                match (it.next(), exp_it.next()) {
                    (Some(Err(e)), Some(exp)) => {
                        panic!(
                            "token at position {}\nexpected : {:?}\ngot     : <error> {:?}",
                            pos, exp, e
                        )
                    }
                    (Some(Ok(got)), Some(exp)) => {
                        let no_pos_token = spanned_tree_no_pos(got);
                        assert!(
                            &no_pos_token == exp,
                            "token at position {}\nexpected : {:?}\ngot      : {:?}",
                            pos,
                            exp,
                            no_pos_token
                        )
                    }
                    (Some(Err(e)), None) => {
                        panic!(
                            "token at position {}\nexpected : <EOF>\ngot     : <error> {:?}",
                            pos, e
                        )
                    }
                    (Some(Ok(got)), None) => {
                        panic!(
                            "token at position {}\nexpected : <EOF>\ngot     : {:?}",
                            pos, got.token
                        )
                    }
                    (None, Some(exp)) => {
                        panic!(
                            "token at position {}\nexpected : {:?}\ngot     : <EOF>",
                            pos, exp
                        )
                    }
                    (None, None) => {
                        break;
                    }
                }
                pos += 1;
            }
        }};
    }

    fn token_num(encoding: NumberEncoding, s: &str) -> TokenTree {
        TokenTree::Literal(Literal::Number(Number {
            encoding,
            raw: s.to_string(),
        }))
    }

    fn token_dec(s: &str) -> TokenTree {
        token_num(NumberEncoding::Decimal, s)
    }

    /*
    fn token_hex(s: &str) -> Tree {
        token_num(NumberEncoding::Hexadecimal, s)
    }

    fn token_bin(s: &str) -> Tree {
        token_num(NumberEncoding::Binary, s)
    }
    */

    fn token_ident(s: &str) -> TokenTree {
        TokenTree::Ident(s.to_string())
    }

    fn token_punct_joint(c: char) -> TokenTree {
        TokenTree::Punct(c, Spacing::Joint)
    }

    fn token_punct_alone(c: char) -> TokenTree {
        TokenTree::Punct(c, Spacing::Alone)
    }

    const NO_POSITION: core::ops::Range<usize> = core::ops::Range { start: 0, end: 0 };

    fn token_group(delim: GroupDelim, tokens: &[TokenTree]) -> TokenTree {
        TokenTree::Group(
            delim,
            tokens
                .iter()
                .map(|t| SpannedTree {
                    span: NO_POSITION,
                    token: t.clone(),
                })
                .collect::<Vec<_>>(),
        )
    }

    fn token_group_paren(tokens: &[TokenTree]) -> TokenTree {
        token_group(GroupDelim::Parenthesis, tokens)
    }

    fn token_group_brace(tokens: &[TokenTree]) -> TokenTree {
        token_group(GroupDelim::Brace, tokens)
    }

    fn token_group_bracket(tokens: &[TokenTree]) -> TokenTree {
        token_group(GroupDelim::Bracket, tokens)
    }

    #[test]
    fn it_works() {
        test_tree!("let x", &[token_ident("let"), token_ident("x")]);
    }

    #[test]
    fn puncts() {
        test_tree!(
            "# @ + -|@",
            &[
                token_punct_alone('#'),
                token_punct_alone('@'),
                token_punct_alone('+'),
                token_punct_joint('-'),
                token_punct_joint('|'),
                token_punct_alone('@')
            ]
        );
    }

    #[test]
    fn grouping_test() {
        test_tree!("( )", &[token_group_paren(&[])]);
        test_tree!(
            "zomb ( # { let x } )",
            &[
                token_ident("zomb"),
                token_group_paren(&[
                    token_punct_alone('#'),
                    token_group_brace(&[token_ident("let"), token_ident("x")])
                ])
            ]
        );
        println!("x");
        test_tree!(
            "# xy abc = 123 + (group ! [])",
            &[
                token_punct_alone('#'),
                token_ident("xy"),
                token_ident("abc"),
                token_punct_alone('='),
                token_dec("123"),
                token_punct_alone('+'),
                token_group_paren(&[
                    token_ident("group"),
                    token_punct_alone('!'),
                    token_group_bracket(&[])
                ])
            ]
        );
    }
}
