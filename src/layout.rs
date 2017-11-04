//! Layout Parser
//! Based on the syntax of Haskell 2010: https://www.haskell.org/onlinereport/haskell2010/haskellch10.html

use tokparse::{Location, Source, Token, EnclosureKind, Keyword};
use std::mem::replace;

#[derive(Debug)]
pub enum LexemeInsertions<'s> { Token(Token<'s>), BraceIndent(usize), AngleIndent(usize) }
pub enum InsertionState { ExpectingNextToInsertBraceIndent, IndentInserted, Free }
pub struct LexemeIndentInsertions<'s>
{
    src: Source<'s>, poke1: Option<Token<'s>>, last_line: Option<usize>, following_brace: bool, state: InsertionState
}
impl<'s> From<Source<'s>> for LexemeIndentInsertions<'s>
{
    fn from(src: Source<'s>) -> Self { LexemeIndentInsertions { src, poke1: None, last_line: None, following_brace: false, state: InsertionState::Free } }
}
impl<'s> LexemeIndentInsertions<'s>
{
    fn acquire_poke1(&mut self) { if self.poke1.is_none() { self.poke1 = Some(self.src.next()); } }
}
impl<'s> Iterator for LexemeIndentInsertions<'s>
{
    type Item = LexemeInsertions<'s>;
    fn next(&mut self) -> Option<Self::Item>
    {
        match self.state
        {
            InsertionState::ExpectingNextToInsertBraceIndent =>
            {
                self.state = InsertionState::IndentInserted; self.acquire_poke1();
                match self.poke1
                {
                    Some(Token::EOF(_)) => Some(LexemeInsertions::BraceIndent(0)),
                    Some(ref t) => Some(LexemeInsertions::BraceIndent(t.position().column)),
                    None => unreachable!()
                }
            },
            InsertionState::IndentInserted =>
            {
                self.state = InsertionState::Free;
                let t = replace(&mut self.poke1, None).unwrap_or_else(|| self.src.next());
                if !self.following_brace
                {
                    match t
                    {
                        Token::Keyword(_, kw) if kw == Keyword::Let || kw == Keyword::Do || kw == Keyword::Where || kw == Keyword::Of =>
                        {
                            self.state = InsertionState::ExpectingNextToInsertBraceIndent;
                        },
                        _ => ()
                    }
                }
                self.following_brace = if let &Token::BeginEnclosure(_, EnclosureKind::Brace) = &t { true } else { false };
                self.last_line = Some(t.position().line);
                Some(LexemeInsertions::Token(t))
            },
            InsertionState::Free =>
            {
                let t = replace(&mut self.poke1, None).unwrap_or_else(|| self.src.next());
                if !self.following_brace
                {
                    match t
                    {
                        Token::Keyword(_, kw) if kw == Keyword::Let || kw == Keyword::Do || kw == Keyword::Where || kw == Keyword::Of =>
                        {
                            self.state = InsertionState::ExpectingNextToInsertBraceIndent;
                        },
                        _ => ()
                    }
                }
                self.following_brace = if let &Token::BeginEnclosure(_, EnclosureKind::Brace) = &t { true } else { false };
                if let Some(n) = self.last_line
                {
                    if n != t.position().line && t.position().column > 1
                    {
                        self.last_line = Some(t.position().line);
                        self.poke1 = Some(t); self.state = InsertionState::IndentInserted;
                        return Some(LexemeInsertions::AngleIndent(self.poke1.as_ref().unwrap().position().column));
                    }
                }
                self.last_line = Some(t.position().line);
                Some(LexemeInsertions::Token(t))
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LFTState { Free, EmptyInserted }
pub struct LayoutFreeTokenStream<'s>
{
    source: LexemeIndentInsertions<'s>, lookahead: Option<LexemeInsertions<'s>>,
    indent_stack: Vec<usize>, state: LFTState
}
impl<'s> From<LexemeIndentInsertions<'s>> for LayoutFreeTokenStream<'s>
{
    fn from(v: LexemeIndentInsertions<'s>) -> Self
    {
        LayoutFreeTokenStream { source: v, lookahead: None, indent_stack: Vec::new(), state: LFTState::Free }
    }
}
impl<'s> LayoutFreeTokenStream<'s>
{
    fn look1(&mut self) -> Option<LexemeInsertions<'s>>
    {
        if self.lookahead.is_none() { self.source.next() } else { self.lookahead.take() }
    }
}
impl<'s> Iterator for LayoutFreeTokenStream<'s>
{
    type Item = Token<'s>;
    fn next(&mut self) -> Option<Self::Item>
    {
        fn from_angle_indent<'s>(this: &mut LayoutFreeTokenStream<'s>, n: usize) -> Option<Token<'s>>
        {
            if let Some(&m) = this.indent_stack.last()
            {
                if m == n
                {
                    return Some(Token::StatementDelimiter(Location::default()));
                }
                else if n < m
                {
                    this.lookahead = Some(LexemeInsertions::AngleIndent(n));
                    this.indent_stack.pop();
                    return Some(Token::EndEnclosure(Location::default(), EnclosureKind::Brace));
                }
            }
            this.next()
        }

        match self.state
        {
            LFTState::Free => match self.look1().unwrap()
            {
                LexemeInsertions::AngleIndent(n) => from_angle_indent(self, n),
                LexemeInsertions::BraceIndent(n) =>
                {
                    if let Some(&m) = self.indent_stack.last()
                    {
                        if n > m
                        {
                            self.indent_stack.push(n);
                            return Some(Token::BeginEnclosure(Location::default(), EnclosureKind::Brace));
                        }
                    }
                    else if n > 0
                    {
                        self.indent_stack.push(n);
                        return Some(Token::BeginEnclosure(Location::default(), EnclosureKind::Brace));
                    }
                    self.state = LFTState::EmptyInserted; self.lookahead = Some(LexemeInsertions::AngleIndent(n));
                    Some(Token::BeginEnclosure(Location::default(), EnclosureKind::Brace))
                },
                LexemeInsertions::Token(Token::EndEnclosure(p, EnclosureKind::Brace)) =>
                {
                    if self.indent_stack.last() == Some(&0)
                    {
                        self.indent_stack.pop(); Some(Token::EndEnclosure(p, EnclosureKind::Brace))
                    }
                    else
                    {
                        panic!("Layout error at {}", p);
                    }
                },
                LexemeInsertions::Token(Token::BeginEnclosure(p, EnclosureKind::Brace)) =>
                {
                    self.indent_stack.push(0); Some(Token::BeginEnclosure(p, EnclosureKind::Brace))
                },
                LexemeInsertions::Token(Token::EOF(p)) =>
                {
                    let rval = if let Some(&m) = self.indent_stack.last()
                    {
                        if m != 0 { Some(Token::EndEnclosure(p.clone(), EnclosureKind::Brace)) }
                        else { panic!("Layout error at {}", p) }
                    }
                    else { None };
                    self.lookahead = Some(LexemeInsertions::Token(Token::EOF(p))); rval
                }
                LexemeInsertions::Token(t) =>
                {
                    /*if let Some(&m) = self.indent_stack.last()
                    {
                        if m != 0
                        {
                            self.indent_stack.pop(); self.lookahead = Some(LexemeInsertions::Token(t));
                            return Some(Token::EndEnclosure(t.position.clone(), EnclosureKind::Brace));
                        }
                        // if m != 0 { panic!("Layout error at {}", t.position().clone()); }
                    }*/
                    Some(t)
                }
            },
            LFTState::EmptyInserted =>
            {
                self.state = LFTState::Free; Some(Token::EndEnclosure(Location::default(), EnclosureKind::Brace))
            }
        }
    }
}

/*
pub trait LayoutFreeTokenStream<'s> : Iterator<Item = Token<'s>> {  }

pub struct Memoize<Stream: Iterator>(Stream, Vec<Stream::Item>, usize);
impl<'s> Source<'s>
{
    pub fn memoize(self) -> Memoize<Self> { Memoize(self, Vec::new(), 0) }
}
impl<Stream: Iterator> Memoize<Stream>
{
    /// Returns: reached to end of stream
    fn fill_until(&mut self, count: usize) -> bool
    {
        while count <= self.1.len()
        {
            match self.0.next() { None => return true, e => self.1.push(e) }
        }
        false
    }
    pub fn current(&mut self) -> Option<&Stream::Item>
    {
        if self.fill_until(self.2) { None } else { Some(&self.1[self.2]) }
    }
    /*pub fn current_mut(&mut self) -> Option<&mut Stream::Item>
    {
        if self.fill_until(self.2) { None } else { Some(&mut self.1[self.2]) }
    }*/
    pub fn shift(&mut self) { self.2 += 1; }
    pub fn unshift(&mut self) { self.2 = self.2.saturating_sub(1); }
}

pub struct LFTokenStream<'s> { pub src: Memoize<Source<'s>>, pub indent_stack: Vec<usize> }
impl From<Source<'s>> for LFTokenStream<'s> { fn from(src: Source<'s>) -> Self { LFTokenStream { src: src.memoize(), indent_stack: Vec::new() } } }

pub fn parse_layout<'s>(src: &Source<'s>)
{
    let mut indent_stack: Vec<usize> = Vec::new();
}
*/
