//! Layout Parser
//! Based on the syntax of Haskell 2010: https://www.haskell.org/onlinereport/haskell2010/haskellch10.html

use tokparse::{Source, Token, EnclosureKind, Keyword};
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
