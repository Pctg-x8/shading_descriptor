//! Tokenizer

use std::ops::{Add, AddAssign};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location { pub line: usize, pub column: usize }
impl Default for Location { fn default() -> Self { Location { line: 1, column: 1 } } }
impl Add<usize> for Location { type Output = Self; fn add(mut self, other: usize) -> Self { self.column += other; self } }
impl AddAssign<usize> for Location { fn add_assign(&mut self, other: usize) { self.column += other; } }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source<'s> { pub pos: Location, pub slice: &'s str }
impl<'s> Source<'s>
{
    pub fn new(s: &'s str) -> Self { Source { pos: Location::default(), slice: s } }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericTy { Float, Double, Long, Unsigned, UnsignedLong }

impl<'s> Source<'s>
{
    fn split(&mut self, at: usize, charat: usize) -> Self
    {
        let sf = &self.slice[..at]; self.slice = &self.slice[at..];
        let pf = self.pos.clone(); self.pos += charat;
        Source { pos: pf, slice: sf }
    }

    /// Strips an identifier ([a-zA-Z_][:alphanumeric:_]*)
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("ident(");
    /// 
    /// assert_eq!(s.identifier(), Some(Token::Identifier(Source { pos: Location::default(), slice: "ident" })));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 6 }, slice: "(" });
    /// ```
    pub fn identifier(&mut self) -> Option<Token<'s>>
    {
        if self.slice.starts_with(|c: char| (c.is_alphanumeric() && !c.is_digit(10)) || c == '_')
        {
            let (c, b) = self.slice.chars().take_while(|&c| c.is_alphanumeric() || c == '_').fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
            assert!(c > 0);
            Some(Token::Identifier(self.split(b, c)))
        }
        else { None }
    }
    /// Strips an numeric ([0-9_]+(\.[0-9_]*)?(fuld){0,2})
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("0.33f4");
    ///
    /// assert_eq!(s.numeric(), Some(Token::NumericF(Source { pos: Location::default(), slice: "0.33" }, Some(NumericTy::Float))));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 6 }, slice: "4" });
    /// ```
    pub fn numeric(&mut self) -> Option<Token<'s>>
    {
        let (ipart_c, ipart_b) = self.slice.chars().take_while(|&c| c.is_digit(10) || c == '_').fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
        if ipart_c <= 0 { return None; }
        let s_rest = &self.slice[ipart_b..];
        if s_rest.starts_with(".") && s_rest.chars().nth(1).map(|c| c.is_digit(10)).unwrap_or(false)
        {
            let (fpart_c, fpart_b) = s_rest.chars().skip(1).take_while(|&c| c.is_digit(10) || c == '_').fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
            let ss = self.split(ipart_b + 1 + fpart_b, ipart_c + 1 + fpart_c);
            Some(Token::NumericF(ss, self.numeric_ty()))
        }
        else
        {
            let ss = self.split(ipart_b + 1, ipart_c + 1);
            Some(Token::NumericF(ss, self.numeric_ty()))
        }
    }
    fn numeric_ty(&mut self) -> Option<NumericTy>
    {
        let mut iter = self.slice.chars();
        match iter.next()
        {
            Some(c@'f') | Some(c@'F') | Some(c@'ｆ') | Some(c@'Ｆ') => { self.split(c.len_utf8(), 1); Some(NumericTy::Float) },
            Some(c@'d') | Some(c@'D') | Some(c@'ｄ') | Some(c@'Ｄ') => { self.split(c.len_utf8(), 1); Some(NumericTy::Double) },
            Some(c@'l') | Some(c@'L') | Some(c@'ｌ') | Some(c@'Ｌ') => match iter.next()
            {
                Some(c2@'u') | Some(c2@'U') | Some(c2@'ｕ') | Some(c2@'Ｕ') => { self.split(c.len_utf8() + c2.len_utf8(), 2); Some(NumericTy::UnsignedLong) },
                _ => { self.split(c.len_utf8(), 1); Some(NumericTy::Long) }
            },
            Some(c@'u') | Some(c@'U') | Some(c@'ｕ') | Some(c@'Ｕ') => match iter.next()
            {
                Some(c2@'l') | Some(c2@'L') | Some(c2@'ｌ') | Some(c2@'Ｌ') => { self.split(c.len_utf8() + c2.len_utf8(), 2); Some(NumericTy::UnsignedLong) },
                _ => { self.split(c.len_utf8(), 1); Some(NumericTy::Unsigned) }
            },
            _ => None
        }
    }
}
