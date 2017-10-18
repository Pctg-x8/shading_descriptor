//! Tokenizer

use std::ops::{Add, AddAssign};
use std::io::prelude::*;
use std::io::stderr;
use std::fmt::{Display, Formatter, Result as FmtResult};

/// 2なら1, 4なら2, 8なら3...
static mut TAB_ALIGNED_BITS: usize = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location { pub line: usize, pub column: usize }
impl Default for Location { fn default() -> Self { Location { line: 1, column: 1 } } }
impl Add<usize> for Location { type Output = Self; fn add(mut self, other: usize) -> Self { self.column += other; self } }
impl AddAssign<usize> for Location { fn add_assign(&mut self, other: usize) { self.column += other; } }
impl Location
{
    fn advance_line(&mut self) { self.line += 1; self.column = 1; }
    fn advance_tab(&mut self)
    {
        self.column = unsafe { (((self.column - 1) >> TAB_ALIGNED_BITS) + 1 << TAB_ALIGNED_BITS) + 1 };
    }
}
impl Display for Location
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "line {}, column {}", self.line, self.column) }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source<'s> { pub pos: Location, pub slice: &'s str }
impl<'s> Source<'s>
{
    pub fn new(s: &'s str) -> Self { Source { pos: Location::default(), slice: s } }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>),
    Operator(Source<'s>), Equal(Location), Arrow(Location)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericTy { Float, Double, Long, Unsigned, UnsignedLong }

const OPCLASS: &'static [char] = &['<', '＜', '>', '＞', '=', '＝', '!', '！', '$', '＄', '%', '％', '&', '＆', '~', '～', '^', '＾', '-', 'ー',
    '@', '＠', '+', '＋', '*', '＊', '/', '／', '・', '?', '？', '|', '｜', '∥', '―'];

impl<'s> Source<'s>
{
    fn split(&mut self, at: usize, charat: usize) -> Self
    {
        let sf = &self.slice[..at]; self.slice = &self.slice[at..];
        let pf = self.pos.clone(); self.pos += charat;
        Source { pos: pf, slice: sf }
    }

    /// Drops ignored characters and comments
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("{# drop #}#test 2\n\t8");
    ///
    /// s.drop_ignores();
    /// assert_eq!(s, Source { pos: Location { line: 2, column: 3 }, slice: "8" });
    /// ```
    pub fn drop_ignores(&mut self)
    {
        if self.slice.starts_with("\n")
        {
            self.slice = &self.slice['\n'.len_utf8()..]; self.pos.advance_line(); self.drop_ignores();
        }
        else if self.slice.starts_with("\t")
        {
            self.slice = &self.slice['\t'.len_utf8()..]; self.pos.advance_tab(); self.drop_ignores();
        }
        else if self.slice.starts_with(char::is_whitespace)
        {
            self.slice = &self.slice[self.slice.chars().next().unwrap().len_utf8()..];
            self.pos += 1; self.drop_ignores();
        }
        else if self.slice.starts_with("#") { self.drop_line_comment(); self.drop_ignores(); }
        else if Self::bc_start(self.slice)
        {
            if let Err(pb) = self.drop_blocked_comment()
            {
                writeln!(stderr(), "Warning: A blocked comment beginning at {} is not closed", pb).unwrap();
            }
            self.drop_ignores();
        }
    }
    /// Drops a line comment
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("# test\n20");
    ///
    /// s.drop_line_comment();
    /// assert_eq!(s, Source { pos: Location { line: 2, column: 1 }, slice: "20" });
    /// ```
    pub fn drop_line_comment(&mut self)
    {
        if self.slice.starts_with("#") || self.slice.starts_with("＃")
        {
            let b = self.slice.chars().take_while(|&c| c != '\n').fold(0, |bb, c| bb + c.len_utf8());
            self.slice = &self.slice[(b + '\n'.len_utf8())..]; self.pos.advance_line();
        }
    }
    fn bc_start(s: &str) -> bool { s.starts_with("{#") || s.starts_with("{＃") || s.starts_with("｛#") || s.starts_with("｛＃") }
    fn bc_end  (s: &str) -> bool { s.starts_with("#}") || s.starts_with("＃}") || s.starts_with("#｝") || s.starts_with("＃｝") }
    /// Drops a blocked comment
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("{# test {# nest #} test #}1");
    ///
    /// s.drop_blocked_comment().unwrap();
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 27 }, slice: "1" });
    /// ```
    pub fn drop_blocked_comment(&mut self) -> Result<(), Location>
    {
        if Self::bc_start(self.slice)
        {
            let begin = self.pos.clone();
            self.split(self.slice.chars().nth(0).unwrap().len_utf8() + self.slice.chars().nth(1).unwrap().len_utf8(), 2);
            while !Self::bc_end(self.slice)
            {
                if Self::bc_start(self.slice) { self.drop_blocked_comment()?; }
                if self.slice.is_empty() { return Err(begin); }
                self.split(self.slice.chars().nth(0).unwrap().len_utf8(), 1);
            }
            self.split(self.slice.chars().nth(0).unwrap().len_utf8() + self.slice.chars().nth(1).unwrap().len_utf8(), 2);
        }
        Ok(())
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
    /// Strips a numeric ([0-9_]+(\.[0-9_]*)?(fuld){0,2})
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

    /// Strips an operator ([<>=!$%&~^-@+*/?|]+)
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("++=");
    /// 
    /// assert_eq!(s.operator(), Some(Token::Operator(Source { pos: Location::default(), slice: "++=" })));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 4 }, slice: "" });
    /// ```
    pub fn operator(&mut self) -> Option<Token<'s>>
    {
        let (c, b) = self.slice.chars().take_while(|&c| OPCLASS.iter().any(|&x| x == c)).fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
        if c > 0
        {
            let ss = self.split(b, c);
            if ss.slice == "=" || ss.slice == "＝" { Some(Token::Equal(ss.pos)) }
            else if ss.slice == "=>" || ss.slice == "＝＞" || ss.slice == "=＞" || ss.slice == "＝>" { Some(Token::Arrow(ss.pos)) }
            else { Some(Token::Operator(ss)) }
        }
        else { None }
    }
}
