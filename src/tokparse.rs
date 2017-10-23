//! Tokenizer

use std::ops::{Add, AddAssign};
use std::io::prelude::*;
use std::io::stderr;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::cell::RefCell;
use std;

use regex::Regex;

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
    Operator(Source<'s>), Equal(Location), Arrow(Location), TyArrow(Location), BeginEnclosure(Location, EnclosureKind), EndEnclosure(Location, EnclosureKind),
    ListDelimiter(Location), StatementDelimiter(Location), ItemDescriptorDelimiter(Location), ObjectDescender(Location), EOF(Location), UnknownChar(Location), Placeholder(Location),

    Keyword(Location, Keyword), Semantics(Location, Semantics), BasicType(Location, BType)
}
impl<'s> Token<'s>
{
    pub fn position(&self) -> &Location
    {
        use Token::*;

        match *self
        {
            Identifier(Source { ref pos, .. }) | Numeric(Source { ref pos, .. }, _) | NumericF(Source { ref pos, .. }, _) | Operator(Source { ref pos, .. })
            | Equal(ref pos) | Arrow(ref pos) | TyArrow(ref pos) | BeginEnclosure(ref pos, _) | EndEnclosure(ref pos, _)
            | ListDelimiter(ref pos) | StatementDelimiter(ref pos) | ItemDescriptorDelimiter(ref pos) | ObjectDescender(ref pos) | EOF(ref pos) | UnknownChar(ref pos)
            | Placeholder(ref pos) | Keyword(ref pos, _) | Semantics(ref pos, _) | BasicType(ref pos, _) => pos
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericTy { Float, Double, Long, Unsigned, UnsignedLong }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnclosureKind { Parenthese, Bracket, Brace }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword
{
    Let, In, Out, Uniform, Constant, Set, Binding, VertexShader, FragmentShader, GeometryShader, HullShader, DomainShader,
    DepthTest, DepthWrite, StencilTest, Blend,
    // blend ops //
    Add, Sub,
    // blend factors //
    SrcColor, SrcAlpha, DestColor, DestAlpha, ConstantFactor
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Semantics { Position(usize), SVPosition, Texcoord(usize), Color(usize), SVTarget }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BType
{
    Bool, Uint, Int, Float, Double, FVec(u8), IVec(u8), UVec(u8), DVec(u8),
    FMat(u8, u8), DMat(u8, u8), IMat(u8, u8), UMat(u8, u8),
    Sampler(u8), Texture(u8)
}

pub struct TokenizerCache<'s: 't, 't> { counter: usize, cache: &'t RefCell<Vec<Token<'s>>>, source: &'t RefCell<Source<'s>> }
impl<'s: 't, 't> TokenizerCache<'s, 't>
{
    pub fn new(cache: &'t RefCell<Vec<Token<'s>>>, source: &'t RefCell<Source<'s>>) -> Self
    {
        TokenizerCache { counter: 0, cache, source }
    }
    pub fn save(&self) -> Self
    {
        TokenizerCache { counter: self.counter, cache: self.cache, source: self.source }
    }
    pub fn current(&self) -> &'t Token<'s>
    {
        while self.counter >= self.cache.borrow().len()
        {
            self.cache.borrow_mut().push(self.source.borrow_mut().next());
        }
        unsafe { &std::mem::transmute::<_, &'t Vec<_>>(&*self.cache.borrow())[self.counter] }
    }
    pub fn consume(&mut self) -> &mut Self { self.counter += 1; self }
    pub fn unshift(&mut self) -> &mut Self { self.counter = self.counter.saturating_sub(1); self }
    
    pub fn next(&mut self) -> &'t Token<'s>
    {
        let t = self.current(); self.consume(); t
    }
    pub fn prev(&mut self) -> &'t Token<'s> { self.unshift(); self.current() }

    pub fn drop_until<F: Fn(&'t Token<'s>) -> bool>(&mut self, predicate: F) -> &mut Self
    {
        while !predicate(self.current()) { self.consume(); }
        self
    }
}
impl<'s> Token<'s>
{
    pub fn is_list_delimiter(&self) -> bool { match self { &Token::ListDelimiter(_) => true, _ => false } }
    pub fn is_basic_type(&self) -> bool { match self { &Token::BasicType(_, _) => true, _ => false } }
}

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

    pub fn next(&mut self) -> Token<'s>
    {
        self.drop_ignores();
        
        if self.slice.is_empty() { Token::EOF(self.pos.clone()) }
        else
        {
            self.list_delimiter().or_else(|| self.stmt_delimiter()).or_else(|| self.item_desc_delimiter()).or_else(|| self.object_descender())
                .or_else(|| self.begin_enclosure()).or_else(|| self.end_enclosure())
                .or_else(|| self.numeric()).or_else(|| self.operator()).or_else(|| self.identifier())
                .unwrap_or(Token::UnknownChar(self.pos.clone()))
        }
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
            let s = self.split(b, c);

            lazy_static! {
                static ref RE_POSITION: Regex = Regex::new(r"^P(?i)osition(\d+)?").unwrap();
                static ref RE_TEXCOORD: Regex = Regex::new(r"^T(?i)excoord(\d+)?").unwrap();
                static ref RE_COLOR: Regex = Regex::new(r"^C(?i)olor(\d+)?").unwrap();
                static ref RE_SV_POSITION: Regex = Regex::new(r"^SV_P(?i)osition").unwrap();
                static ref RE_SV_TARGET: Regex = Regex::new(r"^SV_T(?i)arget").unwrap();
                static ref RE_FV: Regex = Regex::new(r"^f(\d)").unwrap();
                static ref RE_DV: Regex = Regex::new(r"^d(\d)").unwrap();
                static ref RE_IV: Regex = Regex::new(r"^i(\d)").unwrap();
                static ref RE_UV: Regex = Regex::new(r"^u(\d)").unwrap();
                static ref RE_MF: Regex = Regex::new(r"^mf(\d)(\d)?").unwrap();
                static ref RE_MD: Regex = Regex::new(r"^md(\d)(\d)?").unwrap();
                static ref RE_MI: Regex = Regex::new(r"^mi(\d)(\d)?").unwrap();
                static ref RE_MU: Regex = Regex::new(r"^mu(\d)(\d)?").unwrap();
                static ref RE_SAMPLER: Regex = Regex::new(r"^sampler(\d)").unwrap();
                static ref RE_TEXTURE: Regex = Regex::new(r"^texture(\d)").unwrap();
            }

            match s.slice
            {
                "_" => Some(Token::Placeholder(s.pos)),
                "let" => Some(Token::Keyword(s.pos, Keyword::Let)),
                "in" => Some(Token::Keyword(s.pos, Keyword::In)),
                "out" => Some(Token::Keyword(s.pos, Keyword::Out)),
                "uniform" => Some(Token::Keyword(s.pos, Keyword::Uniform)),
                "constant" => Some(Token::Keyword(s.pos, Keyword::Constant)),
                "set" => Some(Token::Keyword(s.pos, Keyword::Set)),
                "binding" => Some(Token::Keyword(s.pos, Keyword::Binding)),
                "VertexShader" => Some(Token::Keyword(s.pos, Keyword::VertexShader)),
                "FragmentShader" => Some(Token::Keyword(s.pos, Keyword::FragmentShader)),
                "GeometryShader" => Some(Token::Keyword(s.pos, Keyword::GeometryShader)),
                "HullShader" => Some(Token::Keyword(s.pos, Keyword::HullShader)),
                "DomainShader" => Some(Token::Keyword(s.pos, Keyword::DomainShader)),
                // RenderStates //
                "DepthTest" =>   Some(Token::Keyword(s.pos, Keyword::DepthTest)),
                "DepthWrite" =>  Some(Token::Keyword(s.pos, Keyword::DepthWrite)),
                "StencilTest" => Some(Token::Keyword(s.pos, Keyword::StencilTest)),
                "Blend" =>       Some(Token::Keyword(s.pos, Keyword::Blend)),
                // BlendOps //
                "Add" => Some(Token::Keyword(s.pos, Keyword::Add)),
                "Sub" => Some(Token::Keyword(s.pos, Keyword::Sub)),
                // BlendFactors //
                "SrcColor"  => Some(Token::Keyword(s.pos, Keyword::SrcColor)),
                "SrcAlpha"  => Some(Token::Keyword(s.pos, Keyword::SrcAlpha)),
                "DestColor" => Some(Token::Keyword(s.pos, Keyword::DestColor)),
                "DestAlpha" => Some(Token::Keyword(s.pos, Keyword::DestAlpha)),
                "ConstantFactor" => Some(Token::Keyword(s.pos, Keyword::ConstantFactor)),
                // BasicTypes //
                "bool" =>   Some(Token::BasicType(s.pos, BType::Bool)),
                "int" =>    Some(Token::BasicType(s.pos, BType::Int)),
                "uint" =>   Some(Token::BasicType(s.pos, BType::Uint)),
                "float" =>  Some(Token::BasicType(s.pos, BType::Float)),
                "double" => Some(Token::BasicType(s.pos, BType::Double)),
                _ => if let Some(c) = RE_FV.captures(s.slice) { Some(Token::BasicType(s.pos, BType::FVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_DV.captures(s.slice) { Some(Token::BasicType(s.pos, BType::DVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_IV.captures(s.slice) { Some(Token::BasicType(s.pos, BType::IVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_UV.captures(s.slice) { Some(Token::BasicType(s.pos, BType::UVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_MF.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(Token::BasicType(s.pos, BType::FMat(n, n2)))
                }
                else if let Some(c) = RE_MD.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(Token::BasicType(s.pos, BType::DMat(n, n2)))
                }
                else if let Some(c) = RE_MI.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(Token::BasicType(s.pos, BType::IMat(n, n2)))
                }
                else if let Some(c) = RE_MU.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(Token::BasicType(s.pos, BType::UMat(n, n2)))
                }
                else if let Some(c) = RE_SAMPLER.captures(s.slice) { Some(Token::BasicType(s.pos, BType::Sampler(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_TEXTURE.captures(s.slice) { Some(Token::BasicType(s.pos, BType::Texture(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_POSITION.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(Token::Semantics(s.pos, Semantics::Position(n)))
                }
                else if let Some(c) = RE_TEXCOORD.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(Token::Semantics(s.pos, Semantics::Texcoord(n)))
                }
                else if let Some(c) = RE_COLOR.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(Token::Semantics(s.pos, Semantics::Color(n)))
                }
                else if RE_SV_POSITION.is_match(s.slice) { Some(Token::Semantics(s.pos, Semantics::SVPosition)) }
                else if RE_SV_TARGET.is_match(s.slice) { Some(Token::Semantics(s.pos, Semantics::SVTarget)) }
                else { Some(Token::Identifier(s)) }
            }
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
        if !self.slice.starts_with(|c: char| c.is_digit(10)) { return None; }
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
            let ss = self.split(ipart_b, ipart_c);
            Some(Token::Numeric(ss, self.numeric_ty()))
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
            else if ss.slice == "->" || ss.slice == "ー＞" || ss.slice == "-＞" || ss.slice == "ー>" { Some(Token::TyArrow(ss.pos)) }
            else { Some(Token::Operator(ss)) }
        }
        else { None }
    }

    /// Strips a beginning of enclosure ([({\[])
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("{}");
    ///
    /// assert_eq!(s.begin_enclosure(), Some(Token::BeginEnclosure(Location::default(), EnclosureKind::Brace)));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 2 }, slice: "}" });
    /// ```
    pub fn begin_enclosure(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@'(') | Some(c@'（') => { let s = Token::BeginEnclosure(self.pos.clone(), EnclosureKind::Parenthese); self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'{') | Some(c@'｛') => { let s = Token::BeginEnclosure(self.pos.clone(), EnclosureKind::Brace);      self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'[') | Some(c@'［') => { let s = Token::BeginEnclosure(self.pos.clone(), EnclosureKind::Bracket);    self.split(c.len_utf8(), 1); Some(s) }
            _ => None
        }
    }
    /// Strips a ending of enclosure ([)}\]])
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("{}");
    ///
    /// s.begin_enclosure().unwrap();
    /// assert_eq!(s.end_enclosure(), Some(Token::EndEnclosure(Location { line: 1, column: 2 }, EnclosureKind::Brace)));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 3 }, slice: "" });
    /// ```
    pub fn end_enclosure(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@')') | Some(c@'）') => { let s = Token::EndEnclosure(self.pos.clone(), EnclosureKind::Parenthese); self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'}') | Some(c@'｝') => { let s = Token::EndEnclosure(self.pos.clone(), EnclosureKind::Brace);      self.split(c.len_utf8(), 1); Some(s) },
            Some(c@']') | Some(c@'］') => { let s = Token::EndEnclosure(self.pos.clone(), EnclosureKind::Bracket);    self.split(c.len_utf8(), 1); Some(s) }
            _ => None
        }
    }

    /// Strips a list delimiter (, or 、)
    pub fn list_delimiter(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@',') | Some(c@'、') | Some(c@'，') => Some(Token::ListDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a statement delimiter (; or 。)
    pub fn stmt_delimiter(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@';') | Some(c@'；') | Some(c@'。') => Some(Token::StatementDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a delimiter which is followed by item
    pub fn item_desc_delimiter(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@':') | Some(c@'：') => Some(Token::ItemDescriptorDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a period
    pub fn object_descender(&mut self) -> Option<Token<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@'.') | Some(c@'．') => Some(Token::ObjectDescender(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
}
