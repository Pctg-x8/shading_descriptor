//! Tokenizer

use std::ops::{Add, AddAssign};
use std::io::prelude::*;
use std::io::stderr;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::cell::RefCell;
use std;
use std::mem::discriminant;
use std::cmp::min;
use {Position, EqNoloc};

use regex::Regex;

/// 2なら1, 4なら2, 8なら3...
static mut TAB_ALIGNED_BITS: usize = 1;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location { pub line: usize, pub column: usize }
impl Default for Location { fn default() -> Self { Location { line: 1, column: 1 } } }
impl Add<usize> for Location { type Output = Self; fn add(mut self, other: usize) -> Self { self.column += other; self } }
impl AddAssign<usize> for Location { fn add_assign(&mut self, other: usize) { self.column += other; } }
impl Location
{
    pub const EMPTY: Self = Location { column: 0, line: 0 };
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Source<'s> { pub pos: Location, pub slice: &'s str }
impl<'s> Source<'s>
{
    pub fn new(s: &'s str) -> Self { Source { pos: Location::default(), slice: s } }
}
impl<'s> Position for Source<'s> { fn position(&self) -> &Location { &self.pos } }
/// Generated Text or ref to span
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenSource<'s: 't, 't> { Generated(String), GeneratedSlice(Source<'s>), Sliced(&'t Source<'s>) }
impl<'s: 't, 't> GenSource<'s, 't>
{
    pub fn text(&self) -> &str
    {
        match self
        {
            &GenSource::Generated(ref t) => t, &GenSource::Sliced(&Source { slice, .. }) => slice,
            &GenSource::GeneratedSlice(ref s) => &s.slice
        }
    }
    pub fn position(&self) -> &Location
    {
        match self
        {
            &GenSource::Generated(_) => &Location::EMPTY, &GenSource::Sliced(&Source { ref pos, .. }) => pos,
            &GenSource::GeneratedSlice(Source { ref pos, .. }) => pos
        }
    }
}
impl<'s: 't, 't> From<&'t Source<'s>> for GenSource<'s, 't> { fn from(s: &'t Source<'s>) -> Self { GenSource::Sliced(s) } }
impl<'s: 't, 't> From<String> for GenSource<'s, 't> { fn from(s: String) -> Self { GenSource::Generated(s) } }
impl<'s: 't, 't> Position for GenSource<'s, 't>
{
    fn position(&self) -> &Location
    {
        match *self { GenSource::Generated(_) => &Location::EMPTY, GenSource::Sliced(s) => s.position(), GenSource::GeneratedSlice(ref s) => s.position() }
    }
}
impl<'s> EqNoloc for Source<'s> { fn eq_nolocation(&self, other: &Self) -> bool { self.slice == other.slice } }
impl<'s: 't, 't> EqNoloc for GenSource<'s, 't> { fn eq_nolocation(&self, other: &Self) -> bool { self.text() == other.text() } }
/// Generatd Numeric or ref to span
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenNumeric<'s: 't, 't> { GeneratedInt(u64), Ref(&'t ::lambda::Numeric<'s>) }
impl<'s: 't, 't> From<u64> for GenNumeric<'s, 't> { fn from(v: u64) -> Self { GenNumeric::GeneratedInt(v) } }
impl<'s: 't, 't> From<&'t ::lambda::Numeric<'s>> for GenNumeric<'s, 't> { fn from(v: &'t ::lambda::Numeric<'s>) -> Self { GenNumeric::Ref(v) } }
impl<'s: 't, 't> Position for GenNumeric<'s, 't>
{
    fn position(&self) -> &Location
    {
        match *self { GenNumeric::Ref(s) => s.position(), GenNumeric::GeneratedInt(_) => &Location::EMPTY }
    }
}
impl<'s: 't, 't> EqNoloc for GenNumeric<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            GenNumeric::Ref(n) => if let GenNumeric::Ref(n2) = *other { n.eq_nolocation(n2) } else { false },
            GenNumeric::GeneratedInt(n) => if let GenNumeric::GeneratedInt(n2) = *other { n == n2 } else { false }
        }
    }
}
impl<'s: 't, 't> Display for GenNumeric<'s, 't>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        match *self
        {
            GenNumeric::GeneratedInt(n) => write!(fmt, "{}u64", n),
            GenNumeric::Ref(n) => n.text.slice.fmt(fmt)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'s> { pub line_head: bool, pub kind: TokenKind<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>),
    Operator(Source<'s>), Equal(Location), Arrow(Location), TyArrow(Location), BeginEnclosure(Location, EnclosureKind), EndEnclosure(Location, EnclosureKind),
    ListDelimiter(Location), StatementDelimiter(Location), ItemDescriptorDelimiter(Location), ObjectDescender(Location), EOF(Location), UnknownChar(Location), Placeholder(Location),
    WrappedOp(Source<'s>), InfixIdent(Source<'s>),

    Keyword(Location, Keyword), Semantics(Location, Semantics), BasicType(Location, BType), Backquote(Location)
}
impl<'s> TokenKind<'s>
{
    pub fn position(&self) -> &Location
    {
        use self::TokenKind::*;

        match *self
        {
            Identifier(Source { ref pos, .. }) | Numeric(Source { ref pos, .. }, _) | NumericF(Source { ref pos, .. }, _) | Operator(Source { ref pos, .. })
            | Equal(ref pos) | Arrow(ref pos) | TyArrow(ref pos) | BeginEnclosure(ref pos, _) | EndEnclosure(ref pos, _)
            | ListDelimiter(ref pos) | StatementDelimiter(ref pos) | ItemDescriptorDelimiter(ref pos) | ObjectDescender(ref pos) | EOF(ref pos) | UnknownChar(ref pos)
            | Placeholder(ref pos) | Keyword(ref pos, _) | Semantics(ref pos, _) | BasicType(ref pos, _)
            | WrappedOp(Source { ref pos, .. }) | InfixIdent(Source { ref pos, .. }) | Backquote(ref pos) => pos
        }
    }
    pub fn is_begin_enclosure_of(&self, kind: EnclosureKind) -> bool
    {
        match *self { TokenKind::BeginEnclosure(_, k) => k == kind, _ => false }
    }
    pub fn is_end_enclosure_of(&self, kind: EnclosureKind) -> bool
    {
        match *self { TokenKind::EndEnclosure(_, k) => k == kind, _ => false }
    }
}
/// typed container accessors
impl<'s> TokenKind<'s>
{
    pub fn keyword(&self)  -> Option<Keyword>     { match *self { TokenKind::Keyword(_, k)   => Some(k), _ => None } }
    pub fn operator(&self) -> Option<&Source<'s>> { match *self { TokenKind::Operator(ref s) => Some(s), _ => None } }
    pub fn identifier(&self) -> Option<&Source<'s>> { match *self { TokenKind::Identifier(ref s) => Some(s), _ => None } }
    pub fn numeric(&self) -> Option<&Source<'s>> { match *self { TokenKind::Numeric(ref s, _) => Some(s), _ => None } }
    pub fn infix_assoc(&self) -> bool { match self.keyword() { Some(Keyword::Infix) | Some(Keyword::Infixl) | Some(Keyword::Infixr) => true, _ => false } }
    pub fn is_list_delimiter(&self) -> bool { match *self { TokenKind::ListDelimiter(_) => true, _ => false } }
    pub fn is_item_delimiter(&self) -> bool { discriminant(self) == discriminant(&TokenKind::ItemDescriptorDelimiter(Location::default())) }
    pub fn is_basic_type(&self) -> bool { match *self { TokenKind::BasicType(_, _) => true, _ => false } }
    pub fn is_eof(&self) -> bool { discriminant(self) == discriminant(&TokenKind::EOF(Location::default())) }
    pub fn is_equal(&self) -> bool { discriminant(self) == discriminant(&TokenKind::Equal(Location::default())) }
    pub fn is_placeholder(&self) -> bool { discriminant(self) == discriminant(&TokenKind::Placeholder(Location::default())) }
    pub fn is_tyarrow(&self) -> bool { discriminant(self) == discriminant(&TokenKind::TyArrow(Location::default())) }
    pub fn is_text_period(&self) -> bool
    {
        match *self
        {
            TokenKind::ObjectDescender(_) | TokenKind::Operator(Source { slice: ".", .. }) | TokenKind::Operator(Source { slice: "．", .. }) => true,
            _ => false
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NumericTy { Float, Double, Long, Unsigned, UnsignedLong }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnclosureKind { Parenthese, Bracket, Brace }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword
{
    Let, In, Out, Uniform, Constant, Set, Binding, VertexShader, FragmentShader, GeometryShader, HullShader, DomainShader,
    DepthTest, DepthWrite, DepthBounds, StencilTest, StencilOps, StencilCompare, StencilWriteMask, Blend, Type, Data,
    If, Then, Else, Unless, Infixl, Infixr, Infix, Forall, Import, Qualified, As, Hiding, Class, Instance,
    // reserved but not used //
    Where, Do, Case, Of,
    // blend ops //
    Add, Sub,
    // blend factors //
    SrcColor, SrcAlpha, DestColor, DestAlpha,
    // Compare Ops //
    Always, Never, Equal, Inequal, Greater, Less, GreaterEq, LessEq,
    // Stencil Ops //
    Keep, Zero, Replace, IncrWrap, IncrClamp, DecrWrap, DecrClamp, Invert
}
/// セマンティクス
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Semantics { Position(usize), SVPosition, Texcoord(usize), Color(usize), SVTarget }
/// 基本型/組み込み型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BType
{
    Bool, Uint, Int, Float, Double, FVec(u8), IVec(u8), UVec(u8), DVec(u8),
    FMat(u8, u8), DMat(u8, u8), IMat(u8, u8), UMat(u8, u8),
    Sampler(u8), Texture(u8)
}
impl Display for Semantics
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        use self::Semantics::*;
        match *self
        {
            Position(index) => write!(fmt, "POSITION{}", index),
            SVPosition => write!(fmt, "SV_Position"),
            Texcoord(index) => write!(fmt, "TEXCOORD{}", index),
            Color(index) => write!(fmt, "COLOR{}", index),
            SVTarget => write!(fmt, "SV_Target")
        }
    }
}
impl Display for BType
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        use self::BType::*;
        match *self
        {
            Bool => write!(fmt, "bool"), Uint => write!(fmt, "uint"), Int => write!(fmt, "int"), Float => write!(fmt, "float"), Double => write!(fmt, "double"),
            FVec(n) => write!(fmt, "f{}", n), IVec(n) => write!(fmt, "i{}", n), UVec(n) => write!(fmt, "u{}", n), DVec(n) => write!(fmt, "d{}", n),
            FMat(n, m) => write!(fmt, "f{}{}", n, m), DMat(n, m) => write!(fmt, "d{}{}", n, m), IMat(n, m) => write!(fmt, "i{}{}", n, m), UMat(n, m) => write!(fmt, "u{}{}", n, m),
            Sampler(n) => write!(fmt, "sampler{}d", n), Texture(n) => write!(fmt, "texture{}d", n)
        }
    }
}
impl<'s> Display for Source<'s>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { Display::fmt(&self.slice, fmt) }
}
impl<'s: 't, 't> Display for GenSource<'s, 't>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { self.text().fmt(fmt) }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenizerState<'s> { pub src: Source<'s>, pub last_line: usize, pub cache: Vec<Token<'s>> }
impl<'s> From<Source<'s>> for TokenizerState<'s>
{
    fn from(src: Source<'s>) -> Self { TokenizerState { src, last_line: 0, cache: Vec::new() } }
}
/// Source shorthand
impl<'s> From<&'s str> for TokenizerState<'s>
{
    fn from(src: &'s str) -> Self { Self::from(Source::new(src)) }
}
/// The Token object must have an individual lifetime <'t> from self's lifetime
/// and required to have fixed address(e.g. boxed or immutable vector)
pub trait TokenStream<'s: 't, 't>
{
    /// get nth token(minimum impl)
    fn nth_token(&self, count: usize) -> &'t Token<'s>;
    /// get current token
    fn current_token(&self) -> &'t Token<'s> { self.nth_token(0) }
    /// get nth token kind
    fn nth(&self, count: usize) -> &'t TokenKind<'s> { &self.nth_token(count).kind }
    /// get current token kind
    fn current(&self) -> &'t TokenKind<'s> { self.nth(0) }
    /// whether the nth token is head of line
    fn nth_is_linehead(&self, count: usize) -> bool { self.nth_token(count).line_head }
    /// whether the current token is head of line
    fn on_linehead(&self) -> bool { self.nth_is_linehead(0) }
    /// shift n tokens(minimum impl)
    fn shift_n(&mut self, count: usize) -> &mut Self;
    /// shift a token
    fn shift(&mut self) -> &mut Self { self.shift_n(1) }
    /// unshift a token(minimum impl)
    fn unshift(&mut self) -> &mut Self;

    // extra shifts
    /// shift an object descender token, error if the next token is not ObjectDescender
    fn shift_object_descender(&mut self) -> Result<(), &'t Location>
    {
        if let &TokenKind::ObjectDescender(_) = self.current() { self.shift(); Ok(()) }
        else { Err(self.current().position()) }
    }
    /// shift an closing enclosure token, error if the next token is not EndEnclosure of specific kind
    fn shift_end_enclosure_of(&mut self, k: EnclosureKind) -> Result<(), &'t Location>
    {
        match self.current() { &TokenKind::EndEnclosure(_, kk) if kk == k => { self.shift(); Ok(()) }, p => Err(p.position()) }
    }
    /// shift a keyword token, error if the next token is not Keyword of specific kind
    fn shift_keyword(&mut self, k: Keyword) -> Result<&'t Location, &'t Location>
    {
        match self.current() { &TokenKind::Keyword(ref p, kk) if kk == k => { self.shift(); Ok(p) }, p => Err(p.position()) }
    }
    /// shift an equal token, error if the next token is not Equal
    fn shift_equal(&mut self) -> Result<&'t Location, &'t Location>
    {
        match self.current() { &TokenKind::Equal(ref p) => { self.shift(); Ok(p) }, p => Err(p.position()) }
    }
    /// shift an arrow token, error if the next token is not Arrow
    fn shift_arrow(&mut self) -> Result<&'t Location, &'t Location>
    {
        match self.current() { &TokenKind::TyArrow(ref p) => { self.shift(); Ok(p) }, p => Err(p.position()) }
    }
    /// shift a placeholder token, error if the next token is not Placeholder
    fn shift_placeholder(&mut self) -> Result<&'t Location, &'t Location>
    {
        match self.current() { &TokenKind::Placeholder(ref p) => { self.shift(); Ok(p) }, p => Err(p.position()) }
    }
    /// shift a list delimiter token, error if the next token is not ListDelimiter
    fn shift_list_delimiter(&mut self) -> Result<(), &'t Location>
    {
        match self.current() { &TokenKind::ListDelimiter(_) => { self.shift(); Ok(()) }, p => Err(p.position()) }
    }
    /// shift an identifier, error if the next token is not Identifier
    fn shift_identifier(&mut self) -> Result<&'t Source<'s>, &'t Location>
    {
        match self.current() { &TokenKind::Identifier(ref s) => { self.shift(); Ok(s) }, p => Err(p.position()) }
    }
    /// shift a semantics, error if the next tokne is not Semantics
    fn shift_semantics(&mut self) -> Result<Semantics, &'t Location>
    {
        match self.current() { &TokenKind::Semantics(_, s) => { self.shift(); Ok(s) }, p => Err(p.position()) }
    }

    /// drop tokens until satisfying a predicate
    fn drop_until<F: Fn(&'t Token<'s>) -> bool>(&mut self, predicate: F) -> &mut Self
    {
        while !predicate(self.current_token()) { self.shift(); } self
    }
    /// shift tokens while satisfying a predicate
    fn shift_while<F: Fn(&'t Token<'s>) -> bool>(&mut self, predicate: F) -> &mut Self
    {
        while predicate(self.current_token()) { self.shift(); } self
    }
    /// drop tokens on same line
    fn drop_line(&mut self) -> &mut Self
    {
        let inl = self.current().position().line;
        self.drop_until(|t| t.kind.position().line != inl)
    }

    /// Low-cost stream state
    type State: Copy;
    /// save the current stream state
    fn save(&self) -> Self::State;
    /// restore this stream state
    fn restore(&mut self, state: Self::State) -> &mut Self;
}
pub struct TokenizerCache<'s: 't, 't> { counter: usize, cache: &'t RefCell<Vec<Box<Token<'s>>>>, source: &'t RefCell<TokenizerState<'s>> }
impl<'s: 't, 't> TokenStream<'s, 't> for TokenizerCache<'s, 't>
{
    fn nth_token(&self, count: usize) -> &'t Token<'s>
    {
        self.fill(self.counter + count);
        unsafe
        {
            let v = std::mem::transmute::<_, &'t Vec<Box<_>>>(&*self.cache.borrow());
            &*v[self.counter + count]
        }
    }
    fn shift_n(&mut self, count: usize) -> &mut Self { self.counter += count; self }
    fn unshift(&mut self) -> &mut Self { self.counter = self.counter.saturating_sub(1); self }

    type State = usize;
    fn save(&self) -> usize { self.counter }
    fn restore(&mut self, state: usize) -> &mut Self { self.counter = state; self }
}
impl<'s: 't, 't> TokenizerCache<'s, 't>
{
    pub fn new(cache: &'t RefCell<Vec<Box<Token<'s>>>>, source: &'t RefCell<TokenizerState<'s>>) -> Self
    {
        TokenizerCache { counter: 0, cache, source }
    }
    fn fill(&self, to: usize)
    {
        while to >= self.cache.borrow().len()
        {
            let mut b = self.cache.borrow_mut();
            b.place_back() <- box self.source.borrow_mut().next();
        }
    }
}
pub struct PreanalyzedTokenStream<'s: 't, 't>(usize, &'t [Token<'s>]);
impl<'s: 't, 't> TokenStream<'s, 't> for PreanalyzedTokenStream<'s, 't>
{
    fn nth_token(&self, count: usize) -> &'t Token<'s> { &self.1[min(self.0 + count, self.1.len() - 1)] }
    fn shift_n(&mut self, count: usize) -> &mut Self { self.0 = min(self.0 + count, self.1.len() - 1); self }
    fn unshift(&mut self) -> &mut Self { self.0 = self.0.saturating_sub(1); self }

    type State = usize;
    fn save(&self) -> usize { self.0 }
    fn restore(&mut self, state: usize) -> &mut Self { self.0 = state; self }
}
impl<'s: 't, 't> From<&'t [Token<'s>]> for PreanalyzedTokenStream<'s, 't>
{
    fn from(tokens: &'t [Token<'s>]) -> Self { PreanalyzedTokenStream(0, tokens) }
}
impl<'s: 't, 't> PreanalyzedTokenStream<'s, 't>
{
    /// Whether all tokens are consumed
    pub fn is_empty(&self) -> bool { self.0 >= self.1.len() }
}

const OPCLASS: &'static [char] = &['<', '＜', '>', '＞', '=', '＝', '!', '！', '$', '＄', '%', '％', '&', '＆', '~', '～', '^', '＾', '-', 'ー',
    '@', '＠', '+', '＋', '*', '＊', '/', '／', '・', '?', '？', '|', '｜', '∥', '―', '\\', '￥', '＼'];

impl<'s> TokenizerState<'s>
{
    fn take_one(&mut self) -> Token<'s>
    {
        let visual_separated = self.src.drop_ignores();
        
        if self.src.slice.is_empty() { Token { kind: TokenKind::EOF(self.src.pos.clone()), line_head: self.src.pos.line != self.last_line } }
        else
        {
            let tk = self.src.list_delimiter().or_else(|| self.src.stmt_delimiter()).or_else(|| self.src.item_desc_delimiter()).or_else(|| self.src.object_descender(visual_separated))
                .or_else(|| self.src.begin_enclosure()).or_else(|| self.src.end_enclosure()).or_else(|| self.src.backquote())
                .or_else(|| self.src.numeric()).or_else(|| self.src.operator()).or_else(|| self.src.identifier())
                .unwrap_or(TokenKind::UnknownChar(self.src.pos.clone()));
            let line_head = tk.position().line != self.last_line;
            self.last_line = tk.position().line;
            Token { line_head, kind: tk }
        }
    }
    fn next_one(&mut self) -> Token<'s>
    {
        if let Some(t) = self.cache.pop() { t } else { self.take_one() }
    }
    pub fn next(&mut self) -> Token<'s>
    {
        // Combine multiple tokens
        let s1 = self.next_one();
        match s1.kind
        {
            TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) =>
            {
                let s2 = self.next_one();
                let s2op = if let TokenKind::Operator(ref s) = s2.kind { s.clone() } else { self.cache.push(s2); return s1; };
                let s3 = self.next_one();
                if let TokenKind::EndEnclosure(_, EnclosureKind::Parenthese) = s3.kind
                {
                    Token { kind: TokenKind::WrappedOp(s2op), line_head: s1.line_head }
                }
                else { self.cache.push(s3); self.cache.push(s2); s1 }
            },
            TokenKind::Backquote(_) =>
            {
                let s2 = self.next_one();
                let s2ident = if let TokenKind::Identifier(ref s) = s2.kind { s.clone() } else { self.cache.push(s2); return s1; };
                let s3 = self.next_one();
                if let &TokenKind::Backquote(_) = &s3.kind
                {
                    Token { kind: TokenKind::InfixIdent(s2ident), line_head: s1.line_head }
                }
                else { self.cache.push(s3); self.cache.push(s2); s1 }
            },
            _ => s1
        }
    }
    /// Tokenize entire contents
    ///
    /// ## Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let sv = TokenizerState::from("out a = 2").strip_all();
    /// assert_eq!(sv[0].kind.keyword(), Some(Keyword::Out));
    /// assert_eq!(sv[1].kind.identifier().map(|x| x.slice), Some("a"));
    /// assert!   (sv[2].kind.is_equal());
    /// assert_eq!(sv[3].kind.numeric().map(|x| x.slice), Some("2"));
    /// ```
    pub fn strip_all(mut self) -> Vec<Token<'s>>
    {
        let mut v = Vec::new();
        loop
        {
            v.place_back() <- self.next();
            if v.last().unwrap().kind.is_eof() { return v; }
        }
    }
}
impl<'s> Source<'s>
{
    fn split(&mut self, at: usize, charat: usize) -> Self
    {
        let sf = &self.slice[..at]; self.slice = &self.slice[at..];
        let pf = self.pos.clone(); self.pos += charat;
        Source { pos: pf, slice: sf }
    }

    /// Drops ignored characters and comments
    /// ## Returns
    /// true if spaces are found
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let mut s = Source::new("{# drop #}#test 2\n\t8");
    ///
    /// s.drop_ignores();
    /// assert_eq!(s, Source { pos: Location { line: 2, column: 3 }, slice: "8" });
    /// ```
    pub fn drop_ignores(&mut self) -> bool
    {
        if self.slice.starts_with("\n")
        {
            self.slice = &self.slice['\n'.len_utf8()..]; self.pos.advance_line(); self.drop_ignores(); true
        }
        else if self.slice.starts_with("\t")
        {
            self.slice = &self.slice['\t'.len_utf8()..]; self.pos.advance_tab(); self.drop_ignores(); true
        }
        else if self.slice.starts_with(char::is_whitespace)
        {
            self.slice = &self.slice[self.slice.chars().next().unwrap().len_utf8()..];
            self.pos += 1; self.drop_ignores(); true
        }
        else if self.slice.starts_with("#") { self.drop_line_comment(); self.drop_ignores() }
        else if Self::bc_start(self.slice)
        {
            if let Err(pb) = self.drop_blocked_comment()
            {
                writeln!(stderr(), "Warning: A blocked comment beginning at {} is not closed", pb).unwrap();
            }
            self.drop_ignores()
        }
        else { false }
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
    /// assert_eq!(s.identifier(), Some(TokenKind::Identifier(Source { pos: Location::default(), slice: "ident" })));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 6 }, slice: "(" });
    /// ```
    pub fn identifier(&mut self) -> Option<TokenKind<'s>>
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
                "_" => Some(TokenKind::Placeholder(s.pos)),
                "let" => Some(TokenKind::Keyword(s.pos, Keyword::Let)),
                "where" => Some(TokenKind::Keyword(s.pos, Keyword::Where)),
                "do" => Some(TokenKind::Keyword(s.pos, Keyword::Do)),
                "case" => Some(TokenKind::Keyword(s.pos, Keyword::Case)),
                "of" => Some(TokenKind::Keyword(s.pos, Keyword::Of)),
                "if" => Some(TokenKind::Keyword(s.pos, Keyword::If)),
                "then" => Some(TokenKind::Keyword(s.pos, Keyword::Then)),
                "else" => Some(TokenKind::Keyword(s.pos, Keyword::Else)),
                "unless" => Some(TokenKind::Keyword(s.pos, Keyword::Unless)),
                "in" => Some(TokenKind::Keyword(s.pos, Keyword::In)),
                "out" => Some(TokenKind::Keyword(s.pos, Keyword::Out)),
                "uniform" => Some(TokenKind::Keyword(s.pos, Keyword::Uniform)),
                "constant" => Some(TokenKind::Keyword(s.pos, Keyword::Constant)),
                "type" => Some(TokenKind::Keyword(s.pos, Keyword::Type)),
                "data" => Some(TokenKind::Keyword(s.pos, Keyword::Data)),
                "infix" => Some(TokenKind::Keyword(s.pos, Keyword::Infix)),
                "infixl" => Some(TokenKind::Keyword(s.pos, Keyword::Infixl)),
                "infixr" => Some(TokenKind::Keyword(s.pos, Keyword::Infixr)),
                "forall" => Some(TokenKind::Keyword(s.pos, Keyword::Forall)),
                "import" => Some(TokenKind::Keyword(s.pos, Keyword::Import)),
                "qualified" => Some(TokenKind::Keyword(s.pos, Keyword::Qualified)),
                "as" => Some(TokenKind::Keyword(s.pos, Keyword::As)),
                "hiding" => Some(TokenKind::Keyword(s.pos, Keyword::Hiding)),
                "class" => Some(TokenKind::Keyword(s.pos, Keyword::Class)),
                "instance" => Some(TokenKind::Keyword(s.pos, Keyword::Instance)),
                "VertexShader" => Some(TokenKind::Keyword(s.pos, Keyword::VertexShader)),
                "FragmentShader" => Some(TokenKind::Keyword(s.pos, Keyword::FragmentShader)),
                "GeometryShader" => Some(TokenKind::Keyword(s.pos, Keyword::GeometryShader)),
                "HullShader" => Some(TokenKind::Keyword(s.pos, Keyword::HullShader)),
                "DomainShader" => Some(TokenKind::Keyword(s.pos, Keyword::DomainShader)),
                // RenderStates //
                "DepthTest"   => Some(TokenKind::Keyword(s.pos, Keyword::DepthTest)),
                "DepthWrite"  => Some(TokenKind::Keyword(s.pos, Keyword::DepthWrite)),
                "DepthBounds" => Some(TokenKind::Keyword(s.pos, Keyword::DepthBounds)),
                "StencilTest" => Some(TokenKind::Keyword(s.pos, Keyword::StencilTest)),
                "StencilOps"  => Some(TokenKind::Keyword(s.pos, Keyword::StencilOps)),
                "StencilCompare"   => Some(TokenKind::Keyword(s.pos, Keyword::StencilCompare)),
                "StencilWriteMask" => Some(TokenKind::Keyword(s.pos, Keyword::StencilWriteMask)),
                "Blend"       => Some(TokenKind::Keyword(s.pos, Keyword::Blend)),
                // BlendOps //
                "Add" => Some(TokenKind::Keyword(s.pos, Keyword::Add)),
                "Sub" => Some(TokenKind::Keyword(s.pos, Keyword::Sub)),
                // BlendFactors //
                "SrcColor"  => Some(TokenKind::Keyword(s.pos, Keyword::SrcColor)),
                "SrcAlpha"  => Some(TokenKind::Keyword(s.pos, Keyword::SrcAlpha)),
                "DestColor" => Some(TokenKind::Keyword(s.pos, Keyword::DestColor)),
                "DestAlpha" => Some(TokenKind::Keyword(s.pos, Keyword::DestAlpha)),
                // CompareOps //
                "Always"    => Some(TokenKind::Keyword(s.pos, Keyword::Always)),
                "Never"     => Some(TokenKind::Keyword(s.pos, Keyword::Never)),
                "Equal"     => Some(TokenKind::Keyword(s.pos, Keyword::Equal)),
                "Inequal"   => Some(TokenKind::Keyword(s.pos, Keyword::Inequal)),
                "Greater"   => Some(TokenKind::Keyword(s.pos, Keyword::Greater)),
                "Less"      => Some(TokenKind::Keyword(s.pos, Keyword::Less)),
                "GreaterEq" => Some(TokenKind::Keyword(s.pos, Keyword::GreaterEq)),
                "LessEq"    => Some(TokenKind::Keyword(s.pos, Keyword::LessEq)),
                // StencilOps //
                "Keep" => Some(TokenKind::Keyword(s.pos, Keyword::Keep)),
                "Zero" | "Clear" => Some(TokenKind::Keyword(s.pos, Keyword::Zero)),
                "Replace" => Some(TokenKind::Keyword(s.pos, Keyword::Replace)),
                "IncrementWrap" => Some(TokenKind::Keyword(s.pos, Keyword::IncrWrap)),
                "IncrementClamp" | "IncrementSaturate" => Some(TokenKind::Keyword(s.pos, Keyword::IncrClamp)),
                "DecrementWrap" => Some(TokenKind::Keyword(s.pos, Keyword::DecrWrap)),
                "DecrementClamp" | "DecrementSaturate" => Some(TokenKind::Keyword(s.pos, Keyword::DecrClamp)),
                "Invert" => Some(TokenKind::Keyword(s.pos, Keyword::Invert)),
                // BasicTypes //
                "bool" =>   Some(TokenKind::BasicType(s.pos, BType::Bool)),
                "int" =>    Some(TokenKind::BasicType(s.pos, BType::Int)),
                "uint" =>   Some(TokenKind::BasicType(s.pos, BType::Uint)),
                "float" =>  Some(TokenKind::BasicType(s.pos, BType::Float)),
                "double" => Some(TokenKind::BasicType(s.pos, BType::Double)),
                _ => if let Some(c) = RE_FV.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::FVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_DV.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::DVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_IV.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::IVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_UV.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::UVec(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_MF.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(TokenKind::BasicType(s.pos, BType::FMat(n, n2)))
                }
                else if let Some(c) = RE_MD.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(TokenKind::BasicType(s.pos, BType::DMat(n, n2)))
                }
                else if let Some(c) = RE_MI.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(TokenKind::BasicType(s.pos, BType::IMat(n, n2)))
                }
                else if let Some(c) = RE_MU.captures(s.slice)
                {
                    let n = c[1].parse().unwrap(); let n2 = c.get(2).map(|s| s.as_str().parse().unwrap()).unwrap_or(n);
                    Some(TokenKind::BasicType(s.pos, BType::UMat(n, n2)))
                }
                else if let Some(c) = RE_SAMPLER.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::Sampler(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_TEXTURE.captures(s.slice) { Some(TokenKind::BasicType(s.pos, BType::Texture(c[1].parse().unwrap()))) }
                else if let Some(c) = RE_POSITION.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(TokenKind::Semantics(s.pos, Semantics::Position(n)))
                }
                else if let Some(c) = RE_TEXCOORD.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(TokenKind::Semantics(s.pos, Semantics::Texcoord(n)))
                }
                else if let Some(c) = RE_COLOR.captures(s.slice)
                {
                    let n = c.get(1).map(|s| s.as_str().parse().unwrap()).unwrap_or(0);
                    Some(TokenKind::Semantics(s.pos, Semantics::Color(n)))
                }
                else if RE_SV_POSITION.is_match(s.slice) { Some(TokenKind::Semantics(s.pos, Semantics::SVPosition)) }
                else if RE_SV_TARGET.is_match(s.slice) { Some(TokenKind::Semantics(s.pos, Semantics::SVTarget)) }
                else { Some(TokenKind::Identifier(s)) }
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
    /// assert_eq!(s.numeric(), Some(TokenKind::NumericF(Source { pos: Location::default(), slice: "0.33" }, Some(NumericTy::Float))));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 6 }, slice: "4" });
    /// ```
    pub fn numeric(&mut self) -> Option<TokenKind<'s>>
    {
        if !self.slice.starts_with(|c: char| c.is_digit(10)) { return None; }
        let (ipart_c, ipart_b) = self.slice.chars().take_while(|&c| c.is_digit(10) || c == '_').fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
        if ipart_c <= 0 { return None; }
        let s_rest = &self.slice[ipart_b..];
        if s_rest.starts_with(".") && s_rest.chars().nth(1).map(|c| c.is_digit(10)).unwrap_or(false)
        {
            let (fpart_c, fpart_b) = s_rest.chars().skip(1).take_while(|&c| c.is_digit(10) || c == '_').fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
            let ss = self.split(ipart_b + 1 + fpart_b, ipart_c + 1 + fpart_c);
            Some(TokenKind::NumericF(ss, self.numeric_ty()))
        }
        else
        {
            let ss = self.split(ipart_b, ipart_c);
            Some(TokenKind::Numeric(ss, self.numeric_ty()))
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
    /// assert_eq!(s.operator(), Some(TokenKind::Operator(Source { pos: Location::default(), slice: "++=" })));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 4 }, slice: "" });
    /// ```
    pub fn operator(&mut self) -> Option<TokenKind<'s>>
    {
        let (c, b) = self.slice.chars().take_while(|&c| OPCLASS.iter().any(|&x| x == c)).fold((0, 0), |(cc, bb), c| (cc + 1, bb + c.len_utf8()));
        if c > 0
        {
            let ss = self.split(b, c);
            if ss.slice == "=" || ss.slice == "＝" { Some(TokenKind::Equal(ss.pos)) }
            else if ss.slice == "=>" || ss.slice == "＝＞" || ss.slice == "=＞" || ss.slice == "＝>" { Some(TokenKind::Arrow(ss.pos)) }
            else if ss.slice == "->" || ss.slice == "ー＞" || ss.slice == "-＞" || ss.slice == "ー>" { Some(TokenKind::TyArrow(ss.pos)) }
            else { Some(TokenKind::Operator(ss)) }
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
    /// assert_eq!(s.begin_enclosure(), Some(TokenKind::BeginEnclosure(Location::default(), EnclosureKind::Brace)));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 2 }, slice: "}" });
    /// ```
    pub fn begin_enclosure(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@'(') | Some(c@'（') => { let s = TokenKind::BeginEnclosure(self.pos.clone(), EnclosureKind::Parenthese); self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'{') | Some(c@'｛') => { let s = TokenKind::BeginEnclosure(self.pos.clone(), EnclosureKind::Brace);      self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'[') | Some(c@'［') => { let s = TokenKind::BeginEnclosure(self.pos.clone(), EnclosureKind::Bracket);    self.split(c.len_utf8(), 1); Some(s) }
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
    /// assert_eq!(s.end_enclosure(), Some(TokenKind::EndEnclosure(Location { line: 1, column: 2 }, EnclosureKind::Brace)));
    /// assert_eq!(s, Source { pos: Location { line: 1, column: 3 }, slice: "" });
    /// ```
    pub fn end_enclosure(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@')') | Some(c@'）') => { let s = TokenKind::EndEnclosure(self.pos.clone(), EnclosureKind::Parenthese); self.split(c.len_utf8(), 1); Some(s) },
            Some(c@'}') | Some(c@'｝') => { let s = TokenKind::EndEnclosure(self.pos.clone(), EnclosureKind::Brace);      self.split(c.len_utf8(), 1); Some(s) },
            Some(c@']') | Some(c@'］') => { let s = TokenKind::EndEnclosure(self.pos.clone(), EnclosureKind::Bracket);    self.split(c.len_utf8(), 1); Some(s) }
            _ => None
        }
    }

    /// Strips a list delimiter (, or 、)
    pub fn list_delimiter(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@',') | Some(c@'、') | Some(c@'，') => Some(TokenKind::ListDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a statement delimiter (; or 。)
    pub fn stmt_delimiter(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@';') | Some(c@'；') | Some(c@'。') => Some(TokenKind::StatementDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a delimiter which is followed by item
    pub fn item_desc_delimiter(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@':') | Some(c@'：') => Some(TokenKind::ItemDescriptorDelimiter(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
    /// Strips a period
    pub fn object_descender(&mut self, vsep: bool) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@'.') | Some(c@'．') => Some(if vsep { TokenKind::Operator(self.split(c.len_utf8(), 1)) } else { TokenKind::ObjectDescender(self.split(c.len_utf8(), 1).pos) }),
            _ => None
        }
    }
    /// Backquote(Infixing identifier)
    pub fn backquote(&mut self) -> Option<TokenKind<'s>>
    {
        match self.slice.chars().next()
        {
            Some(c@'`') | Some(c@'‘') => Some(TokenKind::Backquote(self.split(c.len_utf8(), 1).pos)),
            _ => None
        }
    }
}

// Text Conversion //
impl<'s> TokenKind<'s>
{
    pub fn as_f32(&self) -> f32
    {
        match *self
        {
            TokenKind::Numeric(Source { slice, .. }, _) | TokenKind::NumericF(Source { slice, .. }, _) => slice.parse().unwrap(),
            _ => unreachable!()
        }
    }
    pub fn as_usize(&self) -> usize
    {
        match *self
        {
            TokenKind::Numeric(Source { slice, .. }, _) | TokenKind::NumericF(Source { slice, .. }, _) => slice.parse().unwrap(),
            _ => unreachable!()
        }
    }
    pub fn match1(&self) -> bool
    {
        match *self
        {
            TokenKind::Numeric(Source { slice, .. }, Some(NumericTy::Long)) | TokenKind::Numeric(Source { slice, .. }, Some(NumericTy::UnsignedLong))
            | TokenKind::NumericF(Source { slice, .. }, Some(NumericTy::Long)) | TokenKind::NumericF(Source { slice, .. }, Some(NumericTy::UnsignedLong)) => slice.parse::<u64>() == Ok(1),
            TokenKind::Numeric(Source { slice, .. }, _) => slice.parse::<usize>() == Ok(1),
            TokenKind::NumericF(Source { slice, .. }, Some(NumericTy::Double)) => slice.parse::<f64>() == Ok(1.0),
            TokenKind::NumericF(Source { slice, .. }, _) => slice.parse::<f32>() == Ok(1.0),
            _ => false
        }
    }
    pub fn match0(&self) -> bool
    {
        match *self
        {
            TokenKind::Numeric(Source { slice, .. }, t) => match t
            {
                Some(NumericTy::UnsignedLong) | Some(NumericTy::Long) => slice.parse::<u64>() == Ok(0),
                Some(NumericTy::Double) => slice.parse::<f64>() == Ok(0.0),
                Some(NumericTy::Float) => slice.parse::<f32>() == Ok(0.0),
                _ => slice.parse::<usize>() == Ok(0)
            },
            TokenKind::NumericF(Source { slice, .. }, t) => match t
            {
                Some(NumericTy::UnsignedLong) | Some(NumericTy::Long) => slice.parse::<u64>() == Ok(0),
                Some(NumericTy::Float) => slice.parse::<f32>() == Ok(0.0),
                _ => slice.parse::<f64>() == Ok(0.0)
            },
            _ => false
        }
    }
}
