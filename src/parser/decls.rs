//! Declaration Fragments

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDeclaration<'s> { pub pat: Expression<'s>, pub _type: Option<Type<'s>>, pub value: FullExpression<'s> }
impl<'s> ParserWithIndent<'s> for ValueDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse a value declaration
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// # use std::cell::RefCell;
    /// let (s, v) = (RefCell::new(Source::new("succ x: int -> _ = x + 1").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// let vd = ValueDeclaration::parse(&mut tokcache, 0).unwrap();
    /// assert_eq!(vd.pat[0].text(), Some("succ")); assert_eq!(vd.pat[1].text(), Some("x"));
    /// assert_eq!(vd._type.as_ref().unwrap()[0].basic_type(), Some(BType::Int));
    /// assert_eq!(vd._type.as_ref().unwrap()[1].text(), Some("->")); assert!(vd._type.as_ref().unwrap()[2].is_placeholder());
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, Self> where 's: 't
    {
        let pat = BreakParsing!(expr::expression(stream, leftmost, None));
        let _type = type_hint(stream, Leftmost::Exclusive(leftmost)).into_result_opt()?;
        if !Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) || !stream.current().is_equal()
        {
            return Failed(ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()));
        }
        stream.shift(); CheckLayout!(Leftmost::Exclusive(leftmost) => stream);
        let value = expr::full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(ValueDeclaration { pat, _type, value })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniformDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Type<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Option<Type<'s>>, pub value: Option<FullExpression<'s>> }
impl<'s> ParserWithIndent<'s> for UniformDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse an uniform declaration
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// # use std::cell::RefCell;
    /// let (s, v) = (RefCell::new(Source::new("uniform test: mf4").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// let ud = UniformDeclaration::parse(&mut tokcache, 0).unwrap();
    /// assert_eq!(ud, UniformDeclaration { location: Location::default(), name: Some("test"),
    ///     _type: Type(vec![TypeFragment::BasicType(Location { line: 1, column: 15 }, BType::FMat(4, 4))]) });
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(stream; TokenKind::Keyword(ref loc, Keyword::Uniform) => loc.clone());
        let (_, name) = name(stream, Leftmost::Exclusive(leftmost), true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        let _type = type_hint(stream, Leftmost::Exclusive(leftmost)).into_result(|| ParseError::Expecting(ExpectingKind::ItemDelimiter, stream.current().position()))?;
        Success(UniformDeclaration { location, name, _type })
    }
}
impl<'s> ParserWithIndent<'s> for ConstantDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse a constant declaration
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// # use std::cell::RefCell;
    /// let (s, v) = (RefCell::new(Source::new("constant psh1: f2 = (0, 0).yx").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// let cd = ConstantDeclaration::parse(&mut tokcache, 0).unwrap();
    /// assert_eq!(cd.location, Location::default()); assert_eq!(cd.name, Some("psh1"));
    /// assert_eq!(cd._type, Some(Type(vec![TypeFragment::BasicType(Location { line: 1, column: 16 }, BType::FVec(2))])));
    /// assert!(cd.value.is_some());
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(stream; TokenKind::Keyword(ref loc, Keyword::Constant) => loc);
        let (_, name) = name(stream, Leftmost::Exclusive(leftmost), true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        let _type = type_hint(stream, Leftmost::Exclusive(leftmost)).into_result_opt()?;
        let value = if Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) && stream.current().is_equal()
        {
            stream.shift();
            expr::full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position())).map(Some)?
        }
        else { None };
        Success(ConstantDeclaration { location: location.clone(), name, _type, value })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticOutput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: Option<BType>, pub expr: FullExpression<'s> }
impl<'s> ParserWithIndent<'s> for SemanticOutput<'s>
{
    type ResultTy = Self;
    /// Parse an output declaration from each shader stage
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// # use std::cell::RefCell;
    /// let (s, v) = (RefCell::new(Source::new("out _(SV_Position) = mvp * pos").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// let so = SemanticOutput::parse(&mut tokcache, 0).unwrap();
    /// assert_eq!(so.location, Location::default());
    /// assert_eq!(so.name, None); assert_eq!(so.semantics, Semantics::SVPosition); assert_eq!(so._type, None);
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(stream; TokenKind::Keyword(ref loc, Keyword::Out) => loc);
        let (_, name) = name(stream, Leftmost::Exclusive(leftmost), true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        TMatch!(Leftmost::Exclusive(leftmost) => stream; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese),
            |p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
        let semantics = TMatch!(stream; TokenKind::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
        TMatch!(Leftmost::Exclusive(leftmost) => stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
        let _type = type_note(stream, Leftmost::Exclusive(leftmost), true).into_result_opt()?.and_then(|v| v);
        TMatch!(Leftmost::Exclusive(leftmost) => stream; TokenKind::Equal(_), |p| ParseError::Expecting(ExpectingKind::ConcreteExpression, p));
        let expr = expr::full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(SemanticOutput { location: location.clone(), name, semantics, _type, expr })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticInput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: BType }
impl<'s> Parser<'s> for SemanticInput<'s>
{
    type ResultTy = Self;
    /// Parse an input declaration each shader stage
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// # use std::cell::RefCell;
    /// let (s, v) = (RefCell::new(Source::new("pos(POSITION): f4").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// assert_eq!(SemanticInput::parse(&mut tokcache), Success(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
    /// 
    /// // optional `in`
    /// let (s, v) = (RefCell::new(Source::new("in pos(POSITION): f4").into()), RefCell::new(Vec::new()));
    /// let mut tokcache = TokenizerCache::new(&v, &s);
    /// assert_eq!(SemanticInput::parse(&mut tokcache), Success(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Self> where 's: 't
    {
        let location1 = TMatch!(Optional: stream; TokenKind::Keyword(ref loc, Keyword::In) => loc);
        let (location, name) = match *stream.current()
        {
            TokenKind::Identifier(Source { slice, ref pos, .. }) => (location1.unwrap_or(pos), Some(slice)),
            TokenKind::Placeholder(ref pos) => (location1.unwrap_or(pos), None),
            _ if location1.is_none() => return NotConsumed,
            ref e => return Failed(ParseError::Expecting(ExpectingKind::Ident, e.position()))
        }; stream.shift();
        TMatch!(stream; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
        let semantics = TMatch!(stream; TokenKind::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
        TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
        let _type = type_note(stream, Leftmost::Exclusive(location.column), false)
            .into_result(|| ParseError::Expecting(ExpectingKind::ItemDelimiter, stream.current().position()))?.unwrap();
        Success(SemanticInput { location: location.clone(), name, semantics, _type })
    }
}

/// : (basic_type | _)
fn type_note<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost, allow_placeholder: bool) -> ParseResult<'t, Option<BType>>
{
    TMatchFirst!(leftmost => stream; TokenKind::ItemDescriptorDelimiter(_));
    if !leftmost.satisfy(stream.current(), true) { return Failed(ParseError::Expecting(ExpectingKind::Type, stream.current().position())); }
    match *stream.current()
    {
        TokenKind::BasicType(_, t) => { stream.shift(); Success(Some(t)) }, TokenKind::Placeholder(_) if allow_placeholder => { stream.shift(); Success(None) },
        ref e => Failed(ParseError::Expecting(ExpectingKind::Type, e.position()))
    }
}
/// : type
fn type_hint<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Type<'s>>
{
    TMatchFirst!(leftmost => stream; TokenKind::ItemDescriptorDelimiter(_));
    if !leftmost.into_exclusive().satisfy(stream.current(), false) { return Failed(ParseError::Expecting(ExpectingKind::Type, stream.current().position())); }
    user_type(stream, leftmost.num().unwrap_or(0), false).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position())).into()
}
