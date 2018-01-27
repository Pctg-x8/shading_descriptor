//! Declaration Fragments

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueDeclaration<'s>
{
    Prototype(ExprPatSynTree<'s>, FullTypeDesc<'s>),
    WithValue(ExprPatSynTree<'s>, Option<FullTypeDesc<'s>>, FullExpression<'s>)
}
impl<'s> ValueDeclaration<'s>
{
    pub fn pattern(&self) -> &ExprPatSynTree<'s>
    {
        match *self { ValueDeclaration::Prototype(ref p, _) | ValueDeclaration::WithValue(ref p, _, _) => p }
    }
    pub fn type_hint(&self) -> Option<&FullTypeDesc<'s>>
    {
        match *self { ValueDeclaration::Prototype(_, ref p) => Some(p), ValueDeclaration::WithValue(_, ref p, _) => p.as_ref() }
    }
    pub fn value(&self) -> Option<&FullExpression<'s>>
    {
        match *self { ValueDeclaration::Prototype(_, _) => None, ValueDeclaration::WithValue(_, _, ref p) => Some(p) }
    }
}
impl<'s> Parser<'s> for ValueDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse a value declaration
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("succ x: int -> _ = x + 1").strip_all();
    /// let vd = ValueDeclaration::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::NothingIncInc).unwrap();
    /// assert!(vd.type_hint().is_some());
    /// 
    /// // prototype
    /// let s = TokenizerState::from("prec x: int -> int").strip_all();
    /// let vd = ValueDeclaration::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::NothingIncInc).unwrap();
    /// assert!(vd.value().is_none());
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        let pat = BreakParsing!(ExprPatSynTree::parse(stream, leftmost));
        let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(pat.position().column)).into_exclusive();
        let _type = type_hint(stream, leftmost).into_result_opt()?;
        if shift_satisfy_leftmost(stream, leftmost, S::shift_equal).is_ok()
        {
            let value = FullExpression::parse(stream, leftmost).into_result(|| ParseError::expect_expr(stream.current().position()))?;
            Success(ValueDeclaration::WithValue(pat, _type, value))
        }
        else if let Some(th) = _type { Success(ValueDeclaration::Prototype(pat, th)) }
        else { Failed(ParseError::expect_type(stream.current().position())) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniformDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: FullTypeDesc<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Option<FullTypeDesc<'s>>, pub value: Option<FullExpression<'s>> }
impl<'s> Parser<'s> for UniformDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse an uniform declaration
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("uniform test: mf4").strip_all();
    /// let ud = UniformDeclaration::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::NothingInc).unwrap();
    /// assert_eq!(ud.name, Some("test"));
    /// assert_eq!(ud._type, FullTypeDesc { tree: TypeSynTree::Basic(Location { column: 15, line: 1 }, BType::FMat(4, 4)), quantified: Vec::new(), constraints: Vec::new() });
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(leftmost => stream; TokenKind::Keyword(ref loc, Keyword::Uniform) => loc.clone());
        let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(location.column)).into_exclusive();
        let (_, name) = name(stream, leftmost, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        let _type = type_hint(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::ItemDelimiter, stream.current().position()))?;
        Success(UniformDeclaration { location, name, _type })
    }
}
impl<'s> Parser<'s> for ConstantDeclaration<'s>
{
    type ResultTy = Self;
    /// Parse a constant declaration
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("constant psh1 = (0, 0).yx").strip_all();
    /// let cd = ConstantDeclaration::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::NothingInc).unwrap();
    /// assert_eq!(cd.name, Some("psh1")); assert!(cd._type.is_none()); assert!(cd.value.is_some());
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(leftmost => stream; TokenKind::Keyword(ref loc, Keyword::Constant) => loc);
        let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(location.column)).into_exclusive();
        let (_, name) = name(stream, leftmost, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        let _type = type_hint(stream, leftmost).into_result_opt()?;
        let value = if shift_satisfy_leftmost(stream, leftmost, S::shift_equal).is_ok()
        {
            FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position())).map(Some)?
        }
        else { None };
        Success(ConstantDeclaration { location: location.clone(), name, _type, value })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticOutput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: Option<BType>, pub expr: FullExpression<'s> }
impl<'s> Parser<'s> for SemanticOutput<'s>
{
    type ResultTy = Self;
    /// Parse an output declaration from each shader stage  
    /// `"out" ident par_semantics "=" full_expression`
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("out _(SV_Position) = mvp * pos").strip_all();
    /// let so = SemanticOutput::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::NothingInc).unwrap();
    /// assert_eq!((so.name, so.semantics, so._type), (None, Semantics::SVPosition, None));
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(leftmost => stream; TokenKind::Keyword(ref loc, Keyword::Out) => loc);
        let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(location.column)).into_exclusive();
        let (_, name) = name(stream, leftmost, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
        let semantics = par_semantics(stream, leftmost).into_result(|| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, stream.current().position()))?;
        let _type = type_note(stream, leftmost, true).into_result_opt()?.and_then(|v| v);
        shift_satisfy_leftmost(stream, leftmost, S::shift_equal).map_err(ParseError::expect_binding)?;
        let expr = FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(SemanticOutput { location: location.clone(), name, semantics, _type, expr })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticInput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: BType }
impl<'s> FreeParser<'s> for SemanticInput<'s>
{
    type ResultTy = Self;
    /// Parse an input declaration each shader stage  
    /// `"in"? ident par_semantics type_note?`
    /// # Example
    /// 
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("pos(POSITION): f4").strip_all();
    /// let si = SemanticInput::parse(&mut PreanalyzedTokenStream::from(&s[..])).expect("in shortest case");
    /// assert_eq!((si.name, si.semantics, si._type), (Some("pos"), Semantics::Position(0), BType::FVec(4)));
    /// // optional `in`
    /// let s = TokenizerState::from("in pos(POSITION): f4").strip_all();
    /// let si = SemanticInput::parse(&mut PreanalyzedTokenStream::from(&s[..])).expect("in explicit `in`");
    /// assert_eq!((si.name, si.semantics, si._type), (Some("pos"), Semantics::Position(0), BType::FVec(4)));
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
        let semantics = par_semantics(stream, Leftmost::Exclusive(location.column)).into_result(|| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, stream.current().position()))?;
        let _type = type_note(stream, Leftmost::Exclusive(location.column), false)
            .into_result(|| ParseError::Expecting(ExpectingKind::ItemDelimiter, stream.current().position()))?.unwrap();
        Success(SemanticInput { location: location.clone(), name, semantics, _type })
    }
}

/// "(" semantics ")"
fn par_semantics<'s: 't, 't, S: TokenStream<'s, 't>>(s: &mut S, leftmost: Leftmost) -> ParseResult<'t, Semantics>
{
    TMatchFirst!(leftmost => s; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese));
    let leftmost = leftmost.into_exclusive();
    let sem = shift_satisfy_leftmost(s, leftmost, S::shift_semantics).map_err(ParseError::expect_semantics)?;
    shift_satisfy_leftmost(s, leftmost, |s| s.shift_end_enclosure_of(EnclosureKind::Parenthese)).map_err(ParseError::expect_close_parenthese)?;
    Success(sem)
}
/// : (basic_type | _)
fn type_note<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost, allow_placeholder: bool) -> ParseResult<'t, Option<BType>>
{
    let lref = TMatchFirst!(leftmost => stream; TokenKind::ItemDescriptorDelimiter(ref p) => p);
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lref.column)).into_exclusive();
    if !leftmost.satisfy(stream.current()) { return Failed(ParseError::Expecting(ExpectingKind::Type, stream.current().position())); }
    match *stream.current()
    {
        TokenKind::BasicType(_, t) => { stream.shift(); Success(Some(t)) }, TokenKind::Placeholder(_) if allow_placeholder => { stream.shift(); Success(None) },
        ref e => Failed(ParseError::Expecting(ExpectingKind::Type, e.position()))
    }
}
/// : type
fn type_hint<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullTypeDesc<'s>>
{
    let lref = TMatchFirst!(leftmost => stream; TokenKind::ItemDescriptorDelimiter(ref p) => p);
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lref.column)).into_exclusive();
    if !leftmost.satisfy(stream.current()) { return Failed(ParseError::Expecting(ExpectingKind::Type, stream.current().position())); }
    FullTypeDesc::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position())).into()
}
