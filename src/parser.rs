//! Syntax Parser

use tokparse::*;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::error::Error;
use expression_parser::*;
use typeparser::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ExpectingKind
{
	ItemDelimiter, Semantics, Type, ShaderStage, OutDef, UniformDef, ConstantDef, Ident, ValueDecl,
	ConcreteExpression, Expression, Pattern
}
#[derive(Clone, PartialEq, Eq)]
pub enum ParseError<'t>
{
	ExpectingIdentNextIn(&'t Location), ExpectingIdentOrIn(&'t Location), Expecting(ExpectingKind, &'t Location),
	ExpectingListDelimiterOrParentheseClosing(&'t Location),
	ExpectingEnclosed(ExpectingKind, EnclosureKind, &'t Location), ExpectingOpen(EnclosureKind, &'t Location), ExpectingClose(EnclosureKind, &'t Location),
	UnexpectedClose(EnclosureKind, &'t Location), InvalidExpressionFragment(&'t Location)
}
impl<'t> Debug for ParseError<'t>
{
	fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{} at {}", self.description(), self.position()) }
}
impl<'t> Display for ParseError<'t>
{
	fn fmt(&self, fmt: &mut Formatter) -> FmtResult { Debug::fmt(self, fmt) }
}
impl<'t> ParseError<'t>
{
	fn position(&self) -> &'t Location
	{
		use self::ParseError::*;
		match *self
		{
			ExpectingIdentNextIn(p) | ExpectingIdentOrIn(p) | Expecting(_, p)  | ExpectingEnclosed(_, _, p) | ExpectingClose(_, p)
			| ExpectingListDelimiterOrParentheseClosing(p) | ExpectingOpen(_, p) | UnexpectedClose(_, p) | InvalidExpressionFragment(p) => p
		}
	}
}
impl<'t> Error for ParseError<'t>
{
	fn description(&self) -> &str
	{
		match *self
		{
			ParseError::ExpectingIdentNextIn(_) => "Expecting an `Identifier` next of an `in`",
			ParseError::ExpectingIdentOrIn(_) => "Expecting an `Identifier` or an `in`",
			ParseError::Expecting(ExpectingKind::ItemDelimiter, _) => "Expecting a `:`",
			ParseError::Expecting(ExpectingKind::Type, _) => "Expecting a type",
			ParseError::Expecting(ExpectingKind::ShaderStage, _) => "Expecting any of shader stage(VertexShader, FragmentShader, GeometryShader, HullShader or DomainShader)",
			ParseError::Expecting(ExpectingKind::OutDef, _) => "Expecting `out`",
			ParseError::Expecting(ExpectingKind::UniformDef, _) => "Expecting `uniform`",
			ParseError::Expecting(ExpectingKind::ConstantDef, _) => "Expecting `constant`",
			ParseError::Expecting(ExpectingKind::Ident, _) => "Expecting an identifier",
			ParseError::Expecting(ExpectingKind::ConcreteExpression, _) => "Expecting a concrete expression",
			ParseError::Expecting(ExpectingKind::Expression, _) => "Expecting an expression",
			ParseError::Expecting(ExpectingKind::ValueDecl, _) => "Expecting `let`",
			ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, _) => "Expecting a semantic enclosured by ()",
			ParseError::ExpectingClose(EnclosureKind::Parenthese, _) => "Expecting a `)`",
			ParseError::ExpectingOpen(EnclosureKind::Parenthese, _) => "Expecting a `(`",
			ParseError::ExpectingListDelimiterOrParentheseClosing(_) => "Expecting a ',' or a ')'",
			ParseError::UnexpectedClose(EnclosureKind::Parenthese, _) => "Unexpected ')'",
			ParseError::UnexpectedClose(EnclosureKind::Brace, _) => "Unexpected '}'",
			ParseError::UnexpectedClose(EnclosureKind::Bracket, _) => "Unexpected ']'",
			ParseError::InvalidExpressionFragment(_) => "An invalid expression fragment found",
			_ => unreachable!()
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShaderStage { Vertex, Fragment, Geometry, Hull, Domain }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShaderStageDefinition<'s> { pub location: Location, pub stage: ShaderStage, pub inputs: Vec<SemanticInput<'s>> }
/// Parse an shader stage definition
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("FragmentShader(uv(TEXCOORD0): f2,)")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(shader_stage_definition(&mut tokcache), Ok(ShaderStageDefinition
/// {
///   location: Location::default(), stage: ShaderStage::Fragment, inputs: vec![
///     SemanticInput { location: Location { line: 1, column: 16 }, name: Some("uv"), semantics: Semantics::Texcoord(0), _type: BType::FVec(2) }
///   ]
/// }));
/// ```
pub fn shader_stage_definition<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<ShaderStageDefinition<'s>, Vec<ParseError<'t>>>
{
	let (location, stage) = match tok.next()
	{
		&Token::Keyword(ref pos, Keyword::VertexShader) => (pos.clone(), ShaderStage::Vertex),
		&Token::Keyword(ref pos, Keyword::FragmentShader) => (pos.clone(), ShaderStage::Fragment),
		&Token::Keyword(ref pos, Keyword::GeometryShader) => (pos.clone(), ShaderStage::Geometry),
		&Token::Keyword(ref pos, Keyword::HullShader) => (pos.clone(), ShaderStage::Hull),
		&Token::Keyword(ref pos, Keyword::DomainShader) => (pos.clone(), ShaderStage::Domain),
		e => return Err(vec![ParseError::Expecting(ExpectingKind::ShaderStage, e.position())])
	};
	match tok.next() { &Token::BeginEnclosure(_, EnclosureKind::Parenthese) => (), e => return Err(vec![ParseError::ExpectingOpen(EnclosureKind::Parenthese, e.position())]) }
	let inputs = match semantic_inputs(tok) { Ok(v) => v, Err(ev) => return Err(ev) };
	match tok.next()
	{
		&Token::EndEnclosure(_, EnclosureKind::Parenthese) => Ok(ShaderStageDefinition { location, stage, inputs }),
		e => Err(vec![ParseError::ExpectingClose(EnclosureKind::Parenthese, e.position())])
	}
}

macro_rules! TMatch
{
	($stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.consume(); $extract }, ref e => return Err($err(e.position())) }
	};
	($stream: expr; $pat: pat, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.consume(); }, ref e => return Err($err(e.position())) }
	}
}
pub fn name<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, allow_placeholder: bool) -> Result<(&'t Location, Option<&'s str>), ParseError<'t>>
{
	match *tok.next()
	{
		Token::Placeholder(ref p) if allow_placeholder => Ok((p, None)), Token::Identifier(Source { slice, ref pos }) => Ok((pos, Some(slice))),
		ref e => Err(ParseError::Expecting(ExpectingKind::Ident, e.position()))
	}
}

fn determine_expression_head<'s: 't, 't>(tok: &TokenizerCache<'s, 't>, loc: &'t Location) -> Option<Option<usize>>
{
	if tok.current().position().line == loc.line { Some(Some(loc.column)) }
	else if tok.current().position().column > loc.column { Some(None) } else { None }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDeclaration<'s> { pub location: Location, pub pat: Expression<'s>, pub _type: Option<Type<'s>>, pub value: Expression<'s> }
/// Parse a value(`let`) declaration
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("let succ x: int -> _ = x + 1")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let vd = value_decl(&mut tokcache).unwrap();
/// assert_eq!(vd.location, Location::default());
/// assert_eq!(vd.pat[0].text(), Some("succ")); assert_eq!(vd.pat[1].text(), Some("x"));
/// assert_eq!(vd._type.as_ref().unwrap()[0].basic_type(), Some(BType::Int));
/// assert_eq!(vd._type.as_ref().unwrap()[1].text(), Some("->")); assert!(vd._type.as_ref().unwrap()[2].is_placeholder());
/// assert_eq!(vd.value[0].text(), Some("x")); assert_eq!(vd.value[1].text(), Some("+"));
/// assert_eq!(vd.value[2].text(), Some("1"));
/// ```
pub fn value_decl<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<ValueDeclaration<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; Token::Keyword(ref loc, Keyword::Let) => loc, |p| ParseError::Expecting(ExpectingKind::ValueDecl, p));
	let pbegin = determine_expression_head(tok, location).ok_or_else(|| ParseError::Expecting(ExpectingKind::Pattern, tok.current().position()))?;
	let pat = expression(tok, pbegin, None)?;
	let _type = if tok.current().is_item_delimiter() { tok.consume(); Some(user_type(tok, None)?) }
	else { None };
	TMatch!(tok; Token::Equal(_), |p| ParseError::Expecting(ExpectingKind::ConcreteExpression, p));
	let vbegin = determine_expression_head(tok, location).ok_or_else(|| ParseError::Expecting(ExpectingKind::ConcreteExpression, tok.current().position()))?;
	let value = expression(tok, vbegin, None)?;
	Ok(ValueDeclaration { location: location.clone(), pat, _type, value })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniformDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Type<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Option<Type<'s>>, pub value: Option<Expression<'s>> }
/// Parse an uniform declaration
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("uniform test: mf4")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let ud = uniform_decl(&mut tokcache).unwrap();
/// assert_eq!(ud, UniformDeclaration { location: Location::default(), name: Some("test"),
///     _type: Type(vec![TypeFragment::BasicType(Location { line: 1, column: 15 }, BType::FMat(4, 4))]) });
/// ```
pub fn uniform_decl<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<UniformDeclaration<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; Token::Keyword(ref loc, Keyword::Uniform) => loc.clone(), |p| ParseError::Expecting(ExpectingKind::UniformDef, p));
	let (_, name) = name(tok, true)?;
	TMatch!(tok; Token::ItemDescriptorDelimiter(_), |p| ParseError::Expecting(ExpectingKind::ItemDelimiter, p));
	let _type = user_type(tok, None)?;
	Ok(UniformDeclaration { location, name, _type })
}
/// Parse a constant declaration
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("constant psh1: f2 = (0, 0).yx")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let cd = constant_decl(&mut tokcache).unwrap();
/// assert_eq!(cd.location, Location::default()); assert_eq!(cd.name, Some("psh1")); assert_eq!(cd._type, Some(Type(vec![TypeFragment::BasicType(Location { line: 1, column: 16 }, BType::FVec(2))])));
/// assert_eq!(cd.value.as_ref().unwrap()[0].children().unwrap()[0].text(), Some("0")); assert_eq!(cd.value.as_ref().unwrap()[0].children().unwrap()[1].text(), Some(","));
/// assert_eq!(cd.value.as_ref().unwrap()[0].children().unwrap()[2].text(), Some("0"));
/// assert_eq!(cd.value.as_ref().unwrap()[1].text(), Some(".")); assert_eq!(cd.value.as_ref().unwrap()[2].text(), Some("yx"));
/// ```
pub fn constant_decl<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<ConstantDeclaration<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; Token::Keyword(ref loc, Keyword::Constant) => loc.clone(), |p| ParseError::Expecting(ExpectingKind::ConstantDef, p));
	let (_, name) = name(tok, true)?;
	let _type = if let Token::ItemDescriptorDelimiter(_) = *tok.current() { tok.consume(); Some(user_type(tok, None)?) }
	else { None };
	let value = if let Token::Equal(_) = *tok.current()
	{
		tok.consume();
		let e_begin = if tok.current().position().line == location.line { Some(location.column) }
		else if tok.current().position().column > location.column { None }
		else { return Err(ParseError::Expecting(ExpectingKind::ConcreteExpression, tok.current().position())); };
		Some(expression(tok, e_begin, None)?)
	}
	else { None };
	Ok(ConstantDeclaration { location, name, _type, value })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticOutput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: Option<BType>, pub expr: Expression<'s> }
/// Parse an output declaration from each shader stage
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("out _(SV_Position) = mvp * pos")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let so = semantic_output(&mut tokcache).unwrap();
/// assert_eq!(so.location, Location::default());
/// assert_eq!(so.name, None); assert_eq!(so.semantics, Semantics::SVPosition); assert_eq!(so._type, None);
/// ```
pub fn semantic_output<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<SemanticOutput<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; Token::Keyword(ref loc, Keyword::Out) => loc.clone(), |p| ParseError::Expecting(ExpectingKind::OutDef, p));
	let (_, name) = name(tok, true)?;
	TMatch!(tok; Token::BeginEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
	let semantics = TMatch!(tok; Token::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
	TMatch!(tok; Token::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
	let _type = match tok.current()
	{
		&Token::ItemDescriptorDelimiter(_) =>
		{
			tok.consume();
			match tok.next()
			{
				&Token::BasicType(_, t) => Some(t), &Token::Placeholder(_) => None, e => return Err(ParseError::Expecting(ExpectingKind::Type, e.position()))
			}
		},
		_ => None
	};
	TMatch!(tok; Token::Equal(_), |p| ParseError::Expecting(ExpectingKind::ConcreteExpression, p));
	let e_begin = if tok.current().position().line == location.line { Some(location.column) }
	else if tok.current().position().column > location.column { None }
	else { return Err(ParseError::Expecting(ExpectingKind::ConcreteExpression, tok.current().position())); };
	expression(tok, e_begin, None).map(|expr| SemanticOutput { location, name, semantics, _type, expr })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticInput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: BType }
/// Parse an input declaration each shader stage
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("pos(POSITION): f4")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(semantic_input(&mut tokcache), Ok(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
/// 
/// // optional `in`
/// let (s, v) = (RefCell::new(Source::new("in pos(POSITION): f4")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(semantic_input(&mut tokcache), Ok(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
/// ```
pub fn semantic_input<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<SemanticInput<'s>, ParseError<'t>>
{
	let (location, name) = match tok.next()
	{
		&Token::Keyword(ref loc, Keyword::In) => match tok.next()
		{
			&Token::Identifier(Source { slice, .. }) => (loc.clone(), Some(slice)),
			&Token::Placeholder(_) => (loc.clone(), None),
			e => return Err(ParseError::ExpectingIdentNextIn(e.position()))
		},
		&Token::Identifier(Source { ref pos, slice }) => (pos.clone(), Some(slice)),
		&Token::Placeholder(ref pos) => (pos.clone(), None),
		e => return Err(ParseError::ExpectingIdentOrIn(e.position()))
	};
	TMatch!(tok; Token::BeginEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
	let semantics = TMatch!(tok; Token::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
	TMatch!(tok; Token::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
	TMatch!(tok; Token::ItemDescriptorDelimiter(_), |p| ParseError::Expecting(ExpectingKind::ItemDelimiter, p));
	match tok.next()
	{
		&Token::BasicType(_, _type) => Ok(SemanticInput { location, name, semantics, _type }),
		e => Err(ParseError::Expecting(ExpectingKind::Type, e.position()))
	}
}
/// Parse a list of shader input
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("pos(POSITION): f4, _(TEXCOORD0): f2)")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let seminputs = semantic_inputs(&mut tokcache).unwrap();
/// assert_eq!(seminputs[0], SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) });
/// assert_eq!(seminputs[1], SemanticInput { location: Location { line: 1, column: 20 }, name: None, semantics: Semantics::Texcoord(0), _type: BType::FVec(2) });
/// assert_eq!(tokcache.next(), &Token::EndEnclosure(Location { line: 1, column: 36 }, EnclosureKind::Parenthese));
/// ```
pub fn semantic_inputs<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<Vec<SemanticInput<'s>>, Vec<ParseError<'t>>>
{
	let (mut semantics, mut errors) = (Vec::new(), Vec::new());

	loop
	{
		let p1 = tok.current().position();
		match semantic_input(tok)
		{
			Ok(s) => semantics.push(s), Err(e) => { if e.position() == p1 { tok.unshift(); break; } else { errors.push(e); tok.drop_until(Token::is_basic_type).consume(); } }
		}
		let delimitered = match tok.current() { &Token::ListDelimiter(_) => { tok.consume(); true }, _ => false };
		match tok.current() { &Token::ListDelimiter(_) if !delimitered => { tok.consume(); }, _ => if !delimitered { break; } }
	}
	if errors.is_empty() { Ok(semantics) } else { Err(errors) }
}
