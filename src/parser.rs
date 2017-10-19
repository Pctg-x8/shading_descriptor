//! Syntax Parser

use tokparse::*;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::error::Error;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ExpectingKind
{
	ItemDelimiter, Semantics, Type, ShaderStage
}
#[derive(Clone, PartialEq, Eq)]
pub enum ParseError<'t>
{
	ExpectingIdentNextIn(&'t Location), ExpectingIdentOrIn(&'t Location), Expecting(ExpectingKind, &'t Location),
	ExpectingListDelimiterOrParentheseClosing(&'t Location),
	ExpectingEnclosed(ExpectingKind, EnclosureKind, &'t Location), ExpectingOpen(EnclosureKind, &'t Location), ExpectingClose(EnclosureKind, &'t Location)
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
			| ExpectingListDelimiterOrParentheseClosing(p) | ExpectingOpen(_, p) => p
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
			ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, _) => "Expecting a semantic enclosured by ()",
			ParseError::ExpectingClose(EnclosureKind::Parenthese, _) => "Expecting a `)`",
			ParseError::ExpectingOpen(EnclosureKind::Parenthese, _) => "Expecting a `(`",
			ParseError::ExpectingListDelimiterOrParentheseClosing(_) => "Expecting a ',' or a ')'",
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
	match tok.next() { &Token::BeginEnclosure(_, EnclosureKind::Parenthese) => (), e => return Err(ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, e.position())) }
	let semantics = match tok.next()
	{
		&Token::Semantics(_, sem) => sem,
		e => return Err(ParseError::Expecting(ExpectingKind::Semantics, e.position()))
	};
	match tok.next() { &Token::EndEnclosure(_, EnclosureKind::Parenthese) => (), e => return Err(ParseError::ExpectingClose(EnclosureKind::Parenthese, e.position())) };
	match tok.next() { &Token::ItemDescriptorDelimiter(_) => (), e => return Err(ParseError::Expecting(ExpectingKind::ItemDelimiter, e.position())) }
	match tok.next()
	{
		&Token::BasicType(_, ty) => Ok(SemanticInput { location, name, semantics, _type: ty }),
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
			Ok(s) => semantics.push(s), Err(e) => { if e.position() == p1 { tok.revert(); break; } else { errors.push(e); tok.drop_until(Token::is_basic_type).consume(); } }
		}
		let delimitered = match tok.current() { &Token::ListDelimiter(_) => { tok.consume(); true }, _ => false };
		match tok.current() { &Token::ListDelimiter(_) if !delimitered => { tok.consume(); }, _ => if !delimitered { break; } }
	}
	if errors.is_empty() { Ok(semantics) } else { Err(errors) }
}
