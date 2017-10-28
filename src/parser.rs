//! Syntax Parser

use tokparse::*;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error;
use expression_parser::*;
use typeparser::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectingKind
{
	ItemDelimiter, Semantics, Type, ShaderStage, OutDef, UniformDef, ConstantDef, Ident, ValueDecl,
	ConcreteExpression, Expression, Pattern, Numeric,
	CompareOps, StencilOps, DepthStencilStates, BlendOps, BlendFactors, Keyword(Keyword)
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError<'t>
{
	ExpectingIdentNextIn(&'t Location), ExpectingIdentOrIn(&'t Location), Expecting(ExpectingKind, &'t Location),
	ExpectingListDelimiterOrParentheseClosing(&'t Location),
	ExpectingEnclosed(ExpectingKind, EnclosureKind, &'t Location), ExpectingOpen(EnclosureKind, &'t Location), ExpectingClose(EnclosureKind, &'t Location),
	UnexpectedClose(EnclosureKind, &'t Location), Unexpected(&'t Location), InvalidExpressionFragment(&'t Location),
	PartialDisabling(Keyword, &'t Location), BlendFactorRestriction(&'t Location)
}
impl<'t> Display for ParseError<'t>
{
	fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{} at {}", self.description(), self.position()) }
}
impl<'t> ParseError<'t>
{
	fn position(&self) -> &'t Location
	{
		use self::ParseError::*;
		match *self
		{
			ExpectingIdentNextIn(p) | ExpectingIdentOrIn(p) | Expecting(_, p)  | ExpectingEnclosed(_, _, p) | ExpectingClose(_, p) | Unexpected(p)
			| ExpectingListDelimiterOrParentheseClosing(p) | ExpectingOpen(_, p) | UnexpectedClose(_, p) | InvalidExpressionFragment(p)
			| PartialDisabling(_, p) | BlendFactorRestriction(p) => p
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
			ParseError::Expecting(ExpectingKind::CompareOps, _) => "Expecting a comparsion operator",
			ParseError::Expecting(ExpectingKind::StencilOps, _) => "Expecting a stencil operator",
			ParseError::Expecting(ExpectingKind::Numeric, _) => "Expecting a numeric literal",
			ParseError::Expecting(ExpectingKind::BlendOps, _) => "Expecting a blend operators",
			ParseError::Expecting(ExpectingKind::BlendFactors, _) => "Expecting a blend factors",
			ParseError::Expecting(ExpectingKind::DepthStencilStates, _) => "Expecting any of depth stencil states",
			ParseError::Expecting(ExpectingKind::Keyword(Keyword::Blend), _) => "Expecting `Blend`",
			ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, _) => "Expecting a semantic enclosured by ()",
			ParseError::ExpectingClose(EnclosureKind::Parenthese, _) => "Expecting a `)`",
			ParseError::ExpectingOpen(EnclosureKind::Parenthese, _) => "Expecting a `(`",
			ParseError::ExpectingListDelimiterOrParentheseClosing(_) => "Expecting a ',' or a ')'",
			ParseError::UnexpectedClose(EnclosureKind::Parenthese, _) => "Unexpected ')'",
			ParseError::UnexpectedClose(EnclosureKind::Brace, _) => "Unexpected '}'",
			ParseError::UnexpectedClose(EnclosureKind::Bracket, _) => "Unexpected ']'",
			ParseError::InvalidExpressionFragment(_) => "An invalid expression fragment found",
			ParseError::Unexpected(_) => "Unexpected token",
			ParseError::PartialDisabling(Keyword::StencilCompare, _) => "`StencilCompare` cannot be disabled partially",
			ParseError::PartialDisabling(Keyword::StencilOps, _) => "`StencilOps` cannot be disabled partially",
			ParseError::PartialDisabling(Keyword::StencilWriteMask, _) => "`StencilWriteMask` cannot be disabled partially",
			ParseError::BlendFactorRestriction(_) => "Constant Blend Factor must be 0 or 1",
			ref de => unreachable!(de)
		}
	}
}

/// トークンマッチングマクロ
macro_rules! TMatch
{
	($stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.consume(); $extract }, ref e => return Err($err(e.position())) }
	};
	($stream: expr; $pat: pat, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.consume(); }, ref e => return Err($err(e.position())) }
	};
	(Numeric: $stream: expr; $err: expr) =>
	{
		match *$stream.current()
		{
			ref t@Token::Numeric(_, _) | ref t@Token::NumericF(_, _) => { $stream.consume(); t },
			ref e => return Err($err(e.position()))
		}
	};
	(Optional: $stream: expr; $pat: pat => $act: expr) =>
	{
		if let $pat = *$stream.current() { $stream.consume(); Some($act) } else { None }
	};
	(Optional: $stream: expr; $pat: pat) =>
	{
		if let $pat = *$stream.current() { $stream.consume(); true } else { false }
	}
}

/// シェーディングパイプライン(コンパイル単位)
#[derive(Debug, Clone)]
pub struct ShadingPipeline<'s>
{
	state: ShadingStates,
	vsh: Option<ShaderStageDefinition<'s>>,
	hsh: Option<ShaderStageDefinition<'s>>, dsh: Option<ShaderStageDefinition<'s>>,
	gsh: Option<ShaderStageDefinition<'s>>, fsh: Option<ShaderStageDefinition<'s>>
}
pub fn shading_pipeline<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<ShadingPipeline<'s>, Vec<ParseError<'t>>>
{
	let mut sp = ShadingPipeline { state: Default::default(), vsh: None, hsh: None, dsh: None, gsh: None, fsh: None };
	let mut errors = Vec::new();

	loop
	{
		let headp = stream.current().position();
		let mut errors_t = Vec::new();
		let mut has_error = false;
		let save = stream.save();
		// println!("dbg: head : {:?}", stream.current());
		match shader_stage_definition(stream)
		{
			Ok((ShaderStage::Vertex, v))   => { sp.vsh = Some(v); continue; }
			Ok((ShaderStage::Hull, v))     => { sp.hsh = Some(v); continue; }
			Ok((ShaderStage::Domain, v))   => { sp.dsh = Some(v); continue; }
			Ok((ShaderStage::Geometry, v)) => { sp.gsh = Some(v); continue; }
			Ok((ShaderStage::Fragment, v)) => { sp.fsh = Some(v); continue; }
			Err(mut e) => if headp != stream.current().position()
			{
				errors_t.append(&mut e); *stream = save; has_error = true;
			}
		}
		// println!("dbg: no shader stage : {:?}", headp);
		let save = stream.save();
		match BlendingStateConfig::switched_parse(stream)
		{
			Ok(bs) => { sp.state.blending = bs; continue; }
			Err(e) => if headp != stream.current().position()
			{
				errors_t.push(e); *stream = save;
				has_error = true;
			}
		}
		let save = stream.save();
		if let Err(e) = depth_state(stream, &mut sp.state)
		{
			if headp != stream.current().position()
			{
				errors_t.push(e); *stream = save;
				has_error = true;
			}
		}
		else { continue; }
		errors.append(&mut errors_t);
		if has_error
		{
			stream.drop_line(); while stream.current().position().column > headp.column { stream.drop_line(); }
		}
		else { break; }
	}
	if errors.is_empty() { Ok(sp) } else { Err(errors) }
}

/// シェーディングパイプラインステート
#[derive(Debug, Clone, PartialEq)]
pub enum ShadingState<T> { Enable(T), Disable }
impl<T: Copy> Copy for ShadingState<T> {}
impl<T: Eq> Eq for ShadingState<T> {}
impl<T: Default> ShadingState<T>
{
	fn modify_part(&mut self) -> &mut T
	{
		if let ShadingState::Disable = *self
		{
			*self = ShadingState::Enable(T::default());
		}
		if let ShadingState::Enable(ref mut v) = *self { v } else { unreachable!(); }
	}
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareOp { Always, Never, Equal, Inequal, Greater, Less, GreaterEq, LessEq }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StencilOp { Keep, Zero, Replace, IncrementWrap, DecrementWrap, IncrementClamp, DecrementClamp, Invert }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlendOp { Add, Sub }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlendFactor { SrcColor(bool), SrcAlpha(bool), DestColor(bool), DestAlpha(bool), One, Zero }
#[derive(Debug, Clone, PartialEq)]
pub struct ShadingStates
{
	depth_test: ShadingState<CompareOp>, depth_write: ShadingState<()>,
	depth_bounds: ShadingState<[f32; 2]>, stencil_test: ShadingState<StencilTestConfig>,
	blending: ShadingState<BlendingStateConfig>
}
impl Default for ShadingStates
{
	fn default() -> Self
	{
		ShadingStates
		{
			depth_test: ShadingState::Enable(CompareOp::Greater),
			depth_write: ShadingState::Enable(()),
			depth_bounds: ShadingState::Enable([0.0, 1.0]),
			stencil_test: ShadingState::Disable,
			blending: ShadingState::Disable
		}
	}
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StencilTestConfig
{
	pub op_fail: StencilOp, pub op_pass: StencilOp, pub op_depth_fail: StencilOp,
	pub op_compare: CompareOp, pub compare_mask: u32, pub reference: u32, pub write_mask: u32
}
impl Default for StencilTestConfig
{
	fn default() -> Self
	{
		StencilTestConfig
		{
			op_fail: StencilOp::Keep, op_pass: StencilOp::Keep, op_depth_fail: StencilOp::Keep,
			op_compare: CompareOp::Always, compare_mask: 0xffff_ffff, reference: 0, write_mask: 0xffff_ffff
		}
	}
}
#[derive(Debug, Clone, PartialEq)]
pub struct BlendingStateConfig
{
	pub color_op: BlendOp, pub color_factor_src: BlendFactor, pub color_factor_dest: BlendFactor,
	pub alpha_op: BlendOp, pub alpha_factor_src: BlendFactor, pub alpha_factor_dest: BlendFactor
}

pub fn depth_state<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, sink: &mut ShadingStates) -> Result<(), ParseError<'t>>
{
	let disabling = if let Token::Operator(Source { slice: "!", .. }) = *tok.current() { tok.consume(); true } else { false };

	match *tok.next()
	{
		Token::Keyword(_, Keyword::DepthTest) =>
		{
			sink.depth_test = if disabling { ShadingState::Disable } else
			{
				ShadingState::Enable(CompareOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?)
			};
		},
		Token::Keyword(_, Keyword::DepthWrite) => { sink.depth_write = if disabling { ShadingState::Disable } else { ShadingState::Enable(()) }; },
		Token::Keyword(_, Keyword::DepthBounds) =>
		{
			sink.depth_bounds = if disabling { ShadingState::Disable } else
			{
				let min = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				let max = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				ShadingState::Enable([min.as_f32(), max.as_f32()])
			};
		},
		Token::Keyword(ref p, Keyword::StencilOps) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilOps, p)); }
			let opf  = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			let opp  = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			let opdf = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			sink.stencil_test.modify_part().op_fail = opf;
			sink.stencil_test.modify_part().op_pass = opp;
			sink.stencil_test.modify_part().op_depth_fail = opdf;
		},
		Token::Keyword(ref p, Keyword::StencilCompare) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilCompare, p)); }
			let op = CompareOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?;
			let mask = if let Token::BeginEnclosure(_, EnclosureKind::Parenthese) = *tok.current()
			{
				tok.consume();
				let n = TMatch!(tok; Token::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				TMatch!(tok; Token::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
				Some(n)
			}
			else { None };
			let refer = TMatch!(tok; Token::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
			sink.stencil_test.modify_part().op_compare = op;
			if let Some(m) = mask { sink.stencil_test.modify_part().compare_mask = m; }
			sink.stencil_test.modify_part().reference = refer;
		},
		Token::Keyword(ref p, Keyword::StencilWriteMask) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilWriteMask, p)); }
			let mask = TMatch!(tok; Token::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
			sink.stencil_test.modify_part().write_mask = mask;
		},
		Token::Keyword(_, Keyword::StencilTest) if disabling => { sink.stencil_test = ShadingState::Disable; },
		ref e => { tok.unshift(); return Err(ParseError::Expecting(ExpectingKind::DepthStencilStates, e.position())); }
	}
	Ok(())
}
pub trait Parser<'s>
{
	type ResultTy: 's;
	fn parse<'t>(tok: &mut TokenizerCache<'s, 't>) -> Result<Self::ResultTy, ParseError<'t>> where 's: 't;
}
pub trait ShadingStateParser<'s> : Parser<'s>
{
	const HEADING_KEYWORD: Keyword;
	fn switched_parse<'t>(tok: &mut TokenizerCache<'s, 't>) -> Result<ShadingState<<Self as Parser<'s>>::ResultTy>, ParseError<'t>>
	{
		if let Token::Operator(Source { slice: "!", .. }) = *tok.current()
		{
			tok.consume();
			match *tok.current()
			{
				Token::Keyword(_, kw) if kw == Self::HEADING_KEYWORD => Ok(ShadingState::Disable),
				ref e => Err(ParseError::Expecting(ExpectingKind::Keyword(Self::HEADING_KEYWORD), e.position()))
			}
		}
		else { Self::parse(tok).map(ShadingState::Enable) }
	}
}
impl<'s> ShadingStateParser<'s> for BlendingStateConfig { const HEADING_KEYWORD: Keyword = Keyword::Blend; }
impl<'s> Parser<'s> for BlendingStateConfig
{
	type ResultTy = Self;
	fn parse<'t>(tok: &mut TokenizerCache<'s, 't>) -> Result<Self::ResultTy, ParseError<'t>> where 's: 't
	{
		fn pat_poland<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<(BlendOp, BlendFactor, BlendFactor), ParseError<'t>>
		{
			let op = BlendOp::consume_classify(stream).ok_or_else(|| ParseError::Expecting(ExpectingKind::BlendOps, stream.current().position()))?;
			let srcfactor = BlendFactor::parse(stream)?;
			let dstfactor = BlendFactor::parse(stream)?;
			Ok((op, srcfactor, dstfactor))
		}
		fn pat_infix<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<(BlendOp, BlendFactor, BlendFactor), ParseError<'t>>
		{
			let srcfactor = BlendFactor::parse(stream)?;
			let op = BlendOp::consume_classify(stream).ok_or_else(|| ParseError::Expecting(ExpectingKind::BlendOps, stream.current().position()))?;
			let dstfactor = BlendFactor::parse(stream)?;
			Ok((op, srcfactor, dstfactor))
		}

		TMatch!(tok; Token::Keyword(_, Self::HEADING_KEYWORD), |p| ParseError::Expecting(ExpectingKind::Keyword(Self::HEADING_KEYWORD), p));
		let in_enclosure = TMatch!(Optional: tok; Token::BeginEnclosure(_, e) => e);
		let (color_op, color_factor_src, color_factor_dest) = {
			let save = tok.save();
			if let Ok(v) = pat_poland(tok) { v } else { *tok = save; pat_infix(tok)? }
		};
		if let Some(e) = in_enclosure
		{
			match *tok.current()
			{
				Token::EndEnclosure(_, ee) if ee == e => { tok.consume(); },
				ref et => return Err(ParseError::ExpectingClose(e, et.position()))
			}
		}
		let in_enclosure = TMatch!(Optional: tok; Token::BeginEnclosure(_, e) => e);
		let (alpha_op, alpha_factor_src, alpha_factor_dest) = {
			let save = tok.save();
			if let Ok(v) = pat_poland(tok) { v } else { *tok = save; pat_infix(tok)? }
		};
		if let Some(e) = in_enclosure
		{
			match *tok.current()
			{
				Token::EndEnclosure(_, ee) if ee == e => { tok.consume(); },
				ref et => return Err(ParseError::ExpectingClose(e, et.position()))
			}
		}

		Ok(BlendingStateConfig { color_op, color_factor_src, color_factor_dest, alpha_op, alpha_factor_src, alpha_factor_dest })
	}
}
impl CompareOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match *tok.next()
		{
			Token::Keyword(_, Keyword::Always) => Some(CompareOp::Always),
			Token::Keyword(_, Keyword::Never)  => Some(CompareOp::Never),
			Token::Keyword(_, Keyword::Equal)     | Token::Operator(Source { slice: "==", .. }) => Some(CompareOp::Equal),
			Token::Keyword(_, Keyword::Inequal)   | Token::Operator(Source { slice: "!=", .. }) => Some(CompareOp::Inequal),
			Token::Keyword(_, Keyword::Greater)   | Token::Operator(Source { slice: ">", .. })  => Some(CompareOp::Greater),
			Token::Keyword(_, Keyword::Less)      | Token::Operator(Source { slice: "<", .. })  => Some(CompareOp::Less),
			Token::Keyword(_, Keyword::GreaterEq) | Token::Operator(Source { slice: ">=", .. }) => Some(CompareOp::GreaterEq),
			Token::Keyword(_, Keyword::LessEq)    | Token::Operator(Source { slice: "<=", .. }) => Some(CompareOp::LessEq),
			_ => { tok.unshift(); None }
		}
	}
}
impl StencilOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match *tok.next()
		{
			Token::Keyword(_, Keyword::Keep)      => Some(StencilOp::Keep),
			Token::Keyword(_, Keyword::Zero)      => Some(StencilOp::Zero),
			Token::Keyword(_, Keyword::Replace)   => Some(StencilOp::Replace),
			Token::Keyword(_, Keyword::Invert)    => Some(StencilOp::Invert),
			Token::Keyword(_, Keyword::IncrWrap)  => Some(StencilOp::IncrementWrap),
			Token::Keyword(_, Keyword::DecrWrap)  => Some(StencilOp::DecrementWrap),
			Token::Keyword(_, Keyword::IncrClamp) => Some(StencilOp::IncrementClamp),
			Token::Keyword(_, Keyword::DecrClamp) => Some(StencilOp::DecrementClamp),
			_ => { tok.unshift(); None }
		}
	}
}
impl BlendOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match *tok.next()
		{
			Token::Keyword(_, Keyword::Add) => Some(BlendOp::Add),
			Token::Keyword(_, Keyword::Sub) => Some(BlendOp::Sub),
			_ => { tok.unshift(); None }
		}
	}
}
impl<'s> Parser<'s> for BlendFactor
{
	type ResultTy = Self;
	fn parse<'t>(stream: &mut TokenizerCache<'s, 't>) -> Result<Self, ParseError<'t>> where 's: 't
	{
		let inv = TMatch!(Optional: stream; Token::Operator(Source { slice: "~", .. }));
		match *stream.next()
		{
			Token::Keyword(_, Keyword::SrcColor)  => Ok(BlendFactor::SrcColor(inv)),
			Token::Keyword(_, Keyword::SrcAlpha)  => Ok(BlendFactor::SrcAlpha(inv)),
			Token::Keyword(_, Keyword::DestColor) => Ok(BlendFactor::DestColor(inv)),
			Token::Keyword(_, Keyword::DestAlpha) => Ok(BlendFactor::DestAlpha(inv)),
			ref n@Token::Numeric(_, _) | ref n@Token::NumericF(_, _) =>
				if n.match1() { Ok(if inv { BlendFactor::Zero } else { BlendFactor::One }) }
				else if n.match0() { Ok(if inv { BlendFactor::One } else { BlendFactor::Zero }) }
				else { Err(ParseError::BlendFactorRestriction(n.position())) },
			ref e => Err(ParseError::Expecting(ExpectingKind::BlendFactors, e.position()))
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShaderStage { Vertex, Fragment, Geometry, Hull, Domain }
/// シェーダステージ定義
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShaderStageDefinition<'s>
{
	pub location: Location,
	pub inputs: Vec<SemanticInput<'s>>, pub outputs: Vec<SemanticOutput<'s>>,
	pub uniforms: Vec<UniformDeclaration<'s>>, pub constants: Vec<ConstantDeclaration<'s>>,
	pub values: Vec<ValueDeclaration<'s>>
}
/// Parse an shader stage definition
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("FragmentShader(uv(TEXCOORD0): f2,)")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(shader_stage_definition(&mut tokcache), Ok((ShaderStage::Fragment, ShaderStageDefinition
/// {
///   location: Location::default(), inputs: vec![
///     SemanticInput { location: Location { line: 1, column: 16 }, name: Some("uv"), semantics: Semantics::Texcoord(0), _type: BType::FVec(2) },
///   ], outputs: Vec::new(), uniforms: Vec::new(), constants: Vec::new(), values: Vec::new()
/// })));
/// ```
pub fn shader_stage_definition<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<(ShaderStage, ShaderStageDefinition<'s>), Vec<ParseError<'t>>>
{
	let (location, stage) = match *tok.next()
	{
		Token::Keyword(ref pos, Keyword::VertexShader) => (pos, ShaderStage::Vertex),
		Token::Keyword(ref pos, Keyword::FragmentShader) => (pos, ShaderStage::Fragment),
		Token::Keyword(ref pos, Keyword::GeometryShader) => (pos, ShaderStage::Geometry),
		Token::Keyword(ref pos, Keyword::HullShader) => (pos, ShaderStage::Hull),
		Token::Keyword(ref pos, Keyword::DomainShader) => (pos, ShaderStage::Domain),
		ref e => { tok.unshift(); return Err(vec![ParseError::Expecting(ExpectingKind::ShaderStage, e.position())]) }
	};
	TMatch!(tok; Token::BeginEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingOpen(EnclosureKind::Parenthese, p)]);
	let inputs = match semantic_inputs(tok) { Ok(v) => v, Err(ev) => return Err(ev) };
	TMatch!(tok; Token::EndEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingClose(EnclosureKind::Parenthese, p)]);
	TMatch!(tok; Token::ItemDescriptorDelimiter(_), |p| vec![ParseError::Expecting(ExpectingKind::ItemDelimiter, p)]);
	let (mut outputs, mut uniforms, mut constants, mut values) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
	let mut errors = Vec::new();
	loop
	{
		if tok.current().is_eof() || tok.current().position().column <= location.column { break; }
		let head_loc = tok.current().position();
		match semantic_output(tok)
		{
			Ok(v) => { outputs.push(v); continue; },
			Err(e) => if e.position() != head_loc
			{
				errors.push(e);
				tok.drop_line(); while tok.current().position().column > head_loc.column { tok.drop_line(); }
				continue;
			}
		}
		match uniform_decl(tok)
		{
			Ok(v) => { uniforms.push(v); continue; },
			Err(e) => if e.position() != head_loc
			{
				errors.push(e);
				tok.drop_line(); while tok.current().position().column > head_loc.column { tok.drop_line(); }
				continue;
			}
		}
		match constant_decl(tok)
		{
			Ok(v) => { constants.push(v); continue; },
			Err(e) => if e.position() != head_loc
			{
				errors.push(e);
				tok.drop_line(); while tok.current().position().column > head_loc.column { tok.drop_line(); }
				continue;
			}
		}
		match value_decl(tok)
		{
			Ok(v) => { values.push(v); continue; },
			Err(e) => if e.position() != head_loc
			{
				errors.push(e);
				tok.drop_line(); while tok.current().position().column > head_loc.column { tok.drop_line(); }
				continue;
			}
		}
		errors.push(ParseError::Unexpected(head_loc));
		tok.drop_line(); while tok.current().position().column > head_loc.column { tok.drop_line(); }
	}
	if errors.is_empty() { Ok((stage, ShaderStageDefinition { location: location.clone(), inputs, outputs, uniforms, constants, values })) }
	else { Err(errors) }
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
