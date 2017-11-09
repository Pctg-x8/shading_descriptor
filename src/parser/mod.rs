//! Syntax Parser

#[macro_use] pub mod utils;
pub mod err;
mod expr; mod types;
pub use self::expr::{FullExpression, Expression, ExpressionFragment, expression, full_expression, expr_lettings};
pub use self::types::{Type, TypeFragment, user_type};
use self::utils::*;
use self::err::*; use self::err::ParseResult::*;
use tokparse::*;

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

/// 型シノニム/データ定義
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeFn<'s> { pub location: Location, pub defs: Vec<(Type<'s>, Type<'s>)> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructor<'s> { pub location: Location, pub name: &'s str, pub args: Vec<&'s str> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclaration<'s> { pub location: Location, pub defs: Vec<(Type<'s>, Vec<DataConstructor<'s>>)> }
/// Parse a type synonim declaration
/// # Examples
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
///
/// let (src, tvec) = (RefCell::new(Source::new("type Xnum = Int").into()), RefCell::new(Vec::new()));
/// let mut cache = TokenizerCache::new(&tvec, &src);
/// type_fn(&mut cache).expect("in case 1");
/// // multiple definition
/// let (src, tvec) = (RefCell::new(Source::new("type Xnum = int; Vec4 = f4").into()), RefCell::new(Vec::new()));
/// let mut cache = TokenizerCache::new(&tvec, &src);
/// type_fn(&mut cache).expect("in case 2");
/// ```
pub fn type_fn<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<TypeFn<'s>, ParseError<'t>>
{
	let location = TMatch!(stream; TokenKind::Keyword(ref p, Keyword::Type) => p, |p| ParseError::Expecting(ExpectingKind::Keyword(Keyword::Type), p));
	let block_start = take_current_block_begin(stream);
	let mut defs = Vec::new();
	while block_start.satisfy(stream.current(), true)
	{
		let defblock_begin = get_definition_leftmost(block_start, stream);
		let pat = types::user_type(stream, defblock_begin, false).into_result(|| ParseError::Expecting(ExpectingKind::TypePattern, stream.current().position()))?;
		if !Leftmost::Exclusive(defblock_begin).satisfy(stream.current(), true) || !stream.current().is_equal()
		{
			return Err(ParseError::Expecting(ExpectingKind::ConcreteType, stream.current().position()));
		}
		stream.shift(); CheckLayout!(Leftmost::Exclusive(defblock_begin) => stream, R);
		let bound = types::user_type(stream, defblock_begin, false).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
		defs.place_back() <- (pat, bound);

		let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
		if block_start.is_nothing() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
		{
			return Ok(TypeFn { location: location.clone(), defs })
		}
		if !delimitered || (stream.current().line_head && block_start.satisfy(stream.current(), false)) { break; }
	}
	if block_start.is_nothing() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
	Ok(TypeFn { location: location.clone(), defs })
}
pub fn type_decl<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<TypeDeclaration<'s>, ParseError<'t>>
{
	fn prefix<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: usize) -> ParseResult<'t, DataConstructor<'s>>
	{
		let (location, name) = match prefix_declarator(stream, Leftmost::Inclusive(leftmost))
		{
			Success(v) => v, Failed(e) => return Failed(e), NotConsumed => return NotConsumed
		};
		let leftmost = Leftmost::Exclusive(leftmost);
		let mut args = Vec::new();
		while leftmost.satisfy(stream.current(), true)
		{
			match stream.current().kind
			{
				TokenKind::Identifier(Source { slice, .. }) => { stream.shift(); args.push(slice) },
				_ => break
			}
		}
		Success(DataConstructor { location: location.clone(), name, args })
	}
	fn infix<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: usize) -> ParseResult<'t, DataConstructor<'s>>
	{
		if !Leftmost::Inclusive(leftmost).satisfy(stream.current(), false) { return NotConsumed; }
		let (location, arg1) = if let TokenKind::Identifier(ref s) = stream.current().kind { stream.shift(); (&s.pos, s.slice) } else { return NotConsumed };
		let leftmost = Leftmost::Exclusive(leftmost);
		CheckLayout!(leftmost => stream);
		let name = take_operator(stream).map_err(|p| ParseError::Expecting(ExpectingKind::Operator, p))?.slice;
		CheckLayout!(leftmost => stream);
		match stream.current().kind
		{
			TokenKind::Identifier(Source { slice: arg2, .. }) =>
			{
				stream.shift(); Success(DataConstructor { location: location.clone(), name, args: vec![arg1, arg2] })
			},
			ref e => Failed(ParseError::Expecting(ExpectingKind::Argument, e.position()))
		}
	}
	let location = TMatch!(stream; TokenKind::Keyword(ref p, Keyword::Data) => p, |p| ParseError::Expecting(ExpectingKind::Keyword(Keyword::Data), p));
	let block_start = take_current_block_begin(stream);
	let mut defs = Vec::new();
	while block_start.satisfy(stream.current(), true)
	{
		let defblock_begin = get_definition_leftmost(block_start, stream);
		let pat = types::user_type(stream, defblock_begin, false)?;
		let t_eq = if let TokenKind::Equal(_) = stream.current().kind { block_start.satisfy(stream.current(), true) } else { false };
		if !t_eq { return Err(ParseError::LayoutViolation(stream.current().position())); }
		let (mut constructors, mut correct_brk) = (Vec::new(), false);
		while block_start.into_exclusive().satisfy(stream.current(), true)
		{
			let prefix_constructor = if stream.current().is_begin_enclosure_of(EnclosureKind::Parenthese) { true }
				else
				{
					let b = if let TokenKind::Operator(_) = stream.shift().current().kind { false } else { true };
					stream.unshift(); b
				};
			let dc = if prefix_constructor { prefix(stream, defblock_begin) } else { infix(stream, defblock_begin) }.into_result_opt()?;
			if let Some(p) = dc { constructors.push(p); } else { break; }

			if let TokenKind::Operator(Source { slice: "|", .. }) = stream.current().kind { stream.shift(); }
			else { correct_brk = true; break; }
		}
		if !correct_brk { return Err(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
		defs.place_back() <- (pat, constructors);

		let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
		if block_start.is_nothing() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
		{
			return Ok(TypeDeclaration { location: location.clone(), defs })
		}
		if !delimitered || (stream.current().line_head && block_start.into_exclusive().satisfy(stream.current(), false)) { break; }
	}
	if block_start.is_nothing() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
	Ok(TypeDeclaration { location: location.clone(), defs })
}

fn prefix_declarator<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: Leftmost) -> ParseResult<'t, (&'t Location, &'s str)>
{
	let leftmost = leftmost.into_nothing_as(Leftmost::Inclusive(stream.current().position().column));
	if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
	match stream.next().kind
	{
		TokenKind::Identifier(Source { slice, ref pos, .. }) => Success((pos, slice)),
		TokenKind::BeginEnclosure(ref p, EnclosureKind::Parenthese) =>
		{
			CheckLayout!(leftmost.into_exclusive() => stream);
			let name = take_operator(stream).map_err(|p| ParseError::Expecting(ExpectingKind::Operator, p))?.slice;
			CheckLayout!(leftmost.into_exclusive() => stream);
			if let TokenKind::EndEnclosure(_, EnclosureKind::Parenthese) = stream.current().kind { stream.shift(); Success((p, name)) }
			else { Failed(ParseError::ExpectingClose(EnclosureKind::Parenthese, stream.current().position())) }
		},
		_ => { stream.unshift(); NotConsumed }
	}
}
fn take_operator<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<&'t Source<'s>, &'t Location>
{
	match stream.next().kind { TokenKind::Operator(ref s) => Ok(s), ref e => { stream.unshift(); Err(e.position()) } }
}
fn name<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, allow_placeholder: bool) -> Result<(&'t Location, Option<&'s str>), &'t Location>
{
	match tok.next().kind
	{
		TokenKind::Placeholder(ref p) if allow_placeholder => Ok((p, None)), TokenKind::Identifier(Source { slice, ref pos, .. }) => Ok((pos, Some(slice))),
		ref e => Err(e.position())
	}
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
	let disabling = TMatch!(Optional: tok; TokenKind::Operator(Source { slice: "!", .. }));

	match tok.next().kind
	{
		TokenKind::Keyword(_, Keyword::DepthTest) =>
		{
			sink.depth_test = if disabling { ShadingState::Disable } else
			{
				ShadingState::Enable(CompareOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?)
			};
		},
		TokenKind::Keyword(_, Keyword::DepthWrite) => { sink.depth_write = if disabling { ShadingState::Disable } else { ShadingState::Enable(()) }; },
		TokenKind::Keyword(_, Keyword::DepthBounds) =>
		{
			sink.depth_bounds = if disabling { ShadingState::Disable } else
			{
				let min = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				let max = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				ShadingState::Enable([min.as_f32(), max.as_f32()])
			};
		},
		TokenKind::Keyword(ref p, Keyword::StencilOps) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilOps, p)); }
			let opf  = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			let opp  = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			let opdf = StencilOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?;
			sink.stencil_test.modify_part().op_fail = opf;
			sink.stencil_test.modify_part().op_pass = opp;
			sink.stencil_test.modify_part().op_depth_fail = opdf;
		},
		TokenKind::Keyword(ref p, Keyword::StencilCompare) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilCompare, p)); }
			let op = CompareOp::consume_classify(tok).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?;
			let mask = if let TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) = tok.current().kind
			{
				tok.shift();
				let n = TMatch!(tok; TokenKind::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				TMatch!(tok; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
				Some(n)
			}
			else { None };
			let refer = TMatch!(tok; TokenKind::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
			sink.stencil_test.modify_part().op_compare = op;
			if let Some(m) = mask { sink.stencil_test.modify_part().compare_mask = m; }
			sink.stencil_test.modify_part().reference = refer;
		},
		TokenKind::Keyword(ref p, Keyword::StencilWriteMask) =>
		{
			if disabling { tok.unshift(); return Err(ParseError::PartialDisabling(Keyword::StencilWriteMask, p)); }
			let mask = TMatch!(tok; TokenKind::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
			sink.stencil_test.modify_part().write_mask = mask;
		},
		TokenKind::Keyword(_, Keyword::StencilTest) if disabling => { sink.stencil_test = ShadingState::Disable; },
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
		if let TokenKind::Operator(Source { slice: "!", .. }) = tok.current().kind
		{
			tok.shift();
			match tok.current().kind
			{
				TokenKind::Keyword(_, kw) if kw == Self::HEADING_KEYWORD => { tok.shift(); Ok(ShadingState::Disable) },
				ref e => Err(ParseError::Expecting(ExpectingKind::Keyword(Self::HEADING_KEYWORD), e.position()))
			}
		}
		else { Self::parse(tok).map(ShadingState::Enable) }
	}
}
fn maybe_enclosed<'s: 't, 't, F, R>(stream: &mut TokenizerCache<'s, 't>, inner: F) -> Result<R, ParseError<'t>>
	where F: FnOnce(&mut TokenizerCache<'s, 't>) -> Result<R, ParseError<'t>>
{
	let in_enclosure = TMatch!(Optional: stream; TokenKind::BeginEnclosure(_, e) => e);
	let r = inner(stream)?;
	if let Some(k) = in_enclosure
	{
		match stream.current().kind
		{
			TokenKind::EndEnclosure(_, kk) if k == kk => { stream.shift(); Ok(r) },
			ref e => Err(ParseError::ExpectingClose(k, e.position()))
		}
	}
	else { Ok(r) }
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

		TMatch!(tok; TokenKind::Keyword(_, Self::HEADING_KEYWORD), |p| ParseError::Expecting(ExpectingKind::Keyword(Self::HEADING_KEYWORD), p));
		let (color_op, color_factor_src, color_factor_dest) = maybe_enclosed(tok, |stream|
		{
			let save = stream.save();
			pat_poland(stream).or_else(|_| { *stream = save; pat_infix(stream) })
		})?;
		let (alpha_op, alpha_factor_src, alpha_factor_dest) = maybe_enclosed(tok, |stream|
		{
			let save = stream.save();
			pat_poland(stream).or_else(|_| { *stream = save; pat_infix(stream) })
		})?;

		Ok(BlendingStateConfig { color_op, color_factor_src, color_factor_dest, alpha_op, alpha_factor_src, alpha_factor_dest })
	}
}
impl CompareOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match tok.next().kind
		{
			TokenKind::Keyword(_, Keyword::Always) => Some(CompareOp::Always),
			TokenKind::Keyword(_, Keyword::Never)  => Some(CompareOp::Never),
			TokenKind::Keyword(_, Keyword::Equal)     | TokenKind::Operator(Source { slice: "==", .. }) => Some(CompareOp::Equal),
			TokenKind::Keyword(_, Keyword::Inequal)   | TokenKind::Operator(Source { slice: "!=", .. }) => Some(CompareOp::Inequal),
			TokenKind::Keyword(_, Keyword::Greater)   | TokenKind::Operator(Source { slice: ">", .. })  => Some(CompareOp::Greater),
			TokenKind::Keyword(_, Keyword::Less)      | TokenKind::Operator(Source { slice: "<", .. })  => Some(CompareOp::Less),
			TokenKind::Keyword(_, Keyword::GreaterEq) | TokenKind::Operator(Source { slice: ">=", .. }) => Some(CompareOp::GreaterEq),
			TokenKind::Keyword(_, Keyword::LessEq)    | TokenKind::Operator(Source { slice: "<=", .. }) => Some(CompareOp::LessEq),
			_ => { tok.unshift(); None }
		}
	}
}
impl StencilOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match tok.next().kind
		{
			TokenKind::Keyword(_, Keyword::Keep)      => Some(StencilOp::Keep),
			TokenKind::Keyword(_, Keyword::Zero)      => Some(StencilOp::Zero),
			TokenKind::Keyword(_, Keyword::Replace)   => Some(StencilOp::Replace),
			TokenKind::Keyword(_, Keyword::Invert)    => Some(StencilOp::Invert),
			TokenKind::Keyword(_, Keyword::IncrWrap)  => Some(StencilOp::IncrementWrap),
			TokenKind::Keyword(_, Keyword::DecrWrap)  => Some(StencilOp::DecrementWrap),
			TokenKind::Keyword(_, Keyword::IncrClamp) => Some(StencilOp::IncrementClamp),
			TokenKind::Keyword(_, Keyword::DecrClamp) => Some(StencilOp::DecrementClamp),
			_ => { tok.unshift(); None }
		}
	}
}
impl BlendOp
{
	fn consume_classify(tok: &mut TokenizerCache) -> Option<Self>
	{
		match tok.next().kind
		{
			TokenKind::Keyword(_, Keyword::Add) => Some(BlendOp::Add),
			TokenKind::Keyword(_, Keyword::Sub) => Some(BlendOp::Sub),
			_ => { tok.unshift(); None }
		}
	}
}
impl<'s> Parser<'s> for BlendFactor
{
	type ResultTy = Self;
	fn parse<'t>(stream: &mut TokenizerCache<'s, 't>) -> Result<Self, ParseError<'t>> where 's: 't
	{
		let inv = TMatch!(Optional: stream; TokenKind::Operator(Source { slice: "~", .. }));
		match stream.next().kind
		{
			TokenKind::Keyword(_, Keyword::SrcColor)  => Ok(BlendFactor::SrcColor(inv)),
			TokenKind::Keyword(_, Keyword::SrcAlpha)  => Ok(BlendFactor::SrcAlpha(inv)),
			TokenKind::Keyword(_, Keyword::DestColor) => Ok(BlendFactor::DestColor(inv)),
			TokenKind::Keyword(_, Keyword::DestAlpha) => Ok(BlendFactor::DestAlpha(inv)),
			ref n@TokenKind::Numeric(_, _) | ref n@TokenKind::NumericF(_, _) =>
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
/// let (s, v) = (RefCell::new(Source::new("FragmentShader(uv(TEXCOORD0): f2,):").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let (stg, def) = shader_stage_definition(&mut tokcache).unwrap();
/// assert_eq!(stg, ShaderStage::Fragment);
/// assert_eq!(def, ShaderStageDefinition
/// {
///   location: Location::default(), inputs: vec![
///     SemanticInput { location: Location { line: 1, column: 16 }, name: Some("uv"), semantics: Semantics::Texcoord(0), _type: BType::FVec(2) },
///   ], outputs: Vec::new(), uniforms: Vec::new(), constants: Vec::new(), values: Vec::new()
/// });
/// ```
pub fn shader_stage_definition<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<(ShaderStage, ShaderStageDefinition<'s>), Vec<ParseError<'t>>>
{
	let (location, stage) = match tok.next().kind
	{
		TokenKind::Keyword(ref pos, Keyword::VertexShader) => (pos, ShaderStage::Vertex),
		TokenKind::Keyword(ref pos, Keyword::FragmentShader) => (pos, ShaderStage::Fragment),
		TokenKind::Keyword(ref pos, Keyword::GeometryShader) => (pos, ShaderStage::Geometry),
		TokenKind::Keyword(ref pos, Keyword::HullShader) => (pos, ShaderStage::Hull),
		TokenKind::Keyword(ref pos, Keyword::DomainShader) => (pos, ShaderStage::Domain),
		ref e => { tok.unshift(); return Err(vec![ParseError::Expecting(ExpectingKind::ShaderStage, e.position())]) }
	};
	TMatch!(tok; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingOpen(EnclosureKind::Parenthese, p)]);
	let inputs = if !tok.current().is_end_enclosure_of(EnclosureKind::Parenthese)
	{
		let mut inputs = vec![semantic_input(tok).map_err(|v| vec![v])?];
		while let TokenKind::ListDelimiter(_) = tok.current().kind
		{
			while let TokenKind::ListDelimiter(_) = tok.current().kind { tok.shift(); }
			if tok.current().is_end_enclosure_of(EnclosureKind::Parenthese) { break; }
			inputs.place_back() <- semantic_input(tok).map_err(|v| vec![v])?;
		}
		inputs
	}
	else { Vec::new() };
	TMatch!(tok; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingClose(EnclosureKind::Parenthese, p)]);
	match tok.current().kind
	{
		TokenKind::ItemDescriptorDelimiter(_) | TokenKind::Keyword(_, Keyword::Where) => { tok.shift(); }
		ref e => return Err(vec![ParseError::Expecting(ExpectingKind::ShaderBlock, e.position())])
	}
	let block_start = take_current_block_begin(tok);
	let (mut outputs, mut uniforms, mut constants, mut values) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
	let mut errors = Vec::new();
	while block_start.satisfy(tok.current(), true)
	{
		let defblock_begin = get_definition_leftmost(block_start, tok);
		match tok.current().kind
		{
			TokenKind::EOF(_) => break,
			TokenKind::Keyword(_, Keyword::Uniform) => match uniform_decl(tok, defblock_begin)
			{
				Ok(v) => { uniforms.push(v); },
				Err(e) =>
				{
					errors.push(e); tok.drop_line();
					while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
				}
			},
			TokenKind::Keyword(_, Keyword::Constant) => match constant_decl(tok, defblock_begin)
			{
				Ok(v) => { constants.push(v); },
				Err(e) =>
				{
					errors.push(e); tok.drop_line();
					while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
				}
			},
			TokenKind::Keyword(_, Keyword::Out) => match semantic_output(tok, defblock_begin)
			{
				Ok(v) => { outputs.push(v); },
				Err(e) =>
				{
					errors.push(e); tok.drop_line();
					while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
				}
			},
			TokenKind::Keyword(_, Keyword::Let) =>
			{
				tok.shift();
				match value_decl(tok, defblock_begin)
				{
					Ok(v) => values.push(v),
					Err(e) => { errors.push(e); tok.drop_line(); while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); } }
				}
			},
			TokenKind::Identifier(_) | TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) => match value_decl(tok, defblock_begin)
			{
				Ok(v) => values.push(v),
				Err(e) => { errors.push(e); tok.drop_line(); while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); } }
			},
			ref e =>
			{
				errors.push(ParseError::Unexpected(e.position())); tok.drop_line();
				while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
			}
		}
	}
	if errors.is_empty() { Ok((stage, ShaderStageDefinition { location: location.clone(), inputs, outputs, uniforms, constants, values })) }
	else { Err(errors) }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDeclaration<'s> { pub location: Location, pub pat: Expression<'s>, pub _type: Option<Type<'s>>, pub value: FullExpression<'s> }
/// Parse a value declaration
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("succ x: int -> _ = x + 1").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let vd = value_decl(&mut tokcache, 0).unwrap();
/// assert_eq!(vd.location, Location::default());
/// assert_eq!(vd.pat[0].text(), Some("succ")); assert_eq!(vd.pat[1].text(), Some("x"));
/// assert_eq!(vd._type.as_ref().unwrap()[0].basic_type(), Some(BType::Int));
/// assert_eq!(vd._type.as_ref().unwrap()[1].text(), Some("->")); assert!(vd._type.as_ref().unwrap()[2].is_placeholder());
/// ```
pub fn value_decl<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: usize) -> Result<ValueDeclaration<'s>, ParseError<'t>>
{
	let location = stream.current().position();
	let pat = expr::expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, stream.current().position()))?;
	let _type = if Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) && stream.current().is_item_delimiter()
	{
		stream.shift(); Some(types::user_type(stream, leftmost, false)?)
	}
	else { None };
	if !Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) || !stream.current().is_equal()
	{
		return Err(ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()));
	}
	stream.shift(); CheckLayout!(Leftmost::Exclusive(leftmost) => stream, R);
	let value = expr::full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
	Ok(ValueDeclaration { location: location.clone(), pat, _type, value })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniformDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Type<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration<'s> { pub location: Location, pub name: Option<&'s str>, pub _type: Option<Type<'s>>, pub value: Option<FullExpression<'s>> }
/// Parse an uniform declaration
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("uniform test: mf4").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let ud = uniform_decl(&mut tokcache, 0).unwrap();
/// assert_eq!(ud, UniformDeclaration { location: Location::default(), name: Some("test"),
///     _type: Type(vec![TypeFragment::BasicType(Location { line: 1, column: 15 }, BType::FMat(4, 4))]) });
/// ```
pub fn uniform_decl<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, leftmost: usize) -> Result<UniformDeclaration<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; TokenKind::Keyword(ref loc, Keyword::Uniform) => loc.clone(), |p| ParseError::Expecting(ExpectingKind::UniformDef, p));
	CheckLayout!(Leftmost::Exclusive(leftmost) => tok, R);
	let (_, name) = name(tok, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
	TMatch!(Leftmost::Exclusive(leftmost) => tok; TokenKind::ItemDescriptorDelimiter(_), |p| ParseError::Expecting(ExpectingKind::ItemDelimiter, p));
	let _type = types::user_type(tok, leftmost, false)?;
	Ok(UniformDeclaration { location, name, _type })
}
/// Parse a constant declaration
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("constant psh1: f2 = (0, 0).yx").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let cd = constant_decl(&mut tokcache, 0).unwrap();
/// assert_eq!(cd.location, Location::default()); assert_eq!(cd.name, Some("psh1"));
/// assert_eq!(cd._type, Some(Type(vec![TypeFragment::BasicType(Location { line: 1, column: 16 }, BType::FVec(2))])));
/// assert!(cd.value.is_some());
/// ```
pub fn constant_decl<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, leftmost: usize) -> Result<ConstantDeclaration<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; TokenKind::Keyword(ref loc, Keyword::Constant) => loc, |p| ParseError::Expecting(ExpectingKind::ConstantDef, p));
	let (_, name) = name(tok, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
	let _type = if Leftmost::Exclusive(leftmost).satisfy(tok.current(), false) && tok.current().is_item_delimiter()
	{
		tok.shift(); types::user_type(tok, leftmost, false).into_result(|| ParseError::Expecting(ExpectingKind::Type, tok.current().position())).map(Some)?
	}
	else { None };
	let value = if Leftmost::Exclusive(leftmost).satisfy(tok.current(), false) && tok.current().is_equal()
	{
		tok.shift();
		expr::full_expression(tok, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, tok.current().position())).map(Some)?
	}
	else { None };
	Ok(ConstantDeclaration { location: location.clone(), name, _type, value })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticOutput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: Option<BType>, pub expr: FullExpression<'s> }
/// Parse an output declaration from each shader stage
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("out _(SV_Position) = mvp * pos").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let so = semantic_output(&mut tokcache, 0).unwrap();
/// assert_eq!(so.location, Location::default());
/// assert_eq!(so.name, None); assert_eq!(so.semantics, Semantics::SVPosition); assert_eq!(so._type, None);
/// ```
pub fn semantic_output<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>, leftmost: usize) -> Result<SemanticOutput<'s>, ParseError<'t>>
{
	let location = TMatch!(tok; TokenKind::Keyword(ref loc, Keyword::Out) => loc, |p| ParseError::Expecting(ExpectingKind::OutDef, p));
	CheckLayout!(Leftmost::Exclusive(leftmost) => tok, R);
	let (_, name) = name(tok, true).map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?;
	TMatch!(Leftmost::Exclusive(leftmost) => tok; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese),
		|p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
	let semantics = TMatch!(tok; TokenKind::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
	TMatch!(Leftmost::Exclusive(leftmost) => tok; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
	let _type = if Leftmost::Exclusive(leftmost).satisfy(tok.current(), false) && tok.current().is_item_delimiter()
	{
		tok.shift(); CheckLayout!(Leftmost::Exclusive(leftmost) => tok, R);
		match tok.next().kind
		{
			TokenKind::BasicType(_, t) => Some(t), TokenKind::Placeholder(_) => None,
			ref e => return Err(ParseError::Expecting(ExpectingKind::Type, e.position()))
		}
	}
	else { None };
	TMatch!(Leftmost::Exclusive(leftmost) => tok; TokenKind::Equal(_), |p| ParseError::Expecting(ExpectingKind::ConcreteExpression, p));
	let expr = expr::full_expression(tok, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, tok.current().position()))?;
	Ok(SemanticOutput { location: location.clone(), name, semantics, _type, expr })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticInput<'s> { pub location: Location, pub name: Option<&'s str>, pub semantics: Semantics, pub _type: BType }
/// Parse an input declaration each shader stage
/// # Example
/// 
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("pos(POSITION): f4").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(semantic_input(&mut tokcache), Ok(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
/// 
/// // optional `in`
/// let (s, v) = (RefCell::new(Source::new("in pos(POSITION): f4").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// assert_eq!(semantic_input(&mut tokcache), Ok(SemanticInput { location: Location::default(), name: Some("pos"), semantics: Semantics::Position(0), _type: BType::FVec(4) }));
/// ```
pub fn semantic_input<'s: 't, 't>(tok: &mut TokenizerCache<'s, 't>) -> Result<SemanticInput<'s>, ParseError<'t>>
{
	let location1 = TMatch!(Optional: tok; TokenKind::Keyword(ref loc, Keyword::In) => loc);
	let (location, name) = match tok.next().kind
	{
		TokenKind::Identifier(Source { slice, ref pos, .. }) => (location1.unwrap_or(pos), Some(slice)),
		TokenKind::Placeholder(ref pos) => (location1.unwrap_or(pos), None),
		ref e => return Err(ParseError::Expecting(ExpectingKind::Ident, e.position()))
	};
	TMatch!(tok; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, p));
	let semantics = TMatch!(tok; TokenKind::Semantics(_, sem) => sem, |p| ParseError::Expecting(ExpectingKind::Semantics, p));
	TMatch!(tok; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
	TMatch!(tok; TokenKind::ItemDescriptorDelimiter(_), |p| ParseError::Expecting(ExpectingKind::ItemDelimiter, p));
	match tok.next().kind
	{
		TokenKind::BasicType(_, _type) => Ok(SemanticInput { location: location.clone(), name, semantics, _type }),
		ref e => Err(ParseError::Expecting(ExpectingKind::Type, e.position()))
	}
}
