//! Syntax Parser

#[macro_use] pub mod utils;
pub mod err;
mod assoc;
mod expr; mod types; mod decls;
pub use self::err::{Success, SuccessM, Failed, FailedM, NotConsumed, NotConsumedM};
pub use self::expr::{FullExpression, Expression, ExpressionFragment, expression, full_expression, expr_lettings};
pub use self::types::{Type, TypeFragment, user_type};
pub use self::decls::{ValueDeclaration, UniformDeclaration, ConstantDeclaration, SemanticOutput, SemanticInput};
pub use self::assoc::{Associativity, AssociativityEnv};
use self::utils::*; use self::err::*;
use tokparse::*;
use std::rc::Rc; use std::cell::RefCell;

type RcMut<T> = Rc<RefCell<T>>;
fn new_rcmut<T>(init: T) -> RcMut<T> { Rc::new(RefCell::new(init)) }

/// シェーディングパイプライン(コンパイル単位)
#[derive(Debug, Clone)]
pub struct ShadingPipeline<'s>
{
	state: ShadingStates,
	vsh: Option<ShaderStageDefinition<'s>>,
	hsh: Option<ShaderStageDefinition<'s>>, dsh: Option<ShaderStageDefinition<'s>>,
	gsh: Option<ShaderStageDefinition<'s>>, fsh: Option<ShaderStageDefinition<'s>>,
	values: Vec<ValueDeclaration<'s>>, assoc: Rc<RefCell<AssociativityEnv<'s>>>
}
pub fn shading_pipeline<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Result<ShadingPipeline<'s>, Vec<ParseError<'t>>>
{
	let mut sp = ShadingPipeline
	{
		state: Default::default(), vsh: None, hsh: None, dsh: None, gsh: None, fsh: None,
		values: Vec::new(), assoc: Rc::new(RefCell::new(AssociativityEnv::new(None)))
	};
	let mut errors = Vec::new();

	loop
	{
		let leftmost = get_definition_leftmost(Leftmost::Inclusive(1), stream);
		let mut errors_t = Vec::new();
		let inst = stream.save();
		let has_error = if stream.current().infix_assoc()
		{
			match Associativity::parse(stream).into_result(|| ParseError::Expecting(ExpectingKind::Infix, stream.current().position()))
			{
				Ok((v, a)) => for op in v
				{
					match sp.assoc.borrow_mut().register(op.slice, op.pos, a)
					{
						Some(p) => { errors.place_back() <- ParseError::DuplicatePrecedences(p.clone(), stream.current().position()); },
						None => ()
					}
				},
				Err(e) => { errors.push(e); }
			}
			true
		}
		else
		{
			let mut b = match shader_stage_definition(stream)
			{
				SuccessM((ShaderStage::Vertex, v))   => { sp.vsh = Some(v); continue; }
				SuccessM((ShaderStage::Hull, v))     => { sp.hsh = Some(v); continue; }
				SuccessM((ShaderStage::Domain, v))   => { sp.dsh = Some(v); continue; }
				SuccessM((ShaderStage::Geometry, v)) => { sp.gsh = Some(v); continue; }
				SuccessM((ShaderStage::Fragment, v)) => { sp.fsh = Some(v); continue; }
				FailedM(mut e) => { errors_t.append(&mut e); true }, _ => false
			};
			b |= match BlendingStateConfig::switched_parse(stream.restore(inst))
			{
				Success(bs) => { sp.state.blending = bs; continue; }
				Failed(e) => { errors_t.push(e); true }, _ => false
			};
			b |= match depth_state(stream.restore(inst), &mut sp.state)
			{
				Failed(e) => { errors_t.push(e); true },
				Success(_) => continue, _ => false
			};
			b | match ValueDeclaration::parse(stream.restore(inst), leftmost)
			{
				Failed(e) => { errors_t.push(e); true },
				Success(v) => { sp.values.push(v); continue; }, _ => false
			}
		};
		errors.append(&mut errors_t);
		if has_error
		{
			stream.drop_line(); while Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) { stream.drop_line(); }
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
pub fn type_fn<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<TypeFn<'s>, ParseError<'t>>
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
		stream.shift(); CheckLayout!(Leftmost::Exclusive(defblock_begin) => stream);
		let bound = types::user_type(stream, defblock_begin, false).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
		defs.place_back() <- (pat, bound);

		let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
		if block_start.is_nothing() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
		{
			return Ok(TypeFn { location: location.clone(), defs })
		}
		if !delimitered || (stream.on_linehead() && block_start.satisfy(stream.current(), false)) { break; }
	}
	if block_start.is_nothing() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
	Ok(TypeFn { location: location.clone(), defs })
}
pub fn type_decl<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<TypeDeclaration<'s>, ParseError<'t>>
{
	fn prefix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, DataConstructor<'s>>
	{
		let (location, name) = match prefix_declarator(stream, Leftmost::Inclusive(leftmost))
		{
			Success(v) => v, Failed(e) => return Failed(e), NotConsumed => return NotConsumed
		};
		let leftmost = Leftmost::Exclusive(leftmost);
		let mut args = Vec::new();
		while leftmost.satisfy(stream.current(), true)
		{
			match *stream.current()
			{
				TokenKind::Identifier(Source { slice, .. }) => { stream.shift(); args.push(slice) },
				_ => break
			}
		}
		Success(DataConstructor { location: location.clone(), name, args })
	}
	fn infix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, DataConstructor<'s>>
	{
		if !Leftmost::Inclusive(leftmost).satisfy(stream.current(), false) { return NotConsumed; }
		let (location, arg1) = if let TokenKind::Identifier(ref s) = *stream.current() { stream.shift(); (&s.pos, s.slice) } else { return NotConsumed };
		let leftmost = Leftmost::Exclusive(leftmost);
		CheckLayout!(leftmost => stream);
		let name = take_operator(stream).map_err(|p| ParseError::Expecting(ExpectingKind::Operator, p))?.slice;
		CheckLayout!(leftmost => stream);
		match *stream.current()
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
		if block_start.satisfy(stream.current(), true) && stream.current().is_equal() { stream.shift(); }
		else { return Err(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
		let (mut constructors, mut correct_brk) = (Vec::new(), false);
		while block_start.into_exclusive().satisfy(stream.current(), true)
		{
			let prefix_constructor = if stream.current().is_begin_enclosure_of(EnclosureKind::Parenthese) { true }
				else if let TokenKind::Operator(_) = *stream.nth(1) { false }
				else { true };
			let dc = if prefix_constructor { prefix(stream, defblock_begin) } else { infix(stream, defblock_begin) }.into_result_opt()?;
			if let Some(p) = dc { constructors.push(p); } else { break; }

			if let TokenKind::Operator(Source { slice: "|", .. }) = *stream.current() { stream.shift(); }
			else { correct_brk = true; break; }
		}
		if !correct_brk { return Err(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
		defs.place_back() <- (pat, constructors);

		let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
		if block_start.is_nothing() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
		{
			return Ok(TypeDeclaration { location: location.clone(), defs })
		}
		if !delimitered || (stream.on_linehead() && block_start.into_exclusive().satisfy(stream.current(), false)) { break; }
	}
	if block_start.is_nothing() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
	Ok(TypeDeclaration { location: location.clone(), defs })
}
/// ident | ( operator )
fn prefix_declarator<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, (&'t Location, &'s str)>
{
	let leftmost = leftmost.into_nothing_as(Leftmost::Inclusive(stream.current().position().column));
	if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
	match *stream.current()
	{
		TokenKind::Identifier(Source { slice, ref pos, .. }) => { stream.shift(); Success((pos, slice)) },
		TokenKind::BeginEnclosure(ref p, EnclosureKind::Parenthese) =>
		{
			stream.shift();
			let name = take_operator(stream).map_err(|p| ParseError::Expecting(ExpectingKind::Operator, p))?.slice;
			if stream.current().is_end_enclosure_of(EnclosureKind::Parenthese) { stream.shift(); Success((p, name)) }
			else { Failed(ParseError::ExpectingClose(EnclosureKind::Parenthese, stream.current().position())) }
		},
		_ => NotConsumed
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

pub fn depth_state<'s: 't, 't, S: TokenStream<'s, 't>>(tok: &mut S, sink: &mut ShadingStates) -> ParseResult<'t, ()>
{
	let disabling = TMatch!(Optional: tok; TokenKind::Operator(Source { slice: "!", .. }));

	match *tok.current()
	{
		TokenKind::Keyword(_, Keyword::DepthTest) =>
		{
			tok.shift();
			sink.depth_test = if disabling { ShadingState::Disable } else
			{
				ShadingState::Enable({
					let c = CompareOp::classify(tok.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?;
					tok.shift(); c
				})
			};
			Success(())
		},
		TokenKind::Keyword(_, Keyword::DepthWrite) => { tok.shift(); sink.depth_write = if disabling { ShadingState::Disable } else { ShadingState::Enable(()) }; Success(()) },
		TokenKind::Keyword(_, Keyword::DepthBounds) =>
		{
			tok.shift();
			sink.depth_bounds = if disabling { ShadingState::Disable } else
			{
				let min = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				let max = TMatch!(Numeric: tok; |p| ParseError::Expecting(ExpectingKind::Numeric, p));
				ShadingState::Enable([min.as_f32(), max.as_f32()])
			};
			Success(())
		},
		TokenKind::Keyword(ref p, k@Keyword::StencilOps) | TokenKind::Keyword(ref p, k@Keyword::StencilCompare) | TokenKind::Keyword(ref p, k@Keyword::StencilWriteMask)
			 if disabling => Failed(ParseError::PartialDisabling(k, p)),
		TokenKind::Keyword(_, Keyword::StencilOps) =>
		{
			tok.shift();
			let opf  = StencilOp::classify(tok.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?; tok.shift();
			let opp  = StencilOp::classify(tok.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?; tok.shift();
			let opdf = StencilOp::classify(tok.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::StencilOps, tok.current().position()))?; tok.shift();
			sink.stencil_test.modify_part().op_fail = opf;
			sink.stencil_test.modify_part().op_pass = opp;
			sink.stencil_test.modify_part().op_depth_fail = opdf;
			Success(())
		},
		TokenKind::Keyword(_, Keyword::StencilCompare) =>
		{
			tok.shift();
			let op = CompareOp::classify(tok.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::CompareOps, tok.current().position()))?; tok.shift();
			let mask = if tok.current().is_begin_enclosure_of(EnclosureKind::Parenthese)
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
			Success(())
		},
		TokenKind::Keyword(_, Keyword::StencilWriteMask) =>
		{
			tok.shift();
			let mask = TMatch!(tok; TokenKind::Numeric(Source { slice, .. }, _) => slice.parse().unwrap(), |p| ParseError::Expecting(ExpectingKind::Numeric, p));
			sink.stencil_test.modify_part().write_mask = mask;
			Success(())
		},
		TokenKind::Keyword(_, Keyword::StencilTest) if disabling => { tok.shift(); sink.stencil_test = ShadingState::Disable; Success(()) },
		ref e if disabling => Failed(ParseError::Expecting(ExpectingKind::DepthStencilStates, e.position())),
		_ => NotConsumed
	}
}
pub trait Parser<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, Self::ResultTy> where 's: 't;
}
pub trait ParserWithIndent<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S, leftmost: usize) -> ParseResult<'t, Self::ResultTy> where 's: 't;
}
pub trait ShadingStateParser<'s> : Parser<'s>
{
	const HEADING_KEYWORD: Keyword;
	fn switched_parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, ShadingState<<Self as Parser<'s>>::ResultTy>> where 's: 't
	{
		if let TokenKind::Operator(Source { slice: "!", .. }) = *tok.current()
		{
			tok.shift();
			match *tok.current()
			{
				TokenKind::Keyword(_, kw) if kw == Self::HEADING_KEYWORD => { tok.shift(); Success(ShadingState::Disable) },
				ref e => Failed(ParseError::Expecting(ExpectingKind::Keyword(Self::HEADING_KEYWORD), e.position()))
			}
		}
		else { Self::parse(tok).map(ShadingState::Enable) }
	}
}
fn maybe_enclosed<'s: 't, 't, S: TokenStream<'s, 't>, F, R>(stream: &mut S, inner: F) -> Result<R, ParseError<'t>>
	where F: FnOnce(&mut S) -> Result<R, ParseError<'t>>
{
	let in_enclosure = TMatch!(Optional: stream; TokenKind::BeginEnclosure(_, e) => e);
	let r = inner(stream)?;
	if let Some(k) = in_enclosure
	{
		match *stream.current()
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
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, Self::ResultTy> where 's: 't
	{
		fn pat_poland<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, (BlendOp, BlendFactor, BlendFactor)>
		{
			let op = if let Some(o) = BlendOp::classify(stream.current()) { stream.shift(); o } else { return NotConsumed; };
			let srcfactor = BlendFactor::parse(stream)?;
			let dstfactor = BlendFactor::parse(stream)?;
			Success((op, srcfactor, dstfactor))
		}
		fn pat_infix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, (BlendOp, BlendFactor, BlendFactor)>
		{
			let srcfactor = BlendFactor::parse(stream)?;
			let op = BlendOp::classify(stream.current()).ok_or_else(|| ParseError::Expecting(ExpectingKind::BlendOps, stream.current().position()))?; stream.shift();
			let dstfactor = BlendFactor::parse(stream)?;
			Success((op, srcfactor, dstfactor))
		}

		TMatchFirst!(tok; TokenKind::Keyword(_, Self::HEADING_KEYWORD));
		let (color_op, color_factor_src, color_factor_dest) = maybe_enclosed(tok, |stream|
		{
			let save = stream.save();
			pat_poland(stream).or_else(|| pat_infix(stream.restore(save))).into_result(|| ParseError::Expecting(ExpectingKind::BlendOps, stream.current().position()))
		})?;
		let (alpha_op, alpha_factor_src, alpha_factor_dest) = maybe_enclosed(tok, |stream|
		{
			let save = stream.save();
			pat_poland(stream).or_else(|| pat_infix(stream.restore(save))).into_result(|| ParseError::Expecting(ExpectingKind::BlendOps, stream.current().position()))
		})?;

		Success(BlendingStateConfig { color_op, color_factor_src, color_factor_dest, alpha_op, alpha_factor_src, alpha_factor_dest })
	}
}
impl CompareOp
{
	fn classify(tok: &TokenKind) -> Option<Self>
	{
		match *tok
		{
			TokenKind::Keyword(_, Keyword::Always) => Some(CompareOp::Always),
			TokenKind::Keyword(_, Keyword::Never)  => Some(CompareOp::Never),
			TokenKind::Keyword(_, Keyword::Equal)     | TokenKind::Operator(Source { slice: "==", .. }) => Some(CompareOp::Equal),
			TokenKind::Keyword(_, Keyword::Inequal)   | TokenKind::Operator(Source { slice: "!=", .. }) => Some(CompareOp::Inequal),
			TokenKind::Keyword(_, Keyword::Greater)   | TokenKind::Operator(Source { slice: ">", .. })  => Some(CompareOp::Greater),
			TokenKind::Keyword(_, Keyword::Less)      | TokenKind::Operator(Source { slice: "<", .. })  => Some(CompareOp::Less),
			TokenKind::Keyword(_, Keyword::GreaterEq) | TokenKind::Operator(Source { slice: ">=", .. }) => Some(CompareOp::GreaterEq),
			TokenKind::Keyword(_, Keyword::LessEq)    | TokenKind::Operator(Source { slice: "<=", .. }) => Some(CompareOp::LessEq),
			_ => None
		}
	}
}
impl StencilOp
{
	fn classify(tok: &TokenKind) -> Option<Self>
	{
		match *tok
		{
			TokenKind::Keyword(_, Keyword::Keep)      => Some(StencilOp::Keep),
			TokenKind::Keyword(_, Keyword::Zero)      => Some(StencilOp::Zero),
			TokenKind::Keyword(_, Keyword::Replace)   => Some(StencilOp::Replace),
			TokenKind::Keyword(_, Keyword::Invert)    => Some(StencilOp::Invert),
			TokenKind::Keyword(_, Keyword::IncrWrap)  => Some(StencilOp::IncrementWrap),
			TokenKind::Keyword(_, Keyword::DecrWrap)  => Some(StencilOp::DecrementWrap),
			TokenKind::Keyword(_, Keyword::IncrClamp) => Some(StencilOp::IncrementClamp),
			TokenKind::Keyword(_, Keyword::DecrClamp) => Some(StencilOp::DecrementClamp),
			_ => None
		}
	}
}
impl BlendOp
{
	fn classify(tok: &TokenKind) -> Option<Self>
	{
		match *tok
		{
			TokenKind::Keyword(_, Keyword::Add) => Some(BlendOp::Add),
			TokenKind::Keyword(_, Keyword::Sub) => Some(BlendOp::Sub),
			_ => None
		}
	}
}
impl<'s> Parser<'s> for BlendFactor
{
	type ResultTy = Self;
	fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Self> where 's: 't
	{
		let inv = TMatch!(Optional: stream; TokenKind::Operator(Source { slice: "~", .. }));
		match *stream.current()
		{
			TokenKind::Keyword(_, Keyword::SrcColor)  => { stream.shift(); Success(BlendFactor::SrcColor (inv)) },
			TokenKind::Keyword(_, Keyword::SrcAlpha)  => { stream.shift(); Success(BlendFactor::SrcAlpha (inv)) },
			TokenKind::Keyword(_, Keyword::DestColor) => { stream.shift(); Success(BlendFactor::DestColor(inv)) },
			TokenKind::Keyword(_, Keyword::DestAlpha) => { stream.shift(); Success(BlendFactor::DestAlpha(inv)) },
			ref n@TokenKind::Numeric(_, _) | ref n@TokenKind::NumericF(_, _) =>
				if n.match1() { stream.shift(); Success(if inv { BlendFactor::Zero } else { BlendFactor::One }) }
				else if n.match0() { stream.shift(); Success(if inv { BlendFactor::One } else { BlendFactor::Zero }) }
				else if inv { Failed(ParseError::BlendFactorRestriction(n.position())) }
				else { NotConsumed },
			ref e if inv => Failed(ParseError::Expecting(ExpectingKind::BlendFactors, e.position())),
			_ => NotConsumed
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShaderStage { Vertex, Fragment, Geometry, Hull, Domain }
/// シェーダステージ定義
#[derive(Debug, Clone)]
pub struct ShaderStageDefinition<'s>
{
	pub location: Location,
	pub inputs: Vec<SemanticInput<'s>>, pub outputs: Vec<SemanticOutput<'s>>,
	pub uniforms: Vec<UniformDeclaration<'s>>, pub constants: Vec<ConstantDeclaration<'s>>,
	pub values: Vec<ValueDeclaration<'s>>, pub assoc: RcMut<AssociativityEnv<'s>>
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
/// assert_eq!(def.location, Location::default());
/// assert_eq!(def.inputs, vec![SemanticInput { location: Location { line: 1, column: 16 }, name: Some("uv"), semantics: Semantics::Texcoord(0), _type: BType::FVec(2) }]);
/// assert!(def.outputs.is_empty()); assert!(def.uniforms.is_empty()); assert!(def.constants.is_empty()); assert!(def.values.is_empty());
/// ```
pub fn shader_stage_definition<'s: 't, 't, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResultM<'t, (ShaderStage, ShaderStageDefinition<'s>)>
{
	let (location, stage) = match *tok.current()
	{
		TokenKind::Keyword(ref pos, Keyword::VertexShader) => (pos, ShaderStage::Vertex),
		TokenKind::Keyword(ref pos, Keyword::FragmentShader) => (pos, ShaderStage::Fragment),
		TokenKind::Keyword(ref pos, Keyword::GeometryShader) => (pos, ShaderStage::Geometry),
		TokenKind::Keyword(ref pos, Keyword::HullShader) => (pos, ShaderStage::Hull),
		TokenKind::Keyword(ref pos, Keyword::DomainShader) => (pos, ShaderStage::Domain),
		_ => return NotConsumedM
	}; tok.shift();
	TMatch!(tok; TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingOpen(EnclosureKind::Parenthese, p)]);
	let inputs = if !tok.current().is_end_enclosure_of(EnclosureKind::Parenthese)
	{
		let mut inputs = vec![SemanticInput::parse(tok)?];
		while tok.current().is_list_delimiter()
		{
			tok.shift_while(|t| t.kind.is_list_delimiter());
			if tok.current().is_end_enclosure_of(EnclosureKind::Parenthese) { break; }
			inputs.place_back() <- SemanticInput::parse(tok)?;
		}
		inputs
	}
	else { Vec::new() };
	TMatch!(tok; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| vec![ParseError::ExpectingClose(EnclosureKind::Parenthese, p)]);
	let block_start_opt = match *tok.current()
	{
		TokenKind::ItemDescriptorDelimiter(_) | TokenKind::Keyword(_, Keyword::Where) => { Some(take_current_block_begin(tok.shift())) }
		_ => None
	};
	if let Some(block_start) = block_start_opt
	{
		let (mut outputs, mut uniforms, mut constants, mut values) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
		let assoc = new_rcmut(AssociativityEnv::new(None));
		let mut errors = Vec::new();
		while block_start.satisfy(tok.current(), true)
		{
			let defblock_begin = get_definition_leftmost(block_start, tok);
			match *tok.current()
			{
				TokenKind::EOF(_) => break,
				TokenKind::Keyword(_, Keyword::Infix) => match Associativity::parse(tok).into_result(|| ParseError::Expecting(ExpectingKind::Infix, tok.current().position()))
				{
					Ok((ops, a)) => for op in ops
					{
						if let Some(p) = assoc.borrow_mut().register(op.slice, op.pos, a)
						{
							errors.place_back() <- ParseError::DuplicatePrecedences(p.clone(), tok.current().position());
						}
					},
					Err(e) =>
					{
						errors.push(e); tok.drop_line();
						while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
					}
				},
				TokenKind::Keyword(_, Keyword::Uniform) => match UniformDeclaration::parse(tok, defblock_begin)
				{
					Success(v) => { uniforms.push(v); },
					Failed(e) =>
					{
						errors.push(e); tok.drop_line();
						while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
					},
					_ => unreachable!()
				},
				TokenKind::Keyword(_, Keyword::Constant) => match ConstantDeclaration::parse(tok, defblock_begin)
				{
					Success(v) => { constants.push(v); },
					Failed(e) =>
					{
						errors.push(e); tok.drop_line();
						while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
					},
					_ => unreachable!()
				},
				TokenKind::Keyword(_, Keyword::Out) => match SemanticOutput::parse(tok, defblock_begin)
				{
					Success(v) => { outputs.push(v); },
					Failed(e) =>
					{
						errors.push(e); tok.drop_line();
						while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); }
					},
					_ => unreachable!()
				},
				TokenKind::Keyword(_, Keyword::Let) =>
				{
					tok.shift();
					match ValueDeclaration::parse(tok, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, tok.current().position()))
					{
						Ok(v) => values.push(v),
						Err(e) => { errors.push(e); tok.drop_line(); while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); } }
					}
				},
				_ => match ValueDeclaration::parse(tok, defblock_begin).into_result(|| ParseError::Unexpected(tok.current().position()))
				{
					Ok(v) => values.push(v),
					Err(e) => { errors.push(e); tok.drop_line(); while Leftmost::Exclusive(defblock_begin).satisfy(tok.current(), false) { tok.drop_line(); } }
				}
			}
		}
		if errors.is_empty() { SuccessM((stage, ShaderStageDefinition { location: location.clone(), inputs, outputs, uniforms, constants, values, assoc })) }
		else { FailedM(errors) }
	}
	else
	{
		SuccessM((stage, ShaderStageDefinition
		{
			location: location.clone(), inputs: Vec::new(), outputs: Vec::new(), uniforms: Vec::new(), constants: Vec::new(), values: Vec::new(),
			assoc: new_rcmut(AssociativityEnv::new(None))
		}))
	}
}
