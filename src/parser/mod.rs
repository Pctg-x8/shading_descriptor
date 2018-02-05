//! Syntax Parser

#[macro_use] pub mod utils;
pub mod err; mod block;
mod assoc; mod expr; mod types; mod decls; mod class;
pub use self::err::{Success, SuccessM, Failed, FailedM, NotConsumed, NotConsumedM};
use self::utils::*; use self::err::*; use self::block::*;
use tokparse::*;
use std::rc::Rc; use std::cell::RefCell;
use Position;

// child parsers //
pub use self::types::{FullTypeDesc, TypeSynTree, TypeFn, TypeDeclaration, DataConstructor, InferredArrayDim};
pub use self::expr::{FullExpression, ExpressionSynTree, BlockContent, ExprPatSynTree, Binding};
pub use self::decls::{ValueDeclaration, UniformDeclaration, ConstantDeclaration, SemanticOutput, SemanticInput};
pub use self::assoc::{Associativity, AssociativityEnv, AssociativityEnvironment};
pub use self::class::{ClassDef, InstanceDef};

type RcMut<T> = Rc<RefCell<T>>;
fn new_rcmut<T>(init: T) -> RcMut<T> { Rc::new(RefCell::new(init)) }

/// ident (. ident)*
fn module_path<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Vec<&'t Source<'s>>>
{
	let mut idents = vec![match shift_satisfy_leftmost(stream, leftmost, |s| s.shift_identifier()) { Ok(v) => v, _ => return NotConsumed }];
	let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(idents[0].position().column)).into_exclusive();
	while shift_satisfy_leftmost(stream, leftmost, S::shift_object_descender).is_ok()
	{
		match shift_satisfy_leftmost(stream, leftmost, S::shift_identifier)
		{
			Ok(ident) => { idents.push(ident); }, Err(p) => return Failed(ParseError::Expecting(ExpectingKind::Ident, p))
		}
	}
	Success(idents)
}
/// [as ident]
fn maybe_qualified<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<Option<&'t Source<'s>>, ParseError<'t>>
{
	if stream.shift_keyword(Keyword::As).is_ok()
	{
		stream.shift_identifier().map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p)).map(Some)
	}
	else { Ok(None) }
}
/// module_path [as ident / "(" [ident [as ident] (, ident [as ident])*] ")"]
fn import1<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, SymbolImportSpec<'s>>
{
	let path = BreakParsing!(module_path(stream, leftmost));
	let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(path.position().column)).into_exclusive();
	if leftmost.satisfy(stream.current())
	{
		match *stream.current()
		{
			TokenKind::Keyword(_, Keyword::As) =>
			{
				stream.shift();
				stream.shift_identifier().map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))
					.map(|a| SymbolImportSpec::Qualified(path.into_iter().cloned().collect(), a.clone())).into()
			},
			TokenKind::Keyword(_, Keyword::Hiding) =>
			{
				stream.shift();
				let mut subimports = Vec::new();
				if let Ok(s1) = stream.shift_identifier()
				{
					subimports.push(s1);
					while stream.shift_list_delimiter().is_ok()
					{
						subimports.place_back() <- TMatch!(stream; TokenKind::Identifier(ref s) => s, |p| ParseError::Expecting(ExpectingKind::Ident, p));
					}
				}
				TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
				Success(if subimports.is_empty()
				{
					SymbolImportSpec::PathOnly(path.into_iter().cloned().collect())
				}
				else
				{
					SymbolImportSpec::HidingSubimports(path.into_iter().cloned().collect(), subimports.into_iter().cloned().collect())
				})
			},
			TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) =>
			{
				stream.shift();
				let mut subimports = Vec::new();
				if let Ok(s1) = stream.shift_identifier()
				{
					subimports.place_back() <- (s1.clone(), maybe_qualified(stream)?.map(Clone::clone));
					while stream.shift_list_delimiter().is_ok()
					{
						let s = TMatch!(stream; TokenKind::Identifier(ref s) => s, |p| ParseError::Expecting(ExpectingKind::Ident, p));
						subimports.place_back() <- (s.clone(), maybe_qualified(stream)?.map(Clone::clone));
					}
				}
				TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
				Success(if subimports.is_empty()
				{
					SymbolImportSpec::PathOnly(path.into_iter().cloned().collect())
				}
				else
				{
					SymbolImportSpec::WithSubimports(path.into_iter().cloned().collect(), subimports)
				})
			},
			_ => Success(SymbolImportSpec::PathOnly(path.into_iter().cloned().collect()))
		}
	}
	else { Success(SymbolImportSpec::PathOnly(path.into_iter().cloned().collect())) }
}

/// インポート
#[derive(Debug, Clone)]
pub enum SymbolImportSpec<'s>
{
	PathOnly(Vec<Source<'s>>), Qualified(Vec<Source<'s>>, Source<'s>),
	WithSubimports(Vec<Source<'s>>, Vec<(Source<'s>, Option<Source<'s>>)>),
	HidingSubimports(Vec<Source<'s>>, Vec<Source<'s>>)
}
#[derive(Debug, Clone)] pub struct SymbolImport<'s> { pub qualified: bool, pub spec: SymbolImportSpec<'s> }
impl<'s> BlockParser<'s> for SymbolImport<'s>
{
	type ResultTy = Vec<Self>;
	fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Vec<Self>> where 's: 't
	{
		TMatchFirst!(stream; TokenKind::Keyword(_, Keyword::Import));
		let qualified = TMatch!(Optional: stream; TokenKind::Keyword(_, Keyword::Qualified));
		let blk_start = take_current_block_begin(stream);
		
		let mut imports = vec![
			import1(stream, blk_start).into_result(|| ParseError::Expecting(ExpectingKind::ModulePath, stream.current().position()))
				.map(|spec| SymbolImport { qualified, spec })?
		];
		while stream.shift_list_delimiter().is_ok()
		{
			imports.place_back() <- import1(stream, blk_start).into_result(|| ParseError::Expecting(ExpectingKind::ModulePath, stream.current().position()))
				.map(|spec| SymbolImport { qualified, spec })?;
		}
		Success(imports)
	}
}

/// シェーディングパイプライン(コンパイル単位)
#[derive(Debug, Clone)]
pub struct ShadingPipeline<'s>
{
	state: ShadingStates, pub imports: Vec<SymbolImport<'s>>,
	pub vsh: Option<ShaderStageDefinition<'s>>,
	pub hsh: Option<ShaderStageDefinition<'s>>, pub dsh: Option<ShaderStageDefinition<'s>>,
	pub gsh: Option<ShaderStageDefinition<'s>>, pub fsh: Option<ShaderStageDefinition<'s>>,
	pub values: Vec<ValueDeclaration<'s>>, types: Vec<TypeDeclaration<'s>>, typefns: Vec<TypeFn<'s>>,
	pub assoc: RcMut<AssociativityEnv<'s>>,
	pub classes: Vec<ClassDef<'s>>, pub instances: Vec<InstanceDef<'s>>
}
pub fn shading_pipeline<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<ShadingPipeline<'s>, Vec<ParseError<'t>>>
{
	let mut sp = ShadingPipeline
	{
		state: Default::default(), imports: Vec::new(), vsh: None, hsh: None, dsh: None, gsh: None, fsh: None,
		values: Vec::new(), types: Vec::new(), typefns: Vec::new(), assoc: new_rcmut(AssociativityEnv::new(None)),
		classes: Vec::new(), instances: Vec::new()
	};
	let mut errors = Vec::new();

	loop
	{
		let leftmost = Leftmost::Inclusive(get_definition_leftmost(Leftmost::Inclusive(1), stream));
		let mut errors_t = Vec::new();
		let inst = stream.save();
		match *stream.current()
		{
			TokenKind::Keyword(_, Keyword::Type) => match TypeFn::parse(stream)
			{
				Failed(e) => { errors_t.push(e); }, Success(tf) => { sp.typefns.push(tf); continue; }, _ => unreachable!()
			},
			TokenKind::Keyword(_, Keyword::Data) => match TypeDeclaration::parse(stream)
			{
				Failed(e) => { errors_t.push(e); }, Success(td) => { sp.types.push(td); continue; }, _ => unreachable!()
			},
			TokenKind::Keyword(_, Keyword::Import) => match SymbolImport::parse(stream)
			{
				Failed(e) => { errors_t.push(e); }, Success(mut sis) => { sp.imports.append(&mut sis); continue; }, _ => unreachable!()
			},
			TokenKind::Keyword(_, Keyword::Class) => match ClassDef::parse(stream)
			{
				FailedM(mut e) => { errors_t.append(&mut e); }, SuccessM(cd) => { sp.classes.push(cd); continue; }, _ => unreachable!()
			},
			TokenKind::Keyword(_, Keyword::Instance) => match InstanceDef::parse(stream)
			{
				FailedM(mut e) => { errors_t.append(&mut e); }, SuccessM(id) => { sp.instances.push(id); continue; }, _ => unreachable!()
			},
			TokenKind::Keyword(_, Keyword::Infix) | TokenKind::Keyword(_, Keyword::Infixl) | TokenKind::Keyword(_, Keyword::Infixr) => match Associativity::parse(stream)
			{
				Success((v, a)) =>
				{
					for op in v
					{
						if let Some(p) = sp.assoc.borrow_mut().register(op.slice, op.pos, a)
						{
							errors_t.place_back() <- ParseError::DuplicatePrecedences(p.clone(), stream.current().position());
						}
					}
					if errors_t.is_empty() { continue; }
				},
				Failed(e) => { errors_t.push(e); }, _ => unreachable!()
			},
			_ => ()
		}
		match ShaderStageDefinition::parse(stream)
		{
			SuccessM((ShaderStage::Vertex, v))   => { v.assoc.borrow_mut().parent = Some(Rc::downgrade(&sp.assoc)); sp.vsh = Some(v); continue; }
			SuccessM((ShaderStage::Hull, v))     => { v.assoc.borrow_mut().parent = Some(Rc::downgrade(&sp.assoc)); sp.hsh = Some(v); continue; }
			SuccessM((ShaderStage::Domain, v))   => { v.assoc.borrow_mut().parent = Some(Rc::downgrade(&sp.assoc)); sp.dsh = Some(v); continue; }
			SuccessM((ShaderStage::Geometry, v)) => { v.assoc.borrow_mut().parent = Some(Rc::downgrade(&sp.assoc)); sp.gsh = Some(v); continue; }
			SuccessM((ShaderStage::Fragment, v)) => { v.assoc.borrow_mut().parent = Some(Rc::downgrade(&sp.assoc)); sp.fsh = Some(v); continue; }
			FailedM(mut e) => { errors_t.append(&mut e); }, _ => ()
		}
		match BlendingStateConfig::switched_parse(stream.restore(inst))
		{
			Success(bs) => { sp.state.blending = bs; continue; }, Failed(e) => { errors_t.push(e); }, _ => ()
		}
		match depth_state(stream.restore(inst), &mut sp.state)
		{
			Failed(e) => { errors_t.push(e); }, Success(_) => continue, _ => ()
		}
		match ValueDeclaration::parse(stream.restore(inst), leftmost)
		{
			Failed(e) => { errors_t.push(e); }, Success(v) => { sp.values.push(v); continue; }, _ => ()
		}
		let has_error = !errors_t.is_empty();
		errors.append(&mut errors_t);
		if has_error
		{
			stream.drop_line(); while leftmost.into_exclusive().satisfy(stream.current()) { stream.drop_line(); }
		}
		else { break; }
	}
	if errors.is_empty() { Ok(sp) } else { Err(errors) }
}
impl<'s> AssociativityEnvironment<'s> for ShadingPipeline<'s> { fn assoc_env(&self) -> &RcMut<AssociativityEnv<'s>> { &self.assoc } }

/// シェーディングパイプラインステート
#[derive(Debug, Clone, PartialEq)]
pub enum ShadingState<T> { Enable(T), Disable }
impl<T: Copy> Copy for ShadingState<T> {}
impl<T: Eq> Eq for ShadingState<T> {}
impl<T: Default> ShadingState<T>
{
	fn modify_part(&mut self) -> &mut T
	{
		if let ShadingState::Disable = *self { *self = ShadingState::Enable(T::default()); }
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

/// Parses a depth state
/// # Examples
///
/// ```
/// # use pureshader::*;
/// let mut ss = ShadingStates::default();
/// let src = TokenizerState::from("!DepthTest").strip_all();
/// depth_state(&mut PreanalyzedTokenStream::from(&src[..]), &mut ss).expect("!DepthTest");
/// let src = TokenizerState::from("!DepthWrite").strip_all();
/// depth_state(&mut PreanalyzedTokenStream::from(&src[..]), &mut ss).expect("!DepthWrite");
/// let src = TokenizerState::from("DepthBounds 0.0 1.0").strip_all();
/// depth_state(&mut PreanalyzedTokenStream::from(&src[..]), &mut ss).expect("DepthBounds");
/// let src = TokenizerState::from("!StencilTest").strip_all();
/// depth_state(&mut PreanalyzedTokenStream::from(&src[..]), &mut ss).expect("!StencilTest");
/// let src = TokenizerState::from("StencilWriteMask 128").strip_all();
/// depth_state(&mut PreanalyzedTokenStream::from(&src[..]), &mut ss).expect("StencilWriteMask");
/// ```
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
/// Parser of a block
pub trait BlockParser<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, Self::ResultTy> where 's: 't;
}
/// Parser of a block, yielding multiple errors
pub trait BlockParserM<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResultM<'t, Self::ResultTy> where 's: 't;
}
/// Parser of an indented element
pub trait Parser<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self::ResultTy> where 's: 't;
}
/// Parser of an indent independent element
pub trait FreeParser<'s>
{
	type ResultTy: 's;
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, Self::ResultTy> where 's: 't;
}
/// Parser of a shading state, which can disable following "!"
pub trait ShadingStateParser<'s> : FreeParser<'s>
{
	const HEADING_KEYWORD: Keyword;
	fn switched_parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResult<'t, ShadingState<<Self as FreeParser<'s>>::ResultTy>> where 's: 't
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
/// "(" <inner> ")" / <inner>
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
impl<'s> FreeParser<'s> for BlendingStateConfig
{
	type ResultTy = Self;
	/// Parses a blending state
	/// # Examples
	///
	/// ```
	/// # use pureshader::*;
	/// let src = TokenizerState::from("Blend (Add 1 ~SrcAlpha) (~DestAlpha + 1)").strip_all();
	/// println!("{:?}", src);
	/// BlendingStateConfig::parse(&mut PreanalyzedTokenStream::from(&src[..])).unwrap();
	/// ```
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
			let srcfactor = BreakParsing!(BlendFactor::parse(stream));
			println!("infix op: {:?}", stream.current());
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
			TokenKind::Keyword(_, Keyword::Add) | TokenKind::Operator(Source { slice: "+", .. }) | TokenKind::Operator(Source { slice: "＋", .. }) => Some(BlendOp::Add),
			TokenKind::Keyword(_, Keyword::Sub) | TokenKind::Operator(Source { slice: "-", .. }) | TokenKind::Operator(Source { slice: "ー", .. }) => Some(BlendOp::Sub),
			_ => None
		}
	}
}
impl<'s> FreeParser<'s> for BlendFactor
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

/// "(" [?] (, ?)* ")"
fn parse_parenthesed_list<'s: 't, 't, S: TokenStream<'s, 't>, R, F, E>(stream: &mut S, childparser: F, head_error: E) -> ParseResultM<'t, Vec<R>>
	where F: Fn(&mut S) -> ParseResult<'t, R>, E: Fn(&'t Location) -> ParseError<'t>
{
	stream.shift_begin_enclosure_of(EnclosureKind::Parenthese).map_err(|p| ParseError::ExpectingOpen(EnclosureKind::Parenthese, p))?;
	let mut err = Vec::new();
	let r = if stream.current().is_end_enclosure_of(EnclosureKind::Parenthese) { Vec::new() }
	else
	{
		let mut vs = match childparser(stream)
		{
			NotConsumed =>
			{
				err.place_back() <- head_error(stream.current().position());
				stream.shift_until(|t| t.kind.is_end_enclosure_of(EnclosureKind::Parenthese) || t.kind.is_list_delimiter());
				Vec::new()
			},
			Failed(e) =>
			{
				err.push(e);
				stream.shift_until(|t| t.kind.is_end_enclosure_of(EnclosureKind::Parenthese) || t.kind.is_list_delimiter());
				Vec::new()
			}, Success(v) => vec![v]
		};
		while stream.shift_many(TokenKind::is_list_delimiter).is_ok()
		{
			if stream.current().is_end_enclosure_of(EnclosureKind::Parenthese) { break; }
			match childparser(stream)
			{
				NotConsumed =>
				{
					err.place_back() <- head_error(stream.current().position());
					stream.shift_until(|t| t.kind.is_end_enclosure_of(EnclosureKind::Parenthese) || t.kind.is_list_delimiter());
				},
				Failed(e) =>
				{
					err.push(e);
					stream.shift_until(|t| t.kind.is_end_enclosure_of(EnclosureKind::Parenthese) || t.kind.is_list_delimiter());
				}, Success(v) => { vs.push(v); }
			}
		}
		vs
	};
	if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Parenthese) { err.place_back() <- ParseError::expect_close_parenthese(p); }
	if err.is_empty() { SuccessM(r) } else { FailedM(err) }
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
	pub values: Vec<ValueDeclaration<'s>>, pub assoc: RcMut<AssociativityEnv<'s>>,
	pub typedecls: Vec<TypeDeclaration<'s>>, pub typefns: Vec<TypeFn<'s>>
}
impl<'s> ShaderStageDefinition<'s>
{
	pub fn empty() -> Self
	{
		ShaderStageDefinition
		{
			location: Location::default(), inputs: Vec::new(), outputs: Vec::new(),
			uniforms: Vec::new(), constants: Vec::new(), values: Vec::new(), assoc: new_rcmut(AssociativityEnv::new(None)),
			typedecls: Vec::new(), typefns: Vec::new()
		}
	}
}
impl<'s> BlockParserM<'s> for ShaderStageDefinition<'s>
{
	type ResultTy = (ShaderStage, ShaderStageDefinition<'s>);
	/// Parse an shader stage definition  
	/// <ShaderStage> "(" <SemanticInput>,* ")" [":"/"where" ...]
	/// # Example
	/// 
	/// ```
	/// # use pureshader::*;
	/// let s = TokenizerState::from("FragmentShader(uv(TEXCOORD0): f2,):").strip_all();
	/// let (stg, def) = ShaderStageDefinition::parse(&mut PreanalyzedTokenStream::from(&s[..])).unwrap();
	/// assert_eq!(stg, ShaderStage::Fragment);
	/// assert_eq!((def.inputs[0].name, def.inputs[0].semantics, def.inputs[0]._type), (Some("uv"), Semantics::Texcoord(0), BType::FVec(2)));
	/// ```
	fn parse<'t, S: TokenStream<'s, 't>>(tok: &mut S) -> ParseResultM<'t, (ShaderStage, ShaderStageDefinition<'s>)> where 's: 't
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
		let leftmost = Leftmost::Inclusive(location.column);
		let inputs = parse_parenthesed_list(tok, SemanticInput::parse, ParseError::expect_ident)?;
		let mut def = ShaderStageDefinition { location: location.clone(), inputs, .. Self::empty() };
		if let Ok(block_start) = intro_block(tok, leftmost)
		{
			let mut errors = Vec::new();
			while block_start.satisfy(tok.current())
			{
				if block_start.is_explicit() && tok.shift_end_enclosure_of(EnclosureKind::Brace).is_ok() { return SuccessM((stage, def)); }
				let defblock_begin = Leftmost::Inclusive(get_definition_leftmost(block_start, tok));
				match *tok.current()
				{
					TokenKind::EOF(_) => break,
					TokenKind::Keyword(_, Keyword::Infix) => match Associativity::parse(tok).into_result(|| ParseError::Expecting(ExpectingKind::Infix, tok.current().position()))
					{
						Ok((ops, a)) => for op in ops
						{
							if let Some(p) = def.assoc.borrow_mut().register(op.slice, op.pos, a)
							{
								errors.place_back() <- ParseError::DuplicatePrecedences(p.clone(), tok.current().position());
							}
						},
						Err(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
					},
					TokenKind::Keyword(_, Keyword::Uniform) => match UniformDeclaration::parse(tok, defblock_begin)
					{
						Success(v) => { def.uniforms.push(v); }, Failed(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
						_ => unreachable!()
					},
					TokenKind::Keyword(_, Keyword::Constant) => match ConstantDeclaration::parse(tok, defblock_begin)
					{
						Success(v) => { def.constants.push(v); }, Failed(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
						_ => unreachable!()
					},
					TokenKind::Keyword(_, Keyword::Out) => match SemanticOutput::parse(tok, defblock_begin)
					{
						Success(v) => { def.outputs.push(v); }, Failed(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
						_ => unreachable!()
					},
					TokenKind::Keyword(_, Keyword::Type) => match TypeFn::parse(tok)
					{
						Success(v) => { def.typefns.push(v); }, Failed(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
						_ => unreachable!()
					},
					TokenKind::Keyword(_, Keyword::Data) => match TypeDeclaration::parse(tok)
					{
						Success(v) => { def.typedecls.push(v); }, Failed(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); },
						_ => unreachable!()
					},
					TokenKind::Keyword(_, Keyword::Let) =>
					{
						tok.shift();
						match ValueDeclaration::parse(tok, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, tok.current().position()))
						{
							Ok(v) => def.values.push(v), Err(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); }
						}
					},
					_ => match ValueDeclaration::parse(tok, defblock_begin).into_result(|| ParseError::Unexpected(tok.current().position()))
					{
						Ok(v) => def.values.push(v), Err(e) => { errors.push(e); drop_for_nextdef(defblock_begin, tok); }
					}
				}
			}
			if let Err(p) = outro_block(tok, block_start) { errors.place_back() <- ParseError::failed_to_leave_block(p); }
			if !errors.is_empty() { return FailedM(errors); }
		}
		SuccessM((stage, def))
	}
}
impl<'s> AssociativityEnvironment<'s> for ShaderStageDefinition<'s> { fn assoc_env(&self) -> &RcMut<AssociativityEnv<'s>> { &self.assoc } }

pub trait TypeDeclarable<'s>
{
	fn type_decls(&self) -> &Vec<TypeDeclaration<'s>>;
	fn type_fns(&self) -> &Vec<TypeFn<'s>>;
}
impl<'s> TypeDeclarable<'s> for ShadingPipeline<'s>
{
	fn type_decls(&self) -> &Vec<TypeDeclaration<'s>> { &self.types } fn type_fns(&self) -> &Vec<TypeFn<'s>> { &self.typefns }
}
impl<'s> TypeDeclarable<'s> for ShaderStageDefinition<'s>
{
	fn type_decls(&self) -> &Vec<TypeDeclaration<'s>> { &self.typedecls } fn type_fns(&self) -> &Vec<TypeFn<'s>> { &self.typefns }
}
