//! Complex type parser

use tokparse::{Location, Source, TokenKind, TokenStream, Keyword, BType, EnclosureKind};
use super::expr::{FullExpression, full_expression};
use super::err::*;
use super::utils::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeSynTree<'s>
{
    Prefix(Vec<TypeSynTree<'s>>), Infix { lhs: Box<TypeSynTree<'s>>, mods: Vec<(Source<'s>, TypeSynTree<'s>)> },
    ArrowInfix { lhs: Box<TypeSynTree<'s>>, rhs: Box<TypeSynTree<'s>> },
    Basic(Location, BType), SymReference(Source<'s>), Placeholder(Location),
    ArrayDim { lhs: Box<TypeSynTree<'s>>, num: InferredArrayDim<'s> },
    PathRef(Box<TypeSynTree<'s>>, Vec<Source<'s>>), Tuple(Vec<TypeSynTree<'s>>)
}
#[derive(Debug, Clone, PartialEq, Eq)] pub enum InferredArrayDim<'s> { Unsized, Inferred(Location), Fixed(FullExpression<'s>) }
/// Arrow <- Infix (-> Infix)*
fn arrow_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut lhs = BreakParsing!(infix_ty(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    while leftmost.satisfy(stream.current(), false) && stream.shift_arrow().is_ok()
    {
        lhs = TypeSynTree::ArrowInfix
        {
            lhs: box lhs,
            rhs: box infix_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?
        };
    }
    Success(lhs)
}
/// Infix <- Prefix ((op|infixident) Prefix)*
fn infix_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let lhs = BreakParsing!(prefix_ty(stream, leftmost)); let leftmost = leftmost.into_exclusive();
    let mut mods = Vec::new();
    while let Ok(op) = shift_infix_ops(stream, leftmost)
    {
        mods.place_back() <- (op.clone(), prefix_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?);
    }
    Success(if mods.is_empty() { lhs } else { TypeSynTree::Infix { lhs: box lhs, mods } })
}
/// Prefix <- Term Term*
fn prefix_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut lhs = vec![BreakParsing!(term_ty(stream, leftmost))];
    let leftmost = leftmost.into_exclusive();
    while let Some(p) = term_ty(stream, leftmost).into_result_opt()? { lhs.push(p); }
    Success(if lhs.len() == 1 { lhs.pop().unwrap() } else { TypeSynTree::Prefix(lhs) })
}
/// Term <- Factor (. ident / [ FullEx ])*
fn term_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut e = BreakParsing!(factor_ty(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            &TokenKind::ObjectDescender(_) =>
            {
                let mut p = Vec::new();
                while stream.shift_object_descender().is_ok()
                {
                    p.place_back() <- TMatch!(stream; TokenKind::Identifier(ref s) => s.clone(), |p| ParseError::Expecting(ExpectingKind::Ident, p));
                }
                assert!(!p.is_empty());
                e = TypeSynTree::PathRef(box e, p);
            },
            &TokenKind::BeginEnclosure(_, EnclosureKind::Bracket) =>
            {
                stream.shift();
                let num = if let Ok(p) = stream.shift_placeholder() { InferredArrayDim::Inferred(p.clone()) }
                    else
                    {
                        full_expression(stream, Leftmost::Nothing).into_result_opt()?.map_or(InferredArrayDim::Unsized, InferredArrayDim::Fixed)
                    };
                if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Bracket) { return Failed(ParseError::ExpectingClose(EnclosureKind::Bracket, p)); }
                e = TypeSynTree::ArrayDim { lhs: box e, num };
            },
            _ => break
        }
    }
    Success(e)
}
/// Factor <- ident / basic / ( Arrow (, Arrow)* )
fn factor_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    match stream.current()
    {
        &TokenKind::Identifier(ref s) => { stream.shift(); Success(TypeSynTree::SymReference(s.clone())) },
        &TokenKind::BasicType(ref p, bt) => { stream.shift(); Success(TypeSynTree::Basic(p.clone(), bt)) },
        &TokenKind::Placeholder(ref p) => { stream.shift(); Success(TypeSynTree::Placeholder(p.clone())) },
        &TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) =>
        {
            let leftmost = leftmost.into_exclusive();
            let mut p = vec![arrow_ty(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?];
            while stream.shift_list_delimiter().is_ok()
            {
                p.place_back() <- arrow_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
            }
            if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Parenthese) { return Failed(ParseError::ExpectingClose(EnclosureKind::Parenthese, p)); }
            Success(if p.len() == 1 { p.pop().unwrap() } else { TypeSynTree::Tuple(p) })
        },
        _ => NotConsumed
    }
}

/// Parses a type
/// # Example
///
/// ```
/// # use pureshader::*;
/// let ts = Source::new("z :+: String").into().all();
/// let _ty = ty(&mut From::from(&ts), Leftmost::Nothing).unwrap();
/// ```
pub fn ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>> { arrow_ty(stream, leftmost) }

/// Quantiied: 明示的なものだけ(forall ..., <tree>)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullTypeDesc<'s> { quantified: Vec<Source<'s>>, constraints: Vec<TypeSynTree<'s>>, tree: TypeSynTree<'s> }
/// Parses a fully descripted type(forall and constraints)
/// # Example
///
/// ```
/// # use pureshader::*;
/// let ts = Source::new("forall z. (Show z, Read z) => Eq z => z -> (z, String)").into().all();
/// let _ty = full_type(&mut From::from(&ts), Leftmost::Nothing).unwrap();
/// ```
pub fn full_type<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, mut leftmost: Leftmost) -> ParseResult<'t, FullTypeDesc<'s>>
{
    let mut quantified = Vec::new();
    while leftmost.satisfy(stream.current(), true) && stream.shift_keyword(Keyword::Forall).is_ok()
    {
        leftmost = leftmost.into_exclusive();
        while let &TokenKind::Identifier(ref s) = stream.current() { stream.shift(); quantified.place_back() <- s.clone(); }
        if !stream.current().is_text_period() { return Failed(ParseError::Expecting(ExpectingKind::Period, stream.current().position())); }
        stream.shift();
    }
    let mut constraints = Vec::new();
    loop
    {
        let tt = match arrow_ty(stream, leftmost)
        {
            NotConsumed if quantified.is_empty() => return NotConsumed,
            NotConsumed => return Failed(ParseError::Expecting(ExpectingKind::Type, stream.current().position())),
            Failed(e) => return Failed(e), Success(s) => s
        };
        leftmost = leftmost.into_exclusive();
        if let &TokenKind::Arrow(_) = stream.current()
        {
            // constraint
            stream.shift();
            match tt
            {
                TypeSynTree::Tuple(mut v) => constraints.append(&mut v),
                t => constraints.push(t)
            }
        }
        else { return Success(FullTypeDesc { quantified, constraints, tree: tt }); }
    }
}

/// 型シノニム/データ定義
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeFn<'s> { pub location: Location, pub defs: Vec<(TypeSynTree<'s>, FullTypeDesc<'s>)> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructor<'s> { pub location: Location, pub name: &'s str, pub args: Vec<&'s str> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclaration<'s> { pub location: Location, pub defs: Vec<(TypeSynTree<'s>, Vec<DataConstructor<'s>>)> }
/// Parse a type synonim declaration
/// # Examples
/// ```
/// # use pureshader::*;
/// let src = Source::new("type Xnum = Int").into().all();
/// type_fn(&mut PreanalyzedTokenStream::from(&src)).expect("in case 1");
/// // multiple definition
/// let src = Source::new("type Xnum a = a; Vec4 = f4").into().all();
/// type_fn(&mut PreanalyzedTokenStream::from(&src)).expect("in case 2");
/// ```
pub fn type_fn<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<TypeFn<'s>, ParseError<'t>>
{
	let location = TMatch!(stream; TokenKind::Keyword(ref p, Keyword::Type) => p, |p| ParseError::Expecting(ExpectingKind::Keyword(Keyword::Type), p));
	let block_start = take_current_block_begin(stream);
	let mut defs = Vec::new();
	while block_start.satisfy(stream.current(), true)
	{
		let defblock_begin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
		let pat = ty(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::TypePattern, stream.current().position()))?;
		let defblock_begin = defblock_begin.into_exclusive();
		if !defblock_begin.satisfy(stream.current(), true) || !stream.current().is_equal()
		{
			return Err(ParseError::Expecting(ExpectingKind::ConcreteType, stream.current().position()));
		}
		stream.shift(); CheckLayout!(defblock_begin => stream);
		let bound = full_type(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
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
/// Parses a data declaration
/// # Examples
///
/// ```
/// # use pureshader::*;
/// let src = Source::new("data Np x = Np x Int").into().all();
/// type_decl(&mut PreanalyzedTokenStream::from(&src)).expect("in simple case");
/// // infix declaration
/// let src = Source::new("data a Np x = x :,: a").into().all();
/// type_decl(&mut PreanalyzedTokenStream::from(&src)).expect("in infix case");
/// ```
pub fn type_decl<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<TypeDeclaration<'s>, ParseError<'t>>
{
	fn prefix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, DataConstructor<'s>>
	{
		let (location, name) = match shift_prefix_declarator(stream, leftmost)
		{
			Success(v) => v, Failed(e) => return Failed(e), NotConsumed => return NotConsumed
		};
		let leftmost = leftmost.into_exclusive();
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
	fn infix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, DataConstructor<'s>>
	{
		if !leftmost.satisfy(stream.current(), false) { return NotConsumed; }
		let (location, arg1) = if let TokenKind::Identifier(ref s) = *stream.current() { stream.shift(); (&s.pos, s.slice) } else { return NotConsumed };
		let leftmost = leftmost.into_exclusive();
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
		let defblock_begin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
		let pat = ty(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
		let defblock_begin = defblock_begin.into_exclusive();
		if defblock_begin.satisfy(stream.current(), true) && stream.current().is_equal() { stream.shift(); }
		else { return Err(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
		let (mut constructors, mut correct_brk) = (Vec::new(), false);
		while defblock_begin.satisfy(stream.current(), true)
		{
			let dc = prefix(stream, defblock_begin).or_else(|| infix(stream, defblock_begin)).into_result_opt()?;
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
