//! Complex type parser

use tokparse::{Location, Source, TokenKind, TokenStream, Keyword, BType, EnclosureKind};
use super::expr::FullExpression;
use super::err::*;
use super::utils::*;
use super::{Parser, BlockParser};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeSynTree<'s>
{
    Prefix(Vec<TypeSynTree<'s>>), Infix { lhs: Box<TypeSynTree<'s>>, mods: Vec<(Source<'s>, TypeSynTree<'s>)> },
    ArrowInfix { op_pos: Location, lhs: Box<TypeSynTree<'s>>, rhs: Box<TypeSynTree<'s>> },
    Basic(Location, BType), SymReference(Source<'s>), Placeholder(Location),
    ArrayDim { lhs: Box<TypeSynTree<'s>>, num: InferredArrayDim<'s> },
    PathRef(Box<TypeSynTree<'s>>, Vec<Source<'s>>), Tuple(Location, Vec<TypeSynTree<'s>>)
}
impl<'s> TypeSynTree<'s>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            TypeSynTree::Prefix(ref v) => v.first().expect("Prefix TypeExpr").position(),
            TypeSynTree::Infix { ref lhs, .. } | TypeSynTree::ArrowInfix { ref lhs, .. } | TypeSynTree::ArrayDim { ref lhs, .. } | TypeSynTree::PathRef(ref lhs, _) => lhs.position(),
            TypeSynTree::Basic(ref l, _) | TypeSynTree::SymReference(Source { pos: ref l, .. }) | TypeSynTree::Placeholder(ref l) | TypeSynTree::Tuple(ref l, _) => l
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)] pub enum InferredArrayDim<'s> { Unsized, Inferred(Location), Fixed(FullExpression<'s>) }
/// Arrow <- Infix (-> Infix)*
fn arrow_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    fn shift_arrow<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> Result<&'t Location, &'t Location>
    {
        if leftmost.satisfy(stream.current(), false) { stream.shift_arrow() } else { Err(stream.current().position()) }
    }
    let mut lhs = BreakParsing!(infix_ty(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
    while let Ok(p) = shift_arrow(stream, leftmost)
    {
        lhs = TypeSynTree::ArrowInfix
        {
            op_pos: p.clone(), lhs: box lhs,
            rhs: box infix_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?
        };
    }
    Success(lhs)
}
/// Infix <- Prefix ((op|infixident) Prefix)*
fn infix_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let lhs = BreakParsing!(prefix_ty(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
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
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs[0].position().column)).into_exclusive();
    while let Some(p) = term_ty(stream, leftmost).into_result_opt()? { lhs.push(p); }
    Success(if lhs.len() == 1 { lhs.pop().unwrap() } else { TypeSynTree::Prefix(lhs) })
}
/// Term <- Factor (. ident / [ FullEx? ])*
fn term_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut e = BreakParsing!(factor_ty(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(e.position().column)).into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        e = match stream.current()
        {
            &TokenKind::ObjectDescender(_) =>
            {
                let mut p = Vec::new();
                while stream.shift_object_descender().is_ok()
                {
                    p.place_back() <- stream.shift_identifier().map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?.clone();
                }
                assert!(!p.is_empty());
                TypeSynTree::PathRef(box e, p)
            },
            &TokenKind::BeginEnclosure(_, EnclosureKind::Bracket) =>
            {
                stream.shift();
                let num = stream.shift_placeholder().map(|p| InferredArrayDim::Inferred(p.clone()))
                    .or_else(|_| FullExpression::parse(stream, Leftmost::Nothing).into_result_opt()
                        .map(|v| v.map_or(InferredArrayDim::Unsized, InferredArrayDim::Fixed)))?;
                stream.shift_end_enclosure_of(EnclosureKind::Bracket).map_err(|p| ParseError::ExpectingClose(EnclosureKind::Bracket, p))?;
                TypeSynTree::ArrayDim { lhs: box e, num }
            },
            _ => break
        }
    }
    Success(e)
}
/// Factor <- ident / basic / ( [Arrow (, Arrow)*] )
fn factor_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, TypeSynTree<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    match stream.current()
    {
        &TokenKind::Identifier(ref s) => { stream.shift(); Success(TypeSynTree::SymReference(s.clone())) },
        &TokenKind::BasicType(ref p, bt) => { stream.shift(); Success(TypeSynTree::Basic(p.clone(), bt)) },
        &TokenKind::Placeholder(ref p) => { stream.shift(); Success(TypeSynTree::Placeholder(p.clone())) },
        &TokenKind::WrappedOp(ref s) => { stream.shift(); Success(TypeSynTree::SymReference(s.clone())) },
        &TokenKind::BeginEnclosure(ref pp, EnclosureKind::Parenthese) =>
        {
            stream.shift();
            if stream.shift_end_enclosure_of(EnclosureKind::Parenthese).is_ok() { return Success(TypeSynTree::Tuple(pp.clone(), Vec::new())); }
            let leftmost = leftmost.into_exclusive();
            let mut p = vec![arrow_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?];
            while stream.shift_list_delimiter().is_ok()
            {
                p.place_back() <- TypeSynTree::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
            }
            stream.shift_end_enclosure_of(EnclosureKind::Parenthese).map_err(|p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p))?;
            Success(if p.len() == 1 { p.pop().unwrap() } else { TypeSynTree::Tuple(pp.clone(), p) })
        },
        _ => NotConsumed
    }
}

impl<'s> Parser<'s> for TypeSynTree<'s>
{
    type ResultTy = Self;
    /// Parses a type
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let ts = TokenizerState::from("z :+: String").strip_all();
    /// let _ty = TypeSynTree::parse(&mut PreanalyzedTokenStream::from(&ts[..]), Leftmost::Nothing).unwrap();
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(s: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't { arrow_ty(s, leftmost) }
}

/// Quantified: 明示的なものだけ(forall ..., <tree>)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullTypeDesc<'s> { pub quantified: Vec<Source<'s>>, pub constraints: Vec<TypeSynTree<'s>>, pub tree: TypeSynTree<'s> }
impl<'s> Parser<'s> for FullTypeDesc<'s>
{
    type ResultTy = Self;
    /// Parses a fully descripted type(forall and constraints)
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let ts = TokenizerState::from("forall z. (Show z, Read z) => Eq z => z -> (z, String)").strip_all();
    /// let _ty = FullTypeDesc::parse(&mut PreanalyzedTokenStream::from(&ts[..]), Leftmost::Nothing).unwrap();
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, mut leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
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
                    TypeSynTree::Tuple(_, mut v) => constraints.append(&mut v),
                    t => constraints.push(t)
                }
            }
            else { return Success(FullTypeDesc { quantified, constraints, tree: tt }); }
        }
    }
}

/// 型シノニム/データ定義
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeFn<'s> { pub location: Location, pub defs: Vec<(TypeSynTree<'s>, FullTypeDesc<'s>)> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructor<'s> { pub location: Location, pub tree: TypeSynTree<'s> }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclaration<'s> { pub location: Location, pub defs: Vec<(TypeSynTree<'s>, Vec<DataConstructor<'s>>)> }
impl<'s> BlockParser<'s> for TypeFn<'s>
{
    type ResultTy = Self;
    /// Parse a type synonim declaration
    /// # Examples
    /// ```
    /// # use pureshader::*;
    /// let src = TokenizerState::from("type Xnum = Int").strip_all();
    /// TypeFn::parse(&mut PreanalyzedTokenStream::from(&src[..])).expect("in case 1");
    /// // multiple definition
    /// let src = TokenizerState::from("type Xnum a = a; Vec4 = f4").strip_all();
    /// TypeFn::parse(&mut PreanalyzedTokenStream::from(&src[..])).expect("in case 2");
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Self> where 's: 't
    {
        let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Type) => p);
        let block_start = take_current_block_begin(stream);
        let mut defs = Vec::new();
        while block_start.satisfy(stream.current(), true)
        {
            let defblock_begin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
            let pat = TypeSynTree::parse(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::TypePattern, stream.current().position()))?;
            let defblock_begin = defblock_begin.into_exclusive();
            TMatch!(defblock_begin => stream; TokenKind::Equal(_), |p| ParseError::Expecting(ExpectingKind::Binding, p));
            let bound = FullTypeDesc::parse(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
            defs.place_back() <- (pat, bound);

            let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
            if block_start.is_explicit() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
            {
                return Success(TypeFn { location: location.clone(), defs })
            }
            if !delimitered || (stream.on_linehead() && block_start.satisfy(stream.current(), false)) { break; }
        }
        if block_start.is_explicit() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
        Success(TypeFn { location: location.clone(), defs })
    }
}
impl<'s> BlockParser<'s> for TypeDeclaration<'s>
{
    type ResultTy = Self;
    /// Parses a data declaration
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let src = TokenizerState::from("data Np x = Np x Int").strip_all();
    /// TypeDeclaration::parse(&mut PreanalyzedTokenStream::from(&src[..])).expect("in simple case");
    /// // infix declaration
    /// let src = TokenizerState::from("data a Np x = x :,: a").strip_all();
    /// TypeDeclaration::parse(&mut PreanalyzedTokenStream::from(&src[..])).expect("in infix case");
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Self> where 's: 't
    {
        // op term...
        fn prefix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, DataConstructor<'s>>
        {
            let name = BreakParsing!(shift_prefix_declarator(stream, leftmost));
            let leftmost = leftmost.into_exclusive();
            let mut ap_list = vec![TypeSynTree::SymReference(name.clone())];
            while leftmost.satisfy(stream.current(), true)
            {
                match term_ty(stream, leftmost)
                {
                   Success(v) => ap_list.push(v), Failed(e) => return Failed(e), NotConsumed => break
                }
            }
            Success(DataConstructor { location: name.pos.clone(), tree: TypeSynTree::Prefix(ap_list) })
        }
        // term op term
        fn infix<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, DataConstructor<'s>>
        {
            let arg1 = BreakParsing!(term_ty(stream, leftmost));
            let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(arg1.position().column)).into_exclusive();
            let name = shift_infix_ops(stream, leftmost).map_err(|p| ParseError::Expecting(ExpectingKind::Operator, p))?;
            let arg2 = term_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Argument, stream.current().position()))?;
            Success(DataConstructor { location: arg1.position().clone(), tree: TypeSynTree::Prefix(vec![TypeSynTree::SymReference(name.clone()), arg1, arg2]) })
        }
        let location = TMatch!(stream; TokenKind::Keyword(ref p, Keyword::Data) => p, |p| ParseError::Expecting(ExpectingKind::Keyword(Keyword::Data), p));
        let block_start = take_current_block_begin(stream);
        let mut defs = Vec::new();
        while block_start.satisfy(stream.current(), true)
        {
            let defblock_begin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
            let pat = TypeSynTree::parse(stream, defblock_begin).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
            let defblock_begin = defblock_begin.into_exclusive();
            if defblock_begin.satisfy(stream.current(), true) && stream.current().is_equal() { stream.shift(); }
            else { return Failed(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
            let (mut constructors, mut correct_brk) = (Vec::new(), false);
            while defblock_begin.satisfy(stream.current(), true)
            {
                let dc = prefix(stream, defblock_begin).or_else(|| infix(stream, defblock_begin)).into_result_opt()?;
                if let Some(p) = dc { constructors.push(p); } else { break; }

                if let TokenKind::Operator(Source { slice: "|", .. }) = *stream.current() { stream.shift(); }
                else { correct_brk = true; break; }
            }
            if !correct_brk { return Failed(ParseError::Expecting(ExpectingKind::Constructor, stream.current().position())); }
            defs.place_back() <- (pat, constructors);

            let delimitered = TMatch!(Optional: stream; TokenKind::StatementDelimiter(_));
            if block_start.is_nothing() && TMatch!(Optional: stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace))
            {
                return Success(TypeDeclaration { location: location.clone(), defs })
            }
            if !delimitered || (stream.on_linehead() && block_start.into_exclusive().satisfy(stream.current(), false)) { break; }
        }
        if block_start.is_nothing() { TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Brace), |p| ParseError::ExpectingClose(EnclosureKind::Brace, p)); }
        Success(TypeDeclaration { location: location.clone(), defs })
    }
}
