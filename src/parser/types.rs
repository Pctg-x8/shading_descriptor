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
pub fn arrow_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut lhs = BreakParsing!(infix_ty(stream, leftmost));
    while stream.shift_arrow().is_ok()
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
pub fn infix_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, TypeSynTree<'s>>
{
    let lhs = BreakParsing!(prefix_ty(stream, leftmost));
    let mut mods = Vec::new();
    while let Ok(op) = shift_infix_ops(stream)
    {
        mods.place_back() <- (op.clone(), prefix_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?);
    }
    Success(if mods.is_empty() { lhs } else { TypeSynTree::Infix { lhs: box lhs, mods } })
}
/// Prefix <- Term Term*
pub fn prefix_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut lhs = vec![BreakParsing!(term_ty(stream, leftmost))];
    while let Some(p) = term_ty(stream, leftmost).into_result_opt()? { lhs.push(p); }
    Success(if lhs.len() == 1 { lhs.pop().unwrap() } else { TypeSynTree::Prefix(lhs) })
}
/// Term <- Factor (. ident / [ FullEx ])*
pub fn term_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, TypeSynTree<'s>>
{
    let mut e = BreakParsing!(factor_ty(stream, leftmost));
    loop
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
                        full_expression(stream, leftmost).into_result_opt()?.map_or(InferredArrayDim::Unsized, InferredArrayDim::Fixed)
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
pub fn factor_ty<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, TypeSynTree<'s>>
{
    match stream.current()
    {
        &TokenKind::Identifier(ref s) => { stream.shift(); Success(TypeSynTree::SymReference(s.clone())) },
        &TokenKind::BasicType(ref p, bt) => { stream.shift(); Success(TypeSynTree::Basic(p.clone(), bt)) },
        &TokenKind::Placeholder(ref p) => { stream.shift(); Success(TypeSynTree::Placeholder(p.clone())) },
        &TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) =>
        {
            let mut p = vec![arrow_ty(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?];
            while stream.shift_list_delimiter().is_ok()
            {
                p.place_back() <- arrow_ty(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Type, stream.current().position()))?;
            }
            if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Bracket) { return Failed(ParseError::ExpectingClose(EnclosureKind::Parenthese, p)); }
            Success(if p.len() == 1 { p.pop().unwrap() } else { TypeSynTree::Tuple(p) })
        },
        _ => NotConsumed
    }
}

/// Quantiied: 明示的なものだけ(forall ..., <tree>)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullTypeDesc<'s> { quantified: Vec<Source<'s>>, constraints: Vec<TypeSynTree<'s>>, tree: TypeSynTree<'s> }
/// Parses a fully descripted type(forall and constraints)
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("forall z. (Show z, Read z) => z -> (z, String)").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let _ty = full_type(&mut tokcache, 0).into_result_opt().unwrap().unwrap();
/// ```
pub fn full_type<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, FullTypeDesc<'s>>
{
    let mut quantified = Vec::new();
    while stream.shift_keyword(Keyword::Forall).is_ok()
    {
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
