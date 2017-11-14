//! Complex type parser

use tokparse::{Location, Source, TokenKind, TokenizerCache, BType, EnclosureKind};
use super::expr::{Expression, expression};
use super::err::*;
use super::utils::Leftmost;
use std::ops::Deref;
use std::mem::discriminant;
use std::collections::HashMap;
use std::borrow::Cow;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeFragment<'s>
{
    BasicType(Location, BType), UserType(Source<'s>), Operator(Source<'s>), OpArrow(Location), OpConstraint(Location), Placeholder(Location),
    ArrayDim(Location, Option<Expression<'s>>), Primary(Location, Type<'s>)
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypePatFragment<'s>
{
    BasicType(Location, BType), UserType(Source<'s>),
    Operator(Source<'s>, Box<TypePatFragment<'s>>, Box<TypePatFragment<'s>>),
    OpArrow (Location,   Box<TypePatFragment<'s>>, Box<TypePatFragment<'s>>), Placeholder(Location),
    ArrayDim(Box<TypePatFragment<'s>>, Option<Box<TypePatFragment<'s>>>), Apply(Box<TypePatFragment<'s>>, Box<TypePatFragment<'s>>)
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypePattern<'s> { pub tyvars: HashMap<Cow<'s, str>, *mut TypePatFragment<'s>>, pub ty: TypePatFragment<'s> }
impl<'s> TypeFragment<'s>
{
    pub fn text(&self) -> Option<&'s str>
    {
        match *self
        {
            TypeFragment::UserType(Source { slice, .. }) | TypeFragment::Operator(Source { slice, .. }) => Some(slice),
            TypeFragment::OpArrow(_) => Some("->"), TypeFragment::OpConstraint(_) => Some("=>"),
            _ => None
        }
    }
    pub fn is_placeholder(&self) -> bool { discriminant(self) == discriminant(&TypeFragment::Placeholder(Location::default())) }
    pub fn basic_type(&self) -> Option<BType>
    {
        match *self { TypeFragment::BasicType(_, ty) => Some(ty), _ => None }
    }
    pub fn inner_expr(&self) -> Option<&Expression<'s>>
    {
        match *self { TypeFragment::ArrayDim(_, ref e) => e.as_ref(), _ => None }
    }
    pub fn children(&self) -> Option<&Type<'s>>
    {
        match *self { TypeFragment::Primary(_, ref t) => Some(t), _ => None }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type<'s>(pub Vec<TypeFragment<'s>>);
impl<'s> Deref for Type<'s> { type Target = [TypeFragment<'s>]; fn deref(&self) -> &[TypeFragment<'s>] { &self.0 } }

/// Parses an user-defined type
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("(f4 -> _)[2]").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let uty = user_type(&mut tokcache, 0, false).into_result_opt().unwrap().unwrap();
/// assert_eq!(uty[0].children().unwrap()[0].basic_type(), Some(BType::FVec(4)));
/// assert_eq!(uty[0].children().unwrap()[1].text(), Some("->"));
/// assert!   (uty[0].children().unwrap()[2].is_placeholder());
/// assert_eq!(uty[1].inner_expr().unwrap()[0].text(), Some("2"));
/// ```
pub fn user_type<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: usize, in_prior: bool) -> ParseResult<'t, Type<'s>>
{
    enum ConvResult<'s: 't, 't> { Fragment(TypeFragment<'s>), EnterPrior(&'t Location), LeavePrior, Term, Failed(ParseError<'t>) }
    fn conv_type_fragment<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, leftmost: usize, in_prior: bool) -> ConvResult<'s, 't>
    {
        match stream.next().kind
        {
            TokenKind::EOF(ref p) => if in_prior { stream.unshift(); ConvResult::Failed(ParseError::ExpectingClose(EnclosureKind::Parenthese, p)) } else { ConvResult::Term },
            TokenKind::BeginEnclosure(ref p, EnclosureKind::Parenthese) => ConvResult::EnterPrior(p),
            TokenKind::BeginEnclosure(ref p, EnclosureKind::Bracket) =>
            {
                if !Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) { return ConvResult::Failed(ParseError::LayoutViolation(stream.current().position())); }
                if let TokenKind::Placeholder(_) = stream.current().kind
                {
                    stream.shift();
                    if !Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) { return ConvResult::Failed(ParseError::LayoutViolation(stream.current().position())); }
                    match stream.current().kind
                    {
                        TokenKind::EndEnclosure(_, EnclosureKind::Bracket) => { stream.shift(); ConvResult::Fragment(TypeFragment::ArrayDim(p.clone(), None)) }
                        ref e => { stream.unshift(); ConvResult::Failed(ParseError::ExpectingClose(EnclosureKind::Bracket, e.position())) }
                    }
                }
                else
                {
                    match expression(stream, leftmost, Some(EnclosureKind::Bracket))
                    {
                        Success(e) => ConvResult::Fragment(TypeFragment::ArrayDim(p.clone(), Some(e))),
                        Failed(e) => ConvResult::Failed(e), _ => unreachable!()
                    }
                }
            },
            TokenKind::EndEnclosure(ref p, EnclosureKind::Parenthese) => if in_prior { ConvResult::LeavePrior }
            else { stream.unshift(); ConvResult::Failed(ParseError::UnexpectedClose(EnclosureKind::Parenthese, p)) },
            TokenKind::Placeholder(ref p) => ConvResult::Fragment(TypeFragment::Placeholder(p.clone())),
            TokenKind::BasicType(ref p, t) => ConvResult::Fragment(TypeFragment::BasicType(p.clone(), t)),
            TokenKind::Identifier(ref s) => ConvResult::Fragment(TypeFragment::UserType(s.clone())),
            TokenKind::TyArrow(ref p) => ConvResult::Fragment(TypeFragment::OpArrow(p.clone())),
            TokenKind::Arrow(ref p) => ConvResult::Fragment(TypeFragment::OpConstraint(p.clone())),
            TokenKind::Operator(ref s) => ConvResult::Fragment(TypeFragment::Operator(s.clone())),
            _ => { stream.unshift(); ConvResult::Term }
        }
    }
    let mut v = Vec::new();
    if !Leftmost::Inclusive(leftmost).satisfy(stream.current(), false) { return NotConsumed; }
    match conv_type_fragment(stream, leftmost, in_prior)
    {
        ConvResult::Failed(e) => return Failed(e),
        ConvResult::LeavePrior => return Success(Type(v)),
        ConvResult::Term => return NotConsumed,
        ConvResult::EnterPrior(p) => { v.place_back() <- TypeFragment::Primary(p.clone(), user_type(stream, leftmost, true)?); },
        ConvResult::Fragment(f) => v.push(f)
    }
    while Leftmost::Exclusive(leftmost).satisfy(stream.current(), true)
    {
        match conv_type_fragment(stream, leftmost, in_prior)
        {
            ConvResult::Failed(e) => return Failed(e),
            ConvResult::Term | ConvResult::LeavePrior => break,
            ConvResult::EnterPrior(p) => { v.place_back() <- TypeFragment::Primary(p.clone(), user_type(stream, leftmost, true)?); },
            ConvResult::Fragment(f) => v.push(f)
        }
    }
    Success(Type(v))
}
