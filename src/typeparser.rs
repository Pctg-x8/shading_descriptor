//! Complex type parser

use tokparse::{Location, Source, Token, TokenizerCache, BType, EnclosureKind};
use expression_parser::{Expression, expression};
use parser::{ParseError, ExpectingKind};
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
    Operator    (Source<'s>, Box<TypePatFragment<'s>>, Box<TypePatFragment<'s>>),
    OpArrow     (Location,   Box<TypePatFragment<'s>>, Box<TypePatFragment<'s>>), Placeholder(Location),
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
/// let (s, v) = (RefCell::new(Source::new("(f4 -> _)[2]")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let uty = user_type(&mut tokcache, None).unwrap();
/// assert_eq!(uty[0].children().unwrap()[0].basic_type(), Some(BType::FVec(4)));
/// assert_eq!(uty[0].children().unwrap()[1].text(), Some("->"));
/// assert!   (uty[0].children().unwrap()[2].is_placeholder());
/// assert_eq!(uty[1].inner_expr().unwrap()[0].text(), Some("2"));
/// ```
pub fn user_type<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, corresponding_enclosure: Option<EnclosureKind>) -> Result<Type<'s>, ParseError<'t>>
{
    let mut v = Vec::new();
    loop
    {
        match *stream.next()
        {
            Token::EOF(ref p) => if let Some(k) = corresponding_enclosure { return Err(ParseError::ExpectingClose(k, p)); } else { break; }
            Token::BeginEnclosure(ref p, k@EnclosureKind::Parenthese) | Token::BeginEnclosure(ref p, k@EnclosureKind::Brace) =>
            {
                v.place_back() <- TypeFragment::Primary(p.clone(), user_type(stream, Some(k))?);
            }
            Token::BeginEnclosure(ref p, EnclosureKind::Bracket) => match *stream.current()
            {
                Token::Placeholder(_) => { stream.consume(); v.place_back() <- TypeFragment::ArrayDim(p.clone(), None); }
                _ => { v.place_back() <- TypeFragment::ArrayDim(p.clone(), Some(expression(stream, None, Some(EnclosureKind::Bracket))?)); }
            }
            Token::EndEnclosure(_, k) if Some(k) == corresponding_enclosure => break,
            Token::EndEnclosure(ref p, k) => { stream.unshift(); return Err(ParseError::UnexpectedClose(k, p)); }
            Token::Placeholder(ref p) => { v.place_back() <- TypeFragment::Placeholder(p.clone()); }
            Token::BasicType(ref p, t) => { v.place_back() <- TypeFragment::BasicType(p.clone(), t); }
            Token::Identifier(ref s) => { v.place_back() <- TypeFragment::UserType(s.clone()); }
            Token::TyArrow(ref p) => { v.place_back() <- TypeFragment::OpArrow(p.clone()); }
            Token::Arrow(ref p) => { v.place_back() <- TypeFragment::OpConstraint(p.clone()); }
            Token::Operator(ref s) => { v.place_back() <- TypeFragment::Operator(s.clone()); }
            _ => { stream.unshift(); break; }
        }
    }
    if v.is_empty() { Err(ParseError::Expecting(ExpectingKind::Type, stream.current().position())) } else { Ok(Type(v)) }
}
