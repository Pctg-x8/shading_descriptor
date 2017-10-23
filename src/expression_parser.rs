//! Expression Parser

use tokparse::{Location, Source, Token, TokenizerCache, NumericTy, EnclosureKind};
use parser::ParseError;
use std::ops::Deref;

// Expression = a list of some tokens

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionFragment<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>), Operator(Source<'s>),
    Primary(Location, Box<Expression<'s>>), ObjectDescender(Location)
}
impl<'s> ExpressionFragment<'s>
{
    pub fn text(&self) -> Option<&'s str>
    {
        match *self
        {
            ExpressionFragment::Identifier(ref s) | ExpressionFragment::Numeric(ref s, _) | ExpressionFragment::NumericF(ref s, _) | ExpressionFragment::Operator(ref s) => Some(s.slice),
            _ => None
        }
    }
    pub fn children(&self) -> Option<&Expression<'s>>
    {
        match *self
        {
            ExpressionFragment::Primary(_, ref x) => Some(&**x), _ => None
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression<'s>(Vec<ExpressionFragment<'s>>);
impl<'s> Deref for Expression<'s>
{
    type Target = [ExpressionFragment<'s>]; fn deref(&self) -> &[ExpressionFragment<'s>] { &self.0 }
}

/// Parses an expression
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("23 + ft (vec2 4 0).x")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let expr = expression(&mut tokcache, None).unwrap();
/// assert_eq!(expr[0].text(), Some("23"));
/// assert_eq!(expr[1].text(), Some("+"));
/// assert_eq!(expr[2].text(), Some("ft"));
/// assert_eq!(expr[3].children().unwrap()[0].text(), Some("vec2"));
/// assert_eq!(expr[3].children().unwrap()[1].text(), Some("4"));
/// assert_eq!(expr[3].children().unwrap()[2].text(), Some("0"));
/// assert_eq!(expr[4], ExpressionFragment::ObjectDescender(Location { line: 1, column: 19 }));
/// assert_eq!(expr[5].text(), Some("x"));
/// ```
pub fn expression<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, correspond_closing: Option<EnclosureKind>) -> Result<Expression<'s>, ParseError<'t>>
{
    let mut v = Vec::new();
    loop
    {
        match *stream.next()
        {
            Token::EOF(ref p) => if let Some(k) = correspond_closing { return Err(ParseError::ExpectingClose(k, p)); } else { break; },
            Token::BeginEnclosure(ref p, k@EnclosureKind::Parenthese) | Token::BeginEnclosure(ref p, k@EnclosureKind::Brace) =>
            {
                v.place_back() <- ExpressionFragment::Primary(p.clone(), box expression(stream, Some(k))?);
            },
            Token::EndEnclosure(_, k) if Some(k) == correspond_closing => break,
            Token::EndEnclosure(ref p, k) => { stream.unshift(); return Err(ParseError::UnexpectedClose(k, p)); },
            Token::Identifier(ref s) => { v.place_back() <- ExpressionFragment::Identifier(s.clone()); },
            Token::Numeric(ref s, t) => { v.place_back() <- ExpressionFragment::Numeric(s.clone(), t); },
            Token::NumericF(ref s, t) => { v.place_back() <- ExpressionFragment::NumericF(s.clone(), t); },
            Token::Operator(ref s) => { v.place_back() <- ExpressionFragment::Operator(s.clone()); },
            Token::ObjectDescender(ref p) => { v.place_back() <- ExpressionFragment::ObjectDescender(p.clone()); },
            ref e => { stream.unshift(); return Err(ParseError::InvalidExpressionFragment(e.position())); }
        }
    }
    Ok(Expression(v))
}
