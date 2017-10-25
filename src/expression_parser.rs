//! Expression Parser

use tokparse::{Location, Source, Token, TokenizerCache, NumericTy, EnclosureKind};
use parser::{ParseError, ExpectingKind};
use std::ops::Deref;

// Expression(Pattern) = a list of some tokens

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionFragment<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>), Operator(Source<'s>),
    Primary(Location, Box<Expression<'s>>), ObjectDescender(Location), ListDelimiter(Location)
}
impl<'s> ExpressionFragment<'s>
{
    pub fn text(&self) -> Option<&'s str>
    {
        match *self
        {
            ExpressionFragment::Identifier(ref s) | ExpressionFragment::Numeric(ref s, _) | ExpressionFragment::NumericF(ref s, _) | ExpressionFragment::Operator(ref s) => Some(s.slice),
            ExpressionFragment::ObjectDescender(_) => Some("."), ExpressionFragment::ListDelimiter(_) => Some(","),
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
/// let (s, v) = (RefCell::new(Source::new("23 + ft (vec2 4 0).x\n4")), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let expr = expression(&mut tokcache, None, None).unwrap();
/// assert_eq!(expr[0].text(), Some("23"));
/// assert_eq!(expr[1].text(), Some("+"));
/// assert_eq!(expr[2].text(), Some("ft"));
/// assert_eq!(expr[3].children().unwrap()[0].text(), Some("vec2"));
/// assert_eq!(expr[3].children().unwrap()[1].text(), Some("4"));
/// assert_eq!(expr[3].children().unwrap()[2].text(), Some("0"));
/// assert_eq!(expr[4], ExpressionFragment::ObjectDescender(Location { line: 1, column: 19 }));
/// assert_eq!(expr[5].text(), Some("x"));
/// assert_eq!(tokcache.current(), &Token::Numeric(Source { pos: Location { line: 2, column: 1 }, slice: "4" }, None));
/// ```
pub fn expression<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>, expression_base: Option<usize>, correspond_closing: Option<EnclosureKind>) -> Result<Expression<'s>, ParseError<'t>>
{
    let mut v = Vec::new();
    let mut last_line = stream.current().position().line;
    let expression_base = expression_base.unwrap_or_else(|| stream.current().position().column);
    loop
    {
        let t = stream.next();
        // break expression on less/equal indentation
        if t.position().line != last_line && t.position().column <= expression_base { stream.unshift(); break; }
        last_line = t.position().line;
        match *t
        {
            Token::EOF(ref p) => if let Some(k) = correspond_closing { return Err(ParseError::ExpectingClose(k, p)); } else { break; },
            Token::BeginEnclosure(ref p, k@EnclosureKind::Parenthese) | Token::BeginEnclosure(ref p, k@EnclosureKind::Brace) =>
            {
                v.place_back() <- ExpressionFragment::Primary(p.clone(), box expression(stream, Some(expression_base), Some(k))?);
            },
            Token::EndEnclosure(_, k) if Some(k) == correspond_closing => break,
            Token::EndEnclosure(ref p, k) => { stream.unshift(); return Err(ParseError::UnexpectedClose(k, p)); },
            Token::Identifier(ref s) => { v.place_back() <- ExpressionFragment::Identifier(s.clone()); },
            Token::Numeric(ref s, t) => { v.place_back() <- ExpressionFragment::Numeric(s.clone(), t); },
            Token::NumericF(ref s, t) => { v.place_back() <- ExpressionFragment::NumericF(s.clone(), t); },
            Token::Operator(ref s) => { v.place_back() <- ExpressionFragment::Operator(s.clone()); },
            Token::ObjectDescender(ref p) => { v.place_back() <- ExpressionFragment::ObjectDescender(p.clone()); },
            Token::ListDelimiter(ref p) => { v.place_back() <- ExpressionFragment::ListDelimiter(p.clone()); },
            _ => { stream.unshift(); break; }
        }
    }
    if v.is_empty() { Err(ParseError::Expecting(ExpectingKind::Expression, stream.current().position())) }
    else { Ok(Expression(v)) }
}
