//! Expression Parser

use tokparse::{Location, Source, TokenKind, Keyword, TokenStream, NumericTy, EnclosureKind};
use super::err::*;
use parser::{ExpectingKind, Leftmost, take_current_block_begin, get_definition_leftmost, Parser};
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq, Eq)] pub enum ExpressionSynTree<'s>
{
    SymReference(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>), ArrayLiteral(Location, Vec<FullExpression<'s>>),
    RefPath(Box<FullExpression<'s>>, Vec<Source<'s>>), ArrayRef(Box<FullExpression<'s>>, Box<FullExpression<'s>>),
    Prefix(Vec<FullExpression<'s>>), Infix { lhs: Box<FullExpression<'s>>, mods: Vec<(Source<'s>, FullExpression<'s>)> }, Tuple(Vec<FullExpression<'s>>)
}

/// Infix <- Prefix ((op/infixident) Prefix)*
pub fn infix_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let lhs = BreakParsing!(prefix_expr(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    let mut rhs = Vec::new();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            &TokenKind::Operator(ref s) | &TokenKind::InfixIdent(ref s) =>
            {
                let e = prefix_expr(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
                rhs.place_back() <- (s.clone(), e);
            },
            _ => break
        }
    }
    Success(if rhs.is_empty() { lhs } else { ExpressionSynTree::Infix { lhs: box lhs, mods: rhs }.into() })
}
/// Prefix <- Term Term*
pub fn prefix_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let mut lhs = vec![BreakParsing!(term_expr(stream, leftmost))];
    let leftmost = leftmost.into_exclusive();
    while let Some(rhs) = term_expr(stream, leftmost).into_result_opt()? { lhs.push(rhs); }
    Success(if lhs.len() > 1 { ExpressionSynTree::Prefix(lhs).into() } else { lhs.pop().unwrap() })
}
/// Term <- Factor (. ident / [ FullEx ])*
pub fn term_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let mut lhs = BreakParsing!(factor_expr(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            &TokenKind::ObjectDescender(_) =>
            {
                let mut rhs = Vec::new();
                while stream.shift_object_descender().is_ok()
                {
                    rhs.place_back() <- TMatch!(stream; TokenKind::Identifier(ref s) => s.clone(), |p| ParseError::Expecting(ExpectingKind::Ident, p));
                }
                lhs = ExpressionSynTree::RefPath(box lhs.into(), rhs).into();
            },
            &TokenKind::BeginEnclosure(_, EnclosureKind::Bracket) =>
            {
                let e = FullExpression::parse(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
                if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Bracket) { return Failed(ParseError::ExpectingClose(EnclosureKind::Bracket, p)); }
                lhs = ExpressionSynTree::ArrayRef(box lhs.into(), box e).into();
            },
            _ => break
        }
    }
    Success(lhs.into())
}
/// Factor <- ident / numeric / numericf / [ (FullEx (, FullEx)*)? ] / ( FullEx (, FullEx)* )
pub fn factor_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    if !leftmost.satisfy(stream.current(), false) { return NotConsumed; }
    match stream.current()
    {
        &TokenKind::Identifier(ref s) | &TokenKind::WrappedOp(ref s) => { stream.shift(); Success(ExpressionSynTree::SymReference(s.clone()).into()) },
        &TokenKind::Numeric (ref s, nt) => { stream.shift(); Success(ExpressionSynTree::Numeric (s.clone(), nt).into()) },
        &TokenKind::NumericF(ref s, nt) => { stream.shift(); Success(ExpressionSynTree::NumericF(s.clone(), nt).into()) },
        &TokenKind::BeginEnclosure(ref p, EnclosureKind::Bracket) =>
        {
            stream.shift(); let leftmost = leftmost.into_exclusive();
            let es = if !stream.current().is_end_enclosure_of(EnclosureKind::Bracket)
            {
                full_expressions(stream, leftmost, Some(EnclosureKind::Bracket)).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?
            }
            else { Vec::new() };
            TMatch!(leftmost => stream; TokenKind::EndEnclosure(_, EnclosureKind::Bracket), |p| ParseError::ExpectingClose(EnclosureKind::Bracket, p));
            Success(ExpressionSynTree::ArrayLiteral(p.clone(), es).into())
        },
        &TokenKind::BeginEnclosure(_, EnclosureKind::Parenthese) =>
        {
            let leftmost = leftmost.into_exclusive();
            let mut e = full_expressions(stream.shift(), leftmost, Some(EnclosureKind::Parenthese))
                .into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
            TMatch!(leftmost => stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
            Success(if e.len() == 1 { e.pop().unwrap() } else { ExpressionSynTree::Tuple(e).into() })
        },
        _ => NotConsumed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionFragment<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>), Operator(Source<'s>),
    Primary(Location, FullExpression<'s>), Bracketed(Location, Vec<FullExpression<'s>>), ObjectDescender(Location)
}
impl<'s> ExpressionFragment<'s>
{
    pub fn text(&self) -> Option<&'s str>
    {
        match *self
        {
            ExpressionFragment::Identifier(ref s) | ExpressionFragment::Numeric(ref s, _) | ExpressionFragment::NumericF(ref s, _) | ExpressionFragment::Operator(ref s) => Some(s.slice),
            ExpressionFragment::ObjectDescender(_) => Some("."),
            _ => None
        }
    }
    /// A child expression
    pub fn child(&self) -> Option<&FullExpression<'s>>
    {
        match self { &ExpressionFragment::Primary(_, ref x) => Some(x), _ => None }
    }
    /// Children expression
    pub fn children(&self) -> Option<&Vec<FullExpression<'s>>>
    {
        match self { &ExpressionFragment::Bracketed(_, ref v) => Some(v), _ => None }
    }
}
impl<'s> Into<Expression<'s>> for ExpressionFragment<'s> { fn into(self) -> Expression<'s> { Expression(vec![self]) } }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression<'s>(Vec<ExpressionFragment<'s>>);
impl<'s> Deref for Expression<'s>
{
    type Target = [ExpressionFragment<'s>]; fn deref(&self) -> &[ExpressionFragment<'s>] { &self.0 }
}
impl<'s> Into<FullExpression<'s>> for ExpressionSynTree<'s>
{
    fn into(self) -> FullExpression<'s> { FullExpression::Expression(self) }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockContent<'s>
{
    BlockVars { location: Location, vals: Vec<(FullExpression<'s>, FullExpression<'s>)> },
    Expression(FullExpression<'s>)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FullExpression<'s>
{
    Lettings { location: Location, vals: Vec<(FullExpression<'s>, FullExpression<'s>)>, subexpr: Box<FullExpression<'s>> },
    Conditional { location: Location, inv: bool, cond: Box<FullExpression<'s>>, then: Box<FullExpression<'s>>, else_: Option<Box<FullExpression<'s>>> },
    Block(Location, Vec<BlockContent<'s>>), Expression(ExpressionSynTree<'s>)
}
impl<'s> Parser<'s> for FullExpression<'s>
{
    type ResultTy = Self;
    /// Parse a full expression(contains let, if or do)
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let s = Source::new("let b = if true then 2 else 3 in do trace $ show b; return b").into().all();
    /// FullExpression::parse(&mut PreanalyzedTokenStream::from(&s), Leftmost::Nothing).unwrap();
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
        match *stream.current()
        {
            TokenKind::Keyword(_, Keyword::Let) => expr_lettings(stream, leftmost),
            TokenKind::Keyword(_, Keyword::If) | TokenKind::Keyword(_, Keyword::Unless) => expr_conditional(stream, leftmost),
            TokenKind::Keyword(_, Keyword::Do) => block_content(stream),
            _ => infix_expr(stream, leftmost)
        }
    }
}
pub fn full_expressions<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost, enclosure: Option<EnclosureKind>) -> ParseResult<'t, Vec<FullExpression<'s>>>
{
    let mut v = vec![BreakParsing!(FullExpression::parse(stream, leftmost))];
    let leftmost = leftmost.into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            k if k.is_list_delimiter() =>
            {
                v.place_back() <- FullExpression::parse(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
            },
            &TokenKind::EndEnclosure(_, k) if Some(k) == enclosure => break,
            &TokenKind::EndEnclosure(ref p, k) => return Failed(ParseError::UnexpectedClose(k, p)),
            k => return Failed(ParseError::Unexpected(k.position()))
        }
    }
    Success(v)
}
/// let ... in ...
fn expr_lettings<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    TMatch!(IndentedKw; leftmost => stream; Keyword::In, ExpectingKind::LetIn);
    let subexpr = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    Success(FullExpression::Lettings { location: location.clone(), vals, subexpr })
}
/// if ... then ... [else ...]
fn expr_conditional<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    let (inv, location) = match *stream.current()
    {
        TokenKind::Keyword(ref p, Keyword::If) => { stream.shift(); (false, p) },
        TokenKind::Keyword(ref p, Keyword::Unless) => { stream.shift(); (true, p) },
        _ => return NotConsumed
    };
    let leftmost = leftmost.into_exclusive();
    let cond = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::ConditionExpr, stream.current().position()))?;
    TMatch!(IndentedKw; leftmost => stream; Keyword::Then);
    let then = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    let else_ = if leftmost.satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::Else)
    {
        stream.shift();
        Some(box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?)
    }
    else { None };
    Success(FullExpression::Conditional { location: location.clone(), cond, inv, then, else_ })
}
/// do ...
fn block_content<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, FullExpression<'s>>
{
    let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Do) => p);
    let block_start = take_current_block_begin(stream);
    let mut s = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Success(FullExpression::Block(location.clone(), s)); }
        let defbegin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
        if stream.current().keyword() == Some(Keyword::Let) { s.place_back() <- blk_vars(stream, defbegin)?; }
        else
        {
            match FullExpression::parse(stream, defbegin)
            {
                Success(x) => { s.place_back() <- BlockContent::Expression(x); },
                Failed(f) => return Failed(f),
                NotConsumed => break
            }
        }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position())); }
    Success(FullExpression::Block(location.clone(), s))
}
fn blk_vars<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, BlockContent<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    if leftmost.satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::In)
    {
        stream.shift();
        let subexpr = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(BlockContent::Expression(FullExpression::Lettings { location: location.clone(), vals, subexpr }))
    }
    else { Success(BlockContent::BlockVars { location: location.clone(), vals }) }
}
/// let (decls) [in?]
fn letting_common<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, (&'t Location, Vec<(FullExpression<'s>, FullExpression<'s>)>)>
{
    let location = TMatchFirst!(leftmost => stream; TokenKind::Keyword(ref p, Keyword::Let) => p);
    let block_start = take_current_block_begin(stream);
    let mut vals = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if stream.current().keyword() == Some(Keyword::In) { break; }
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { break; }
        let defbegin = get_definition_leftmost(block_start, stream);
        let pat = expression(stream, Leftmost::Inclusive(defbegin)).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, stream.current().position()))?;
        let defbegin = Leftmost::Exclusive(defbegin);
        if !stream.current().is_equal() || !defbegin.satisfy(stream.current(), false)
        {
            return Failed(ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()));
        }
        stream.shift(); CheckLayout!(defbegin => stream);
        let rhs = FullExpression::parse(stream, defbegin).into_result(|| ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()))?;
        vals.place_back() <- (pat, rhs);
        while TMatch!(Optional: stream; TokenKind::StatementDelimiter(_)) {  }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position())); }
    Success((location, vals))
}

/// Parses an expression
/// # Example
///
/// ```
/// # use pureshader::*;
/// let s = Source::new("23 + ft (vec2 4 0).x\n4").into().all();
/// let mut st = PreanalyzedTokenStream::from(&s);
/// expression(&mut st, Leftmost::Nothing).unwrap();
/// assert!(!st.is_empty());
/// ```
pub fn expression<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>> { infix_expr(stream, leftmost) }

/*
/// ラムダ抽象
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lambda<'s> { Binder(&'s str, Box<Lambda<'s>>), Expression(Expression<'s>) }
// let a b = \x -> c ==> let a = \b -> \x -> c (bを移項する)
// let a ~> b = a / b ==> let (~>) a b = a / b ==> let ~> = \a -> \b -> a / b (二項演算パターンを分解してa, bを右から移項する)
// let (n ~> m) x = ... ==> let n ~> m = \x -> ... ==> let ~> = \n -> \m -> \x -> ... (関数適用パターンとみて先に移項する)
// let f (Ty a) = ... ==> let f a0 | Ty a = a0 = ... ==> let f a0 = case a0 of Ty a => ... ==> let f = \a0 -> case a0 of Ty a => ...
//  (コンストラクタパターンをa0(自動生成)に置換してガード化、その後caseに置換して最後にa0を移項)

// f a ([Var "f", Var "a"]) => 最後の1ブロックになるまで移項 => "f" = Lambda::Binder (Var "a") ...
// a ~> b ([Op "~>" (Var "a") (Var "b")]) => もともと(~>) a bの形になっているのでそのまま最後の1ブロックになるまで移項 => "~>" = Lambda::Binder (Var "a") (Lambda::Binder (Var "b") ...)
// data f4 = f4 float float float float, f4 x y z w = \c -> c x y z w
// case v of f4 x y z w => x + y + z + w => v (\x -> \y -> \z -> \w -> x + y + z + w)
//   => (\c -> c x y z w) (\x -> \y -> \z -> \w -> x + y + z + w)
// data Either a b = Left a | Right b, Left a = \l -> \r -> l a, Right b = \l -> \r -> r b
// case x of Left a => a + 3 ==> x (\a -> a + 3) (\_ -> <<Error(どうしよう)>>)
*/
