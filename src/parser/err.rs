//! Parsing Error Handlings

use tokparse::{Location, EnclosureKind, Keyword};
use std::fmt::{Formatter, Display, Debug, Result as FmtResult};
use std::error::Error;
use std::ops::Try;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectingKind
{
	ItemDelimiter, Semantics, Type, ShaderStage, OutDef, UniformDef, ConstantDef, Ident, ValueDecl, Constructor,
	Expression, Numeric, Operator, PrefixDeclarator, Argument, ShaderBlock,
	CompareOps, StencilOps, DepthStencilStates, BlendOps, BlendFactors, LetIn, TypePattern, ExpressionPattern, ConditionExpr,
	AssocPriority, Infix, Keyword(Keyword), Period, Binding, Arrow1, ModulePath
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError<'t>
{
	ExpectingIdentNextIn(&'t Location), ExpectingIdentOrIn(&'t Location), Expecting(ExpectingKind, &'t Location),
	ExpectingListDelimiterOrParentheseClosing(&'t Location),
	ExpectingEnclosed(ExpectingKind, EnclosureKind, &'t Location), ExpectingOpen(EnclosureKind, &'t Location), ExpectingClose(EnclosureKind, &'t Location),
	UnexpectedClose(EnclosureKind, &'t Location), Unexpected(&'t Location), InvalidExpressionFragment(&'t Location),
	PartialDisabling(Keyword, &'t Location), BlendFactorRestriction(&'t Location), LayoutViolation(&'t Location),
	DuplicatePrecedences(Location, &'t Location)
}
impl<'t> Display for ParseError<'t>
{
	fn fmt(&self, fmt: &mut Formatter) -> FmtResult
	{
		write!(fmt, "{} at {}", match self
		{
			&ParseError::DuplicatePrecedences(ref prev, _) => ::std::borrow::Cow::Owned(format!("Duplicated precedence declaration. First declaration was at {}", prev)),
			e => ::std::borrow::Cow::Borrowed(e.description())
		}, self.position())
	}
}
impl<'t> ParseError<'t>
{
	fn position(&self) -> &'t Location
	{
		use self::ParseError::*;
		match *self
		{
			ExpectingIdentNextIn(p) | ExpectingIdentOrIn(p) | Expecting(_, p)  | ExpectingEnclosed(_, _, p) | ExpectingClose(_, p) | Unexpected(p)
			| ExpectingListDelimiterOrParentheseClosing(p) | ExpectingOpen(_, p) | UnexpectedClose(_, p) | InvalidExpressionFragment(p)
			| PartialDisabling(_, p) | BlendFactorRestriction(p) | LayoutViolation(p) | DuplicatePrecedences(_, p) => p
		}
	}
}
impl<'t> Error for ParseError<'t>
{
	fn description(&self) -> &str
	{
		match *self
		{
			ParseError::ExpectingIdentNextIn(_) => "Expecting an `Identifier` next of an `in`",
			ParseError::ExpectingIdentOrIn(_) => "Expecting an `Identifier` or an `in`",
			ParseError::Expecting(k, _) => match k
			{
				ExpectingKind::ItemDelimiter => "Expecting a `:`",
				ExpectingKind::Type => "Expecting a type",
				ExpectingKind::ShaderStage => "Expecting a shader stage(VertexShader, FragmentShader, GeometryShader, HullShader or DomainShader)",
				ExpectingKind::OutDef => "Expecting a `out`",
				ExpectingKind::UniformDef => "Expecting a `uniform`",
				ExpectingKind::ConstantDef => "Expecting a `constant`",
				ExpectingKind::Ident => "Expecting an identifier",
				ExpectingKind::Numeric => "Expecting a number literal",
				ExpectingKind::Operator => "Expecting an operator",
				ExpectingKind::Expression => "Expecting an expression",
				ExpectingKind::TypePattern => "Expecting a type pattern",
				ExpectingKind::Semantics => "Expecting a semantics",
				ExpectingKind::ExpressionPattern => "Expecting and expression pattern",
				ExpectingKind::ValueDecl => "Expecting a `let` or an expression pattern",
				ExpectingKind::CompareOps => "Expecting a comparsion operator",
				ExpectingKind::StencilOps => "Expecting a stencil operator",
				ExpectingKind::BlendOps => "Expecting a blend operator",
				ExpectingKind::BlendFactors => "Expecting a blend factor",
				ExpectingKind::DepthStencilStates => "Expecting a depth stencil state",
				ExpectingKind::PrefixDeclarator => "Expecting an identifier or an operator enclosed by parentheses",
				ExpectingKind::Constructor => "Expecting a constructor",
				ExpectingKind::Argument => "Expecting an argument",
				ExpectingKind::ShaderBlock => "Expecting a shader block, which has to be followed by `where` or `:`",
				ExpectingKind::LetIn => "Expecting a `let .. in ..`, maybe missing `in`",
				ExpectingKind::ConditionExpr => "Expecting an expression for the condition",
				ExpectingKind::AssocPriority => "Expecting a priority of associativity",
				ExpectingKind::Infix => "Expecting an infix declaration",
				ExpectingKind::Period => "Expecting a `.`",
				ExpectingKind::Binding => "Expecting a binding, maybe missing `=`",
				ExpectingKind::Arrow1 => "Expecting a `->`",
				ExpectingKind::ModulePath => "Expecting a path to module",
				ExpectingKind::Keyword(kw) => match kw
				{
					Keyword::Blend => "Expecting a `Blend`",
					Keyword::Type => "Expecting a `type`",
					Keyword::Data => "Expecting a `data`",
					Keyword::Of => "Expecting a `of`",
					Keyword::Then => "Expecting a `then`",
					_ => unreachable!()
				}
			},
			ParseError::ExpectingEnclosed(ExpectingKind::Semantics, EnclosureKind::Parenthese, _) => "Expecting a semantic enclosured by ()",
			ParseError::ExpectingClose(EnclosureKind::Parenthese, _) => "Expecting a `)`",
			ParseError::ExpectingOpen(EnclosureKind::Parenthese, _) => "Expecting a `(`",
			ParseError::ExpectingListDelimiterOrParentheseClosing(_) => "Expecting a ',' or a ')'",
			ParseError::UnexpectedClose(EnclosureKind::Parenthese, _) => "Unexpected ')'",
			ParseError::UnexpectedClose(EnclosureKind::Brace, _) => "Unexpected '}'",
			ParseError::UnexpectedClose(EnclosureKind::Bracket, _) => "Unexpected ']'",
			ParseError::InvalidExpressionFragment(_) => "An invalid expression fragment found",
			ParseError::Unexpected(_) => "Unexpected token",
			ParseError::PartialDisabling(Keyword::StencilCompare, _) => "`StencilCompare` cannot be disabled partially",
			ParseError::PartialDisabling(Keyword::StencilOps, _) => "`StencilOps` cannot be disabled partially",
			ParseError::PartialDisabling(Keyword::StencilWriteMask, _) => "`StencilWriteMask` cannot be disabled partially",
			ParseError::BlendFactorRestriction(_) => "Constant Blend Factor must be 0 or 1",
			ParseError::LayoutViolation(_) => "Layout violation",
			ref de => unreachable!(de)
		}
	}
}

pub enum ParseResult<'t, T> { NotConsumed, Success(T), Failed(ParseError<'t>) }
pub enum ParseResultM<'t, T> { NotConsumed, Success(T), Failed(Vec<ParseError<'t>>) }
pub use self::ParseResult::{NotConsumed, Success, Failed};
pub use self::ParseResultM::{NotConsumed as NotConsumedM, Success as SuccessM, Failed as FailedM};
impl<'t, T> ParseResult<'t, T>
{
	pub fn into_result<Fe: FnOnce() -> ParseError<'t>>(self, not_consumed_err: Fe) -> Result<T, ParseError<'t>>
	{
		match self
		{
			NotConsumed => Err(not_consumed_err()),
			Success(t) => Ok(t), Failed(e) => Err(e)
		}
	}
	pub fn into_result_opt(self) -> Result<Option<T>, ParseError<'t>>
	{
		match self
		{
			NotConsumed => Ok(None), Success(t) => Ok(Some(t)), Failed(e) => Err(e)
		}
	}
}
impl<'t, T> ParseResultM<'t, T>
{
	pub fn into_result_err<Fe: FnOnce() -> ParseError<'t>>(self, not_consumed_err: Fe) -> Result<T, Vec<ParseError<'t>>>
	{
		match self
		{
			NotConsumedM => Err(vec![not_consumed_err()]),
			SuccessM(t) => Ok(t), FailedM(e) => Err(e)
		}
	}
	pub fn into_result_opt(self) -> Result<Option<T>, Vec<ParseError<'t>>>
	{
		match self
		{
			NotConsumedM => Ok(None), SuccessM(t) => Ok(Some(t)), FailedM(e) => Err(e)
		}
	}
}
impl<'t, T> From<Result<T, ParseError<'t>>> for ParseResult<'t, T>
{
	fn from(r: Result<T, ParseError<'t>>) -> Self { match r { Ok(v) => Success(v), Err(e) => Failed(e) } }
}
impl<'t, T> From<Result<T, ParseError<'t>>> for ParseResultM<'t, T>
{
	fn from(r: Result<T, ParseError<'t>>) -> Self { match r { Ok(v) => SuccessM(v), Err(e) => FailedM(vec![e]) } }
}
impl<'t, T> From<Result<T, Vec<ParseError<'t>>>> for ParseResultM<'t, T>
{
	fn from(r: Result<T, Vec<ParseError<'t>>>) -> Self { match r { Ok(v) => SuccessM(v), Err(e) => FailedM(e) } }
}
impl<'t> From<ParseError<'t>> for Vec<ParseError<'t>> { fn from(v: ParseError<'t>) -> Self { vec![v] } }
impl<'t, T> Try for ParseResult<'t, T>
{
	type Ok = T; type Error = ParseError<'t>;
	fn from_ok(v: T) -> Self { Success(v) } fn from_error(e: Self::Error) -> Self { Failed(e) }
	fn into_result(self) -> Result<Self::Ok, Self::Error>
	{
		match self { NotConsumed => panic!("Cannot throw a NotConsumed via std::ops::Try"), Success(v) => Ok(v), Failed(v) => Err(v) }
	}
}
impl<'t, T> Try for ParseResultM<'t, T>
{
	type Ok = T; type Error = Vec<ParseError<'t>>;
	fn from_ok(v: T) -> Self { SuccessM(v) } fn from_error(e: Self::Error) -> Self { FailedM(e) }
	fn into_result(self) -> Result<Self::Ok, Self::Error>
	{
		match self { NotConsumedM => panic!("Cannot throw a NotConsumed via std::ops::Try"), SuccessM(v) => Ok(v), FailedM(v) => Err(v) }
	}
}
impl<'t, T: Debug> Debug for ParseResult<'t, T>
{
	fn fmt(&self, fmt: &mut Formatter) -> FmtResult
	{
		match *self { Success(ref v) => write!(fmt, "Success({:?})", v), Failed(ref e) => write!(fmt, "Failed({:?})", e), NotConsumed => write!(fmt, "NotConsumed") }
	}
}
impl<'t, T: PartialEq> PartialEq for ParseResult<'t, T>
{
	fn eq(&self, other: &Self) -> bool
	{
		match *self
		{
			Success(ref v) => match *other { Success(ref vo) => v == vo, _ => false },
			Failed (ref v) => match *other { Failed (ref vo) => v == vo, _ => false },
			NotConsumed => match *other { NotConsumed => true, _ => false }
		}
	}
}

/// Continuous computations
impl<'t, T> ParseResult<'t, T>
{
    pub fn map<F, R>(self, mapper: F) -> ParseResult<'t, R> where F: FnOnce(T) -> R
    {
        match self
        {
            ParseResult::Success(v) => ParseResult::Success(mapper(v)),
            ParseResult::Failed(f) => ParseResult::Failed(f), ParseResult::NotConsumed => ParseResult::NotConsumed
        }
    }
    pub fn and_then<F, R>(self, next: F) -> ParseResult<'t, R> where F: FnOnce(T) -> ParseResult<'t, R>
    {
        match self
        {
            ParseResult::Success(v) => next(v),
            ParseResult::Failed(f) => ParseResult::Failed(f), ParseResult::NotConsumed => ParseResult::NotConsumed
        }
    }
	pub fn or_else<F>(self, alter: F) -> ParseResult<'t, T> where F: FnOnce() -> ParseResult<'t, T>
	{
		match self
		{
			Success(s) => Success(s), _ => alter()
		}
	}
}
/// Panicking
impl<'t, T> ParseResult<'t, T>
{
	pub fn unwrap(self) -> T
	{
		match self { Success(e) => e, Failed(e) => panic!("{:?}", e), NotConsumed => panic!("NotConsumed") }
	}
	pub fn expect(self, message: &str) -> T
	{
		match self { Success(e) => e, Failed(e) => panic!("{}: {:?}", message, e), NotConsumed => panic!("{}: NotConsumed", message) }
	}
}
/// Panicking
impl<'t, T> ParseResultM<'t, T>
{
	pub fn unwrap(self) -> T
	{
		match self { SuccessM(e) => e, FailedM(e) => panic!("{:?}", e), NotConsumedM => panic!("NotConsumed") }
	}
	pub fn expect(self, message: &str) -> T
	{
		match self { SuccessM(e) => e, FailedM(e) => panic!("{}: {:?}", message, e), NotConsumedM => panic!("{}: NotConsumed", message) }
	}
}
