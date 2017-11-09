//! Parser utils

use tokparse::{TokenizerCache, Token, TokenKind, EnclosureKind};

macro_rules! CheckLayout
{
	($leftmost: expr => $stream: expr) =>
	{
		if !$leftmost.satisfy($stream.current(), true) { return Failed(ParseError::LayoutViolation($stream.current().position())); }
	};
	($leftmost: expr => $stream: expr, R) =>
	{
		if !$leftmost.satisfy($stream.current(), true) { return Err(ParseError::LayoutViolation($stream.current().position())); }
	};
	($leftmost: expr => $stream: expr, NC) =>
	{
		if !$leftmost.satisfy($stream.current(), true) { return NotConsumed; }
	}
}
/// トークンマッチングマクロ
macro_rules! TMatch
{
	($leftmost: expr => $stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{{
		CheckLayout!($leftmost => $stream, R);
		match $stream.current().kind { $pat => { $stream.shift(); $extract }, ref e => return Err($err(e.position())) }
	}};
	($leftmost: expr => $stream: expr; $pat: pat, $err: expr) =>
	{{
		CheckLayout!($leftmost => $stream, R);
		match $stream.current().kind { $pat => { $stream.shift(); }, ref e => return Err($err(e.position())) }
	}};
	($stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{
		match $stream.current().kind { $pat => { $stream.shift(); $extract }, ref e => return Err($err(e.position())) }
	};
	($stream: expr; $pat: pat, $err: expr) =>
	{
		match $stream.current().kind { $pat => { $stream.shift(); }, ref e => return Err($err(e.position())) }
	};
	(Numeric: $stream: expr; $err: expr) =>
	{
		match $stream.current().kind
		{
			ref t@TokenKind::Numeric(_, _) | ref t@TokenKind::NumericF(_, _) => { $stream.shift(); t },
			ref e => return Err($err(e.position()))
		}
	};
	(Optional: $stream: expr; $pat: pat => $act: expr) =>
	{
		if let $pat = $stream.current().kind { $stream.shift(); Some($act) } else { None }
	};
	(Optional: $stream: expr; $pat: pat) =>
	{
		if let $pat = $stream.current().kind { $stream.shift(); true } else { false }
	}
}
/// パース頭向けマッチングマクロ(ない場合はNotConsumedを返してくれる)
macro_rules! TMatchFirst
{
	($stream: expr; $pat: pat => $extract: expr) =>
	{
		if let $pat = $stream.current().kind { $stream.shift(); $extract } else { return NotConsumed; }
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leftmost { Nothing, Inclusive(usize), Exclusive(usize) }
impl Leftmost
{
	pub fn satisfy(&self, tok: &Token, always_satisfy_on_nothing: bool) -> bool
	{
		match *self
		{
			Leftmost::Inclusive(l) => l <= tok.position().column,
			Leftmost::Exclusive(l) => l < tok.position().column,
			Leftmost::Nothing => always_satisfy_on_nothing
		}
	}
	pub fn num(&self) -> Option<usize> { match *self { Leftmost::Nothing => None, Leftmost::Inclusive(n) | Leftmost::Exclusive(n) => Some(n) } }
	pub fn is_nothing(&self) -> bool { match *self { Leftmost::Nothing => true, _ => false } }
	pub fn into_inclusive(self) -> Self
	{
		match self { Leftmost::Nothing | Leftmost::Inclusive(_) => self, Leftmost::Exclusive(n) => Leftmost::Inclusive(n) }
	}
	pub fn into_exclusive(self) -> Self
	{
		match self { Leftmost::Nothing | Leftmost::Exclusive(_) => self, Leftmost::Inclusive(n) => Leftmost::Exclusive(n) }
	}
	pub fn into_nothing_as(self, nothing: Leftmost) -> Self
	{
		match self { Leftmost::Nothing => nothing, _ => self }
	}
}

pub fn take_current_block_begin<'s: 't, 't>(stream: &mut TokenizerCache<'s, 't>) -> Leftmost
{
	match stream.current().kind
	{
		TokenKind::BeginEnclosure(_, EnclosureKind::Brace) => { stream.shift(); Leftmost::Nothing },
		TokenKind::EOF(_) => Leftmost::Inclusive(0),
		ref t => Leftmost::Inclusive(t.position().column)
	}
}
pub fn get_definition_leftmost<'s: 't, 't>(block_leftmost: Leftmost, stream: &TokenizerCache<'s, 't>) -> usize
{
	if stream.current().line_head { stream.current().position().column }
	else { block_leftmost.num().unwrap_or(stream.current().position().column) }
}
