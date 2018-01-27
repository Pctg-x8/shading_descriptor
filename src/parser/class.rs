//! Class/Instance parsing

use super::*;
use {Keyword, Location};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassDef<'s>
{
    pub begin: Location, pub pat: FullTypeDesc<'s>, pub bindings: Vec<ValueDeclaration<'s>>
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceDef<'s>
{
    pub begin: Location, pub pat: FullTypeDesc<'s>, pub bindings: Vec<ValueDeclaration<'s>>
}
impl<'s> Position for ClassDef<'s> { fn position(&self) -> &Location { &self.begin } }
impl<'s> Position for InstanceDef<'s> { fn position(&self) -> &Location { &self.begin } }

impl<'s> BlockParserM<'s> for ClassDef<'s>
{
    type ResultTy = Self;
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResultM<'t, Self> where 's: 't
    {
        let begin = match stream.shift_keyword(Keyword::Class) { Ok(p) => p, Err(_) => return NotConsumedM };
        let leftmost = Leftmost::Inclusive(begin.column);
        let pat = FullTypeDesc::parse(stream, leftmost.into_exclusive()).into_result(|| ParseError::expect_class_def(stream.current().position()))?;
        let mut bindings = Vec::new();
        parse_in_optblock(stream, leftmost, |stream, lmb| match ValueDeclaration::parse(stream, lmb)
        {
            Success(v) => { bindings.push(v); Ok(()) },
            Failed(e) => Err(e), NotConsumed => Err(ParseError::Expecting(ExpectingKind::ValueDecl, stream.current().position()))
        })?;
        SuccessM(ClassDef { begin: begin.clone(), pat, bindings })
    }
}
impl<'s> BlockParserM<'s> for InstanceDef<'s>
{
    type ResultTy = Self;
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResultM<'t, Self> where 's: 't
    {
        let begin = match stream.shift_keyword(Keyword::Instance) { Ok(p) => p, Err(_) => return NotConsumedM };
        let leftmost = Leftmost::Inclusive(begin.column);
        let pat = FullTypeDesc::parse(stream, leftmost.into_exclusive()).into_result(|| ParseError::expect_instance_def(stream.current().position()))?;
        let mut bindings = Vec::new();
        parse_in_optblock(stream, leftmost, |stream, lmb| match ValueDeclaration::parse(stream, lmb)
        {
            Success(v) => { bindings.push(v); Ok(()) },
            Failed(e) => Err(e), NotConsumed => Err(ParseError::Expecting(ExpectingKind::ValueDecl, stream.current().position()))
        })?;
        SuccessM(InstanceDef { begin: begin.clone(), pat, bindings })
    }
}

fn parse_in_optblock<'s: 't, 't, S: TokenStream<'s, 't>, F>(stream: &mut S, leftmost: Leftmost, mut inner: F) -> ParseResultM<'t, ()>
    where F: FnMut(&mut S, Leftmost) -> Result<(), ParseError<'t>>
{
    if let Ok(block_lm) = intro_block(stream, leftmost)
    {
        let mut errors = Vec::new(); let mut early_break = false;
        while block_lm.satisfy(stream.current())
        {
            if outro_block(stream, block_lm).is_ok() { early_break = true; break; }
            let lmb = Leftmost::Inclusive(get_definition_leftmost(block_lm, stream));
            match inner(stream, lmb)
            {
                Err(e) => { errors.push(e); drop_for_nextdef(lmb, stream); }, _ => ()
            }
        }
        if !early_break
        {
            match outro_block(stream, block_lm) { Err(e) => { errors.place_back() <- ParseError::failed_to_leave_block(e); }, _ => () }
        }
        if !errors.is_empty() { FailedM(errors) } else { SuccessM(()) }
    }
    else { SuccessM(()) }
}
