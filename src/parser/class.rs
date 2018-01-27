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
        let pat = FullTypeDesc::parse(stream, leftmost.into_exclusive()).into_result(|| ParseError::expecting_class_def(stream.current().position()))?;
        let mut bindings = Vec::new();
        if shift_block_begin(stream, leftmost).is_ok()
        {
            let block_leftmost = take_current_block_begin(stream);
            let mut errors = Vec::new();
            while block_leftmost.satisfy(stream.current())
            {
                let lmb = Leftmost::Inclusive(get_definition_leftmost(block_leftmost, stream));
                match ValueDeclaration::parse(stream, lmb)
                {
                    Success(v) => { bindings.push(v); }
                    Failed(e) =>
                    {
                        errors.push(e); stream.drop_line();
                        while lmb.into_exclusive().satisfy(stream.current()) { stream.drop_line(); }
                    },
                    NotConsumed => break
                }
            }
            if !errors.is_empty() { return FailedM(errors); }
        }
        SuccessM(ClassDef { begin: begin.clone(), pat, bindings })
    }
}
