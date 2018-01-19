
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait, slice_patterns, inclusive_range_syntax)]

extern crate regex;
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate pshcompile_custom_derive;

#[macro_use] mod macros;
mod tokparse;
mod parser;
mod deformer;
mod symbol;
mod rewrite_expr;
mod typepaint;
mod patresolve;

mod lambda;

pub use tokparse::TokenStream;
pub use tokparse::{Location, Source, GenSource, GenNumeric};
pub use tokparse::{Token, TokenKind, NumericTy, EnclosureKind, Semantics, Keyword, BType};
pub use tokparse::{TokenizerState, TokenizerCache, PreanalyzedTokenStream};
pub use parser::{Success, Failed, NotConsumed, Parser, FreeParser, BlockParser, BlockParserM};
pub use parser::{Associativity, AssociativityEnv};
pub use parser::{SemanticInput, SemanticOutput, UniformDeclaration, ConstantDeclaration, ValueDeclaration};
pub use parser::{ShaderStage, ShaderStageDefinition};
pub use parser::{ShadingState, ShadingStates, CompareOp, StencilOp, StencilTestConfig, BlendingStateConfig, depth_state};
pub use parser::{ShadingPipeline, shading_pipeline};
pub use parser::{ExpressionSynTree, FullExpression, BlockContent, ExprPatSynTree, Binding};
pub use parser::{FullTypeDesc, TypeSynTree, TypeFn, TypeDeclaration, DataConstructor, TypeDeclarable, InferredArrayDim};
pub use parser::utils::Leftmost;

pub use rewrite_expr::{PipelineDeformed, StageDeformed};
pub use rewrite_expr::ComplexDeformationError;

pub use deformer::{EqNoloc, Deformable, DeformationError};

pub use typepaint::{AssociativityDebugPrinter, ConstructorCollector};
pub use typepaint::{ConstructorEnv, ConstructorEnvironment, ShadingPipelineConstructorEnv, ConstructorEnvPerShader};
pub use typepaint::{TypedDataConstructorScope, TypedDataConstructor, DataConstructorIndex};

pub use lambda::{Numeric, Lambda};

// use typepaint::{RcMut, WeakMut};
use std::cell::RefCell;
use std::rc::{Rc, Weak};
pub type RcMut<T> = Rc<RefCell<T>>; pub type WeakMut<T> = Weak<RefCell<T>>;
pub fn new_rcmut<T>(init: T) -> RcMut<T> { Rc::new(RefCell::new(init)) }

/// Pretty-printing(human readable printing)
pub trait PrettyPrint { fn pretty_print<W: std::io::Write>(&self, sink: &mut W) -> std::io::Result<()>; }
/// chained printing helper
pub trait PrettyPrintSink
{
    fn pretty_sink<P: ::PrettyPrint>(&mut self, target: &P) -> std::io::Result<&mut Self>;
    fn print(&mut self, text: &[u8]) -> std::io::Result<&mut Self>;

    fn print_if(&mut self, text: &[u8], cond: bool) -> std::io::Result<&mut Self>
    {
        if cond { self.print(text) } else { Ok(self) }
    }
}
impl<W: std::io::Write> PrettyPrintSink for W
{
    fn pretty_sink<P: ::PrettyPrint>(&mut self, target: &P) -> std::io::Result<&mut Self> { target.pretty_print(self).map(|_| self) }
    fn print(&mut self, text: &[u8]) -> std::io::Result<&mut Self> { self.write(text).map(|_| self) }
}
