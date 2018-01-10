
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait, slice_patterns, inclusive_range_syntax)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod tokparse;
mod parser;
mod deformer;
mod typepaint;

mod lambda;

pub use tokparse::TokenStream;
pub use tokparse::{Location, Source, Token, TokenKind, NumericTy, EnclosureKind, TokenizerCache, Semantics, Keyword, BType, TokenizerState, PreanalyzedTokenStream};
pub use parser::{Success, Failed, NotConsumed, Parser, FreeParser, BlockParser, BlockParserM};
pub use parser::{Associativity, AssociativityEnv};
pub use parser::{SemanticInput, SemanticOutput, UniformDeclaration, ConstantDeclaration, ValueDeclaration};
pub use parser::{ShaderStage, ShaderStageDefinition};
pub use parser::{ShadingState, ShadingStates, CompareOp, StencilOp, StencilTestConfig, BlendingStateConfig, depth_state};
pub use parser::{ShadingPipeline, shading_pipeline};
pub use parser::{ExpressionSynTree, FullExpression, BlockContent, ExprPatSynTree};
pub use parser::{FullTypeDesc, TypeSynTree, TypeFn, TypeDeclaration, DataConstructor, TypeDeclarable, InferredArrayDim};
pub use parser::utils::Leftmost;

pub use deformer::EqNoloc;
pub use deformer::{TyDeformerIntermediate, deform_ty};
pub use deformer::{ExprDeformerIntermediate, deform_expr, deform_expr_full};
pub use deformer::{DeformedExprPat, deform_expr_pat};

pub use typepaint::{AssociativityDebugPrinter, ConstructorCollector};
pub use typepaint::{ConstructorEnv, ConstructorEnvironment, ShadingPipelineConstructorEnv, ConstructorEnvPerShader};
pub use typepaint::{TypedDataConstructorScope, TypedDataConstructor};

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
