
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait, slice_patterns)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod tokparse;
mod parser;
mod typepaint;

pub use tokparse::TokenStream;
pub use tokparse::{Location, Source, Token, TokenKind, NumericTy, EnclosureKind, TokenizerCache, Semantics, Keyword, BType, TokenizerState, PreanalyzedTokenStream};
pub use parser::{Success, Failed, NotConsumed, Parser, FreeParser, BlockParser, BlockParserM};
pub use parser::{Associativity, AssociativityEnv};
pub use parser::{SemanticInput, SemanticOutput, UniformDeclaration, ConstantDeclaration, ValueDeclaration};
pub use parser::{ShaderStage, ShaderStageDefinition};
pub use parser::{ShadingState, ShadingStates, CompareOp, StencilOp, StencilTestConfig, BlendingStateConfig, depth_state};
pub use parser::{ShadingPipeline, shading_pipeline};
pub use parser::{ExpressionSynTree, FullExpression};
pub use parser::{FullTypeDesc, TypeSynTree, TypeFn, TypeDeclaration, DataConstructor, TypeDeclarable};
pub use parser::utils::Leftmost;

pub use typepaint::{AssociativityDebugPrinter, ConstructorCollector};
pub use typepaint::{ConstructorEnv, ConstructorEnvironment, ShadingPipelineConstructorEnv, ConstructorEnvPerShader};
pub use typepaint::{deform_ty, TyDeformerIntermediate};

use typepaint::{RcMut, WeakMut};
