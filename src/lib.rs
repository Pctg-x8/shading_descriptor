
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait, slice_patterns, inclusive_range_syntax)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod pool;

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
pub use parser::{ExpressionSynTree, FullExpression, BlockContent};
pub use parser::{FullTypeDesc, TypeSynTree, TypeFn, TypeDeclaration, DataConstructor, TypeDeclarable, InferredArrayDim};
pub use parser::utils::Leftmost;

pub use deformer::EqNoloc;
pub use deformer::{TyDeformerIntermediate, deform_ty};
pub use deformer::{ExprDeformerIntermediate, deform_expr, deform_expr_full};

pub use typepaint::{AssociativityDebugPrinter, ConstructorCollector};
pub use typepaint::{ConstructorEnv, ConstructorEnvironment, ShadingPipelineConstructorEnv, ConstructorEnvPerShader};

pub use lambda::{Numeric, Lambda};

use typepaint::{RcMut, WeakMut};
