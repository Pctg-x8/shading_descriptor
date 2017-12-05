
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait, slice_patterns)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod tokparse;
mod parser;
// mod typepaint;

pub use tokparse::TokenStream;
pub use tokparse::{Location, Source, Token, TokenKind, NumericTy, EnclosureKind, TokenizerCache, Semantics, Keyword, BType, TokenizerState, PreanalyzedTokenStream};
pub use parser::{Success, Failed, NotConsumed, Parser, ParserWithIndent};
pub use parser::{Associativity, AssociativityEnv};
pub use parser::{SemanticInput, SemanticOutput, UniformDeclaration, ConstantDeclaration, ValueDeclaration};
pub use parser::{ShaderStage, ShaderStageDefinition, shader_stage_definition};
pub use parser::{ShadingState, ShadingStates, CompareOp, StencilOp, StencilTestConfig};
pub use parser::{ShadingPipeline, shading_pipeline};
pub use parser::{Expression, ExpressionFragment, FullExpression, expression, full_expression, expr_lettings};
pub use parser::{FullTypeDesc, full_type};
pub use parser::{TypeFn, TypeDeclaration, type_fn, type_decl};

// pub use typepaint::AssociativityDebugPrinter;
