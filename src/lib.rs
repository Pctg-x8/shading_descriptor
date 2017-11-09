
#![feature(placement_in_syntax, collection_placement, box_syntax, placement_new_protocol, try_trait)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod tokparse; // mod layout;
mod parser;

pub use tokparse::{Location, Source, Token, TokenKind, NumericTy, EnclosureKind, TokenizerCache, Semantics, Keyword, BType};
// pub use layout::{LexemeInsertions, LexemeIndentInsertions, LayoutFreeTokenStream};
pub use parser::{SemanticInput, SemanticOutput, semantic_input, semantic_output};
pub use parser::{UniformDeclaration, ConstantDeclaration, uniform_decl, constant_decl};
pub use parser::{ValueDeclaration, value_decl};
pub use parser::{ShaderStage, ShaderStageDefinition, shader_stage_definition};
pub use parser::{ShadingState, ShadingStates, CompareOp, StencilOp, StencilTestConfig};
pub use parser::{ShadingPipeline, shading_pipeline};
pub use parser::{Expression, ExpressionFragment, FullExpression, expression, full_expression, expr_lettings};
pub use parser::{Type, TypeFragment, user_type};
pub use parser::{TypeFn, TypeDeclaration, type_fn, type_decl};
