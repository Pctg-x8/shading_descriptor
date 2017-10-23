
#![feature(placement_in_syntax, collection_placement, box_syntax)]

extern crate regex;
#[macro_use] extern crate lazy_static;

mod tokparse;
mod parser;
mod expression_parser;

pub use tokparse::{Location, Source, Token, NumericTy, EnclosureKind, TokenizerCache, Semantics, Keyword, BType};
pub use parser::{SemanticInput, semantic_input, semantic_inputs};
pub use parser::{SemanticOutput, semantic_output};
pub use parser::{ShaderStage, ShaderStageDefinition, shader_stage_definition};
pub use expression_parser::{Expression, ExpressionFragment, expression};
