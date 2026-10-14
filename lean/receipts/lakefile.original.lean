import Lake
open Lake DSL

package ChompLean where

lean_lib ChompLean where

@[default_target]
lean_lib ResearchCore where
  roots := #[`ResearchCore]
