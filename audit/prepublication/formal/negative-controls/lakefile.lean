import Lake
open Lake DSL
package NegativeAuditControl where
  moreLeanArgs := #["-DwarningAsError=true"]
@[default_target]
lean_lib AuditBadAxiom where
