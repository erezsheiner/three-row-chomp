# Canonical Lean core

Pinned Lean 4.29.1 package for `lake build ResearchCore ChompLean`.

The reviewed source set contains the original 264 modules plus the separately
promoted `ClaudeFutureFreezeDiagonal` dependency. See the
[full audit](../../audit/full/lean/REPORT.md),
[exact mathematical scopes](../../audit/full/lean/MAIN-CLAIM-MAPPING.md), and
[source manifest](../../audit/full/lean/final-source-manifest.json).

The proof code is unchanged. Misleading documentation was corrected in this
publication copy. The initial full audit included corrections to
`SJSDiagonalDictionary` and `EndToEndInvariantAssembly`. A subsequent review
of all 265 modules corrected 54 prose findings in 45 modules, plus one finite
replay clarification. Every changed module passed strict recompilation; all
2,109 affected serialized declarations retained exactly the same types,
values and declaration-specific fields. The original full kernel audit is
preserved and inherited through this exact identity, not represented as a
second full replay. See the [amendment receipt](../../audit/full/lean-documentation-amendment/receipt.json)
and [revision history](../../audit/full/lean/source-documentation-revisions.json).
The SJS file does not establish its proposed all-row implementation bridge.
The end-to-end interface remains conditional on arbitrary supplied predicates
and functions, without a concrete game algorithm or complexity theorem.

The Lake configuration registers all source modules and treats warnings as
errors, with three stylistic linters disabled. Its historical original is
preserved at [lakefile.original.lean](../receipts/lakefile.original.lean).
No precompiled artifacts are part of this source package. The `audits/`
directory contains inspection tooling, excluded from the 265 proof modules;
its environment-inspection implementation is not a mathematical theorem.
