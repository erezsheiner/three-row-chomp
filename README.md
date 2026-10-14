> Work in progress. This project is under active development and may contain errors. Results, proofs, and documentation may be revised.

# Three-Row Chomp research library

A searchable English collection of formal Lean results and paper proofs with documented model-assisted review for Three-Row Chomp.

This edition contains **265 audited Lean modules and 59 curated paper results**. Each result keeps its exact statement, hypotheses and evidence. Conditional results remain conditional; a theorem proving an implication does not establish its premises.

- [Browse the research library](site/dist/index.html)
- [Read the English proofs](papers/ENGLISH-PROOFS.md)
- [Understand the audit scope](docs/AUDIT-SCOPE.md)
- [Read the renewed prepublication review](docs/PREPUBLICATION-REVIEW.md)
- [See the release notes](RELEASE-NOTES.md)
- [Read the complete definitions and proof supplements](papers/supplements/INDEX.md)

The Lean sources are in `lean/core/`, with the toolchain pinned by `lean-toolchain`. The paper proofs are a separate mathematical layer: their inclusion does not mean that every paper result has been formalized in Lean. Some Lean modules also contain abstract interfaces and definitions of open conditions; their presence is not a proof that those conditions hold.

## Reproduce the formal build

With the pinned Lean toolchain installed, run from `lean/core/`:

```text
lake build ResearchCore ChompLean
```

The [audit scope](docs/AUDIT-SCOPE.md) explains the additional kernel replay, declaration and axiom checks used for this edition. A successful build does not independently repeat the mathematical correspondence review.

## Release scope

This is a deliberately selected release. Its 59 paper entries comprise 56 accepted statements and 3 repaired statements, all in their reviewed form. Two open questions and one unresolved original claim are excluded from the public result catalogue. The excluded claim is not needed to admit the results included here; results with additional unproved suppliers state those suppliers as hypotheses.

The original full collection remains on **HOLD** in its separate local audit directory. Any release approval applies only to the files and hashes listed in this edition's `audit/release/RELEASE-FILES.json` and `audit/release/INPUTS.json`, under `audit/release/REVIEW.json` and `PUBLICATION-STATUS.json`. It does not approve the original collection or later edits automatically.

See [hosting instructions](docs/HOSTING.md) for the static website. Preparing this package does not upload it to GitHub, deploy a website or submit an arXiv revision.

Lean kernel checking and model-assisted mathematical review are separate evidence layers. The review does not claim external human peer review, novelty or priority across the literature. Existing credits and licence notices are retained; this edition does not assign a new blanket licence to historical material.
