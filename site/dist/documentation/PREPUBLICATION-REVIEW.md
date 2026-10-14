# Prepublication review of the corrected edition

The selected edition has completed renewed formal verification and model-assisted mathematical review. Its scope is 265 Lean modules and 59 paper results. Eight paper results are conditional; three excluded claims remain outside the catalogue. Preparing this edition has not published it remotely.

## Formal verification and mathematical correspondence

The corrected Lean source set passed a fresh strict build, exhaustive declaration and axiom inspection, and all five kernel replays. The audit found no `sorryAx`, custom axioms, native trust axioms or unsafe project declarations used as logical evidence. The only axioms were Lean's standard `propext`, `Classical.choice` and `Quot.sound`. All 21,064 serialized declarations matched their inherited types and proof values. This is a declaration census, not a count of independent research theorems.

Every module's displayed statement, hypotheses, source download and fresh declaration export was checked against the renewed semantic ledger. Sixteen explanatory comment corrections in twelve modules restore omitted ranges and distinguish proposed conditions from proved implications. They do not change definitions, theorem statements or proof tokens.

- [Fresh formal audit](../audit/prepublication/formal/FINAL-REVIEW.json)
- [Module-by-module mathematical correspondence](../audit/prepublication/lean-semantics/SEMANTIC-REVIEW.json)
- [Exact public-interface comparison](../audit/prepublication/lean-semantics/FINAL-PUBLIC-INTERFACE-COMPARISON.json)

## Written proofs

All 59 selected paper statements and their arguments were reviewed. The earlier delivery omitted some definitions and complete derivations. Twelve full mathematical supplements now supply those arguments and definitions, with a separate second review. Four text clarifications correct endpoint scope, remove an undefined extraneous formula, repair small-index wording and restrict an abstract sharpness example to its actual domain. The historical count of 56 accepted and 3 repaired original statements is preserved.

Finite certificate checks were replayed on their exact inputs. Their finite conclusions are kept distinct from the accompanying induction arguments. Exact rational and symbolic algebra checks support the asymptotic derivations. A separate direct game-model check supplies finite corroboration; it does not replace the formal universal proof.

- [Complete proof supplements](../papers/supplements/INDEX.md)
- [Statement-by-statement paper review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Final public proof comparison](../audit/prepublication/papers/FINAL-CANDIDATE-PAPER-REVIEW.json)
- [Independent second review of full supplements](../audit/prepublication/root/SUPPLEMENT-SECOND-REVIEW.json)
- [Fresh finite certificate replay](../audit/prepublication/papers/FINITE-CERTIFICATE-REPLAY.json)

## Release boundary

The release gate binds the reviewed inputs and every admitted repository file by SHA-256. Packaging and the Pages exporter use explicit allowlists. Adding a local file does not admit it for publication; changing an approved file invalidates the gate. The ZIP delivery receipt also verifies every archived byte. The original broader collection remains on HOLD.

The review is model-assisted, with separate formal, semantic and paper reviewers. It does not claim external human peer review, literature-wide novelty, formalization of every paper result, or a solution of the excluded open suppliers. The [audit scope](AUDIT-SCOPE.md) and [release notes](../RELEASE-NOTES.md) state those limits explicitly.
