import R151FAtomicPreview

set_option autoImplicit false

namespace ChompLean

/-!
R151F-S: syndeticity and the first-failure ledger at the atomic case.

This file proves the corrected form of [NEAR-G-PREVIEW].  The previously
recorded direction (`H >= g-2`) was wrong; the true consequences of a
3-syndetic freeze word under the atomic boundary are:

* columns `g` and `g+1` are freeze-free for blockers up to `v-3` in the
  no-sibling world (W1) — `g` by the world's defining clause, `g+1` by
  owner coverage alone — so a syndetic window at `{g-1,g,g+1}` forces an
  occupant at exactly `g-1`;
* the preview host therefore satisfies `H <= g-2` (it avoids the occupied
  column `g-1` by `gameF_preview_column_freeze_free` and is below `g` by
  the `g`-extension), and the occupant becomes a forced supplier-law
  crossing into column `H`;
* the first-failure induction ledger pins the occupant to `{v-4, v-3}` —
  the burn row's or the preview row's own value — and kills the sibling
  world W2 outright: no blocker at most `v-3` can freeze exactly at `g`.

Receipts (N=4000, not proof): the occupant of `g(v)` is always `>= v-2`
(zero violations in 1657 blockers), the occupant of `g(v)-1` is always
`>= v-4` (zero violations; `v-3` occurs 193 times, `v-4` once).

The atomic endgame is therefore two worlds: W1 with a named near-sibling
frozen at `g-1` and a forced pre-freeze visit in the preview column, or
W3 with a top sibling `v-2`/`v-1` frozen exactly at `g`.
-/

/-- No blocker below the target freezes strictly above the owner cutoff:
its owner is its freeze, owner coverage bounds it by `g`, and the freeze
column is unique by fixed-row injectivity. -/
theorem gameF_ownerCovered_no_blocker_freeze_above_g
    {v g k c : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hkv : k < v)
    (hck : c < k)
    (hfreeze : gameF k c = k) :
    c <= g := by
  have hkpos : 0 < k := by omega
  rcases howners k hkpos hkv with
      ⟨a, hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
  · exact False.elim (disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨c, hck, hfreeze⟩)
  · have hcrk : c = rk := gameRecurrenceModel.fixed_q_injective
      (q := k) (Nat.le_of_lt hck) (Nat.le_of_lt hrkk)
      (hfreeze.trans hstartk.symm)
    omega

/-! ## 1. The first-failure ledger -/

/-- The first-failure induction ledger in inequality form: every blocker
below the target has a strictly smaller blocker count and respects its
own upper rail (`2*rk <= k + A(k-1) + 2` is exactly
`rk <= blockerMidpoint A k + 1`).  This is R136's
`hfreezeInductionData`, restated. -/
def FirstFailureLedger (A : Nat -> Nat) (q : Nat) : Prop :=
  forall k rk, 0 < k -> k < q + 3 -> rk < k -> gameF k rk = k ->
    A (k - 1) + 1 <= A (q + 2) /\ 2 * rk <= k + A (k - 1) + 2

/-- The ledger kills the sibling world W2: a blocker at most `v-3`
frozen exactly at the target midpoint `g` would violate its own rail —
its midpoint is at least one blocker-count behind. -/
theorem gameF_ledger_no_low_blocker_at_g
    {A : Nat -> Nat} {q g k0 : Nat}
    (hgdef : q + 2 + A (q + 2) <= 2 * g)
    (hledger : FirstFailureLedger A q)
    (hk0q : k0 <= q)
    (hgk : g < k0)
    (hfreeze : gameF k0 g = k0) :
    False := by
  have h := hledger k0 g (by omega) (by omega) hgk hfreeze
  obtain ⟨h1, h2⟩ := h
  omega

/-- Ledger pin for a `g-1` occupant: a blocker at most `v-3` frozen at
`g-1` must be `v-4` or `v-3` itself. -/
theorem gameF_ledger_gm1_occupant_near_v
    {A : Nat -> Nat} {q g k1 : Nat}
    (hgdef : q + 2 + A (q + 2) <= 2 * g)
    (hledger : FirstFailureLedger A q)
    (hg1 : 1 <= g)
    (hk1q : k1 <= q)
    (hgk : g - 1 < k1)
    (hfreeze : gameF k1 (g - 1) = k1) :
    q - 1 <= k1 := by
  have h := hledger k1 (g - 1) (by omega) (by omega) hgk hfreeze
  obtain ⟨h1, h2⟩ := h
  omega

/-! ## 2. Syndeticity forces the `g-1` occupant in W1 -/

/-- 3-syndeticity of the freeze word through blocker size `qb` on columns
up to `L`: every window of three consecutive columns contains the freeze
column of some blocker at most `qb`. -/
def FreezeWordSyndeticThrough (qb L : Nat) : Prop :=
  forall c, c + 2 <= L ->
    exists k rk, k <= qb /\ rk < k /\ c <= rk /\ rk <= c + 2 /\
      gameF k rk = k

/-- In the no-sibling world the columns `g` and `g+1` are freeze-free for
blockers at most `v-3`, so the syndetic window `{g-1,g,g+1}` puts its
occupant at exactly `g-1`. -/
theorem gameF_syndetic_W1_gm1_occupant
    {q g : Nat}
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hNB : Not (exists k0, g < k0 /\ k0 < q + 3 /\ gameF k0 g = k0))
    (hsyn : FreezeWordSyndeticThrough q (g + 1))
    (hg1 : 1 <= g) :
    exists k1, k1 <= q /\ g - 1 < k1 /\ gameF k1 (g - 1) = k1 := by
  rcases hsyn (g - 1) (by omega) with ⟨k, rk, hkq, hrkk, hlo, hhi, hfr⟩
  by_cases hrkg : rk = g
  · exact False.elim
      (hNB ⟨k, by omega, by omega, by rw [← hrkg]; exact hfr⟩)
  · by_cases hrkg1 : rk = g + 1
    · have hfr1 : gameF k (g + 1) = k := by
        rw [← hrkg1]; exact hfr
      have hle := gameF_ownerCovered_no_blocker_freeze_above_g
        (v := q + 3) (g := g) (k := k) (c := g + 1) howners
        (by omega) (by omega) hfr1
      omega
    · have hrkgm1 : rk = g - 1 := by omega
      exact ⟨k, hkq, by omega, by rw [← hrkgm1]; exact hfr⟩

/-! ## 3. The strengthened world splits -/

/-- Three worlds minus one: under the ledger the atomic boundary has only
W1 (no sibling at `g`, column `g` consumed below the burn, `H<g`) and W3
(a top sibling `v-2`/`v-1` frozen at `g`). -/
theorem gameF_atomic_boundary_two_worlds
    {A : Nat -> Nat} {q g H : Nat}
    (hrv : g + 2 < q + 3)
    (hstart : gameF (q + 3) (g + 2) = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : g + 2 <= q - 1)
    (hq1 : 1 <= q)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g)
    (hledger : FirstFailureLedger A q) :
    ((exists w, g < w /\ w < q - 1 /\ gameF w g = q + 3) /\ H < g) \/
    (exists k0, (k0 = q + 1 \/ k0 = q + 2) /\ gameF k0 g = k0) := by
  rcases gameF_atomic_boundary_three_worlds hrv hstart howners hra hq1
      hburn hpreviewLeft hpreview with h1 | h2 | h3
  · exact Or.inl h1
  · rcases h2 with ⟨⟨k0, hgk, hk0q, hfr⟩, _⟩
    exact False.elim
      (gameF_ledger_no_low_blocker_at_g hgdef hledger hk0q hgk hfr)
  · exact Or.inr h3

/-- The atomic endgame under syndeticity and the ledger.  Either W1 with
the full corrected [NEAR-G-PREVIEW] package — an occupant `k1 in
{v-4, v-3}` frozen at `g-1`, the preview host at `H <= g-2`, a forced
supplier-law visit of `k1` in column `H` strictly before its own row,
and the target's column-`g` consumption strictly below the burn — or W3
with a top sibling frozen exactly at `g`. -/
theorem gameF_atomic_syndetic_ledger_endgame
    {A : Nat -> Nat} {q g H : Nat}
    (hrv : g + 2 < q + 3)
    (hstart : gameF (q + 3) (g + 2) = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : g + 2 <= q - 1)
    (hq1 : 1 <= q)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g)
    (hledger : FirstFailureLedger A q)
    (hsyn : FreezeWordSyndeticThrough q (g + 1))
    (hg1 : 1 <= g) :
    (exists k1, (k1 = q - 1 \/ k1 = q) /\ gameF k1 (g - 1) = k1 /\
      H < g - 1 /\
      (exists a, H < a /\ a < k1 /\ gameF a H = k1) /\
      (exists w, g < w /\ w < q - 1 /\ gameF w g = q + 3)) \/
    (exists k0, (k0 = q + 1 \/ k0 = q + 2) /\ gameF k0 g = k0) := by
  by_cases hB : exists k0, g < k0 /\ k0 < q + 3 /\ gameF k0 g = k0
  · rcases hB with ⟨k0, hgk, hkv, hk0⟩
    by_cases hk0q : k0 <= q
    · exact False.elim
        (gameF_ledger_no_low_blocker_at_g hgdef hledger hk0q hgk hk0)
    · exact Or.inr ⟨k0, by omega, hk0⟩
  · left
    rcases gameF_syndetic_W1_gm1_occupant howners hB hsyn hg1 with
      ⟨k1, hk1q, hgk1, hfr1⟩
    have hpin := gameF_ledger_gm1_occupant_near_v hgdef hledger hg1
      hk1q hgk1 hfr1
    have hHne : g - 1 ≠ H :=
      gameF_preview_column_freeze_free hpreview hk1q hgk1 hfr1
    have hext := gameF_atomic_boundary_g_extension hrv hstart howners hB
      hra hq1 hburn hpreviewLeft hpreview
    have hHlt : H < g - 1 := by
      have hHg := hext.2
      omega
    have hvisit := gameF_preview_crossing_blocker_prefreeze_visit
      hpreview hk1q (by omega) hgk1 hfr1
    exact ⟨k1, by omega, hfr1, hHlt, hvisit, hext.1⟩

#print axioms gameF_ownerCovered_no_blocker_freeze_above_g
#print axioms gameF_ledger_no_low_blocker_at_g
#print axioms gameF_ledger_gm1_occupant_near_v
#print axioms gameF_syndetic_W1_gm1_occupant
#print axioms gameF_atomic_boundary_two_worlds
#print axioms gameF_atomic_syndetic_ledger_endgame

end ChompLean
