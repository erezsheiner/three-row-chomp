import XTauWindowLaw
import R184FutureDiagonalPin
import R66CeilingBase

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
# X-TAU: corridor + consumer for the gated future-diagonal pin
(`X-TAU-GATED-FUTURE-DIAGONAL-PIN-AUDIT-2026-07-23.md`, §§3–7)

Formalization of the paper proofs of the audit report:

* §4  — the EXACT factorization
  `GatedFutureDiagonalPin ↔ GatedNoDeepFuture ∧ NoDelayedPenultimateEcho`
  (`gatedFutureDiagonalPin_iff_noDeep_and_noEcho`): the "next diagonal"
  half of the gated pin is literally R184's old atom C.
* §5.1 — `GatedDeepAnchorHostCorridor`: a DEEP gated future-diagonal anchor
  forces a unique row-host of `d(t)` in EVERY corridor row `r ∈ (e, x]`,
  with `d(r) > d(t)`, host column `≤ e` (`= e` exactly at `r = x`,
  `< e` below), `3 ≤ h_r` and the R184 owner window `t ≤ r + h_r` on
  intermediate rows, pairwise-distinct host columns, and the boxed bounds
  `4 ≤ e`, `e+2 ≤ x ≤ 2e-2`, `x < t ≤ 2e`.
* §6.1 — `gated_anchor_suffix_packing`: unconditional suffix bound
  `x - e ≤ d(x) - V` for every gated anchor (row injection + diagonal
  maximality + no-break packing into `(V, d(x)]`).
* §3/§7 — `GatedFutureDiagonalNoRightShift` DECLARED as a `Prop` (OPEN),
  and the §7 consumer: under it every gated range anchor of `d(t)` is
  penultimate (mass exactly 1) and unique — the report's
  `Λ₃(d(t)) ≤ 1`, anchor-by-anchor.

## What is proved UNCONDITIONALLY here

`gameF_diagonal_ne_row_succ`, `gated_deep_anchor_host_corridor`,
`corridor_hosts_pairwise_distinct`, `gated_deep_anchor_corridor_bounds`,
`gated_anchor_suffix_packing`, `gatedFutureDiagonalPin_iff_noDeep_and_noEcho`.

## What is CONDITIONAL (open inputs as explicit hypotheses, never sorries)

* `GatedFutureDiagonalNoRightShift` — §3 target, DECLARED, OPEN.  Consumed by
  `gated_range_anchor_penultimate_of_noRightShift`,
  `gated_range_anchor_unique_of_noRightShift`,
  `gated_range_anchor_mass_one_of_noRightShift`.
* `GatedFutureDiagonalPin` (from `XTauWindowLaw`) stays OPEN; the iff only
  re-expresses it.

## What this file does NOT say

* It does NOT prove `GatedFutureDiagonalNoRightShift`, atom C
  (`NoDelayedPenultimateEcho`), `GatedNoDeepFuture`, or the pin.
* It does NOT claim `GatedFutureDiagonalPin → GatedFutureDiagonalNoRightShift`
  (the early appearance in a right-shift pair may be UNGATED — these are two
  different suppliers; report §7).
* The corridor is NOT a contradiction: a graded matching `h_{e+j} = e-j`
  survives all bounds here (report §5.1, "what the corridor does not do").
* `GatedRangeUnitGap` (`d(x) = V+1`) is NOT a weak form of the pin and is NOT
  used: the gate is silent about `V+1` (report §6.2 caution).
* No global `Λ₃` is defined (same discipline as `XTauWindowLaw`): the §7
  consumer delivers the per-anchor mass-1 law plus uniqueness, which is the
  content the report's boxed `Λ₃(d(t)) ≤ 1` is assembled from.
  CORE: OPEN.
-/

/-! ## 0. Small rails -/

/-- A positive-row diagonal never equals its row successor:
`d(t) ≠ t+1` for `t ≥ 1` — the column-0 rail `f(t,0) = t+1`
(`gameF_col0`) already occupies `t+1` in the diagonal's MEX sources. -/
theorem gameF_diagonal_ne_row_succ {t : Nat} (ht : 0 < t) :
    gameF t t ≠ t + 1 := by
  intro heq
  have hmex : IsMex (B gameF t t) (gameF t t) :=
    gameF_brouwerRecurrence.2 (Nat.le_refl t) (by rintro ⟨hc, -⟩; omega)
  exact hmex.2.1 (Or.inr ⟨0, ht, by rw [gameF_col0]; omega⟩)

/-- Bounded-injective pigeonhole: `n` pairwise-distinct naturals inside
`[lo, lo+m)` force `n ≤ m`.  (Core-Lean induction on `m`; used by the
corridor bounds and the suffix packing.) -/
private theorem strictly_bounded_inj_le :
    ∀ (m : Nat) (g : Nat → Nat) (n lo : Nat),
      (∀ i, i < n → lo ≤ g i ∧ g i < lo + m) →
      (∀ i j, i < n → j < n → g i = g j → i = j) →
      n ≤ m := by
  intro m
  induction m with
  | zero =>
      intro g n lo hbnd _
      rcases Nat.lt_or_ge 0 n with hpos | hz
      · have := hbnd 0 hpos
        omega
      · omega
  | succ m ih =>
      intro g n lo hbnd hinj
      classical
      by_cases htop : ∃ i, i < n ∧ g i = lo + m
      · rcases htop with ⟨i, hin, hgi⟩
        have hle : n - 1 ≤ m := by
          apply ih (fun j => g (if j < i then j else j + 1)) (n - 1) lo
          · intro j hj
            show lo ≤ g (if j < i then j else j + 1) ∧
                 g (if j < i then j else j + 1) < lo + m
            by_cases hji : j < i
            · rw [if_pos hji]
              have hb := hbnd j (by omega)
              have hne : g j ≠ lo + m := by
                intro hgj
                have := hinj j i (by omega) hin (hgj.trans hgi.symm)
                omega
              omega
            · rw [if_neg hji]
              have hb := hbnd (j + 1) (by omega)
              have hne : g (j + 1) ≠ lo + m := by
                intro hgj
                have := hinj (j + 1) i (by omega) hin (hgj.trans hgi.symm)
                omega
              omega
          · intro j k hj hk heq
            have heq' : g (if j < i then j else j + 1) =
                g (if k < i then k else k + 1) := heq
            by_cases hji : j < i
            · by_cases hki : k < i
              · rw [if_pos hji, if_pos hki] at heq'
                exact hinj j k (by omega) (by omega) heq'
              · rw [if_pos hji, if_neg hki] at heq'
                have := hinj j (k + 1) (by omega) (by omega) heq'
                omega
            · by_cases hki : k < i
              · rw [if_neg hji, if_pos hki] at heq'
                have := hinj (j + 1) k (by omega) (by omega) heq'
                omega
              · rw [if_neg hji, if_neg hki] at heq'
                have := hinj (j + 1) (k + 1) (by omega) (by omega) heq'
                omega
        omega
      · have hle : n ≤ m := by
          apply ih g n lo
          · intro i hin
            have hb := hbnd i hin
            have : g i ≠ lo + m := fun hgi => htop ⟨i, hin, hgi⟩
            omega
          · exact hinj
        omega

/-! ## 1. §5.1 — the forced host corridor of a deep gated anchor -/

/-- **§5.1 `GatedDeepAnchorHostCorridor`, per-row content.**  For a DEEP
gated future-diagonal anchor (`e+1 < x < t`, `f(x,e) = d(t)`, gate), every
corridor row `r ∈ (e, x]` satisfies `d(r) > d(t)` and hosts `d(t)` at a
UNIQUE column `h < r`; moreover `h ≤ e`, with `h = e` exactly at the anchor
row and, on intermediate rows `r < x`: `3 ≤ h < e` and the R184 owner
window `t ≤ r + h`.

Mechanism (report §5.1): the diagonal `(r,r)` is a MEX cell whose coverage
must produce `d(t) < d(r)`; the diagonal source arm dies by
`diagonal_general_no_attack` against the unique owner `t`; the row arm is
the host.  `h > e` breaks the gate (no-break), `h = e` below `x` breaks
same-lower no-repeat, `h ∈ {0,1,2}` dies on the column-0 rail, the owner
window, and the `d(t) ≠ t+1` rail respectively. -/
theorem gated_deep_anchor_host_corridor {x e t : Nat}
    (hex : e + 1 < x) (hxt : x < t)
    (hanchor : gameF x e = gameF t t)
    (hgate : A1Gate x e (gameF t t)) :
    ∀ r, e < r → r ≤ x →
      gameF t t < gameF r r ∧
      ∃ h, h < r ∧ gameF r h = gameF t t ∧
        (∀ h', h' < r → gameF r h' = gameF t t → h' = h) ∧
        h ≤ e ∧ (r = x → h = e) ∧
        (r < x → h < e ∧ 3 ≤ h ∧ t ≤ r + h) := by
  intro r her hrx
  have htV : t < gameF t t := encoded_gt game_encodes (Nat.le_refl t)
  -- item 1: every corridor diagonal clears d(t) (no-break vs (r,r) live)
  have hdr : gameF t t < gameF r r := by
    rcases Nat.lt_or_ge (gameF t t) (gameF r r) with hgt | hle
    · exact hgt
    · exact (a1Gate_no_break hgate her
        ⟨r, Nat.le_refl r, hrx,
          Nat.le_of_lt (encoded_gt game_encodes (Nat.le_refl r)), hle⟩).elim
  refine ⟨hdr, ?_⟩
  -- item 2: host existence from the diagonal MEX coverage
  have hmex : IsMex (B gameF r r) (gameF r r) :=
    gameF_brouwerRecurrence.2 (Nat.le_refl r) (by rintro ⟨hc, -⟩; omega)
  rcases hmex.2.2 (gameF t t) (by omega) hdr with hR | hC
  · -- diagonal source arm: killed by the unique diagonal owner t > r
    rcases hR with ⟨a, har, hfa⟩
    rw [Nat.min_eq_left (Nat.le_of_lt har)] at hfa
    exact (encoding_diagonal_general_no_attack game_encodes
      (show a < t by omega) (Nat.le_refl t) hfa).elim
  · rcases hC with ⟨h, hhr, hfh⟩
    -- row injection: the host column is unique
    have huniq : ∀ h', h' < r → gameF r h' = gameF t t → h' = h := by
      intro h' hh'r hfh'
      have := encoding_fixed_q_injective game_encodes
        (Nat.le_of_lt hh'r) (Nat.le_of_lt hhr) (hfh'.trans hfh.symm)
      omega
    -- item 2': h ≤ e, else (r,h) is a live ≤-d(t) cell right of the gate
    have hhe : h ≤ e := by
      rcases Nat.lt_or_ge e h with heh | hhe'
      · exact (a1Gate_no_break hgate heh
          ⟨r, Nat.le_of_lt hhr, hrx, by rw [hfh]; omega,
            Nat.le_of_eq hfh⟩).elim
      · exact hhe'
    refine ⟨h, hhr, hfh, huniq, hhe, ?_, ?_⟩
    · -- item 3: at the anchor row the host IS the anchor column
      intro hrx'
      subst hrx'
      have := encoding_fixed_q_injective game_encodes
        (Nat.le_of_lt hhr) (by omega) (hfh.trans hanchor.symm)
      omega
    · -- items 4/7: intermediate rows
      intro hrltx
      have hwin := futureDiagonal_owner_window gameRecurrenceModel hhr
        (show r < t by omega) hfh
      have hcap : gameF r h ≤ r + h + 1 := hwin.2.1
      have hband : t ≤ r + h := hwin.2.2
      -- h ≠ e below x: same-lower no-repeat against the anchor cell
      have hne : h ≠ e := by
        intro heq
        subst heq
        exact encoding_same_lower_no_repeat game_encodes her hrltx
          (by omega) hfh hanchor
      -- 3 ≤ h: kill columns 0, 1, 2
      have hh3 : 3 ≤ h := by
        rcases Nat.lt_or_ge h 3 with hlt3 | hge3
        · exfalso
          by_cases h0 : h = 0
          · rw [h0, gameF_col0] at hfh
            omega
          · by_cases h1 : h = 1
            · omega
            · have h2 : h = 2 := by omega
              subst h2
              have hV1 : gameF t t = t + 1 := by omega
              exact gameF_diagonal_ne_row_succ (by omega) hV1
        · exact hge3
      exact ⟨by omega, hh3, hband⟩

/-- **§5.1 item 5.**  Corridor hosts occupy pairwise-distinct columns:
two rows `≤ x < t` cannot host `d(t)` in the same column
(same-lower no-repeat at value `d(t) > x`).  Unconditional. -/
theorem corridor_hosts_pairwise_distinct {x t r₁ r₂ h : Nat}
    (hxt : x < t) (hh : h < r₁) (h12 : r₁ < r₂) (h2x : r₂ ≤ x)
    (hf₁ : gameF r₁ h = gameF t t) (hf₂ : gameF r₂ h = gameF t t) : False := by
  have htV : t < gameF t t := encoded_gt game_encodes (Nat.le_refl t)
  exact encoding_same_lower_no_repeat game_encodes hh h12 (by omega) hf₁ hf₂

/-- **§5.1 boxed bounds.**  A deep gated future-diagonal anchor is confined
to the triangular corridor
`4 ≤ e`, `e+2 ≤ x ≤ 2e-2`, `t ≤ 2e`:
the `x-e-1` intermediate host columns are pairwise distinct inside
`{3, …, e-1}` (pigeonhole), and the first corridor row's owner window gives
`t ≤ 2e`. -/
theorem gated_deep_anchor_corridor_bounds {x e t : Nat}
    (hex : e + 1 < x) (hxt : x < t)
    (hanchor : gameF x e = gameF t t)
    (hgate : A1Gate x e (gameF t t)) :
    4 ≤ e ∧ e + 2 ≤ x ∧ x ≤ 2 * e - 2 ∧ t ≤ 2 * e := by
  classical
  have htV : t < gameF t t := encoded_gt game_encodes (Nat.le_refl t)
  have hcorr := gated_deep_anchor_host_corridor hex hxt hanchor hgate
  -- total host selector over the intermediate rows r = e+1+i
  have hHtotal : ∀ i : Nat, ∃ h : Nat, i < x - e - 1 →
      (h < e + 1 + i ∧ gameF (e + 1 + i) h = gameF t t ∧
       3 ≤ h ∧ h < e ∧ t ≤ e + 1 + i + h) := by
    intro i
    rcases Nat.lt_or_ge i (x - e - 1) with hi | hi
    · rcases (hcorr (e + 1 + i) (by omega) (by omega)).2 with
        ⟨h, hh1, hh2, _, _, _, hdeep⟩
      rcases hdeep (by omega) with ⟨hlt, h3, hwinb⟩
      exact ⟨h, fun _ => ⟨hh1, hh2, h3, hlt, hwinb⟩⟩
    · exact ⟨0, fun hcon => absurd hcon (by omega)⟩
  have hg : ∀ i, i < x - e - 1 →
      (Classical.choose (hHtotal i) < e + 1 + i ∧
       gameF (e + 1 + i) (Classical.choose (hHtotal i)) = gameF t t ∧
       3 ≤ Classical.choose (hHtotal i) ∧
       Classical.choose (hHtotal i) < e ∧
       t ≤ e + 1 + i + Classical.choose (hHtotal i)) :=
    fun i hi => Classical.choose_spec (hHtotal i) hi
  have hpig : x - e - 1 ≤ e - 3 := by
    apply strictly_bounded_inj_le (e - 3)
      (fun i => Classical.choose (hHtotal i)) (x - e - 1) 3
    · intro i hi
      show 3 ≤ Classical.choose (hHtotal i) ∧
           Classical.choose (hHtotal i) < 3 + (e - 3)
      have := hg i hi
      omega
    · intro i j hi hj heq
      have heq' : Classical.choose (hHtotal i) =
          Classical.choose (hHtotal j) := heq
      have hgi := hg i hi
      have hgj := hg j hj
      rcases Nat.lt_or_ge i j with hij | hij
      · exfalso
        have h2 : gameF (e + 1 + j) (Classical.choose (hHtotal i)) =
            gameF t t := by rw [heq']; exact hgj.2.1
        exact encoding_same_lower_no_repeat game_encodes hgi.1
          (by omega) (by omega) hgi.2.1 h2
      · rcases Nat.lt_or_ge j i with hji | hji
        · exfalso
          have h2 : gameF (e + 1 + i) (Classical.choose (hHtotal j)) =
              gameF t t := by rw [← heq']; exact hgi.2.1
          exact encoding_same_lower_no_repeat game_encodes hgj.1
            (by omega) (by omega) hgj.2.1 h2
        · omega
  have h0 := hg 0 (by omega)
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## 2. §6.1 — unconditional suffix packing under the gate -/

/-- **§6.1 `GatedAnchorSuffixPacking`.**  For EVERY gated anchor
`f(x,e) = V` (`e < x ≤ V`): `x - e ≤ d(x) - V`.  The `x-e` window cells
`(x,c]`, `e < c ≤ x`, are live (no-hole), of pairwise-distinct values
(row injection), each in `(V, d(x)]` (no-break below, diagonal maximality
above) — a packing of `x-e` distinct values into an interval of size
`d(x) - V`.

§6.2 caution (report): do NOT feed this with `GatedRangeUnitGap`
(`d(x) = V+1`) as a pin substitute — the gate is silent about `V+1`. -/
theorem gated_anchor_suffix_packing {x e : Nat}
    (hex : e < x) (hxV : x ≤ gameF x e)
    (hgate : A1Gate x e (gameF x e)) :
    x - e ≤ gameF x x - gameF x e := by
  have hdxV : gameF x e < gameF x x := by
    rcases Nat.lt_or_ge (gameF x e) (gameF x x) with hlt | hle
    · exact hlt
    · exact (a1Gate_no_break hgate hex
        ⟨x, Nat.le_refl x, Nat.le_refl x,
          Nat.le_of_lt (encoded_gt game_encodes (Nat.le_refl x)), hle⟩).elim
  apply strictly_bounded_inj_le (gameF x x - gameF x e)
    (fun i => gameF x (e + 1 + i)) (x - e) (gameF x e + 1)
  · intro i hi
    show gameF x e + 1 ≤ gameF x (e + 1 + i) ∧
         gameF x (e + 1 + i) < gameF x e + 1 + (gameF x x - gameF x e)
    have hlive : x ≤ gameF x (e + 1 + i) :=
      a1Gate_window_full hgate hxV (e + 1 + i) (by omega) (by omega)
    have hgt : gameF x e < gameF x (e + 1 + i) := by
      rcases Nat.lt_or_ge (gameF x e) (gameF x (e + 1 + i)) with hlt | hle
      · exact hlt
      · exact (a1Gate_no_break hgate (show e < e + 1 + i by omega)
          ⟨x, by omega, Nat.le_refl x, hlive, hle⟩).elim
    have hmax : gameF x (e + 1 + i) ≤ gameF x x :=
      diagonalMaximal gameRecurrenceModel (show e + 1 + i ≤ x by omega)
    omega
  · intro i j hi hj heq
    have heq' : gameF x (e + 1 + i) = gameF x (e + 1 + j) := heq
    have := encoding_fixed_q_injective game_encodes
      (show e + 1 + i ≤ x by omega) (show e + 1 + j ≤ x by omega) heq'
    omega

/-! ## 3. §4 — the exact factorization of the gated pin -/

/-- **§3 `GatedNoDeepFuture` (OPEN).**  No DEEP gated future-diagonal
anchor exists: no packet `e+1 < x < t`, `x ≤ d(t)`, `f(x,e) = d(t)`,
`G(x,e,d(t))`. -/
def GatedNoDeepFuture : Prop :=
  ∀ x e t : Nat, e + 1 < x → x < t → x ≤ gameF t t →
    gameF x e = gameF t t → A1Gate x e (gameF t t) → False

/- `NoDelayedPenultimateEcho` — R184's atom C — is NOT re-declared here:
the factorization below consumes the BANKED `R184FutureDiagonalPin`
definition verbatim (`∀ r t, r+3 ≤ t → gameF (r+1) r ≠ gameF t t`), making
the report's "the next-diagonal half is literally the old atom C" a
definitional identity, not an analogy. -/

/-- **§4.1 (exact factorization).**
`GatedFutureDiagonalPin ↔ GatedNoDeepFuture ∧ NoDelayedPenultimateEcho`.
The gate helps the penultimate half, but the "next diagonal" half of the
gated pin is LITERALLY the old atom C: attacking the full gated pin still
means solving an R184-family wall.  (Forward: the pin's `e = x-1` kills
depth, and at a delayed echo the auto-gate + pin force `t = r+2 < r+3`.
Backward: no-depth forces `e = x-1`; atom C at `r = x-1` forces
`t < x+2`.) -/
theorem gatedFutureDiagonalPin_iff_noDeep_and_noEcho :
    GatedFutureDiagonalPin ↔ (GatedNoDeepFuture ∧ NoDelayedPenultimateEcho) := by
  constructor
  · intro hpin
    constructor
    · intro x e t hex hxt hxV hanchor hgate
      rcases hpin x e t (by omega) hxt hxV hanchor hgate with ⟨-, he⟩
      omega
    · intro r t hrt heq
      have htV : t < gameF t t := encoded_gt game_encodes (Nat.le_refl t)
      have hgate : A1Gate (r + 1) r (gameF t t) := by
        have hauto := gameF_penultimate_gate_auto (x := r + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hauto
        rwa [heq] at hauto
      rcases hpin (r + 1) r t (by omega) (by omega) (by omega) heq hgate with
        ⟨ht, -⟩
      omega
  · rintro ⟨hdeep, hecho⟩ x e t hex hxt hxV hanchor hgate
    have he : e = x - 1 := by
      rcases Nat.lt_or_ge (e + 1) x with hlt | hge
      · exact (hdeep x e t hlt hxt hxV hanchor hgate).elim
      · omega
    have ht : t = x + 1 := by
      rcases Nat.lt_or_ge (x + 1) t with hlt | hge
      · exfalso
        have hx1 : x - 1 + 1 = x := by omega
        apply hecho (x - 1) t (by omega)
        rw [hx1, ← he]
        exact hanchor
      · omega
    exact ⟨ht, he⟩

/-! ## 4. §3/§7 — the weaker sufficient atom and its consumer -/

/-- **§3 `GatedFutureDiagonalNoRightShift` (OPEN; declared, not proved).**
Two early appearances of the same future-diagonal value `d(t)` cannot move
jointly right-and-down when the LATER one is gated: no
`f(r,h) = d(t) = f(s,e)` with `h < r`, `h < e`, `e < s`, `r < s < t` and
`A1Gate s e (d(t))`.  Only the late appearance is required to be gated —
`FutureDiagonalNoRightShift` (no gate premise) is a syntactically stronger ungated requirement and NOT
needed by the consumer.  Kill gates for any proof attempt (report §8/§10):
no full pin, no atom C, no NIE/RM2, no UnitDip/DD1, no range oracle, no
"no earlier appearance" assumption. -/
def GatedFutureDiagonalNoRightShift : Prop :=
  ∀ r h s e t : Nat,
    h < r → h < e → e < s → r < s → s < t →
    gameF r h = gameF t t → gameF s e = gameF t t →
    A1Gate s e (gameF t t) → False

/-- **§7, depth kill.**  Under `GatedFutureDiagonalNoRightShift`, every
gated range anchor of `d(t)` is penultimate: the corridor's first row
`r = e+1` would otherwise produce an early host strictly left of `e`, and
the gated anchor above it is exactly a forbidden right-shift. -/
theorem gated_range_anchor_penultimate_of_noRightShift
    (hnrs : GatedFutureDiagonalNoRightShift)
    {x e t : Nat}
    (hanchor : gameF x e = gameF t t) (hex : e < x)
    (hxV : x ≤ gameF t t) (hgate : A1Gate x e (gameF t t)) :
    e + 1 = x := by
  have hxt : x < t :=
    gated_range_anchor_is_future_preview hanchor hex hxV hgate
  rcases Nat.lt_or_ge (e + 1) x with hdeep | hshallow
  · exfalso
    rcases (gated_deep_anchor_host_corridor hdeep hxt hanchor hgate (e + 1)
        (by omega) (by omega)).2 with ⟨h, hh1, hh2, -, -, -, hd⟩
    rcases hd (by omega) with ⟨hlt, -, -⟩
    exact hnrs (e + 1) h x e t hh1 hlt hex (by omega) hxt hh2 hanchor hgate
  · omega

/-- **§7, uniqueness.**  Under `GatedFutureDiagonalNoRightShift`, two gated
range anchors of the SAME diagonal value coincide (and so does the owner:
diagonal no-attack pins `t`).  Two distinct penultimate anchors of one value
would themselves form a forbidden right-shift. -/
theorem gated_range_anchor_unique_of_noRightShift
    (hnrs : GatedFutureDiagonalNoRightShift)
    {x₁ e₁ t₁ x₂ e₂ t₂ : Nat}
    (h₁ : gameF x₁ e₁ = gameF t₁ t₁) (hex₁ : e₁ < x₁)
    (hxV₁ : x₁ ≤ gameF t₁ t₁) (hg₁ : A1Gate x₁ e₁ (gameF t₁ t₁))
    (h₂ : gameF x₂ e₂ = gameF t₂ t₂) (hex₂ : e₂ < x₂)
    (hxV₂ : x₂ ≤ gameF t₂ t₂) (hg₂ : A1Gate x₂ e₂ (gameF t₂ t₂))
    (hVeq : gameF t₁ t₁ = gameF t₂ t₂) :
    t₁ = t₂ ∧ x₁ = x₂ ∧ e₁ = e₂ := by
  have htt : t₁ = t₂ := by
    rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
    · exact (encoding_diagonal_general_no_attack game_encodes hlt
        (Nat.le_refl t₂) hVeq).elim
    · rcases Nat.lt_or_ge t₂ t₁ with hgt | hle
      · exact (encoding_diagonal_general_no_attack game_encodes hgt
          (Nat.le_refl t₁) hVeq.symm).elim
      · omega
  subst htt
  have hp₁ :=
    gated_range_anchor_penultimate_of_noRightShift hnrs h₁ hex₁ hxV₁ hg₁
  have hp₂ :=
    gated_range_anchor_penultimate_of_noRightShift hnrs h₂ hex₂ hxV₂ hg₂
  have hxt₁ : x₁ < t₁ :=
    gated_range_anchor_is_future_preview h₁ hex₁ hxV₁ hg₁
  have hxt₂ : x₂ < t₁ :=
    gated_range_anchor_is_future_preview h₂ hex₂ hxV₂ hg₂
  have hxx : x₁ = x₂ := by
    rcases Nat.lt_or_ge x₁ x₂ with hlt | hge
    · exact (hnrs x₁ e₁ x₂ e₂ t₁ hex₁ (by omega) hex₂ hlt hxt₂
        h₁ h₂ hg₂).elim
    · rcases Nat.lt_or_ge x₂ x₁ with hgt | hle
      · exact (hnrs x₂ e₂ x₁ e₁ t₁ hex₂ (by omega) hex₁ hgt hxt₁
          h₂ h₁ hg₁).elim
      · omega
  exact ⟨rfl, hxx, by omega⟩

/-- **§7 packaged (the report's boxed `Λ₃(d(t)) ≤ 1`, anchor-by-anchor).**
Under `GatedFutureDiagonalNoRightShift`, a gated range anchor of `d(t)` is
penultimate, sits strictly before the owner's birth, and its window mass is
EXACTLY 1; combined with `gated_range_anchor_unique_of_noRightShift` this
is the full per-value content of `Λ₃(d(t)) ≤ 1` (no global `Λ₃` is defined
here, by the `XTauWindowLaw` discipline). -/
theorem gated_range_anchor_mass_one_of_noRightShift
    (hnrs : GatedFutureDiagonalNoRightShift)
    {x e t : Nat}
    (hanchor : gameF x e = gameF t t) (hex : e < x)
    (hxV : x ≤ gameF t t) (hgate : A1Gate x e (gameF t t)) :
    e + 1 = x ∧ x < t ∧
      ((List.range' (e + 1) (x - e)).filter
        (fun c => decide (x ≤ gameF x c))).length = 1 := by
  have hp :=
    gated_range_anchor_penultimate_of_noRightShift hnrs hanchor hex hxV hgate
  have hxt : x < t :=
    gated_range_anchor_is_future_preview hanchor hex hxV hgate
  have hmass := a1Gate_anchor_mass hanchor hex hxV hgate
  refine ⟨hp, hxt, ?_⟩
  rw [hmass]
  omega

/-! ## 5. §7 addendum — a SPLIT pair of even weaker sufficient atoms

`GatedFutureDiagonalNoRightShift` implies both halves below, and the two
halves already suffice for the whole §7 consumer.  The split replaces the
`{GatedNoDeepFuture, atom C}` factor pair of the PIN by
`{GatedNoDeepFuture, PenultimateEchoPairKill}`.  PairKill is syntactically weaker than atom C: in any echo pair `x₁ < x₂ < t` the earlier echo has
delay `t - x₁ ≥ 2`, which atom C forbids (so atom C ⟹ PairKill —
compiled in `XTauExceederReduction`); as a forbidden-pattern specification, PairKill permits a single
long-delay echo, while atom C excludes it. This does not exhibit an actual-game
realization separating the two assertions.  [Corrected 2026-07-23 after the
fidelity audit: an earlier revision of this comment wrongly called the two
atoms incomparable.] -/

/-- **Split atom 2 (OPEN).**  No future diagonal has TWO penultimate
echoes: `f(x₁,x₁-1) = d(t) = f(x₂,x₂-1)` with `x₁ < x₂ < t` is impossible.
(Both echoes are automatically gated, so no gate premise is carried.) -/
def PenultimateEchoPairKill : Prop :=
  ∀ x₁ x₂ t : Nat, 0 < x₁ → x₁ < x₂ → x₂ < t →
    gameF x₁ (x₁ - 1) = gameF t t → gameF x₂ (x₂ - 1) = gameF t t → False

/-- `GatedFutureDiagonalNoRightShift` implies split atom 1. -/
theorem gatedNoDeepFuture_of_noRightShift
    (hnrs : GatedFutureDiagonalNoRightShift) : GatedNoDeepFuture := by
  intro x e t hex hxt hxV hanchor hgate
  have := gated_range_anchor_penultimate_of_noRightShift hnrs hanchor
    (by omega) hxV hgate
  omega

/-- `GatedFutureDiagonalNoRightShift` implies split atom 2: two penultimate
echoes of one owner are themselves a gated right-shift (the later echo's
gate is automatic). -/
theorem penultimateEchoPairKill_of_noRightShift
    (hnrs : GatedFutureDiagonalNoRightShift) : PenultimateEchoPairKill := by
  intro x₁ x₂ t hx₁ h12 hxt h₁ h₂
  have hgate : A1Gate x₂ (x₂ - 1) (gameF t t) := by
    have hauto := gameF_penultimate_gate_auto (x := x₂) (by omega)
    rwa [h₂] at hauto
  exact hnrs x₁ (x₁ - 1) x₂ (x₂ - 1) t (by omega) (by omega) (by omega)
    h12 hxt h₁ h₂ hgate

/-- The full pin also implies split atom 2 (each echo is a gated anchor, so
the pin pins `t = xᵢ + 1` twice). -/
theorem penultimateEchoPairKill_of_pin
    (hpin : GatedFutureDiagonalPin) : PenultimateEchoPairKill := by
  intro x₁ x₂ t hx₁ h12 hxt h₁ h₂
  have htV : t < gameF t t := encoded_gt game_encodes (Nat.le_refl t)
  have hg₁ : A1Gate x₁ (x₁ - 1) (gameF t t) := by
    have hauto := gameF_penultimate_gate_auto (x := x₁) hx₁
    rwa [h₁] at hauto
  have hg₂ : A1Gate x₂ (x₂ - 1) (gameF t t) := by
    have hauto := gameF_penultimate_gate_auto (x := x₂) (by omega)
    rwa [h₂] at hauto
  rcases hpin x₁ (x₁ - 1) t (by omega) (by omega) (by omega) h₁ hg₁ with
    ⟨ht₁, -⟩
  rcases hpin x₂ (x₂ - 1) t (by omega) (by omega) (by omega) h₂ hg₂ with
    ⟨ht₂, -⟩
  omega

/-- **§7 consumer from the SPLIT pair** (no corridor needed): under
`GatedNoDeepFuture ∧ PenultimateEchoPairKill`, a gated range anchor of
`d(t)` is penultimate with window mass exactly 1, and is unique for its
value.  This is the weakest currently-named sufficient supplier for the
report's `Λ₃(d(t)) ≤ 1`. -/
theorem gated_range_anchor_unique_of_split
    (hdeep : GatedNoDeepFuture) (hpair : PenultimateEchoPairKill)
    {x₁ e₁ t₁ x₂ e₂ t₂ : Nat}
    (h₁ : gameF x₁ e₁ = gameF t₁ t₁) (hex₁ : e₁ < x₁)
    (hxV₁ : x₁ ≤ gameF t₁ t₁) (hg₁ : A1Gate x₁ e₁ (gameF t₁ t₁))
    (h₂ : gameF x₂ e₂ = gameF t₂ t₂) (hex₂ : e₂ < x₂)
    (hxV₂ : x₂ ≤ gameF t₂ t₂) (hg₂ : A1Gate x₂ e₂ (gameF t₂ t₂))
    (hVeq : gameF t₁ t₁ = gameF t₂ t₂) :
    t₁ = t₂ ∧ x₁ = x₂ ∧ e₁ = e₂ ∧ e₁ + 1 = x₁ ∧
      ((List.range' (e₁ + 1) (x₁ - e₁)).filter
        (fun c => decide (x₁ ≤ gameF x₁ c))).length = 1 := by
  have htt : t₁ = t₂ := by
    rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
    · exact (encoding_diagonal_general_no_attack game_encodes hlt
        (Nat.le_refl t₂) hVeq).elim
    · rcases Nat.lt_or_ge t₂ t₁ with hgt | hle
      · exact (encoding_diagonal_general_no_attack game_encodes hgt
          (Nat.le_refl t₁) hVeq.symm).elim
      · omega
  subst htt
  have hxt₁ : x₁ < t₁ :=
    gated_range_anchor_is_future_preview h₁ hex₁ hxV₁ hg₁
  have hxt₂ : x₂ < t₁ :=
    gated_range_anchor_is_future_preview h₂ hex₂ hxV₂ hg₂
  have hp₁ : e₁ + 1 = x₁ := by
    rcases Nat.lt_or_ge (e₁ + 1) x₁ with hlt | hge
    · exact (hdeep x₁ e₁ t₁ hlt hxt₁ hxV₁ h₁ hg₁).elim
    · omega
  have hp₂ : e₂ + 1 = x₂ := by
    rcases Nat.lt_or_ge (e₂ + 1) x₂ with hlt | hge
    · exact (hdeep x₂ e₂ t₁ hlt hxt₂ hxV₂ h₂ hg₂).elim
    · omega
  have h₁' : gameF x₁ (x₁ - 1) = gameF t₁ t₁ := by
    have : e₁ = x₁ - 1 := by omega
    rwa [this] at h₁
  have h₂' : gameF x₂ (x₂ - 1) = gameF t₁ t₁ := by
    have : e₂ = x₂ - 1 := by omega
    rwa [this] at h₂
  have hxx : x₁ = x₂ := by
    rcases Nat.lt_or_ge x₁ x₂ with hlt | hge
    · exact (hpair x₁ x₂ t₁ (by omega) hlt hxt₂ h₁' h₂').elim
    · rcases Nat.lt_or_ge x₂ x₁ with hgt | hle
      · exact (hpair x₂ x₁ t₁ (by omega) hgt hxt₁ h₂' h₁').elim
      · omega
  have hmass := a1Gate_anchor_mass h₁ hex₁ hxV₁ hg₁
  refine ⟨rfl, hxx, by omega, hp₁, ?_⟩
  rw [hmass]
  omega

end ChompLean

#print axioms ChompLean.gameF_diagonal_ne_row_succ
#print axioms ChompLean.gated_deep_anchor_host_corridor
#print axioms ChompLean.corridor_hosts_pairwise_distinct
#print axioms ChompLean.gated_deep_anchor_corridor_bounds
#print axioms ChompLean.gated_anchor_suffix_packing
#print axioms ChompLean.gatedFutureDiagonalPin_iff_noDeep_and_noEcho
#print axioms ChompLean.gated_range_anchor_penultimate_of_noRightShift
#print axioms ChompLean.gated_range_anchor_unique_of_noRightShift
#print axioms ChompLean.gated_range_anchor_mass_one_of_noRightShift
#print axioms ChompLean.gatedNoDeepFuture_of_noRightShift
#print axioms ChompLean.penultimateEchoPairKill_of_noRightShift
#print axioms ChompLean.penultimateEchoPairKill_of_pin
#print axioms ChompLean.gated_range_anchor_unique_of_split
