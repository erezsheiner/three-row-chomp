import RescueSeatCarry
import TopTwoSourceExpansion

set_option autoImplicit false

namespace ChompLean

/-!
Exact source-loss reductions for `TERMINAL-SUB-U-BACKFILL`.

The first theorem identifies the only possible failure of the proposed
`u <= V1(t)` law.  It is not merely another small MEX value: it is a value
which was present in yesterday's `V1` source, solely through yesterday's
strict row prefix, and which is absent from today's `V1` source.  Such a
failure also creates two consecutive rescues with strictly descending
seats.

The second theorem gives the analogous, sharper normal form for a current
`V2` value below the rescue seat.  The value is the positive MEX of the
common `TopTailCore`, and again it is an exact lost value from yesterday's
strict row prefix.

The last two lemmas isolate the finite boundary bookkeeping once backfill
membership is known.  For a MEX terminal value, membership two columns
earlier has only three possible witnesses.  In the `V2` case, the advertised
two-witness normal form needs exactly one further skew-witness exclusion.
-/

/-- Every proper off-diagonal entry is strictly below its row diagonal. -/
theorem recurrence_strict_row_diagonal_maximal
    (M : RecurrenceModel) {q b : Nat} (hbq : b < q) :
    M.f q b < M.f q q := by
  have hle : M.f q b <= M.f q q :=
    diagonalMaximal M (Nat.le_of_lt hbq)
  have hne : M.f q b ≠ M.f q q := by
    intro heq
    have hcols : b = q :=
      M.fixed_q_injective (Nat.le_of_lt hbq) (Nat.le_refl q) heq
    omega
  omega

/--
If today's `V1` falls strictly below yesterday's rescue seat, then the two
rows are consecutive rescues with descending seats.  More importantly, the
new value is an exact source loss: it occurred in yesterday's strict row
prefix, was covered by yesterday's seat MEX, and is absent from today's seat
source.
-/
theorem falling_v1_after_rescue_is_exact_prefix_loss
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {r u v : Nat}
    (hseat : M.f (r + 1) r = u)
    (hnext : M.f (r + 2) (r + 1) = v)
    (hrescue : u < M.f r r)
    (hfall : v < u) :
    RescueAfter M.f r /\
      RescueAfter M.f (r + 1) /\
      IsMex (B M.f (r + 1) r) u /\
      IsMex (B M.f (r + 2) (r + 1)) v /\
      C M.f (r + 1) r v /\
      Not (B M.f (r + 2) (r + 1) v) := by
  have hprevBranch :
      Not (r < r + 1 /\ M.f r r < r + 1) := by
    have hdiag := M.diagonal_gt r
    omega
  have hmexU0 := hrec.2 (q := r + 1) (r := r) (by omega) hprevBranch
  have hmexU : IsMex (B M.f (r + 1) r) u := by
    simpa [hseat] using hmexU0
  have hnextBranch :
      Not (r + 1 < r + 2 /\ M.f (r + 1) (r + 1) < r + 2) := by
    have hdiag := M.diagonal_gt (r + 1)
    omega
  have hmexV0 :=
    hrec.2 (q := r + 2) (r := r + 1) (by omega) hnextBranch
  have hmexV : IsMex (B M.f (r + 2) (r + 1)) v := by
    simpa [hnext] using hmexV0
  have hvPrev : B M.f (r + 1) r v :=
    hmexU.2.2 v hmexV.1 hfall
  have hvNowAbsent : Not (B M.f (r + 2) (r + 1) v) :=
    hmexV.2.1
  have hvPrevPrefix : C M.f (r + 1) r v := by
    rcases hvPrev with hR | hC
    · exfalso
      apply hvNowAbsent
      left
      rcases hR with ⟨a, ha, hvalue⟩
      refine ⟨a, by omega, ?_⟩
      have har : a <= r := by omega
      simpa [Nat.min_eq_left har,
        Nat.min_eq_left (by omega : a <= r + 1)] using hvalue
    · exact hC
  have hfirstRescue : RescueAfter M.f r := by
    simpa [RescueAfter, hseat] using hrescue
  have huBelowNextDiagonal : u < M.f (r + 1) (r + 1) := by
    rw [← hseat]
    exact recurrence_strict_row_diagonal_maximal M (by omega)
  have hsecondRescue : RescueAfter M.f (r + 1) := by
    have : v < M.f (r + 1) (r + 1) := by omega
    simpa [RescueAfter, Nat.add_assoc, hnext] using this
  exact ⟨hfirstRescue, hsecondRescue, hmexU, hmexV,
    hvPrevPrefix, hvNowAbsent⟩

/--
A current `V2` strictly below yesterday's rescue seat cannot be a carry.
It is the first positive hole of the common top-tail core.  The same value
was present in yesterday's `V1` source, necessarily through yesterday's
strict row prefix, and has disappeared from the current prefix.
-/
theorem sub_rescue_v2_is_new_core_hole_and_exact_prefix_loss
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {r u v : Nat}
    (hseat : M.f (r + 1) r = u)
    (hV2 : M.f (r + 2) r = v)
    (hvu : v < u) :
    IsMex (B M.f (r + 2) r) v /\
      IsMex (TopTailCore M.f r) v /\
      C M.f (r + 1) r v /\
      Not (B M.f (r + 2) r v) := by
  have hprevBranch :
      Not (r < r + 1 /\ M.f r r < r + 1) := by
    have hdiag := M.diagonal_gt r
    omega
  have hmexU0 := hrec.2 (q := r + 1) (r := r) (by omega) hprevBranch
  have hmexU : IsMex (B M.f (r + 1) r) u := by
    simpa [hseat] using hmexU0
  have hnotCarry :
      Not (r < r + 2 /\ M.f (r + 1) r < r + 2) := by
    rintro ⟨hr, hsmall⟩
    have heq := hrec.1 (q := r + 2) (r := r) hr hsmall
    have : v = u := by simpa [hV2, hseat] using heq
    omega
  have hmexV0 := hrec.2 (q := r + 2) (r := r) (by omega) hnotCarry
  have hmexV : IsMex (B M.f (r + 2) r) v := by
    simpa [hV2] using hmexV0
  have hvNowAbsent : Not (B M.f (r + 2) r v) := hmexV.2.1
  have hvPrev : B M.f (r + 1) r v :=
    hmexU.2.2 v hmexV.1 hvu
  have hvPrevPrefix : C M.f (r + 1) r v := by
    rcases hvPrev with hR | hC
    · exfalso
      apply hvNowAbsent
      left
      rcases hR with ⟨a, ha, hvalue⟩
      exact ⟨a, by omega, hvalue⟩
    · exact hC
  have hvCoreAbsent : Not (TopTailCore M.f r v) := by
    intro hcore
    apply hvNowAbsent
    exact (source_at_v2 (f := M.f) (r := r) (p := v)).2
      (Or.inl hcore)
  have hvCoreBelow : forall k, 0 < k -> k < v -> TopTailCore M.f r k := by
    intro k hkpos hkv
    have hkB : B M.f (r + 2) r k := hmexV.2.2 k hkpos hkv
    rcases (source_at_v2 (f := M.f) (r := r) (p := k)).1 hkB with
      hkCore | hku
    · exact hkCore
    · rw [hseat] at hku
      omega
  have hmexCore : IsMex (TopTailCore M.f r) v :=
    ⟨hmexV.1, hvCoreAbsent, hvCoreBelow⟩
  exact ⟨hmexV, hmexCore, hvPrevPrefix, hvNowAbsent⟩

/--
Pure boundary bookkeeping.  If a value absent from the `V2` source is
nevertheless already backfilled two columns earlier, its witness is forced
onto one of the last three preceding rows of that boundary column.
-/
theorem absent_v2_backfill_has_three_boundary_witnesses
    {f : Nat -> Nat -> Nat} {e v : Nat}
    (habs : Not (B f (e + 6) (e + 4) v))
    (hbackfill : B f (e + 6) (e + 2) v) :
    f (e + 3) (e + 2) = v \/
      f (e + 4) (e + 2) = v \/
      f (e + 5) (e + 2) = v := by
  rcases hbackfill with hR | hC
  · rcases hR with ⟨a, ha, hvalue⟩
    by_cases haold : a <= e + 2
    · exfalso
      apply habs
      left
      refine ⟨a, ha, ?_⟩
      simpa [Nat.min_eq_left haold,
        Nat.min_eq_left (by omega : a <= e + 4)] using hvalue
    · have ha3 : a = e + 3 \/ a = e + 4 \/ a = e + 5 := by
        omega
      rcases ha3 with rfl | rfl | rfl
      · exact Or.inl (by simpa using hvalue)
      · exact Or.inr (Or.inl (by simpa using hvalue))
      · exact Or.inr (Or.inr (by simpa using hvalue))
  · exfalso
    apply habs
    right
    rcases hC with ⟨b, hb, hvalue⟩
    exact ⟨b, by omega, hvalue⟩

/--
Consequently the sharp two-witness `V2` normal form needs only the exclusion
of the single skew witness in row `e+5`.  This is the exact additional local
premise left after backfill membership; no larger source invariant is hidden
in this packaging lemma.
-/
theorem absent_v2_backfill_two_witnesses_of_no_skew
    {f : Nat -> Nat -> Nat} {e v : Nat}
    (habs : Not (B f (e + 6) (e + 4) v))
    (hbackfill : B f (e + 6) (e + 2) v)
    (hnoSkew : f (e + 5) (e + 2) ≠ v) :
    f (e + 3) (e + 2) = v \/ f (e + 4) (e + 2) = v := by
  rcases absent_v2_backfill_has_three_boundary_witnesses
      habs hbackfill with h3 | h4 | h5
  · exact Or.inl h3
  · exact Or.inr h4
  · exact False.elim (hnoSkew h5)

end ChompLean
