import TopTwoSourceExpansion
import CeilingTopTwoMexAudit

set_option autoImplicit false

namespace ChompLean

/-!
R31: the MEX normal form of the terminal top-two strip.

The two generic lemmas first isolate the elementary set-theoretic fact being
used: adjoining a value strictly above a MEX is irrelevant, and after the
first hole is filled the next MEX gives the exact first-two-hole certificate.

The final theorem specializes this to row `t=e+6`.  Its common source is
`TopTailCore gameF (e+4)`, the previous `V1` is the high value `u`, and the
preceding diagonal is an even higher value.  Thus, when a terminal blocker
`z` is served at `V1` after `w=V2`, `w` and `z` are exactly the first two
positive holes of the common core.  The output in column `e+2` belongs to
that core outright.
-/

/-- Pointwise-equal sources have the same positive MEX predicate. -/
theorem isMex_congr
    {S T : Nat -> Prop} {m : Nat}
    (hST : forall p, S p <-> T p) :
    IsMex S m <-> IsMex T m := by
  constructor
  · intro hm
    exact ⟨hm.1, fun hTm => hm.2.1 ((hST m).2 hTm),
      fun k hkpos hkm => (hST k).1 (hm.2.2 k hkpos hkm)⟩
  · intro hm
    exact ⟨hm.1, fun hSm => hm.2.1 ((hST m).1 hSm),
      fun k hkpos hkm => (hST k).2 (hm.2.2 k hkpos hkm)⟩

/-- Adjoining a singleton strictly above the MEX does not affect the MEX. -/
theorem isMex_remove_strictly_high_singleton
    {S : Nat -> Prop} {u m : Nat}
    (hm : IsMex (fun p => S p \/ u = p) m)
    (hmu : m < u) :
    IsMex S m := by
  refine ⟨hm.1, ?_, ?_⟩
  · intro hSm
    exact hm.2.1 (Or.inl hSm)
  · intro k hkpos hkm
    rcases hm.2.2 k hkpos hkm with hSk | huk
    · exact hSk
    · omega

/--
Second-hole lemma.  If `w` is the first positive hole of `S`, and `z` is
the MEX after adjoining `w` and one value strictly above `z`, then the high
value can be deleted.  Below `z`, `w` is exactly the unique positive hole of
`S`; moreover `z` itself is the next hole of `S`.
-/
theorem second_mex_after_filling_remove_high
    {S : Nat -> Prop} {w z high : Nat}
    (hwMex : IsMex S w)
    (hwz : w < z)
    (hzMexHigh :
      IsMex (fun p => (S p \/ w = p) \/ high = p) z)
    (hzhigh : z < high) :
    IsMex (fun p => S p \/ w = p) z /\
      w < z /\ Not (S w) /\ Not (S z) /\
      forall v, 0 < v -> v < z -> (Not (S v) <-> v = w) := by
  have hzMex : IsMex (fun p => S p \/ w = p) z :=
    isMex_remove_strictly_high_singleton hzMexHigh hzhigh
  have hwHole : Not (S w) := hwMex.2.1
  have hzHole : Not (S z) := by
    intro hSz
    exact hzMex.2.1 (Or.inl hSz)
  refine ⟨hzMex, hwz, hwHole, hzHole, ?_⟩
  intro v hvpos hvz
  constructor
  · intro hvHole
    rcases hzMex.2.2 v hvpos hvz with hSv | hwv
    · exact False.elim (hvHole hSv)
    · exact hwv.symm
  · intro hvw
    subst v
    exact hwHole

/-- The output at column `e+2` (two columns before `V2`) is literally in the common top-tail
core: it already has a current-row host strictly before the `V2` column. -/
theorem gameF_l3_second_output_mem_top_tail_core (e : Nat) :
    TopTailCore gameF (e + 4) (gameF (e + 6) (e + 2)) := by
  right
  exact ⟨e + 2, by omega, rfl⟩

/--
Terminal-strip MEX normal form for the genuine game.

Put `w=V2(e+6)` and suppose `z=V1(e+6)`, with
`e+6 <= z`, `w<z<u`, where `u=V1(e+5)` and the preceding diagonal is above
`u`.  Then `w` is the first positive hole of the common `TopTailCore`, and
`z` is the next positive hole after filling `w`.  The earlier output
`q=f(e+6,e+2)` is in the core and hence cannot equal `w`.
-/
theorem gameF_l3_top_tail_core_first_two_mex
    {e u w z : Nat}
    (hseat : gameF (e + 5) (e + 4) = u)
    (hdiagAbove : u < gameF (e + 5) (e + 5))
    (hV2 : gameF (e + 6) (e + 4) = w)
    (hV1 : gameF (e + 6) (e + 5) = z)
    (htz : e + 6 <= z) (hwz : w < z) (hzu : z < u) :
    let K := TopTailCore gameF (e + 4)
    let q := gameF (e + 6) (e + 2)
    K q /\ q ≠ w /\
      IsMex K w /\
      IsMex (fun p => K p \/ w = p) z /\
      Not (K w) /\ Not (K z) /\
      forall v, 0 < v -> v < z -> (Not (K v) <-> v = w) := by
  dsimp only
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have htop := ceiling_top_two_mex_branches
    hrec gameRecurrenceModel.diagonal_gt (e + 4)
  have hmexV1 :
      IsMex (B gameF (e + 6) (e + 5)) z := by
    rw [← hV1]
    simpa [Nat.add_assoc] using htop.1
  have hmexV2 :
      IsMex (B gameF (e + 6) (e + 4)) w := by
    rcases htop.2.2 with hcarry | hmex
    · rw [hseat] at hcarry
      omega
    · rw [← hV2]
      simpa [Nat.add_assoc] using hmex.2
  have hmexV2Union :
      IsMex (fun p => TopTailCore gameF (e + 4) p \/ u = p) w := by
    apply (isMex_congr (m := w) (fun p => ?_)).1 hmexV2
    rw [source_at_v2]
    rw [hseat]
  have hwMexCore : IsMex (TopTailCore gameF (e + 4)) w :=
    isMex_remove_strictly_high_singleton hmexV2Union (by omega)
  have hmexV1Union :
      IsMex
        (fun p =>
          (TopTailCore gameF (e + 4) p \/ w = p) \/
            gameF (e + 5) (e + 5) = p) z := by
    apply (isMex_congr (m := z) (fun p => ?_)).1 hmexV1
    rw [source_at_v1]
    rw [hV2]
    constructor
    · rintro (hK | hd | hw)
      · exact Or.inl (Or.inl hK)
      · exact Or.inr (by simpa [Nat.add_assoc] using hd)
      · exact Or.inl (Or.inr hw)
    · rintro ((hK | hw) | hd)
      · exact Or.inl hK
      · exact Or.inr (Or.inr hw)
      · exact Or.inr (Or.inl (by simpa [Nat.add_assoc] using hd))
  have hsecond := second_mex_after_filling_remove_high
    hwMexCore hwz hmexV1Union (by omega)
  have hqCore := gameF_l3_second_output_mem_top_tail_core e
  have hqw : gameF (e + 6) (e + 2) ≠ w := by
    intro hqw
    apply hwMexCore.2.1
    simpa [hqw] using hqCore
  exact ⟨hqCore, hqw, hwMexCore, hsecond.1,
    hsecond.2.2.1, hsecond.2.2.2.1, hsecond.2.2.2.2⟩

end ChompLean
