import ChompLean.Statement

set_option autoImplicit false

namespace ChompLean

namespace Pos

@[ext]
theorem ext {x y : Pos}
    (hp : x.p = y.p) (hq : x.q = y.q) (hr : x.r = y.r) : x = y := by
  cases x
  cases y
  simp_all

end Pos

theorem isP_pos {x : Pos} (hx : IsP x) : 0 < x.p := by
  rw [IsP] at hx
  exact hx.left

theorem isP_no_move_to_P {x y : Pos} (hx : IsP x) (hxy : Move x y) :
    ¬ IsP y := by
  rw [IsP] at hx
  exact hx.right y hxy

theorem not_isP_has_move_to_P {x : Pos} (hpos : 0 < x.p) (hnp : ¬ IsP x) :
    ∃ y, Move x y ∧ IsP y := by
  classical
  by_cases hex : ∃ y, Move x y ∧ IsP y
  · exact hex
  · exfalso
    apply hnp
    rw [IsP]
    refine ⟨hpos, ?_⟩
    intro y hxy hy
    exact hex ⟨y, hxy, hy⟩

theorem isP_of_no_cut_replies
    (x : Pos) (hpos : 0 < x.p)
    (hfirst : ∀ a, 0 < a -> a < x.p -> ¬ IsP (Pos.firstCut x a))
    (hsecond : ∀ (a : Nat) (ha : a < x.q),
      ¬ IsP (Pos.secondCut x a (Nat.le_of_lt ha)))
    (hthird : ∀ (b : Nat) (hb : b < x.r),
      ¬ IsP (Pos.thirdCut x b (Nat.le_of_lt hb))) :
    IsP x := by
  rw [IsP]
  refine ⟨hpos, ?_⟩
  intro y hmove
  cases hmove with
  | first a ha0 ha =>
      exact hfirst a ha0 ha
  | second a ha =>
      exact hsecond a ha
  | third b hb =>
      exact hthird b hb

end ChompLean
