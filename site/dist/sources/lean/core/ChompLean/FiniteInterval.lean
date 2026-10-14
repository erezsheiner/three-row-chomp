import Std

set_option autoImplicit false

namespace ChompLean

def swapNat (a b x : Nat) : Nat :=
  if x = a then b else if x = b then a else x

theorem swapNat_left (a b : Nat) : swapNat a b a = b := by
  simp [swapNat]

theorem swapNat_right (a b : Nat) : swapNat a b b = a := by
  by_cases h : b = a
  · simp [swapNat, h]
  · simp [swapNat, h]

theorem swapNat_involutive (a b x : Nat) :
    swapNat a b (swapNat a b x) = x := by
  by_cases hxa : x = a
  · subst x
    rw [swapNat_left]
    exact swapNat_right a b
  · by_cases hxb : x = b
    · subst x
      rw [swapNat_right]
      exact swapNat_left a b
    · have hx : swapNat a b x = x := by
        simp [swapNat, hxa, hxb]
      rw [hx]
      exact hx

theorem swapNat_injective (a b : Nat) :
    Function.Injective (swapNat a b) := by
  intro x y hxy
  have h := congrArg (swapNat a b) hxy
  simpa [swapNat_involutive] using h

theorem swapNat_maps_interval {q p a b x : Nat}
    (ha : q < a ∧ a < p) (hb : q < b ∧ b < p)
    (hx : q < x ∧ x < p) :
    q < swapNat a b x ∧ swapNat a b x < p := by
  by_cases hxa : x = a
  · simp [swapNat, hxa, hb]
  · by_cases hxb : x = b
    · have hba : ¬ b = a := by
        intro h
        exact hxa (hxb.trans h)
      simp [swapNat, hxb, hba, ha]
    · simp [swapNat, hxa, hxb, hx]

theorem interval_inj_surj
    {q p : Nat} (hqp : q < p) (g : Nat -> Nat)
    (hmap : ∀ x, q < x -> x < p -> q < g x ∧ g x < p)
    (hinj :
      ∀ x y, q < x -> x < p -> q < y -> y < p -> g x = g y -> x = y) :
    ∀ k, q < k -> k < p -> ∃ x, q < x ∧ x < p ∧ g x = k := by
  let P : Nat -> Prop :=
    fun d =>
      ∀ q p, p - q = d -> q < p -> ∀ g : Nat -> Nat,
        (∀ x, q < x -> x < p -> q < g x ∧ g x < p) ->
        (∀ x y, q < x -> x < p -> q < y -> y < p -> g x = g y -> x = y) ->
        ∀ k, q < k -> k < p -> ∃ x, q < x ∧ x < p ∧ g x = k
  have hP : ∀ d, P d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro q p hdiff hqp g hmap hinj k hqk hkp
        by_cases hsmall : p <= q + 1
        · omega
        let last := p - 1
        have hlast_gt : q < last := by
          dsimp [last]
          omega
        have hlast_lt : last < p := by
          dsimp [last]
          omega
        let a := g last
        have ha_int : q < a ∧ a < p := hmap last hlast_gt hlast_lt
        let h : Nat -> Nat := fun x => swapNat a last (g x)
        have h_last : h last = last := by
          dsimp [h, a]
          simp [swapNat_left]
        have hmap_h_small :
            ∀ x, q < x -> x < last -> q < h x ∧ h x < last := by
          intro x hqx hxl
          have hxp : x < p := by omega
          have hx_int : q < h x ∧ h x < p := by
            dsimp [h]
            exact swapNat_maps_interval ha_int ⟨hlast_gt, hlast_lt⟩ (hmap x hqx hxp)
          have h_ne_last : h x ≠ last := by
            intro hxlast
            have hx_eq_last : x = last := by
              apply hinj x last hqx hxp hlast_gt hlast_lt
              have heq : h x = h last := by
                rw [hxlast, h_last]
              have hs := congrArg (swapNat a last) heq
              simpa [h, swapNat_involutive] using hs
            omega
          constructor
          · exact hx_int.1
          · omega
        have hinj_h_small :
            ∀ x y, q < x -> x < last -> q < y -> y < last -> h x = h y -> x = y := by
          intro x y hqx hxl hqy hyl hxy
          apply hinj x y hqx (by omega) hqy (by omega)
          have hs := congrArg (swapNat a last) hxy
          simpa [h, swapNat_involutive] using hs
        have hsurj_h :
            ∀ y, q < y -> y < p -> ∃ x, q < x ∧ x < p ∧ h x = y := by
          intro y hqy hyp
          by_cases hylast : y = last
          · refine ⟨last, hlast_gt, hlast_lt, ?_⟩
            simpa [hylast] using h_last
          · have hyltlast : y < last := by omega
            have hdiff_small : last - q < d := by
              dsimp [last] at *
              omega
            rcases ih (last - q) hdiff_small q last rfl hlast_gt h hmap_h_small
                hinj_h_small y hqy hyltlast with ⟨x, hqx, hxlast, hhxy⟩
            exact ⟨x, hqx, by omega, hhxy⟩
        let y := swapNat a last k
        have hy_int : q < y ∧ y < p := by
          dsimp [y]
          exact swapNat_maps_interval ha_int ⟨hlast_gt, hlast_lt⟩ ⟨hqk, hkp⟩
        rcases hsurj_h y hy_int.1 hy_int.2 with ⟨x, hqx, hxp, hhxy⟩
        refine ⟨x, hqx, hxp, ?_⟩
        have hs := congrArg (swapNat a last) hhxy
        simpa [h, y, swapNat_involutive] using hs
  exact hP (p - q) q p rfl hqp g hmap hinj

theorem List.mem_le_sum {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x <= xs.sum := by
  induction xs with
  | nil =>
      cases h
  | cons a xs ih =>
      rw [List.mem_cons] at h
      cases h with
      | inl hx =>
          subst x
          simp [List.sum]
      | inr hxs =>
          have hx_le : x <= xs.sum := ih hxs
          have hx_le' : x <= List.foldr (fun x y => x + y) 0 xs := by
            simpa [List.sum] using hx_le
          simp [List.sum]
          omega

theorem exists_nat_not_mem_list_ge (q : Nat) (xs : List Nat) :
    ∃ p, q <= p ∧ p ∉ xs := by
  refine ⟨q + xs.sum + 1, by omega, ?_⟩
  intro hmem
  have hle := List.mem_le_sum hmem
  omega

end ChompLean
