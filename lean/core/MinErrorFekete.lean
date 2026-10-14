import ChompLean

set_option autoImplicit false

namespace ChompLean

/-!
Finite arithmetic core for the minimum-error Fekete bridge.

The hypothesis permits an additive defect `err n` when a smaller block of
length `n` is appended to a larger block.  Iterating a fixed block `q`
therefore pays the same error `err q` at every concatenation, rather than an
error depending on the growing total length.  If `err q / q -> 0`, this is
the key estimate behind existence of `lim u(n)/n`.
-/

/-- Iterating a fixed positive block under a one-sided minimum-error
subadditivity law. -/
theorem minErrorFekete_mul
    {u err : Nat -> Nat}
    (hadd : forall m n, 0 < n -> n <= m ->
      u (m + n) <= u m + u n + err n)
    {q k : Nat} (hq : 0 < q) (hk : 0 < k) :
    u (k * q) <= k * u q + (k - 1) * err q := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkzero : k = 0
      · subst k
        simp
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
        have hi := ih hkpos
        have hqk : q <= k * q := Nat.le_mul_of_pos_left q hkpos
        have hs := hadd (k * q) q hq hqk
        have herr : (k - 1) * err q + err q = k * err q := by
          have hkone : 1 <= k := by omega
          calc
            (k - 1) * err q + err q =
                (k - 1) * err q + 1 * err q := by simp
            _ = ((k - 1) + 1) * err q := by rw [Nat.add_mul]
            _ = k * err q := by rw [Nat.sub_add_cancel hkone]
        calc
          u ((Nat.succ k) * q) = u (k * q + q) := by simp [Nat.succ_mul]
          _ <= u (k * q) + u q + err q := hs
          _ <= (k * u q + (k - 1) * err q) + u q + err q := by omega
          _ = (Nat.succ k) * u q + k * err q := by
            rw [Nat.succ_mul, ← herr]
            omega
          _ = (Nat.succ k) * u q + (Nat.succ k - 1) * err q := by simp

/-- Fixed-block estimate with a positive remainder smaller than the block. -/
theorem minErrorFekete_mul_add
    {u err : Nat -> Nat}
    (hadd : forall m n, 0 < n -> n <= m ->
      u (m + n) <= u m + u n + err n)
    {q k r : Nat} (hq : 0 < q) (hk : 0 < k)
    (hrpos : 0 < r) (hrq : r < q) :
    u (k * q + r) <=
      k * u q + (k - 1) * err q + u r + err r := by
  have hmul := minErrorFekete_mul hadd hq hk
  have hqk : q <= k * q := Nat.le_mul_of_pos_left q hk
  have hrk : r <= k * q := Nat.le_trans (Nat.le_of_lt hrq) hqk
  have hs := hadd (k * q) r hrpos hrk
  omega

end ChompLean
