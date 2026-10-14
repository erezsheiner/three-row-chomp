import XOBUQAbsoluteRangeLedger

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean
namespace OBUQ

/-!
# Integer square-root adapter for the seeded absolute-hole bound

Work-ID: `X-OBUQ-GLOBAL-LEAN-AND-CONVOY-001`
Run-ID: `XOGC-20260813-SQRT-ROOT`

Lean 4.29's Std layer used by the project has no square-root function.  The
strong kernel-level substitute is a universal square-root certificate: every
natural `R` with `R^2 <= 2*N` is at most the hole count plus the explicit head
constant.  A later Mathlib adapter may instantiate `R` with `Nat.sqrt (2*N)`.
-/

theorem doubledHoleBound_strict_square {N H s0 : Nat}
    (hbound :
      2 * N ≤
        2 * H + 2 * (H + 1) * s0 + H * (H + 1)) :
    2 * N < (H + s0 + 2) * (H + s0 + 2) := by
  have hcomm : s0 * H = H * s0 := Nat.mul_comm s0 H
  have htwoH : H * 2 = 2 * H := Nat.mul_comm H 2
  have htwoS : s0 * 2 = 2 * s0 := Nat.mul_comm s0 2
  have halgebra :
      (2 * H + 2 * (H + 1) * s0 + H * (H + 1)) +
          (s0 * s0 + H + 2 * s0 + 4) =
        (H + s0 + 2) * (H + s0 + 2) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one,
      Nat.mul_assoc]
    omega
  have hpositive : 0 < s0 * s0 + H + 2 * s0 + 4 := by omega
  omega

theorem doubledHoleBound_sqrt_certificate {N H s0 R : Nat}
    (hbound :
      2 * N ≤
        2 * H + 2 * (H + 1) * s0 + H * (H + 1))
    (hroot : R * R ≤ 2 * N) :
    R < H + s0 + 2 := by
  have hstrict := doubledHoleBound_strict_square hbound
  by_cases hlt : R < H + s0 + 2
  · exact hlt
  · have hle : H + s0 + 2 ≤ R := Nat.le_of_not_gt hlt
    have hsquare :
        (H + s0 + 2) * (H + s0 + 2) ≤ R * R :=
      Nat.mul_le_mul hle hle
    omega

theorem doubledHoleBound_sqrt_sub_certificate {N H s0 R : Nat}
    (hbound :
      2 * N ≤
        2 * H + 2 * (H + 1) * s0 + H * (H + 1))
    (hroot : R * R ≤ 2 * N) :
    R - (s0 + 1) ≤ H := by
  have hlt := doubledHoleBound_sqrt_certificate hbound hroot
  omega

theorem autonomousOrbit_absoluteHole_strict_square {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup) (N : Nat) :
    2 * N <
      (absoluteHoleCount Q0 N + Q0.diagonal.length + 2) *
        (absoluteHoleCount Q0 N + Q0.diagonal.length + 2) := by
  apply doubledHoleBound_strict_square
  exact autonomousOrbit_absoluteHole_doubled_bound hA hN N

theorem autonomousOrbit_absoluteHole_sqrt_certificate {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup)
    (N R : Nat) (hroot : R * R ≤ 2 * N) :
    R - (Q0.diagonal.length + 1) ≤ absoluteHoleCount Q0 N := by
  apply doubledHoleBound_sqrt_sub_certificate
  · exact autonomousOrbit_absoluteHole_doubled_bound hA hN N
  · exact hroot

#print axioms doubledHoleBound_strict_square
#print axioms doubledHoleBound_sqrt_certificate
#print axioms doubledHoleBound_sqrt_sub_certificate
#print axioms autonomousOrbit_absoluteHole_strict_square
#print axioms autonomousOrbit_absoluteHole_sqrt_certificate

end OBUQ
end ChompLean
