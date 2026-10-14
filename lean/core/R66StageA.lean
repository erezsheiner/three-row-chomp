import SelectorColHistCausalDepth

/-!
# R66 Stage A — ceiling chain toward DiagDoubleSlack (`d(a) ≤ 2a-2`, `a≥9`)

Formalization of `_v4r3_diagdoubleslack_PROOF.md`, staged.  Priority per the R106/R120
frontier audit: this ceiling freezes the RM2 frontier — proving `T1/J1/J2/DiagDoubleSlack`
banks the paper deletions R97 (LOW-A upper packets) and R101 (LOW-B `u ≤ 2k-6`, retiring the
dead R89/R93/R98 gap-four branch).

**RM2 not proved.** This initial stage proves `d(2)=4` and `d(3)=6`,
with `d(0)=1` and `d(1)=3` in its imports. It does not by itself prove
the full table through row nine. The later `R201DiagDoubleSlackCeilingChain`
contains the completed ceiling chain and `gameF_diagDoubleSlack`.
The two local values are pinned from their explicit MEX sources via
`gameF_value_of_source_mex`; the diagonal cell `(q,q)` is always non-carry (`q<q` is false).

## Historical roadmap at the initial R66 stage

The status words below describe that initial stage, not the current package.
See `R201DiagDoubleSlackCeilingChain` for the later completed ceiling proof.
* **T1** `f(r,c) ≤ r+c` for `3≤c<r` (sharpens B22 `high_cell_output_source_capacity` by 1).
  Induction on `s=r+c`.  ⚠ Needs the *tight* `d(c) ≤ 2c` (`c≥2`) which is **not banked** and is
  entangled with the ceiling (`d(q)=2q+1 ⟺ f(q,q-1)=2q`), so T1's `x=r-1` diagonal case is not a
  clean standalone — the tight diagonal bound must be proved alongside/before T1.
* **ES/OS** saturation forcing (`d=2a ⟹ f(a,a-1)=2a-1`; `d=2a-1 ⟹` one of three Ceil cells).
* **J1** `no f(r,c)=r+c, 3≤c<r, r+c≥11`; strong induction, base FB1 = Ceil1 inventory
  `{(4,3),(5,4),(6,4)}` (needs the small `f` table).  Corollary B': `d(a) ≤ 2a-1`, `a≥6`.
* **J2** `no f(r,c)=r+c-1, 6≤c<r, r+c≥17`; strong induction, base FB2 `{(7,6),(8,6),(8,7)}`.
* **Main** `d(a) ≤ 2a-2`, `a≥9`, via B'/OS/J1/J2 + `d(9)=16`.
Banked ingredients: rails `gameF_col0`, `gameF_col1_rail`, `gameF_col2_rail`, `gameF_one_one`,
`gameF_two_one`; B22 `high_cell_output_source_capacity`; B8-loose `recurrence_diagonal_source_capacity`.
-/

set_option autoImplicit false

namespace ChompLean

/-- `d(2) = 4`.  Source `B(2,2) = {d(0),d(1)} ∪ {f(2,0),f(2,1)} = {1,3} ∪ {3,2} = {1,2,3}`. -/
theorem gameF_diag_two : gameF 2 2 = 4 := by
  apply gameF_value_of_source_mex (q := 2) (r := 2) (m := 4)
  · omega
  · rintro ⟨h, _⟩; omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 := by omega
      rcases hcase with rfl | rfl
      · rw [show min 0 2 = 0 from rfl, gameF_zero_zero] at hval; omega
      · rw [show min 1 2 = 1 from rfl, gameF_one_one] at hval; omega
    · have hcase : b = 0 ∨ b = 1 := by omega
      rcases hcase with rfl | rfl
      · rw [gameF_col0 2] at hval; omega
      · rw [gameF_two_one] at hval; omega
  · intro k hk0 hk4
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by rw [show min 0 2 = 0 from rfl]; exact gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_two_one⟩
    · exact Or.inl ⟨1, by omega, by rw [show min 1 2 = 1 from rfl]; exact gameF_one_one⟩

/-- `d(3) = 6`.  Source `B(3,3) = {d0,d1,d2} ∪ {f(3,0),f(3,1),f(3,2)} = {1,3,4} ∪ {4,2,5}`. -/
theorem gameF_diag_three : gameF 3 3 = 6 := by
  apply gameF_value_of_source_mex (q := 3) (r := 3) (m := 6)
  · omega
  · rintro ⟨h, _⟩; omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [show min 0 3 = 0 from rfl, gameF_zero_zero] at hval; omega
      · rw [show min 1 3 = 1 from rfl, gameF_one_one] at hval; omega
      · rw [show min 2 3 = 2 from rfl, gameF_diag_two] at hval; omega
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [gameF_col0 3] at hval; omega
      · rw [gameF_col1_rail (q := 3) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 3) (by omega)] at hval; omega
  · intro k hk0 hk6
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by rw [show min 0 3 = 0 from rfl]; exact gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 3) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by rw [show min 1 3 = 1 from rfl]; exact gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by rw [show min 2 3 = 2 from rfl]; exact gameF_diag_two⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 3) (by omega)⟩

end ChompLean

#print axioms ChompLean.gameF_diag_two
#print axioms ChompLean.gameF_diag_three
