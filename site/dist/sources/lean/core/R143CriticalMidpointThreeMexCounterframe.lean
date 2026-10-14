import R140CriticalLag3HostStripCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
R143: direct three-cell CM-L3 source audit.

The first section opens the literal Brouwer source at an arbitrary column
and at its successor.  It exposes the unbounded component: the whole strict
vertical tail is replaced when the column advances.

The second section gives a parametric critical source counterframe.  Its
three consecutive exact MEX values are `v+1,v+2,v+3`; the bad diagonal value
`v` is present in all three sources, the row values are distinct, and the
critical count/record coordinates are exact.  Hence MEX, RowInj and the
record pin alone do not imply CM-L3.
-/

def R143DiagBelow (f : Nat -> Nat -> Nat) (c p : Nat) : Prop :=
  exists i, i < c /\ f i i = p

def R143VerticalTail (f : Nat -> Nat -> Nat)
    (q c p : Nat) : Prop :=
  exists i, c <= i /\ i < q /\ f i c = p

def R143RowPrefix (f : Nat -> Nat -> Nat)
    (q c p : Nat) : Prop :=
  exists e, e < c /\ f q e = p

/-- Exact three-channel expansion of Sheiner's/Brouwer's source predicate. -/
theorem r143_source_split
    (f : Nat -> Nat -> Nat) (q c p : Nat) (hcq : c <= q) :
    B f q c p <->
      R143DiagBelow f c p \/
      R143VerticalTail f q c p \/
      R143RowPrefix f q c p := by
  constructor
  · intro h
    rcases h with hR | hC
    · rcases hR with ⟨i, hiq, hvalue⟩
      by_cases hic : i < c
      · left
        refine ⟨i, hic, ?_⟩
        have hmin : min i c = i := Nat.min_eq_left (Nat.le_of_lt hic)
        simpa [hmin] using hvalue
      · right; left
        refine ⟨i, by omega, hiq, ?_⟩
        have hmin : min i c = c := Nat.min_eq_right (by omega)
        simpa [hmin] using hvalue
    · right; right
      exact hC
  · intro h
    rcases h with hD | hT | hP
    · left
      rcases hD with ⟨i, hic, hvalue⟩
      refine ⟨i, by omega, ?_⟩
      have hmin : min i c = i := Nat.min_eq_left (Nat.le_of_lt hic)
      simpa [hmin] using hvalue
    · left
      rcases hT with ⟨i, hci, hiq, hvalue⟩
      refine ⟨i, hiq, ?_⟩
      have hmin : min i c = c := Nat.min_eq_right hci
      simpa [hmin] using hvalue
    · right
      exact hP

/-- Exact successor-column expansion.  The common diagonal and row pieces
are explicit; the strict vertical tail at `c+1` is a new, otherwise
unconstrained predicate. -/
theorem r143_successor_source_split
    (f : Nat -> Nat -> Nat) (q c p : Nat) (hcq : c + 1 <= q) :
    B f q (c + 1) p <->
      R143DiagBelow f c p \/
      f c c = p \/
      R143VerticalTail f q (c + 1) p \/
      R143RowPrefix f q c p \/
      f q c = p := by
  rw [r143_source_split f q (c + 1) p hcq]
  constructor
  · intro h
    rcases h with hD | hT | hP
    · rcases hD with ⟨i, hic, hvalue⟩
      by_cases hi : i < c
      · exact Or.inl ⟨i, hi, hvalue⟩
      · exact Or.inr (Or.inl (by
          have : i = c := by omega
          simpa [this] using hvalue))
    · exact Or.inr (Or.inr (Or.inl hT))
    · rcases hP with ⟨e, hec, hvalue⟩
      by_cases he : e < c
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, hvalue⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by
          have : e = c := by omega
          simpa [this] using hvalue))))
  · intro h
    rcases h with hD | hdiag | hT | hP | hrow
    · left
      rcases hD with ⟨i, hic, hvalue⟩
      exact ⟨i, by omega, hvalue⟩
    · left
      exact ⟨c, by omega, hdiag⟩
    · right; left
      exact hT
    · right; right
      rcases hP with ⟨e, hec, hvalue⟩
      exact ⟨e, by omega, hvalue⟩
    · right; right
      exact ⟨c, by omega, hrow⟩

/-! ## Critical coordinates -/

def r143BCount (m : Nat) : Nat := 2 * m + 1
def r143ACount (m : Nat) : Nat := 4 * m + 5
def r143V (m : Nat) : Nat := 10 * m + 15
def r143T (m : Nat) : Nat := 6 * m + 9
def r143G (m : Nat) : Nat := 7 * m + 10
def r143Q (m : Nat) : Nat := r143V m - 3
def r143C0 (m : Nat) : Nat := r143G m - 2
def r143C1 (m : Nat) : Nat := r143G m - 1
def r143C2 (m : Nat) : Nat := r143G m

theorem r143_critical_coordinates (m : Nat) (hm : 2 <= m) :
    r143V m = 2 * r143ACount m + r143BCount m + 4 /\
      r143T m = r143V m - r143ACount m - 1 /\
      2 * r143G m = r143V m + r143ACount m /\
      r143T m <= r143C0 m /\
      r143C0 m < r143C1 m /\
      r143C1 m < r143C2 m /\
      r143C2 m < r143Q m /\
      r143ACount m + 2 <= 3 * r143BCount m /\
      2 * r143BCount m + 3 <= r143ACount m := by
  simp [r143V, r143ACount, r143BCount, r143T, r143G,
    r143Q, r143C0, r143C1, r143C2]
  omega

/-! ## Record-pin trace -/

/-- A finite diagonal trace with `RM(t-1)=v-1` and `d(t)=v`.
The early values are `1,...,t-1`. -/
def R143DiagAt (m i p : Nat) : Prop :=
  (i < r143T m - 1 /\ p = i + 1) \/
  (i = r143T m - 1 /\ p = r143V m - 1) \/
  (i = r143T m /\ p = r143V m)

theorem r143_diag_trace_functional
    {m i p p' : Nat} (_hm : 2 <= m)
    (hp : R143DiagAt m i p) (hp' : R143DiagAt m i p') :
    p = p' := by
  rcases hp with hp | hp | hp <;>
    rcases hp' with hp' | hp' | hp' <;>
      simp [r143T, r143V] at * <;> omega

theorem r143_diag_trace_injective
    {m i j p : Nat} (_hm : 2 <= m)
    (hi : R143DiagAt m i p) (hj : R143DiagAt m j p) :
    i = j := by
  rcases hi with hi | hi | hi <;>
    rcases hj with hj | hj | hj <;>
      simp [r143T, r143V] at * <;> omega

theorem r143_diag_trace_gt_owner
    {m i p : Nat} (_hm : 2 <= m)
    (hi : R143DiagAt m i p) :
    i < p := by
  rcases hi with hi | hi | hi <;>
    simp [r143T, r143V] at * <;> omega

theorem r143_record_pin (m : Nat) (_hm : 2 <= m) :
    R143DiagAt m (r143T m - 1) (r143V m - 1) /\
      R143DiagAt m (r143T m) (r143V m) /\
      (forall i p, R143DiagAt m i p -> i < r143T m -> p <= r143V m - 1) := by
  constructor
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  constructor
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro i p hip hit
    rcases hip with hip | hip | hip <;>
      simp [r143T, r143V] at * <;> omega

/-! ## Three exact MEX sources -/

def R143PastLow (m p : Nat) : Prop :=
  (0 < p /\ p <= r143T m - 1) \/
  p = r143V m - 1 \/
  p = r143V m

def R143BlockerPrefix (m p : Nat) : Prop :=
  r143T m <= p /\ p <= r143V m - 2

def R143S0 (Extra : Nat -> Prop) (m p : Nat) : Prop :=
  R143PastLow m p \/ R143BlockerPrefix m p \/ Extra p

def R143S1 (Extra : Nat -> Prop) (m p : Nat) : Prop :=
  R143S0 Extra m p \/ p = r143V m + 1

def R143S2 (Extra : Nat -> Prop) (m p : Nat) : Prop :=
  R143S1 Extra m p \/ p = r143V m + 2

/-- The record trace plus the blocker row prefix covers exactly `[1,v]`
at the low-value level. -/
theorem r143_past_blocker_cover
    (m p : Nat) (_hm : 2 <= m) :
    (R143PastLow m p \/ R143BlockerPrefix m p) <->
      (0 < p /\ p <= r143V m) := by
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h | h <;>
        simp [r143T, r143V] at * <;> omega
    · simp [R143BlockerPrefix, r143T, r143V] at *
      omega
  · intro h
    by_cases hp : p <= r143T m - 1
    · left; left
      exact ⟨h.1, hp⟩
    · by_cases hp2 : p <= r143V m - 2
      · right
        exact ⟨by omega, hp2⟩
      · left
        by_cases hpv : p = r143V m - 1
        · exact Or.inr (Or.inl hpv)
        · exact Or.inr (Or.inr (by omega))

/-- Canonical three-cell packet.  `Extra` represents arbitrary finite
high-valued tail fillers; it is required to avoid the relevant low band. -/
theorem r143_three_mex_packet
    (Extra : Nat -> Prop) (m : Nat) (hm : 2 <= m)
    (hExtra : forall p, Extra p -> r143V m + 3 < p) :
    IsMex (R143S0 Extra m) (r143V m + 1) /\
      IsMex (R143S1 Extra m) (r143V m + 2) /\
      IsMex (R143S2 Extra m) (r143V m + 3) /\
      R143S0 Extra m (r143V m) /\
      R143S1 Extra m (r143V m) /\
      R143S2 Extra m (r143V m) := by
  have hcover : forall p, 0 < p -> p <= r143V m ->
      R143S0 Extra m p := by
    intro p hp hle
    rcases (r143_past_blocker_cover m p hm).2 ⟨hp, hle⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h0 : IsMex (R143S0 Extra m) (r143V m + 1) := by
    refine ⟨by omega, ?_, ?_⟩
    · intro h
      rcases h with h | h | h
      · rcases h with h | h | h <;>
          simp [r143T, r143V] at * <;> omega
      · simp [R143BlockerPrefix, r143T, r143V] at h
      · have := hExtra _ h
        omega
    · intro p hp hlt
      exact hcover p hp (by omega)
  have h1 : IsMex (R143S1 Extra m) (r143V m + 2) := by
    refine ⟨by omega, ?_, ?_⟩
    · rintro (h | h)
      · have hnot := h0.2.1
        by_cases hp : r143V m + 2 = r143V m + 1
        · omega
        · rcases h with h | h | h
          · rcases h with h | h | h <;>
              simp [r143T, r143V] at * <;> omega
          · simp [R143BlockerPrefix, r143T, r143V] at h
          · have := hExtra _ h
            omega
      · omega
    · intro p hp hlt
      by_cases hpv : p <= r143V m
      · exact Or.inl (hcover p hp hpv)
      · right
        omega
  have h2 : IsMex (R143S2 Extra m) (r143V m + 3) := by
    refine ⟨by omega, ?_, ?_⟩
    · rintro (h | h)
      · rcases h with h | h
        · rcases h with h | h | h
          · rcases h with h | h | h <;>
              simp [r143T, r143V] at * <;> omega
          · simp [R143BlockerPrefix, r143T, r143V] at h
          · have := hExtra _ h
            omega
        · omega
      · omega
    · intro p hp hlt
      by_cases hpv : p <= r143V m
      · exact Or.inl (Or.inl (hcover p hp hpv))
      · by_cases hp1 : p = r143V m + 1
        · exact Or.inl (Or.inr hp1)
        · exact Or.inr (by omega)
  refine ⟨h0, h1, h2, ?_, ?_, ?_⟩
  · exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))

theorem r143_three_source_transitions
    (Extra : Nat -> Prop) (m p : Nat) :
    (R143S1 Extra m p <-> R143S0 Extra m p \/ p = r143V m + 1) /\
      (R143S2 Extra m p <-> R143S1 Extra m p \/ p = r143V m + 2) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The three counterframe outputs satisfy local RowInj and all lie strictly
above `v`; in particular they violate the required three-cell cap. -/
theorem r143_three_outputs_rowInj_and_no_cap (m : Nat) :
    (r143V m + 1 ≠ r143V m + 2) /\
      (r143V m + 1 ≠ r143V m + 3) /\
      (r143V m + 2 ≠ r143V m + 3) /\
      r143V m < r143V m + 1 /\
      r143V m < r143V m + 2 /\
      r143V m < r143V m + 3 /\
      Not ((r143V m + 1 <= r143V m) \/
        (r143V m + 2 <= r143V m) \/
        (r143V m + 3 <= r143V m)) := by
  simp [r143V]

/-- The exact positive reduction left after opening the three sources:
three lower bounds plus a single three-cell cap force CM-L3. -/
theorem r143_three_lower_bounds_and_cap_force_hit
    {v x0 x1 x2 : Nat}
    (h0 : v <= x0) (h1 : v <= x1) (h2 : v <= x2)
    (hcap : x0 <= v \/ x1 <= v \/ x2 <= v) :
    x0 = v \/ x1 = v \/ x2 = v := by
  rcases hcap with hcap | hcap | hcap <;> omega

#print axioms r143_source_split
#print axioms r143_successor_source_split
#print axioms r143_critical_coordinates
#print axioms r143_diag_trace_injective
#print axioms r143_record_pin
#print axioms r143_three_mex_packet
#print axioms r143_three_outputs_rowInj_and_no_cap
#print axioms r143_three_lower_bounds_and_cap_force_hit

end ChompLean
