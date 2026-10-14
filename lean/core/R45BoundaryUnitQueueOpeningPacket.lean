import R44BoundaryCorridorFirstTransitionReduction
import R30FreezeServiceOrder

set_option autoImplicit false

namespace ChompLean

/-!
R45: opening packet forced by the exact `BoundaryCorridorUnitQueue` atom.

Let `u=s+1` and `q=gameF (u+1) u`.  The R44 queue gives `u<q<d(u+1)`;
the earlier boundary source normal form shows that `q` was already hosted
strictly before column `s` on row `u`.

Opening completeness now has only two sharpened outcomes.

* If `q` is diagonal-owned, its owner is at least `u+2`.  The two prehosts
  on rows `u,u+1` create two concrete no-repeat column deserts up to the
  future owner.
* If `q` is a row start, its freeze is either the boundary `r=u,q=u+1`, or
  lies strictly after `u`.  In the latter case the two preview hosts plus
  all active hosts fit into `[0,r)` with the original constant column `s`
  removed, giving `q+2<=2*r`.

This replaces the queue atom by a smaller diagonal packet or a smaller
row-start packet, without RM2 or UnitDip.
-/

def BoundaryUnitQueueFutureDiagonalPacket (s : Nat) : Prop :=
  let u := s + 1
  let q := gameF (u + 1) u
  exists a b,
    u + 2 <= a /\ a < q /\ gameF a a = q /\
    b < s /\ gameF u b = q /\ gameF (u + 1) u = q /\
    (forall t, u < t -> t < a -> gameF t b ≠ q) /\
    (forall t, u + 1 < t -> t < a -> gameF t u ≠ q)

def BoundaryUnitQueueRowstartPacket (s : Nat) : Prop :=
  let u := s + 1
  let q := gameF (u + 1) u
  exists b r,
    b < s /\ gameF u b = q /\ r < q /\ gameF q r = q /\
    ((q = u + 1 /\ r = u) \/
     (u + 1 < q /\ u < r /\ q + 2 <= r + r))

private theorem r45_nodup_map_of_injective_on
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) (xs : List alpha)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs -> f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- Two preview rows plus every active row, with the original boundary
constant column removed. -/
theorem gameF_boundary_two_preview_rowstart_capacity
    {s u q b r : Nat}
    (hu : u = s + 1)
    (hb : b < s) (huR : u < r) (hrq : r < q)
    (hpreview0 : gameF u b = q)
    (hpreview1 : gameF (u + 1) u = q)
    (hstart : gameF q r = q)
    (hboundary : gameF u s = u) :
    q + 2 <= r + r := by
  classical
  let xs := u :: (u + 1) :: List.range' (r + 1) (q - r - 1)
  have hclass : forall x, x ∈ xs ->
      x = u \/ x = u + 1 \/ (r < x /\ x < q) := by
    intro x hx
    change x ∈ u :: (u + 1) :: List.range' (r + 1) (q - r - 1) at hx
    rcases List.mem_cons.mp hx with h0 | hrest
    · exact Or.inl h0
    · rcases List.mem_cons.mp hrest with h1 | hrange
      · exact Or.inr (Or.inl h1)
      · right
        right
        have hrange := List.mem_range'_1.mp hrange
        omega
  have hxs : xs.Nodup := by
    change (u :: (u + 1) :: List.range' (r + 1) (q - r - 1)).Nodup
    rw [List.nodup_cons, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hEq | hrange
      · omega
      · have hrange := List.mem_range'_1.mp hrange
        omega
    · constructor
      · intro hrange
        have hrange := List.mem_range'_1.mp hrange
        omega
      · exact List.nodup_range' 1
  have hex : forall x, x ∈ xs ->
      exists c, c < r /\ c < x /\ gameF x c = q := by
    intro x hx
    rcases hclass x hx with rfl | rfl | hxActive
    · exact ⟨b, by omega, by omega, hpreview0⟩
    · exact ⟨u, huR, by omega, hpreview1⟩
    · rcases rowStartPropagation gameRecurrenceModel hstart hrq
        hxActive.1 hxActive.2 with ⟨c, hcr, hhost⟩
      exact ⟨c, hcr, by omega, hhost⟩
  have hupper : forall x, x ∈ xs -> x < q := by
    intro x hx
    rcases hclass x hx with rfl | rfl | hxActive
    · omega
    · omega
    · exact hxActive.2
  let host : Nat -> Nat := fun x =>
    if hx : x ∈ xs then Classical.choose (hex x hx) else 0
  have hhost : forall x, x ∈ xs ->
      host x < r /\ host x < x /\ gameF x (host x) = q := by
    intro x hx
    dsimp [host]
    rw [dif_pos hx]
    exact Classical.choose_spec (hex x hx)
  have hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      host x = host y -> x = y := by
    intro x hx y hy hsame
    by_cases hEq : x = y
    · exact hEq
    have hxHost := hhost x hx
    have hyHost := hhost y hy
    by_cases hlt : x < y
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hxHost.2.1 hlt (hupper y hy) hxHost.2.2
          (by simpa [hsame] using hyHost.2.2))
    · have hyx : y < x := by omega
      exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hyHost.2.1 hyx (hupper x hx) hyHost.2.2
          (by simpa [hsame] using hxHost.2.2))
  have hconst : forall y, u <= y -> gameF y s = u := by
    subst u
    exact gameF_boundary_v1_constant_column hboundary
  have havoid : forall x, x ∈ xs -> host x ≠ s := by
    intro x hx hEq
    have hxHost := hhost x hx
    have hxLower : u <= x := by
      rcases hclass x hx with rfl | rfl | hxActive <;> omega
    have hc := hconst x hxLower
    rw [hEq, hc] at hxHost
    omega
  have hmapNodup : (xs.map host).Nodup :=
    r45_nodup_map_of_injective_on host xs hxs hinj
  let cols := List.range' 0 s ++ List.range' (s + 1) (r - s - 1)
  have hsubset : xs.map host ⊆ cols := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨x, hx, rfl⟩
    apply List.mem_append.mpr
    by_cases hcs : host x < s
    · left
      apply List.mem_range'_1.mpr
      exact ⟨Nat.zero_le _, by simpa using hcs⟩
    · right
      apply List.mem_range'_1.mpr
      constructor
      · have hne := havoid x hx
        omega
      · have hcr := (hhost x hx).1
        omega
  have hbound := nodup_subset_length_le hmapNodup hsubset
  have hxsLen : xs.length = q - r + 1 := by
    dsimp [xs]
    simp
    omega
  have hcolsLen : cols.length = r - 1 := by
    dsimp [cols]
    simp
    omega
  have hraw : xs.length <= cols.length := by simpa using hbound
  rw [hxsLen, hcolsLen] at hraw
  omega

/-- Main opening packet for the UnitQueue atom in its original boundary
context. -/
theorem gameF_boundary_unit_queue_forces_future_diagonal_or_rowstart_packet
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hQueue : BoundaryCorridorUnitQueue s) :
    BoundaryUnitQueueFutureDiagonalPacket s \/
      BoundaryUnitQueueRowstartPacket s := by
  dsimp [BoundaryCorridorUnitQueue] at hQueue
  rcases hQueue with ⟨hunit, _hmexQ, hqBelow, _hsourceQ⟩
  let u := s + 1
  let q := gameF (u + 1) u
  have hqPos : 0 < q := by
    have hgt := gameRecurrenceModel.value_gt_index
      (q := u + 1) (r := u) (by omega)
    change u < q at hgt
    omega
  have huq : u < q :=
    gameRecurrenceModel.value_gt_index (by omega)
  have hqOldDiag : q < gameF u u := by
    dsimp [u, q] at hunit hqBelow ⊢
    omega
  have huNeQ : q ≠ u := by omega
  have hOldNF := gameF_late_blocker_boundary_v1_exact_source_normal_form
    hLate hboundary
  dsimp [DipBoundaryV1SourceNormalForm] at hOldNF
  rcases hOldNF with
    ⟨_hmexOld, _hmexOldDiag, hOldBelow, _hxMiss, _hzMiss, _hconst⟩
  have hOldB : B gameF u s q := by
    apply (hOldBelow q hqPos hqOldDiag).2
    exact huNeQ
  rcases gameRecurrenceModel.opening_cover hqPos with hDiag | hRow
  · rcases hDiag with ⟨a, haq, haOwner⟩
    have haLower : u + 2 <= a := by
      apply Nat.le_of_not_gt
      intro haSmall
      by_cases hau : a < u
      · exact gameRecurrenceModel.diagonal_general_no_attack
          hau (by omega) (haOwner.trans rfl)
      · have haCases : a = u \/ a = u + 1 := by omega
        rcases haCases with rfl | rfl
        · have hownerEq : gameF u u = q := by simpa using haOwner
          rw [hownerEq] at hqOldDiag
          omega
        · have hownerEq : gameF (u + 1) (u + 1) = q := haOwner
          dsimp [u, q] at hqBelow hownerEq
          omega
    have hOldC : C gameF u s q := by
      rcases hOldB with hR | hC
      · rcases hR with ⟨i, hiu, hvalue⟩
        have hiLe : i <= s := by omega
        have hiOwner : gameF i i = q := by
          simpa [Nat.min_eq_left hiLe] using hvalue
        have hia := diagonal_injective gameRecurrenceModel
          (hiOwner.trans haOwner.symm)
        omega
      · exact hC
    rcases hOldC with ⟨b, hbs, hpreview⟩
    have hdesert0 : forall t, u < t -> t < a -> gameF t b ≠ q := by
      intro t hut hta htHost
      exact encoding_same_lower_no_repeat game_encodes
        (by omega) hut (by omega) hpreview htHost
    have hdesert1 : forall t, u + 1 < t -> t < a -> gameF t u ≠ q := by
      intro t hut hta htHost
      exact encoding_same_lower_no_repeat game_encodes
        (by omega) hut (by omega) rfl htHost
    left
    exact ⟨a, b, haLower, haq, haOwner, hbs, hpreview, rfl,
      hdesert0, hdesert1⟩
  · rcases hRow with ⟨r, hrq, hstart⟩
    have hOldC : C gameF u s q := by
      rcases hOldB with hR | hC
      · rcases hR with ⟨i, hiu, hvalue⟩
        have hiLe : i <= s := by omega
        have hiOwner : gameF i i = q := by
          simpa [Nat.min_eq_left hiLe] using hvalue
        exact False.elim
          (disjoint_D_S gameRecurrenceModel
            ⟨i, hiOwner⟩ ⟨r, hrq, hstart⟩)
      · exact hC
    rcases hOldC with ⟨b, hbs, hpreview⟩
    have horder := rowstart_host_order_exact gameRecurrenceModel
      hrq hstart (t := u + 1) (b := u) (by omega) (by omega) rfl
    right
    refine ⟨b, r, hbs, hpreview, hrq, hstart, ?_⟩
    rcases horder with ⟨hstrict, hur⟩ | ⟨hboundaryQ, hru⟩
    · right
      have hcap := gameF_boundary_two_preview_rowstart_capacity
        (s := s) (u := u) (q := q) (b := b) (r := r)
        rfl hbs hur hrq hpreview rfl hstart (by simpa [u] using hboundary)
      exact ⟨hstrict, hur, hcap⟩
    · left
      exact ⟨hboundaryQ.symm, hru.symm⟩

end ChompLean
