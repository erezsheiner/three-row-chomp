import R172TerminalOnlyBraidLastTwoRowsNormalForm
import R27ActualGameGapCharge
import R165Lag8HorizontalSeededChronologyNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
# Terminal relay Hall saturation

A row-start freeze `gameF z r = z`, with `r < z`, forces one copy of `z`
on every active row `r < t < z`, strictly inside the prefix `[0,r)`.  The
copy is unique on its row, and actual-game no-repeat makes the host columns
different on different rows.  Thus the whole active interval injects into
the `r` prefix columns.

This file packages the injection as an explicit all-depth certificate.  It
also proves the sharp equality statement: if `z = 2*r+1`, the active relay
is not merely bounded by the prefix -- it is a bijection onto every column
of `[0,r)`.  Finally, any additional occurrence at or before row `r`
deletes the equality case and improves the bound to `z <= 2*r`.
-/

/-- A complete Hall certificate for the relay forced by a terminal freeze.
The `saturatedBijection` field says that at the extremal value every prefix
column is used by exactly one active row. -/
structure TerminalRelayHallCertificate
    (z r : Nat) (host : Nat -> Nat) : Prop where
  hosted : forall t, r < t -> t < z ->
    host t < r /\ gameF t (host t) = z
  uniqueOnRow : forall t, r < t -> t < z -> forall c,
    c < r -> gameF t c = z -> c = host t
  hostMex : forall t, r < t -> t < z ->
    IsMex (B gameF t (host t)) z
  noReuse : forall t1 t2,
    r < t1 -> t1 < t2 -> t2 < z -> host t1 ≠ host t2
  capacity : z <= r + r + 1
  saturatedBijection : z = r + r + 1 -> forall c, c < r ->
    exists t,
      (r < t /\ t < z /\ host t = c) /\
      forall y, r < y /\ y < z /\ host y = c -> y = t

/-- Mapping a duplicate-free list through a function which is injective on
that list preserves duplicate-freeness. -/
private theorem r174_nodup_map_of_injective_on
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

/-- A duplicate-free subset with the same length as its finite ambient list
has exactly the same members. -/
private theorem r174_exact_cover_of_nodup_subset_length
    {target raw : List Nat}
    (hTarget : target.Nodup)
    (hsub : target ⊆ raw)
    (hcard : raw.length = target.length) :
    forall x, x ∈ raw <-> x ∈ target := by
  intro x
  constructor
  · intro hxRaw
    by_cases hxTarget : x ∈ target
    · exact hxTarget
    · exfalso
      have hConsNodup : (x :: target).Nodup :=
        List.nodup_cons.mpr ⟨hxTarget, hTarget⟩
      have hConsSub : (x :: target) ⊆ raw := by
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hxy | hyTarget
        · simpa [hxy] using hxRaw
        · exact hsub hyTarget
      have hle := nodup_subset_length_le hConsNodup hConsSub
      simp only [List.length_cons] at hle
      omega
  · intro hx
    exact hsub hx

/-- The global theorem: every actual terminal freeze carries an explicit
injective relay schedule, the sharp capacity bound, and exact Hall
saturation at equality. -/
theorem gameF_terminal_freeze_relay_hall_certificate
    {z r : Nat}
    (hrz : r < z)
    (hstart : gameF z r = z) :
    exists host, TerminalRelayHallCertificate z r host := by
  classical
  have hExists : forall t, r < t -> t < z ->
      exists c, c < r /\ gameF t c = z := by
    intro t hrt htz
    exact rowStartPropagation gameRecurrenceModel hstart hrz hrt htz
  let host : Nat -> Nat := fun t =>
    if ht : r < t /\ t < z then
      Classical.choose (hExists t ht.1 ht.2)
    else 0
  have hhost : forall t, r < t -> t < z ->
      host t < r /\ gameF t (host t) = z := by
    intro t hrt htz
    dsimp [host]
    rw [dif_pos ⟨hrt, htz⟩]
    exact Classical.choose_spec (hExists t hrt htz)
  have hunique : forall t, r < t -> t < z -> forall c,
      c < r -> gameF t c = z -> c = host t := by
    intro t hrt htz c hcr hc
    have hh := hhost t hrt htz
    exact gameRecurrenceModel.fixed_q_injective
      (by omega) (by omega) (hc.trans hh.2.symm)
  have hmex : forall t, r < t -> t < z ->
      IsMex (B gameF t (host t)) z := by
    intro t hrt htz
    have hh := hhost t hrt htz
    exact gameF_high_host_isMex (by omega) htz hh.2
  have hnoReuse : forall t1 t2,
      r < t1 -> t1 < t2 -> t2 < z -> host t1 ≠ host t2 := by
    intro t1 t2 hrt1 ht12 ht2z heq
    have h1 := hhost t1 hrt1 (by omega)
    have h2 := hhost t2 (by omega) ht2z
    exact encoding_same_lower_no_repeat game_encodes
      (s := host t1) (t₁ := t1) (t₂ := t2) (p := z)
      (by omega) ht12 ht2z h1.2 (by simpa [heq] using h2.2)
  have hcapacity : z <= r + r + 1 := by
    apply Nat.le_of_not_gt
    intro htooLarge
    have hlong : r - 0 < z - r - 1 := by omega
    rcases gameF_long_active_interval_forces_prefix_return
        (c := 0) hstart hrz hlong with ⟨t, _hrt, _htz, hC⟩
    rcases hC with ⟨c, hc0, _hc⟩
    omega
  have hsaturated : z = r + r + 1 -> forall c, c < r ->
      exists t,
        (r < t /\ t < z /\ host t = c) /\
        forall y, r < y /\ y < z /\ host y = c -> y = t := by
    intro hext c hcr
    let xs := List.range' (r + 1) (z - r - 1)
    have hxsNodup : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range' 1
    have hactive : forall t, t ∈ xs -> r < t /\ t < z := by
      intro t ht
      have htrange := List.mem_range'_1.mp (by simpa [xs] using ht)
      omega
    have hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
        host x = host y -> x = y := by
      intro x hx y hy hxy
      have hxa := hactive x hx
      have hya := hactive y hy
      by_cases heq : x = y
      · exact heq
      · by_cases hxyOrder : x < y
        · exact False.elim
            (hnoReuse x y hxa.1 hxyOrder hya.2 hxy)
        · have hyx : y < x := by omega
          exact False.elim
            (hnoReuse y x hya.1 hyx hxa.2 hxy.symm)
    have hmapNodup : (xs.map host).Nodup :=
      r174_nodup_map_of_injective_on host xs hxsNodup hinj
    have hsubset : xs.map host ⊆ List.range' 0 r := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨t, ht, rfl⟩
      have hta := hactive t ht
      have hthost := hhost t hta.1 hta.2
      apply List.mem_range'_1.mpr
      exact ⟨Nat.zero_le _, by simpa using hthost.1⟩
    have hcard : (List.range' 0 r).length = (xs.map host).length := by
      dsimp [xs]
      simp only [List.length_range', List.length_map]
      omega
    have hseteq : forall x,
        x ∈ List.range' 0 r <-> x ∈ xs.map host :=
      r174_exact_cover_of_nodup_subset_length hmapNodup hsubset hcard
    have hcRange : c ∈ List.range' 0 r := by
      exact List.mem_range'_1.mpr ⟨Nat.zero_le c, by simpa using hcr⟩
    have hcMap : c ∈ xs.map host := (hseteq c).mp hcRange
    rcases List.mem_map.mp hcMap with ⟨t, ht, htc⟩
    have hta := hactive t ht
    refine ⟨t, ⟨⟨hta.1, hta.2, htc⟩, ?_⟩⟩
    intro y hy
    by_cases hyt : y = t
    · exact hyt
    · by_cases hytOrder : y < t
      · exact False.elim
          (hnoReuse y t hy.1 hytOrder hta.2
            (hy.2.2.trans htc.symm))
      · have hty : t < y := by omega
        exact False.elim
          (hnoReuse t y hta.1 hty hy.2.1
            (htc.trans hy.2.2.symm))
  refine ⟨host, {
    hosted := hhost
    uniqueOnRow := hunique
    hostMex := hmex
    noReuse := hnoReuse
    capacity := hcapacity
    saturatedBijection := hsaturated
  }⟩

/-- Scalar form of the terminal relay Hall bound. -/
theorem gameF_terminal_freeze_value_le_twice_column_plus_one
    {z r : Nat}
    (hrz : r < z)
    (hstart : gameF z r = z) :
    z <= r + r + 1 := by
  rcases gameF_terminal_freeze_relay_hall_certificate hrz hstart with
    ⟨_host, hcert⟩
  exact hcert.capacity

/-- One additional occurrence at or before the freeze row removes the sole
extremal Hall face.  This includes the previously uncovered boundary case
`s = r`, and sharpens `z <= 2*r+1` to `z <= 2*r`. -/
theorem gameF_prefreeze_host_sharpens_terminal_relay_capacity
    {z r s b : Nat}
    (hrz : r < z)
    (hstart : gameF z r = z)
    (hbs : b < s)
    (hsr : s <= r)
    (hpreview : gameF s b = z) :
    z <= r + r := by
  rcases gameF_terminal_freeze_relay_hall_certificate hrz hstart with
    ⟨host, hcert⟩
  by_cases hext : z = r + r + 1
  · have hbr : b < r := by omega
    rcases hcert.saturatedBijection hext b hbr with
      ⟨t, ht, _htUnique⟩
    exact False.elim
      (encoding_same_lower_no_repeat game_encodes
        (s := b) (t₁ := s) (t₂ := t) (p := z)
        hbs (by omega) ht.2.1 hpreview
        (by simpa [ht.2.2] using (hcert.hosted t ht.1 ht.2.1).2))
  · have hcap := hcert.capacity
    omega

/-- Every failed terminal high braid therefore carries the full global
relay Hall certificate; this is independent of the unresolved strand-order
question. -/
theorem gameF_failedTerminalHighBraid_global_relay_hall
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a) :
    exists host, TerminalRelayHallCertificate v r host :=
  gameF_terminal_freeze_relay_hall_certificate
    hbraid.terminal.1 hbraid.terminal.2

/-- If the old high-braid host occurs already on the freeze-column row, it
is an additional pre-active relay seat, so the stronger even bound holds. -/
theorem gameF_failedTerminalHighBraid_boundary_oldHost_strict_capacity
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (har : a = r) :
    v <= r + r := by
  subst a
  exact gameF_prefreeze_host_sharpens_terminal_relay_capacity
    hbraid.terminal.1 hbraid.terminal.2
    (by have := hbraid.failure; omega) (Nat.le_refl r) hbraid.oldHost

/-- On the extremal Hall face, a failed high braid must start strictly
after row `r`, and its old host is exactly the unique active row using the
rightmost prefix column `r-1`. -/
theorem gameF_failedTerminalHighBraid_extremal_rightmost_relay_pin
    {v r g a : Nat}
    (hbraid : FailedTerminalDeepHistoryHighBraidPacket v r g a)
    (hext : v = r + r + 1) :
    r < a /\
      (forall t, r < t -> t < v -> gameF t (r - 1) = v -> t = a) := by
  have hra : r <= a := hbraid.oldHostChronology.1
  have hraStrict : r < a := by
    by_cases har : a = r
    · have hcap :=
        gameF_failedTerminalHighBraid_boundary_oldHost_strict_capacity
          hbraid har
      omega
    · omega
  refine ⟨hraStrict, ?_⟩
  have hav : a < v := by
    have hadeep := hbraid.oldHostChronology.2
    omega
  intro t hrt htv htHost
  by_cases hta : t = a
  · exact hta
  · by_cases htaOrder : t < a
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          (s := r - 1) (t₁ := t) (t₂ := a) (p := v)
          (by omega) htaOrder hav htHost hbraid.oldHost)
    · have hat : a < t := by omega
      exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          (s := r - 1) (t₁ := a) (t₂ := t) (p := v)
          (by omega) hat htv hbraid.oldHost htHost)

#print axioms gameF_terminal_freeze_relay_hall_certificate
#print axioms gameF_prefreeze_host_sharpens_terminal_relay_capacity
#print axioms gameF_failedTerminalHighBraid_extremal_rightmost_relay_pin

end ChompLean
