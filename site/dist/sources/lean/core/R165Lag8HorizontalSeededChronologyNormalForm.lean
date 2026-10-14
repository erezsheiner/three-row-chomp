import R164Lag8PreviewOwnerTwoArmNormalForm
import R152LowTailCrossingDemand
import R26ActualGameFutureGap

set_option autoImplicit false

namespace ChompLean

/-! Recovered source for the seeded horizontal lag-eight chronology file. -/

def Lag8TargetSixRailPacket (q : Nat) : Prop :=
  gameF (q - 4) 11 = q + 3 /\
    gameF (q - 3) 9 = q + 3 /\
    gameF (q - 2) 7 = q + 3 /\
    gameF (q - 1) 5 = q + 3 /\
    gameF (q + 1) 2 = q + 3 /\
    gameF (q + 2) 0 = q + 3

def Lag8TargetSevenHostSchedule
    (q g : Nat) (host : Nat -> Nat) : Prop :=
  (forall t, q - 4 <= t -> t <= q + 2 ->
      host t <= g /\ gameF t (host t) = q + 3) /\
    (forall t1 t2, q - 4 <= t1 -> t1 < t2 -> t2 <= q + 2 ->
      host t1 ≠ host t2) /\
    host (q - 4) = 11 /\
    host (q - 3) = 9 /\
    host (q - 2) = 7 /\
    host (q - 1) = 5 /\
    host (q + 1) = 2 /\
    host (q + 2) = 0

def Lag8PreviewRowStartRelay (q s : Nat) : Prop :=
  (forall t, s < t -> t < q ->
    exists b, b < s /\ gameF t b = q /\
      forall b', b' < s -> gameF t b' = q -> b' = b) /\
  (forall t1 t2 b1 b2,
    s < t1 -> t1 < t2 -> t2 < q ->
    b1 < s -> b2 < s ->
    gameF t1 b1 = q -> gameF t2 b2 = q -> b1 ≠ b2)

theorem gameF_high_host_isMex
    {t b z : Nat}
    (hbt : b <= t) (htz : t < z) (hhost : gameF t b = z) :
    IsMex (B gameF t b) z := by
  have hnotCarry : Not (b < t /\ gameF (t - 1) b < t) := by
    rintro ⟨hbtStrict, hlow⟩
    have hcarry := gameF_brouwerRecurrence.1 hbtStrict hlow
    rw [hhost] at hcarry
    omega
  have hmex := gameF_brouwerRecurrence.2 hbt hnotCarry
  simpa [hhost] using hmex

theorem source_hole_successor_exact_new_channels
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hhole : Not (B f t e z)) :
    B f t (e + 1) z <->
      (e + 1 < t /\ f (e + 1) (e + 1) = z) \/
      ColTail f t (e + 1) z \/ f t e = z := by
  rw [B_successor_exact_delta]
  constructor
  · rintro (holdDiag | hnewDiag | hnewCol | holdRow | hfresh)
    · exact False.elim
        (hhole (Or.inl (R_iff_diagPrefix_or_colTail.mpr (Or.inl holdDiag))))
    · exact Or.inl hnewDiag
    · exact Or.inr (Or.inl hnewCol)
    · exact False.elim (hhole (Or.inr holdRow))
    · exact Or.inr (Or.inr hfresh)
  · rintro (hnewDiag | hnewCol | hfresh)
    · exact Or.inr (Or.inl hnewDiag)
    · exact Or.inr (Or.inr (Or.inl hnewCol))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hfresh)))

theorem source_interval_drop_has_adjacent_loss
    {f : Nat -> Nat -> Nat} {t z l r : Nat}
    (hlr : l < r)
    (hleft : B f t l z)
    (hright : Not (B f t r z)) :
    exists e, l <= e /\ e < r /\
      B f t e z /\ Not (B f t (e + 1) z) := by
  have aux : forall n l,
      B f t l z -> Not (B f t (l + (n + 1)) z) ->
      exists e, l <= e /\ e < l + (n + 1) /\
        B f t e z /\ Not (B f t (e + 1) z) := by
    intro n
    induction n with
    | zero =>
        intro l hL hR
        refine ⟨l, by omega, by omega, hL, ?_⟩
        simpa using hR
    | succ n ih =>
        intro l hL hR
        by_cases hNext : B f t (l + 1) z
        · have heq : (l + 1) + (n + 1) = l + (n + 1 + 1) := by
            omega
          have hR' : Not (B f t ((l + 1) + (n + 1)) z) := by
            rw [heq]
            exact hR
          rcases ih (l + 1) hNext hR' with
            ⟨e, hle, hlt, hmem, hnot⟩
          refine ⟨e, by omega, ?_, hmem, hnot⟩
          omega
        · refine ⟨l, by omega, ?_, hL, by simpa using hNext⟩
          omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlr)
  cases n with
  | zero => omega
  | succ n =>
      subst r
      exact aux n l hleft hright

theorem gameF_repeat_diagonal_reply_bounds
    {c i t p : Nat}
    (hci : c < i) (hit : i < t) (htp : t < p)
    (hdiag : gameF i i = p) (hrep : gameF t c = p) :
    i < gameF i c /\ gameF i c < p := by
  constructor
  · apply Nat.lt_of_not_ge
    intro hnot
    have hsmall : gameF i c < i + 1 := by omega
    have hconst := constant_from gameRecurrenceModel hci hsmall (t - i)
    have hsum : i + (t - i) = t := by omega
    change gameF (i + (t - i)) c = gameF i c at hconst
    rw [hsum, hrep] at hconst
    omega
  · have hlt := recurrence_strict_row_diagonal_maximal
      gameRecurrenceModel hci
    change gameF i c < gameF i i at hlt
    simpa [hdiag] using hlt

theorem gameF_q_lastFive_prefixHole_iff_qminus3
    {q b x : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (hbq : b <= q - 3) (hhost : gameF (q - 3) b = q)
    (hx0 : q - 5 <= x) (hx1 : x < q) :
    Not (C gameF x b q) <-> x = q - 3 := by
  have hrails := gameF_lag8_preview_fourRailPacket hq
  constructor
  · intro hgap
    have hcases :
        x = q - 5 \/ x = q - 4 \/ x = q - 3 \/
        x = q - 2 \/ x = q - 1 := by
      omega
    rcases hcases with hx | hx | hx | hx | hx
    · subst x
      exact False.elim (hgap ⟨7, h7b, hrails.1⟩)
    · subst x
      exact False.elim (hgap ⟨5, by omega, hrails.2.1⟩)
    · exact hx
    · subst x
      exact False.elim (hgap ⟨2, by omega, hrails.2.2.1⟩)
    · subst x
      exact False.elim (hgap ⟨0, by omega, hrails.2.2.2⟩)
  · intro hx
    subst x
    rintro ⟨b', hb'b, hvalue⟩
    have hb'q : b' <= q - 3 := by omega
    have heq : b' = b :=
      gameRecurrenceModel.fixed_q_injective hb'q hbq
        (hvalue.trans hhost.symm)
    omega

theorem gameF_lag8_target_sixRailPacket
    {q : Nat} (hq : 26 <= q) :
    Lag8TargetSixRailPacket q := by
  have h11raw := gameF_col11_rail (q := q - 4) (by omega)
  have h9raw := gameF_col9_rail (q := q - 3) (by omega)
  have h7raw := gameF_col7_rail (q := q - 2) (by omega)
  have h5raw := gameF_col5_rail (q := q - 1) (by omega)
  have h2raw := gameF_col2_rail (q := q + 1) (by omega)
  have h0raw := gameF_col0 (q + 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem gameF_lag8_failed_band_target_sevenHostSchedule
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    exists host, Lag8TargetSevenHostSchedule q g host := by
  have hlow := gameF_earlyTP_forces_low_tail
    hrv hstart howners hfailure hra (by omega) hburn
  have hExists : forall t, q - 4 <= t -> t <= q + 2 ->
      exists b, b <= g /\ gameF t b = q + 3 := by
    intro t ht0 ht1
    exact hlow t (by omega) (by omega)
  let host := fun t =>
    if ht : q - 4 <= t /\ t <= q + 2 then
      Classical.choose (hExists t ht.1 ht.2)
    else 0
  have hspec : forall t, q - 4 <= t -> t <= q + 2 ->
      host t <= g /\ gameF t (host t) = q + 3 := by
    intro t ht0 ht1
    dsimp [host]
    rw [dif_pos ⟨ht0, ht1⟩]
    exact Classical.choose_spec (hExists t ht0 ht1)
  have hhostRow : forall t, q - 4 <= t -> t <= q + 2 -> host t <= t := by
    intro t ht0 ht1
    have htg := (hspec t ht0 ht1).1
    omega
  have hinj : forall t1 t2, q - 4 <= t1 -> t1 < t2 -> t2 <= q + 2 ->
      host t1 ≠ host t2 := by
    intro t1 t2 ht10 ht12 ht21
    have h1 := hspec t1 ht10 (by omega)
    have h2 := hspec t2 (by omega) ht21
    exact gameF_same_high_target_hosts_have_distinct_columns
      (hH1t1 := by omega) ht12 (by omega) h1.2 h2.2
  rcases gameF_lag8_target_sixRailPacket hq with
    ⟨h11, h9, h7, h5, h2, h0⟩
  have hEq11 : host (q - 4) = 11 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q - 4) (by omega) (by omega)) (by omega)
      ((hspec (q - 4) (by omega) (by omega)).2.trans h11.symm)
  have hEq9 : host (q - 3) = 9 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q - 3) (by omega) (by omega)) (by omega)
      ((hspec (q - 3) (by omega) (by omega)).2.trans h9.symm)
  have hEq7 : host (q - 2) = 7 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q - 2) (by omega) (by omega)) (by omega)
      ((hspec (q - 2) (by omega) (by omega)).2.trans h7.symm)
  have hEq5 : host (q - 1) = 5 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q - 1) (by omega) (by omega)) (by omega)
      ((hspec (q - 1) (by omega) (by omega)).2.trans h5.symm)
  have hEq2 : host (q + 1) = 2 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q + 1) (by omega) (by omega)) (by omega)
      ((hspec (q + 1) (by omega) (by omega)).2.trans h2.symm)
  have hEq0 : host (q + 2) = 0 :=
    gameRecurrenceModel.fixed_q_injective
      (hhostRow (q + 2) (by omega) (by omega)) (by omega)
      ((hspec (q + 2) (by omega) (by omega)).2.trans h0.symm)
  exact ⟨host, hspec, hinj, hEq11, hEq9, hEq7, hEq5, hEq2, hEq0⟩

theorem gameF_lag8_failed_band_cutoff_atLeast_eleven
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    11 <= g := by
  rcases gameF_lag8_failed_band_target_sevenHostSchedule
      hq hrv hstart howners hfailure hra hburn with ⟨host, hsched⟩
  have hspec := hsched.1 (q - 4) (by omega) (by omega)
  rw [hsched.2.2.1] at hspec
  exact hspec.1

theorem gameF_lag8_qminus3_targetRail_strictly_left_of_qHost
    {q b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (hqhost : gameF (q - 3) b = q) :
    gameF (q - 3) 9 = q + 3 /\ 9 < b := by
  have h8 := gameF_col8_rail (q := q - 3) (by omega)
  have h9raw := gameF_col9_rail (q := q - 3) (by omega)
  have h9 : gameF (q - 3) 9 = q + 3 := by omega
  have hb8 : b ≠ 8 := by
    intro hb
    subst b
    rw [h8] at hqhost
    omega
  have hb9 : b ≠ 9 := by
    intro hb
    subst b
    rw [h9] at hqhost
    omega
  exact ⟨h9, by omega⟩

theorem gameF_lag8_qminus3_targetHost_exact_normalForm
    {q r g b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3)
    (hqhost : gameF (q - 3) b = q) :
    9 <= g /\ gameF (q - 3) 9 = q + 3 /\ 9 < b := by
  have hrail := gameF_lag8_qminus3_targetRail_strictly_left_of_qHost
    hq h7b hqhost
  have hlow := gameF_earlyTP_forces_low_tail
    hrv hstart howners hfailure hra (by omega) hburn
  rcases hlow (q - 3) (by omega) (by omega) with ⟨h, hhg, hhval⟩
  have hhrow : h <= q - 3 := by omega
  have heq : h = 9 :=
    gameRecurrenceModel.fixed_q_injective hhrow (by omega)
      (hhval.trans hrail.1.symm)
  subst h
  exact ⟨hhg, hrail.1, hrail.2⟩

theorem gameF_dynamic_qHost_leftDiagonal_sandwich
    {q r g d b : Nat}
    (harm : Lag8PreviewLeftDiagonalOwnerArm q r g d)
    (hbq : b <= q - 3) (hhost : gameF (q - 3) b = q) :
    b < d /\ d < r - 1 := by
  have hdiag := harm.2.1
  have hdq5 := harm.1.2.2.1.2
  have hbd := gameF_past_diagonal_echo_strictly_left
    (a := d) (q := q - 3) (r := b)
    (by omega) hbq (hhost.trans hdiag.symm)
  exact ⟨hbd, harm.1.2.1⟩

theorem gameF_dynamic_qHost_leftRowStart_sandwich
    {q r g s b : Nat}
    (harm : Lag8PreviewLeftRowStartOwnerArm q r g s)
    (hbq : b <= q - 3) (hhost : gameF (q - 3) b = q) :
    b < s /\ s < r - 1 := by
  have hsq := harm.2.1
  have hstart := harm.2.2.1
  have hslt : s < q - 3 := by
    have hs5 := harm.1.2.2.1.2
    omega
  have hbs := gameF_pre_rowStart_host_strictly_left_of_owner
    hstart hsq hslt (by omega) hbq hhost
  exact ⟨hbs, harm.1.2.1⟩

theorem gameF_dynamic_qHost_diagonal_seededGap_normalForm
    {q r g d b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (harm : Lag8PreviewLeftDiagonalOwnerArm q r g d)
    (hbq : b <= q - 3) (hhost : gameF (q - 3) b = q) :
    exists w x,
      w = gameF d b /\ d < w /\ w < q /\
      d < x /\ x < q /\ Not (C gameF x b q) /\
      (x < q - 5 \/ x = q - 3) := by
  have hsand := gameF_dynamic_qHost_leftDiagonal_sandwich harm hbq hhost
  have hdiag := harm.2.1
  have hdq5 := harm.1.2.2.1.2
  let w := gameF d b
  have hwBounds : d < w /\ w < q := by
    dsimp [w]
    exact gameF_repeat_diagonal_reply_bounds hsand.1 (by omega)
      (by omega) hdiag hhost
  have hgapOwner : Not (C gameF d b q) := by
    rintro ⟨k, hkb, hvalue⟩
    have hkd : k <= d := by omega
    have heq : k = d :=
      gameRecurrenceModel.fixed_q_injective hkd (by omega)
        (hvalue.trans hdiag.symm)
    omega
  rcases rightmost_hole_forces_future_prefix_gap
      gameRecurrenceModel hsand.1 rfl hwBounds.1 hwBounds.2 hgapOwner with
    ⟨x, hdx, hxq, hxgap⟩
  have hwhere : x < q - 5 \/ x = q - 3 := by
    by_cases hxold : x < q - 5
    · exact Or.inl hxold
    · exact Or.inr ((gameF_q_lastFive_prefixHole_iff_qminus3
        hq h7b hbq hhost (by omega) hxq).mp hxgap)
  exact ⟨w, x, rfl, hwBounds.1, hwBounds.2,
    hdx, hxq, hxgap, hwhere⟩

theorem gameF_high_host_horizontal_hole_and_fresh_closure
    {t b z : Nat}
    (hbt : b <= t) (htz : t < z) (hhost : gameF t b = z) :
    IsMex (B gameF t b) z /\
      Not (B gameF t b z) /\
      B gameF t (b + 1) z /\
      forall e, b < e -> B gameF t e z := by
  have hmex := gameF_high_host_isMex hbt htz hhost
  exact ⟨hmex, hmex.2.1, fresh_emission_closes_next hhost,
    fun _ hbe => fresh_emission_persists_in_all_later_sources hhost hbe⟩

theorem gameF_lag8_qminus3_nine_fixedRailOrigin
    {q : Nat} (hq : 26 <= q) :
    gameF (q - 6) 9 = q /\ ColTail gameF (q - 3) 9 q := by
  have h9raw := gameF_col9_rail (q := q - 6) (by omega)
  have h9 : gameF (q - 6) 9 = q := by omega
  refine ⟨h9, q - 6, by omega, by omega, h9⟩

theorem gameF_lag8_qminus3_nine_parkedOnly_iff_noExtraChannels
    {q : Nat} (hq : 26 <= q) :
    ParkedOnly gameF (q - 3) 9 q <->
      Not (DiagPrefix gameF (q - 3) 9 q) /\
      Not (C gameF (q - 3) 9 q) := by
  constructor
  · exact fun hpark => hpark.2
  · rintro ⟨hnoDiag, hnoRow⟩
    exact ⟨(gameF_lag8_qminus3_nine_fixedRailOrigin hq).2,
      hnoDiag, hnoRow⟩

theorem gameF_lag8_qminus3_nine_parkedOnly_of_noDiag
    {q b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (hbq : b <= q - 3) (hqhost : gameF (q - 3) b = q)
    (hnoDiag : Not (DiagPrefix gameF (q - 3) 9 q)) :
    ParkedOnly gameF (q - 3) 9 q := by
  have hrail := gameF_lag8_qminus3_targetRail_strictly_left_of_qHost
    hq h7b hqhost
  have hnoRow : Not (C gameF (q - 3) 9 q) := by
    rintro ⟨k, hk9, hkval⟩
    have hkrow : k <= q - 3 := by omega
    have heq : k = b :=
      gameRecurrenceModel.fixed_q_injective hkrow hbq
        (hkval.trans hqhost.symm)
    omega
  exact (gameF_lag8_qminus3_nine_parkedOnly_iff_noExtraChannels hq).2
    ⟨hnoDiag, hnoRow⟩

theorem gameF_lag8_qminus3_nine_parkedOnly_diagonalArm
    {q r g d b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (harm : Lag8PreviewLeftDiagonalOwnerArm q r g d)
    (hbq : b <= q - 3) (hqhost : gameF (q - 3) b = q) :
    9 < b /\ ParkedOnly gameF (q - 3) 9 q := by
  have hleft := gameF_lag8_qminus3_targetRail_strictly_left_of_qHost
    hq h7b hqhost
  have hsand := gameF_dynamic_qHost_leftDiagonal_sandwich harm hbq hqhost
  have hdiag := harm.2.1
  have hdq5 := harm.1.2.2.1.2
  have hnoDiag : Not (DiagPrefix gameF (q - 3) 9 q) := by
    rintro ⟨a, hat, ha9, hadiag⟩
    exact gameRecurrenceModel.diagonal_no_attack
      (by omega) (by omega) hadiag hdiag
  exact ⟨hleft.2,
    gameF_lag8_qminus3_nine_parkedOnly_of_noDiag
      hq h7b hbq hqhost hnoDiag⟩

theorem gameF_lag8_qminus3_nine_parkedOnly_rowStartArm
    {q r g s b : Nat}
    (hq : 26 <= q) (h7b : 7 < b)
    (harm : Lag8PreviewLeftRowStartOwnerArm q r g s)
    (hbq : b <= q - 3) (hqhost : gameF (q - 3) b = q) :
    9 < b /\ ParkedOnly gameF (q - 3) 9 q := by
  have hleft := gameF_lag8_qminus3_targetRail_strictly_left_of_qHost
    hq h7b hqhost
  have hsand := gameF_dynamic_qHost_leftRowStart_sandwich harm hbq hqhost
  have hstart := harm.2.2.1
  have hsq := harm.2.1
  have hnoDiag : Not (DiagPrefix gameF (q - 3) 9 q) := by
    rintro ⟨a, hat, ha9, hadiag⟩
    exact gameRecurrenceModel.rowstart_diagonal_attack
      hstart hsq hadiag (by omega)
  exact ⟨hleft.2,
    gameF_lag8_qminus3_nine_parkedOnly_of_noDiag
      hq h7b hbq hqhost hnoDiag⟩

theorem gameF_lag8_qminus3_fixedRail_parkedChain_exactDeath
    {q b : Nat}
    (hq : 26 <= q) (h9b : 9 < b)
    (hbq : b <= q - 3) (hqhost : gameF (q - 3) b = q)
    (hpark : ParkedOnly gameF (q - 3) 9 q) :
    exists e,
      9 <= e /\ e < b /\
      ParkedOnly gameF (q - 3) e q /\
      Not (e + 1 < q - 3 /\ gameF (e + 1) (e + 1) = q) /\
      Not (ColTail gameF (q - 3) (e + 1) q) /\
      Not (gameF (q - 3) e = q) := by
  have hhole := (gameF_high_host_horizontal_hole_and_fresh_closure
    hbq (by omega) hqhost).2.1
  rcases source_interval_drop_has_adjacent_loss
      h9b (parkedOnly_mem_current_source hpark) hhole with
    ⟨e, h9e, heb, hmem, hnot⟩
  have hexact := (source_loss_iff_parked_and_no_replacement).1
    ⟨hmem, hnot⟩
  exact ⟨e, h9e, heb, hexact.1, hexact.2.1,
    hexact.2.2.1, hexact.2.2.2⟩

theorem gameF_leftRowStartOwner_forces_uniqueRelay
    {q r g s : Nat}
    (harm : Lag8PreviewLeftRowStartOwnerArm q r g s) :
    Lag8PreviewRowStartRelay q s := by
  have hstart := harm.2.2.1
  have hsq := harm.2.1
  constructor
  · intro t hst htq
    rcases rowStartPropagation gameRecurrenceModel hstart hsq hst htq with
      ⟨b, hbs, hvalue⟩
    refine ⟨b, hbs, hvalue, ?_⟩
    intro b' hb's hb'value
    exact gameRecurrenceModel.fixed_q_injective
      (by omega) (by omega) (hb'value.trans hvalue.symm)
  · intro t1 t2 b1 b2 hst1 ht12 ht2q hb1s hb2s h1 h2 heq
    subst b2
    exact encoding_same_lower_no_repeat game_encodes
      (s := b1) (t₁ := t1) (t₂ := t2) (p := q)
      (by omega) ht12 ht2q h1 h2

#print axioms gameF_lag8_failed_band_target_sevenHostSchedule
#print axioms gameF_dynamic_qHost_diagonal_seededGap_normalForm
#print axioms gameF_lag8_qminus3_fixedRail_parkedChain_exactDeath
#print axioms gameF_leftRowStartOwner_forces_uniqueRelay

end ChompLean
