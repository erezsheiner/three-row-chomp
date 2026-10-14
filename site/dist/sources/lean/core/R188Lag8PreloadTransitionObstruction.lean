import R186GreedySeatDensityAudit
import R148bPersistentHostOrderedHall

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight preload: the exact transition obstruction

Let `t = u-8` and `p = u-5`.  Suppose row `t` first hosts the lower
blocker `p` at column `d`, later hosts the target `u` at column `c`, and
the four intervening values `p+1,...,u-1` are already present in the
source at `d`.

The preload does not by itself bound `c-d`.  What it does force is an
exact transition ledger.  At every skipped column between `d` and `c`,
one of three concrete events occurs:

* the recurrence is on its carry branch;
* the target `u` is parked in the old same-column tail; or
* the actual MEX output is one of the seven values in `[u-8,u) \ {u-5}`,
  and that value underwent a named adjacent `ParkedOnly` source loss
  somewhere after `d` and before the skipped column.

Thus the four-value preload eliminates an unstructured lower-hole branch.
The remaining unbounded branch is exactly the rolling `ColTail` cover of
the target (plus carries), not a shortage of intermediate values.
-/

/-- The four values strictly between `u-5` and `u` are already present at
the source of the lower host. -/
def Lag8FourValuePreloaded (u d : Nat) : Prop :=
  forall z, u - 5 < z -> z < u -> B gameF (u - 8) d z

/-- A non-adjacent source loss contains a literal adjacent parked loss. -/
theorem source_interval_loss_has_parked_edge
    {f : Nat -> Nat -> Nat} {t d e z : Nat}
    (hde : d < e)
    (hloaded : B f t d z)
    (hhole : Not (B f t e z)) :
    exists j,
      d <= j /\ j < e /\
      ParkedOnly f t j z /\ Not (B f t (j + 1) z) := by
  rcases source_interval_drop_has_adjacent_loss
      hde hloaded hhole with ⟨j, hdj, hje, hj, hjnext⟩
  exact ⟨j, hdj, hje,
    source_loss_implies_parkedOnly hj hjnext, hjnext⟩

/-- Exact packet produced by a skipped seat after the lower host. -/
structure Lag8PreloadedSkippedTransition
    (u g d e : Nat) : Prop where
  outputBand : u - 8 <= gameF (u - 8) e
  outputBelowTarget : gameF (u - 8) e < u
  outputNotLowerHost : gameF (u - 8) e ≠ u - 5
  parkedLoss : exists j,
    d <= j /\ j < e /\
    ParkedOnly gameF (u - 8) j (gameF (u - 8) e) /\
    Not (B gameF (u - 8) (j + 1) (gameF (u - 8) e))
  rightOwnerOrCurrentFreeze :
    (exists a,
      e < a /\ a <= g /\ gameF a a = gameF (u - 8) e) \/
    (exists s,
      e < s /\ s <= g /\ s < gameF (u - 8) e /\
        gameF (gameF (u - 8) e) s = gameF (u - 8) e) \/
    (gameF (u - 8) e = u - 8 /\
      gameF (u - 8) e = u - 8)

/-- A target `ColTail` is not an anonymous history bit: it has a unique
old relay row.  Uniqueness uses the no-repeat encoding law in its exact
fixed-column form. -/
theorem gameF_lag8_target_colTail_has_unique_relay_row
    {u e : Nat}
    (hu : 8 <= u)
    (htail : ColTail gameF (u - 8) e u) :
    exists a,
      e < a /\ a < u - 8 /\ gameF a e = u /\
      (forall a', e < a' -> a' < u - 8 ->
        gameF a' e = u -> a' = a) := by
  rcases htail with ⟨a, hat, hea, hhost⟩
  refine ⟨a, hea, hat, hhost, ?_⟩
  intro a' hea' ha't hhost'
  by_cases haa' : a = a'
  · exact haa'.symm
  · by_cases haa'Order : a < a'
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hea haa'Order (by omega) hhost hhost')
    · have ha'a : a' < a := by omega
      exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hea' ha'a (by omega) hhost' hhost)

/-- If an intermediate cell is neither a carry nor an old target-tail
seat, its actual output is a short-band value which was loaded at `d` and
then suffered a concrete adjacent parked loss. -/
theorem gameF_lag8_preloaded_clean_skip_exact_transition
    {u r g c d e : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hde : d < e) (hec : e < c)
    (hnotCarry : Not
      (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8))
    (hnoTargetTail : Not (ColTail gameF (u - 8) e u)) :
    Lag8PreloadedSkippedTransition u g d e := by
  have heTop : e <= u - 8 := by omega
  have hgt : g < u - 8 := by omega
  have hRclean : Not (R gameF (u - 8) e u) := by
    intro hR
    exact hnoTargetTail
      ((gameF_rowstart_R_iff_colTail hru hstart).mp hR)
  have hband :=
    gameF_clean_noncarry_before_target_outputBand_and_ownerWindow
      howners hgt hct (by omega) htarget hec hnotCarry hRclean
  let m := gameF (u - 8) e
  have hmLower : m ≠ u - 5 := by
    intro hm
    have heq : gameF (u - 8) e = gameF (u - 8) d := by
      rw [hlower]
      simpa [m] using hm
    have hcol : e = d :=
      gameRecurrenceModel.fixed_q_injective
        heTop hdt heq
    omega
  have hLowerMex := gameF_high_host_isMex
    hdt (by omega : u - 8 < u - 5) hlower
  have hmLoadedAtD : B gameF (u - 8) d m := by
    by_cases hmBelow : m < u - 5
    · exact hLowerMex.2.2 m (by dsimp [m]; omega) hmBelow
    · have hmAbove : u - 5 < m := by omega
      exact hpreload m hmAbove hband.2.1
  have hmMexE : IsMex (B gameF (u - 8) e) m := by
    dsimp [m]
    exact gameF_brouwerRecurrence.2 heTop hnotCarry
  have hmHole : Not (B gameF (u - 8) e m) := hmMexE.2.1
  have hLoss := source_interval_loss_has_parked_edge
    hde hmLoadedAtD hmHole
  exact {
    outputBand := hband.1
    outputBelowTarget := hband.2.1
    outputNotLowerHost := hmLower
    parkedLoss := hLoss
    rightOwnerOrCurrentFreeze := hband.2.2
  }

/-- Complete pointwise obstruction.  The preload turns every intermediate
column into a carry, a target `ColTail`, or the exact parked-loss packet
above. -/
theorem gameF_lag8_preloaded_every_skip_trichotomy
    {u r g c d e : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hde : d < e) (hec : e < c) :
    (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) \/
      ColTail gameF (u - 8) e u \/
      Lag8PreloadedSkippedTransition u g d e := by
  by_cases hcarry : e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8
  · exact Or.inl hcarry
  · right
    by_cases htail : ColTail gameF (u - 8) e u
    · exact Or.inl htail
    · exact Or.inr
        (gameF_lag8_preloaded_clean_skip_exact_transition
          hu hru hstart howners hgc hct hdt htarget hlower hpreload
          hde hec hcarry htail)

/-- The same trichotomy with the target-tail arm expanded into its unique
old relay row.  This is the exact rolling-cover obstruction left by the
preload argument. -/
theorem gameF_lag8_preloaded_every_skip_relay_trichotomy
    {u r g c d e : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hde : d < e) (hec : e < c) :
    (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) \/
      (exists a,
        e < a /\ a < u - 8 /\ gameF a e = u /\
        (forall a', e < a' -> a' < u - 8 ->
          gameF a' e = u -> a' = a)) \/
      Lag8PreloadedSkippedTransition u g d e := by
  rcases gameF_lag8_preloaded_every_skip_trichotomy
      hu hru hstart howners hgc hct hdt htarget hlower hpreload
      hde hec with hcarry | htail | htransition
  · exact Or.inl hcarry
  · exact Or.inr (Or.inl
      (gameF_lag8_target_colTail_has_unique_relay_row hu htail))
  · exact Or.inr (Or.inr htransition)

/-- In the atomic geometry `c=g+1`, if the lower blocker `u-5` freezes at
`g`, then the last skipped seat `g` is forced to be an old target relay.

The carry arm would create a smaller blocker frozen at the same column
`g`.  The parked-loss arm has no owner strictly between `g` and the cutoff
`g`, so it would freeze the current row `u-8` at `g`, again colliding with
the lower blocker.  Freeze-column uniqueness kills both arms. -/
theorem gameF_lag8_atomic_preloaded_last_skip_is_unique_target_relay
    {u r g d : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hct : g + 1 <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) (g + 1) = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hdg : d < g)
    (hlowerFreeze : gameF (u - 5) g = u - 5) :
    exists a,
      g < a /\ a < u - 8 /\ gameF a g = u /\
      (forall a', g < a' -> a' < u - 8 ->
        gameF a' g = u -> a' = a) := by
  have hsplit := gameF_lag8_preloaded_every_skip_relay_trichotomy
    (u := u) (r := r) (g := g) (c := g + 1) (d := d) (e := g)
    hu hru hstart howners (by omega) hct hdt htarget hlower hpreload
    hdg (by omega)
  rcases hsplit with hcarry | hrelay | htransition
  · rcases hcarry with ⟨hgt, hlow⟩
    have hcol : g <= (u - 8) - 1 := by omega
    have hlowLe : gameF ((u - 8) - 1) g <= (u - 8) - 1 := by omega
    have hsmallFreeze := gameF_low_cell_has_rowstart hcol hlowLe
    exact False.elim
      (gameF_freeze_column_unique
        hsmallFreeze.1 hsmallFreeze.2 (by omega) hlowerFreeze)
  · exact hrelay
  · rcases htransition.rightOwnerOrCurrentFreeze with
        hdiag | hrowstart | hfreezeNow
    · rcases hdiag with ⟨a, hga, hag, _hdiag⟩
      omega
    · rcases hrowstart with ⟨s, hgs, hsg, _hsm, _hfreeze⟩
      omega
    · exact False.elim
        (gameF_freeze_column_unique
          (by omega : g < u - 8) hfreezeNow.1
          (by omega : u - 8 < u - 5) hlowerFreeze)

/-- One column farther left, the owner window has width one.  If that seat
is neither a carry nor an old target relay, its named parked-loss output is
forced to be either the diagonal value owned exactly at `g`, or the current
row freeze at `g-1`.  A row-start owner at `g` is impossible because the
lower blocker already owns that freeze column. -/
theorem gameF_lag8_atomic_preloaded_penultimate_skip_menu
    {u r g d : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hct : g + 1 <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) (g + 1) = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hdg : d < g - 1)
    (hlowerFreeze : gameF (u - 5) g = u - 5) :
    ((g - 1 < u - 8) /\
        gameF ((u - 8) - 1) (g - 1) < u - 8) \/
      (exists a,
        g - 1 < a /\ a < u - 8 /\ gameF a (g - 1) = u /\
        (forall a', g - 1 < a' -> a' < u - 8 ->
          gameF a' (g - 1) = u -> a' = a)) \/
      (Lag8PreloadedSkippedTransition u g d (g - 1) /\
        (gameF g g = gameF (u - 8) (g - 1) \/
          gameF (u - 8) (g - 1) = u - 8)) := by
  have hsplit := gameF_lag8_preloaded_every_skip_relay_trichotomy
    (u := u) (r := r) (g := g) (c := g + 1) (d := d) (e := g - 1)
    hu hru hstart howners (by omega) hct hdt htarget hlower hpreload
    (by omega) (by omega)
  rcases hsplit with hcarry | hrelay | htransition
  · exact Or.inl hcarry
  · exact Or.inr (Or.inl hrelay)
  · right
    right
    refine ⟨htransition, ?_⟩
    rcases htransition.rightOwnerOrCurrentFreeze with
        hdiag | hrowstart | hfreezeNow
    · rcases hdiag with ⟨a, hga, hag, hdiag⟩
      have ha : a = g := by omega
      subst a
      exact Or.inl hdiag
    · rcases hrowstart with ⟨s, hgs, hsg, hsm, hfreeze⟩
      have hs : s = g := by omega
      subst s
      have hmNe := htransition.outputNotLowerHost
      by_cases hmOrder : gameF (u - 8) (g - 1) < u - 5
      · exact False.elim
          (gameF_freeze_column_unique hsm hfreeze
            (by omega) hlowerFreeze)
      · have hpOrder : u - 5 < gameF (u - 8) (g - 1) := by omega
        exact False.elim
          (gameF_freeze_column_unique
            (by omega : g < u - 5) hlowerFreeze hpOrder hfreeze)
    · exact Or.inr hfreezeNow.1

/-- Different clean skipped columns produce different parked-loss values.
This makes the seven-value packet a genuine injection, rather than seven
unrelated existential witnesses. -/
theorem gameF_lag8_preloaded_skip_outputs_injective
    {u e1 e2 : Nat}
    (he1 : e1 <= u - 8) (he2 : e2 <= u - 8)
    (hout : gameF (u - 8) e1 = gameF (u - 8) e2) :
    e1 = e2 :=
  gameRecurrenceModel.fixed_q_injective he1 he2 hout

/-! A small arithmetic rank for `[u-8,u) \ {u-5}`. -/

private def lag8SevenRank (u m : Nat) : Nat :=
  if m < u - 5 then m - (u - 8) else m - (u - 8) - 1

private theorem lag8SevenRank_lt
    {u m : Nat} (hu : 8 <= u)
    (hlo : u - 8 <= m) (hhi : m < u) (hne : m ≠ u - 5) :
    lag8SevenRank u m < 7 := by
  simp only [lag8SevenRank]
  split <;> omega

private theorem lag8SevenRank_injective_on_band
    {u m1 m2 : Nat} (hu : 8 <= u)
    (hlo1 : u - 8 <= m1) (hhi1 : m1 < u) (hne1 : m1 ≠ u - 5)
    (hlo2 : u - 8 <= m2) (hhi2 : m2 < u) (hne2 : m2 ≠ u - 5)
    (hrank : lag8SevenRank u m1 = lag8SevenRank u m2) :
    m1 = m2 := by
  simp only [lag8SevenRank] at hrank
  split at hrank <;> split at hrank <;> omega

/-- If carries and old target tails are separately excluded, the preloaded
clean part has length at most seven.  Hence any gap larger than eight must
contain one of those two rolling-cover defects. -/
theorem gameF_lag8_preloaded_gap_le_eight_without_carry_or_targetTail
    {u r g c d : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hdc : d < c)
    (hnoCarry : forall e, d < e -> e < c ->
      Not (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8))
    (hnoTail : forall e, d < e -> e < c ->
      Not (ColTail gameF (u - 8) e u)) :
    c - d <= 8 := by
  let n := c - d - 1
  have hcol : forall i : Fin n,
      d < d + 1 + i.val /\ d + 1 + i.val < c := by
    intro i
    have hi := i.isLt
    dsimp [n] at hi
    omega
  have hpacket : forall i : Fin n,
      Lag8PreloadedSkippedTransition u g d (d + 1 + i.val) := by
    intro i
    have hi := hcol i
    exact gameF_lag8_preloaded_clean_skip_exact_transition
      hu hru hstart howners hgc hct hdt htarget hlower hpreload
      hi.1 hi.2 (hnoCarry _ hi.1 hi.2) (hnoTail _ hi.1 hi.2)
  let allocation : Fin n -> Fin 7 := fun i =>
    ⟨lag8SevenRank u (gameF (u - 8) (d + 1 + i.val)),
      lag8SevenRank_lt hu (hpacket i).outputBand
        (hpacket i).outputBelowTarget (hpacket i).outputNotLowerHost⟩
  have hinj : Function.Injective allocation := by
    intro i j hij
    have hrank := congrArg Fin.val hij
    have hout : gameF (u - 8) (d + 1 + i.val) =
        gameF (u - 8) (d + 1 + j.val) :=
      lag8SevenRank_injective_on_band hu
        (hpacket i).outputBand (hpacket i).outputBelowTarget
          (hpacket i).outputNotLowerHost
        (hpacket j).outputBand (hpacket j).outputBelowTarget
          (hpacket j).outputNotLowerHost hrank
    have hcols : d + 1 + i.val = d + 1 + j.val :=
      gameRecurrenceModel.fixed_q_injective
        (by have hi := (hcol i).2; omega)
        (by have hj := (hcol j).2; omega) hout
    apply Fin.ext
    omega
  have hn : n <= 7 := r148b_fin_injective_card_le allocation hinj
  dsimp [n] at hn
  omega

/-- Contrapositive form: a gap of at least nine cannot be paid by the four
preloaded values.  It forces an actual carry or an old target-tail seat. -/
theorem gameF_lag8_preloaded_large_gap_forces_carry_or_targetTail
    {u r g c d : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hpreload : Lag8FourValuePreloaded u d)
    (hdc : d < c) (hgap : 9 <= c - d) :
    exists e,
      d < e /\ e < c /\
      ((e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) \/
        ColTail gameF (u - 8) e u) := by
  classical
  by_cases hex : exists e,
      d < e /\ e < c /\
      ((e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) \/
        ColTail gameF (u - 8) e u)
  · exact hex
  · have hnoCarry : forall e, d < e -> e < c ->
        Not (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) := by
      intro e hde hec hcarry
      exact hex ⟨e, hde, hec, Or.inl hcarry⟩
    have hnoTail : forall e, d < e -> e < c ->
        Not (ColTail gameF (u - 8) e u) := by
      intro e hde hec htail
      exact hex ⟨e, hde, hec, Or.inr htail⟩
    have hbound :=
      gameF_lag8_preloaded_gap_le_eight_without_carry_or_targetTail
        hu hru hstart howners hgc hct hdt htarget hlower hpreload hdc
        hnoCarry hnoTail
    omega

#print axioms source_interval_loss_has_parked_edge
#print axioms gameF_lag8_preloaded_clean_skip_exact_transition
#print axioms gameF_lag8_preloaded_every_skip_trichotomy
#print axioms gameF_lag8_preloaded_every_skip_relay_trichotomy
#print axioms gameF_lag8_atomic_preloaded_last_skip_is_unique_target_relay
#print axioms gameF_lag8_atomic_preloaded_penultimate_skip_menu
#print axioms gameF_lag8_preloaded_gap_le_eight_without_carry_or_targetTail
#print axioms gameF_lag8_preloaded_large_gap_forces_carry_or_targetTail

end ChompLean
