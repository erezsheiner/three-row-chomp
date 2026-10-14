import R154Lag8TerminalSiblingAudit
import R152Col11Lag7Collapse

set_option autoImplicit false

namespace ChompLean

/-!
# The exact terminal source exchange at a failed upper rail

At the last loaded column `r-1`, every positive value below the target is
present, and the target itself is present through old same-column history.
The cell is therefore a genuine MEX strictly above the target.  Moving one
column to the target freeze preserves every lower value but deletes the
target, whose MEX is now exactly the target.

This packages the surviving lag-eight obstruction as a singleton low-source
loss followed by a strict MEX descent.  It is stronger than the parked-only
packet: it records the old MEX and the complete lower-source preservation on
both sides of the edge.
-/

/-- Owner coverage saturates the target row at every column strictly to the
right of the owner cutoff. -/
theorem gameF_ownerCovered_target_row_saturation
    {v g e : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hge : g < e)
    (hev : e <= v) :
    forall k, 0 < k -> k < v -> B gameF v e k := by
  have hepos : 0 < e := by omega
  have howners' : LowerOwnerCoveredBy v (e - 1) :=
    lowerOwnerCoveredBy_mono (by omega) howners
  have hsat := lowerOwnerCoveredBy_source_saturation
    (v := v) (s := e - 1) (by omega) howners'
  simpa [Nat.sub_add_cancel hepos] using hsat

/-- Beyond the owner cutoff, the predecessor of a genuine target freeze
cannot be on the carry branch.  A low carried value would already be a
row-start value owned at that predecessor column, contradicting the owner
cutoff. -/
theorem gameF_terminal_predecessor_not_carry
    {v r g : Nat}
    (hrv : r < v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r) :
    Not (r - 1 < v /\ gameF (v - 1) (r - 1) < v) := by
  rintro ⟨_hcv, hlow⟩
  have hcprev : r - 1 <= v - 1 := by omega
  have hrow := gameF_low_cell_has_rowstart hcprev (by omega)
  let k := gameF (v - 1) (r - 1)
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hkv : k < v := by
    dsimp [k]
    exact hlow
  rcases howners k hkpos hkv with
      ⟨a, _hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
  · exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨r - 1, hrow.1, hrow.2⟩
  · have hcol : r - 1 = rk :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hrow.1) (Nat.le_of_lt hrkk)
        (hrow.2.trans hstartk.symm)
    omega

/-- Exact terminal-edge packet at a failed upper rail.  The old cell is a
MEX strictly above `v`; the next source has MEX `v`; every positive lower
value is present on both sides; and `v` itself is the source value deleted
on the edge. -/
theorem gameF_failed_terminal_singleton_source_exchange
    {v r g : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r) :
    IsMex (B gameF v (r - 1)) (gameF v (r - 1)) /\
      v < gameF v (r - 1) /\
      ParkedOnly gameF v (r - 1) v /\
      (forall k, 0 < k -> k < v ->
        B gameF v (r - 1) k /\ B gameF v r k) /\
      B gameF v (r - 1) v /\
      Not (B gameF v r v) := by
  have hrpos : 0 < r := by omega
  have hcpv : r - 1 <= v := by omega
  have hnotCarry := gameF_terminal_predecessor_not_carry
    hrv howners hfailure
  have hmex := gameF_brouwerRecurrence.2 hcpv hnotCarry
  have hloaded := gameF_ownerCovered_prefreeze_column_is_loaded
    hvpos hrv hstart howners (e := r - 1) (by omega) (by omega)
  have hBv : B gameF v (r - 1) v := hloaded.2.2
  have hhole : Not (B gameF v r v) :=
    gameF_rowstart_freeze_source_hole hrv hstart
  have hsatOld := gameF_ownerCovered_target_row_saturation
    (v := v) (g := g) (e := r - 1) howners (by omega) (by omega)
  have hsatNew := gameF_ownerCovered_target_row_saturation
    (v := v) (g := g) (e := r) howners (by omega) (by omega)
  have hhigh : v < gameF v (r - 1) := by
    by_cases hlt : gameF v (r - 1) < v
    · exact False.elim
        (hmex.2.1 (hsatOld (gameF v (r - 1)) hmex.1 hlt))
    · by_cases heq : gameF v (r - 1) = v
      · exact False.elim (hmex.2.1 (by rw [heq]; exact hBv))
      · omega
  refine ⟨hmex, hhigh, hloaded.2.1, ?_, hBv, hhole⟩
  intro k hkpos hkv
  exact ⟨hsatOld k hkpos hkv, hsatNew k hkpos hkv⟩

/-- In R151 coordinates, an exact lag-eight burn can survive only through
the terminal singleton exchange above.  The burn also keeps its column
strictly above the target on every intervening pre-birth row. -/
theorem gameF_lag8_failed_terminal_exchange_packet
    {q r g : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    IsMex (B gameF (q + 3) (r - 1))
        (gameF (q + 3) (r - 1)) /\
      q + 3 < gameF (q + 3) (r - 1) /\
      ParkedOnly gameF (q + 3) (r - 1) (q + 3) /\
      (forall k, 0 < k -> k < q + 3 ->
        B gameF (q + 3) (r - 1) k /\
          B gameF (q + 3) r k) /\
      B gameF (q + 3) (r - 1) (q + 3) /\
      Not (B gameF (q + 3) r (q + 3)) /\
      (forall s, q - 5 < s -> s < q + 3 ->
        q + 3 < gameF s (r - 1)) := by
  have hedge := gameF_failed_terminal_singleton_source_exchange
    (v := q + 3) (r := r) (g := g)
    (by omega) hrv hstart howners hfailure
  refine ⟨hedge.1, hedge.2.1, hedge.2.2.1,
    hedge.2.2.2.1, hedge.2.2.2.2.1, hedge.2.2.2.2.2, ?_⟩
  intro s has hsv
  exact gameF_burned_band_column_stays_above_target
    (v := q + 3) (g := g) (a := q - 5) (e := r - 1) (s := s)
    howners (by omega) (by omega) has hsv hburn

#print axioms gameF_ownerCovered_target_row_saturation
#print axioms gameF_terminal_predecessor_not_carry
#print axioms gameF_failed_terminal_singleton_source_exchange
#print axioms gameF_lag8_failed_terminal_exchange_packet

end ChompLean
