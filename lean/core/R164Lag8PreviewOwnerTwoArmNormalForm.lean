import R163Lag8PreviewOwnerOrderReduction
import EarlyAffineRails

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight preview: exact two-arm left-owner normal form

Write `q=v-3` and `c=r-1`. For `q >= 26`, four affine rails emit `q`
strictly before row `q`:

* row `q-5`, column `7`;
* row `q-4`, column `5`;
* row `q-2`, column `2`;
* row `q-1`, column `0`.

Under the displayed lag-eight frame, if owner coverage puts an opening
owner of `q` strictly left of `c`, these
rails do not contradict either possible opening type.  In both arms they
only force the owner into the common interval `(7,c)`:

* for a diagonal owner, the four rails are later echoes and ECHO-LEFT puts
  their columns to the left of the owner;
* for a row-start owner, backward row-start propagation plus fixed-row
  injectivity makes the four rails its unique prehosts, again to the left
  of the owner.

The terminal singleton exchange is carried in full (projected to the old
MEX, the deleted target, the preview value on both sides, and the high
vertical corridor).  It is common to both arms and therefore supplies no
further discriminator between them.
-/

/-- The four unconditional occurrences of the preview value `q`. -/
def Lag8PreviewFourRailPacket (q : Nat) : Prop :=
  gameF (q - 5) 7 = q /\
    gameF (q - 4) 5 = q /\
    gameF (q - 2) 2 = q /\
    gameF (q - 1) 0 = q

/-- The exact terminal-edge information relevant to the preview value.
The value `q` survives on both sides; only the terminal target `q+3` is
deleted. -/
def Lag8PreviewTerminalExchangeProjection (q r : Nat) : Prop :=
  IsMex (B gameF (q + 3) (r - 1)) (gameF (q + 3) (r - 1)) /\
    q + 3 < gameF (q + 3) (r - 1) /\
    ParkedOnly gameF (q + 3) (r - 1) (q + 3) /\
    (B gameF (q + 3) (r - 1) q /\ B gameF (q + 3) r q) /\
    B gameF (q + 3) (r - 1) (q + 3) /\
    Not (B gameF (q + 3) r (q + 3)) /\
    (forall t, q - 5 < t -> t < q + 3 ->
      q + 3 < gameF t (r - 1))

/-- Common positional envelope forced on either kind of left owner by the
four rail hosts.  The four pairs explicitly record the echo/prehost order,
rather than retaining only the strongest inequality `7 < o`. -/
def Lag8PreviewFourRailOwnerEnvelope (q r g o : Nat) : Prop :=
  o <= g /\
    o < r - 1 /\
    (7 < o /\ o < q - 5) /\
    (5 < o /\ o < q - 4) /\
    (2 < o /\ o < q - 2) /\
    (0 < o /\ o < q - 1)

/-- Diagonal-owner arm: the preview source sees `q` through `R`. -/
def Lag8PreviewLeftDiagonalOwnerArm (q r g d : Nat) : Prop :=
  Lag8PreviewFourRailOwnerEnvelope q r g d /\
    gameF d d = q /\
    R gameF q (r - 1) q

/-- Row-start-owner arm: the preview source sees `q` through `C`. -/
def Lag8PreviewLeftRowStartOwnerArm (q r g s : Nat) : Prop :=
  Lag8PreviewFourRailOwnerEnvelope q r g s /\
    s < q /\
    gameF q s = q /\
    C gameF q (r - 1) q

/-- A host before a row-start owner lies strictly left of the owner.  This
is the row-start analogue of ECHO-LEFT: propagation supplies some earlier
prefix host, and fixed-row injectivity identifies it with the named host. -/
theorem gameF_pre_rowStart_host_strictly_left_of_owner
    {p s t b : Nat}
    (hstart : gameF p s = p)
    (hsp : s < p)
    (hst : s < t)
    (htp : t < p)
    (hbt : b <= t)
    (hhost : gameF t b = p) :
    b < s := by
  rcases rowStartPropagation gameRecurrenceModel
      hstart hsp hst htp with ⟨b', hb's, hb'value⟩
  have hb't : b' <= t := by omega
  have heq : b' = b :=
    gameRecurrenceModel.fixed_q_injective
      hb't hbt (hb'value.trans hhost.symm)
  omega

/-- The four affine rails, in target coordinates. -/
theorem gameF_lag8_preview_fourRailPacket
    {q : Nat} (hq : 26 <= q) :
    Lag8PreviewFourRailPacket q := by
  have h7raw := gameF_col7_rail (q := q - 5) (by omega)
  have h5raw := gameF_col5_rail (q := q - 4) (by omega)
  have h2raw := gameF_col2_rail (q := q - 2) (by omega)
  have h0raw := gameF_col0 (q - 1)
  have h7 : gameF (q - 5) 7 = q := by
    calc
      gameF (q - 5) 7 = (q - 5) + 5 := h7raw
      _ = q := by omega
  have h5 : gameF (q - 4) 5 = q := by
    calc
      gameF (q - 4) 5 = (q - 4) + 4 := h5raw
      _ = q := by omega
  have h2 : gameF (q - 2) 2 = q := by
    calc
      gameF (q - 2) 2 = (q - 2) + 2 := h2raw
      _ = q := by omega
  have h0 : gameF (q - 1) 0 = q := by
    calc
      gameF (q - 1) 0 = (q - 1) + 1 := h0raw
      _ = q := by omega
  exact ⟨h7, h5, h2, h0⟩

/-- All proved lag-eight terminal information is common to both owner arms;
in particular the preview value `q` is present on both sides of the terminal
edge while `q+3` alone is deleted. -/
theorem gameF_lag8_preview_terminalExchangeProjection
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    Lag8PreviewTerminalExchangeProjection q r := by
  have hedge := gameF_lag8_failed_terminal_exchange_packet
    (q := q) (r := r) (g := g)
    (by omega) hrv hstart howners hfailure hra hburn
  have hqBoth := hedge.2.2.2.1 q (by omega) (by omega)
  exact ⟨hedge.1, hedge.2.1, hedge.2.2.1, hqBoth,
    hedge.2.2.2.2.1, hedge.2.2.2.2.2.1,
    hedge.2.2.2.2.2.2⟩

/-- Exact surviving split after combining lag eight, owner coverage, all
four fixed rails, and the terminal singleton exchange.  Neither arm is
eliminated: both reduce to an owner in `(7,r-1)`, with the preview value
entering the preview source through its corresponding `R` or `C` channel. -/
theorem gameF_lag8_preview_leftOwner_exact_twoArm_normalForm
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    Lag8PreviewFourRailPacket q /\
      Lag8PreviewTerminalExchangeProjection q r /\
      ((exists d, Lag8PreviewLeftDiagonalOwnerArm q r g d) \/
        (exists s, Lag8PreviewLeftRowStartOwnerArm q r g s)) := by
  have hrails := gameF_lag8_preview_fourRailPacket hq
  have hedge := gameF_lag8_preview_terminalExchangeProjection
    hq hrv hstart howners hfailure hra hburn
  have hcq : r - 1 <= q - 6 := by omega
  rcases howners q (by omega) (by omega) with
      ⟨d, hdg, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have hdc : d < r - 1 := by omega
    have hdq5 : d < q - 5 := by omega
    have h7d : 7 < d := by
      exact gameF_past_diagonal_echo_strictly_left
        (a := d) (q := q - 5) (r := 7)
        hdq5 (by omega) (hrails.1.trans hdiag.symm)
    have henv : Lag8PreviewFourRailOwnerEnvelope q r g d := by
      exact ⟨hdg, hdc,
        ⟨h7d, by omega⟩,
        ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩⟩
    have hR : R gameF q (r - 1) q := by
      refine ⟨d, by omega, ?_⟩
      have hdcLe : d <= r - 1 := by omega
      simpa [Nat.min_eq_left hdcLe] using hdiag
    exact ⟨hrails, hedge, Or.inl ⟨d, henv, hdiag, hR⟩⟩
  · have hsc : s < r - 1 := by omega
    have hsq5 : s < q - 5 := by omega
    have h7s : 7 < s :=
      gameF_pre_rowStart_host_strictly_left_of_owner
        (p := q) (s := s) (t := q - 5) (b := 7)
        hrow hsq hsq5 (by omega) (by omega) hrails.1
    have henv : Lag8PreviewFourRailOwnerEnvelope q r g s := by
      exact ⟨hsg, hsc,
        ⟨h7s, by omega⟩,
        ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩⟩
    have hC : C gameF q (r - 1) q := ⟨s, hsc, hrow⟩
    exact ⟨hrails, hedge, Or.inr ⟨s, henv, hsq, hrow, hC⟩⟩

#print axioms gameF_pre_rowStart_host_strictly_left_of_owner
#print axioms gameF_lag8_preview_fourRailPacket
#print axioms gameF_lag8_preview_terminalExchangeProjection
#print axioms gameF_lag8_preview_leftOwner_exact_twoArm_normalForm

end ChompLean
