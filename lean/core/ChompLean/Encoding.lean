import ChompLean.Game
import ChompLean.FiniteInterval

set_option autoImplicit false

namespace ChompLean

def rowStartPos (p r : Nat) (hrp : r <= p) : Pos :=
  mkPos p p r (Nat.le_refl p) hrp

def stolenRectanglePos (p : Nat) : Pos :=
  mkPos p p (p - 1) (Nat.le_refl p) (Nat.sub_le p 1)

def EncodedPosition (q r p : Nat) : Prop :=
  (∃ h_rp : r < p, ∃ _h_pq : p < q,
      IsP (rowStartPos p r (Nat.le_of_lt h_rp))) ∨
  (∃ _h_rp : r < p, ∃ h_qp : q <= p, ∃ h_rq : r <= q,
      IsP (mkPos p q r h_qp h_rq))

def Encodes (f : Nat -> Nat -> Nat) : Prop :=
  ∀ {q r}, r <= q -> EncodedPosition q r (f q r)

def CompleteEncoding (f : Nat -> Nat -> Nat) : Prop :=
  (∀ {p q r} (h_rp : r < p) (_h_pq : p < q),
      IsP (rowStartPos p r (Nat.le_of_lt h_rp)) -> f q r = p) ∧
  (∀ {p q r} (h_qp : q <= p) (h_rq : r <= q),
      IsP (mkPos p q r h_qp h_rq) -> f q r = p)

def EncodedExists : Prop :=
  ∀ {q r}, r <= q -> ∃ p, EncodedPosition q r p

noncomputable def encodedValue (hex : EncodedExists) (q r : Nat) : Nat :=
  if h : r <= q then Classical.choose (hex h) else 0

theorem encodedPosition_unique {q r p₁ p₂ : Nat}
    (h₁ : EncodedPosition q r p₁) (h₂ : EncodedPosition q r p₂) :
    p₁ = p₂ := by
  have no_lt :
      ∀ {a b}, EncodedPosition q r a -> EncodedPosition q r b -> a < b -> False := by
    intro a b ha hb hab
    rcases ha with haDiag | haRow
    · rcases haDiag with ⟨hra, haq, hPa⟩
      rcases hb with hbDiag | hbRow
      · rcases hbDiag with ⟨hrb, _hbq, hPb⟩
        have hmove :
            Move (rowStartPos b r (Nat.le_of_lt hrb))
              (rowStartPos a r (Nat.le_of_lt hra)) := by
          have hm : Move (rowStartPos b r (Nat.le_of_lt hrb))
              (Pos.firstCut (rowStartPos b r (Nat.le_of_lt hrb)) a) :=
            Move.first (rowStartPos b r (Nat.le_of_lt hrb)) a (by omega) hab
          simpa [rowStartPos, mkPos, Pos.firstCut,
            Nat.min_eq_left (Nat.le_of_lt hab),
            Nat.min_eq_right (Nat.le_of_lt hra)] using hm
        exact (isP_no_move_to_P hPb hmove) hPa
      · rcases hbRow with ⟨_hrb, hqb, hrq, hPb⟩
        have hmove :
            Move (mkPos b q r hqb hrq)
              (rowStartPos a r (Nat.le_of_lt hra)) := by
          have hm : Move (mkPos b q r hqb hrq)
              (Pos.firstCut (mkPos b q r hqb hrq) a) :=
            Move.first (mkPos b q r hqb hrq) a (by omega) hab
          simpa [rowStartPos, mkPos, Pos.firstCut,
            Nat.min_eq_left (Nat.le_of_lt haq),
            Nat.min_eq_right (Nat.le_of_lt hra)] using hm
        exact (isP_no_move_to_P hPb hmove) hPa
    · rcases haRow with ⟨hra, hqa, hrq, hPa⟩
      rcases hb with hbDiag | hbRow
      · rcases hbDiag with ⟨_hrb, hbq, _hPb⟩
        omega
      · rcases hbRow with ⟨_hrb, hqb, _hrq, hPb⟩
        have hmove :
            Move (mkPos b q r hqb hrq)
              (mkPos a q r hqa hrq) := by
          have hm : Move (mkPos b q r hqb hrq)
              (Pos.firstCut (mkPos b q r hqb hrq) a) :=
            Move.first (mkPos b q r hqb hrq) a (by omega) hab
          simpa [mkPos, Pos.firstCut,
            Nat.min_eq_right hqa,
            Nat.min_eq_right (Nat.le_trans hrq hqa)] using hm
        exact (isP_no_move_to_P hPb hmove) hPa
  by_cases hlt : p₁ < p₂
  · exact False.elim (no_lt h₁ h₂ hlt)
  by_cases hgt : p₂ < p₁
  · exact False.elim (no_lt h₂ h₁ hgt)
  omega

theorem encodedValue_encodes (hex : EncodedExists) :
    Encodes (encodedValue hex) := by
  intro q r hrq
  dsimp [encodedValue]
  rw [dif_pos hrq]
  exact Classical.choose_spec (hex hrq)

theorem encoded_gt {f : Nat -> Nat -> Nat} (hf : Encodes f)
    {q r : Nat} (hrq : r <= q) :
    r < f q r := by
  rcases hf hrq with hdiag | hrow
  · rcases hdiag with ⟨h_rp, _h_pq, _hP⟩
    exact h_rp
  · rcases hrow with ⟨h_rp, _h_qp, _h_rq, _hP⟩
    exact h_rp

theorem encoded_isP_of_lt {f : Nat -> Nat -> Nat} (hf : Encodes f)
    {q r : Nat} (hrq : r <= q) (hpq : f q r < q) :
    IsP (rowStartPos (f q r) r (Nat.le_of_lt (encoded_gt hf hrq))) := by
  rcases hf hrq with hdiag | hrow
  · rcases hdiag with ⟨h_rp, _h_pq, hP⟩
    exact hP
  · rcases hrow with ⟨_h_rp, h_qp, _h_rq, _hP⟩
    omega

theorem encoded_isP_of_ge {f : Nat -> Nat -> Nat} (hf : Encodes f)
    {q r : Nat} (hrq : r <= q) (hqp : q <= f q r) :
    IsP (mkPos (f q r) q r hqp hrq) := by
  rcases hf hrq with hdiag | hrow
  · rcases hdiag with ⟨_h_rp, h_pq, _hP⟩
    omega
  · rcases hrow with ⟨_h_rp, _h_qp, _h_rq, hP⟩
    exact hP

theorem move_third_same_top {p q b₁ b₂ : Nat}
    (hqp : q <= p) (hb₁q : b₁ <= q) (hb₂q : b₂ <= q)
    (hb : b₁ < b₂) :
    Move (mkPos p q b₂ hqp hb₂q) (mkPos p q b₁ hqp hb₁q) := by
  let src := mkPos p q b₂ hqp hb₂q
  have hm : Move src (Pos.thirdCut src b₁ (Nat.le_of_lt hb)) :=
    Move.third src b₁ hb
  simpa [src, mkPos, Pos.thirdCut] using hm

theorem move_second_to_same_lower {p q a r : Nat}
    (hrq : r <= q) (hqp : q <= p) (har : r <= a) (haq : a < q) :
    Move (mkPos p q r hqp hrq)
      (mkPos p a r (by omega) har) := by
  let src := mkPos p q r hqp hrq
  have hm : Move src (Pos.secondCut src a (Nat.le_of_lt haq)) :=
    Move.second src a haq
  have hmin : Nat.min a r = r := Nat.min_eq_right har
  simpa [src, mkPos, Pos.secondCut, hmin] using hm

theorem move_second_to_min {p q a r : Nat}
    (hrq : r <= q) (hqp : q <= p) (haq : a < q) :
    Move (mkPos p q r hqp hrq)
      (mkPos p a (Nat.min a r) (by omega) (Nat.min_le_left a r)) := by
  let src := mkPos p q r hqp hrq
  have hm : Move src (Pos.secondCut src a (Nat.le_of_lt haq)) :=
    Move.second src a haq
  simpa [src, mkPos, Pos.secondCut] using hm

theorem move_second_to_diagonal {p q a r : Nat}
    (hrq : r <= q) (hqp : q <= p) (har : a <= r) (haq : a < q) :
    Move (mkPos p q r hqp hrq)
      (lowerSquarePos p a (by omega)) := by
  let src := mkPos p q r hqp hrq
  have hm : Move src (Pos.secondCut src a (Nat.le_of_lt haq)) :=
    Move.second src a haq
  have hmin : Nat.min a r = a := Nat.min_eq_left har
  simpa [src, mkPos, lowerSquarePos, Pos.secondCut, hmin] using hm

theorem encoding_fixed_q_injective {f : Nat -> Nat -> Nat} (hf : Encodes f) :
    ∀ {q b₁ b₂}, b₁ <= q -> b₂ <= q -> f q b₁ = f q b₂ -> b₁ = b₂ := by
  intro q b₁ b₂ hb₁q hb₂q heq
  classical
  have no_lt :
      ∀ {s t}, s <= q -> t <= q -> s < t -> f q s = f q t -> False := by
    intro s t hsq htq hst hst_eq
    let p := f q t
    have htp : t < p := encoded_gt hf htq
    by_cases hpq : p < q
    · have hPsrc :
          IsP (rowStartPos p t (Nat.le_of_lt htp)) := by
        dsimp [p]
        exact encoded_isP_of_lt hf htq hpq
      have hPtgt :
          IsP (rowStartPos p s (by omega)) := by
        dsimp [p]
        simpa [hst_eq] using
          (encoded_isP_of_lt hf hsq (by simpa [hst_eq] using hpq))
      have hmove :
          Move (rowStartPos p t (Nat.le_of_lt htp))
            (rowStartPos p s (by omega)) := by
        simpa [rowStartPos] using
          (move_third_same_top (p := p) (q := p) (b₁ := s) (b₂ := t)
            (Nat.le_refl p) (by omega) (Nat.le_of_lt htp) hst)
      exact (isP_no_move_to_P hPsrc hmove) hPtgt
    · have hqp : q <= p := Nat.le_of_not_gt hpq
      have hPsrc : IsP (mkPos p q t hqp htq) := by
        dsimp [p]
        exact encoded_isP_of_ge hf htq hqp
      have hPtgt : IsP (mkPos p q s hqp hsq) := by
        dsimp [p]
        simpa [hst_eq] using
          (encoded_isP_of_ge hf hsq (by simpa [hst_eq] using hqp))
      have hmove :
          Move (mkPos p q t hqp htq) (mkPos p q s hqp hsq) :=
        move_third_same_top hqp hsq htq hst
      exact (isP_no_move_to_P hPsrc hmove) hPtgt
  by_cases hlt : b₁ < b₂
  · exact False.elim (no_lt hb₁q hb₂q hlt heq)
  by_cases hgt : b₂ < b₁
  · exact False.elim (no_lt hb₂q hb₁q hgt heq.symm)
  omega

theorem encoding_diagonal_no_attack {f : Nat -> Nat -> Nat} (hf : Encodes f) :
    ∀ {a b p}, a < b -> b < p -> f a a = p -> f b b = p -> False := by
  intro a b p hab hbp ha hb
  have hPsrc : IsP (lowerSquarePos p b (Nat.le_of_lt hbp)) := by
    simpa [lowerSquarePos, hb] using
      (encoded_isP_of_ge hf (Nat.le_refl b) (by rw [hb]; omega))
  have hPtgt : IsP (lowerSquarePos p a (by omega)) := by
    simpa [lowerSquarePos, ha] using
      (encoded_isP_of_ge hf (Nat.le_refl a) (by rw [ha]; omega))
  have hmove :
      Move (lowerSquarePos p b (Nat.le_of_lt hbp))
        (lowerSquarePos p a (by omega)) := by
    simpa [lowerSquarePos] using
      (move_second_to_diagonal (p := p) (q := b) (a := a) (r := b)
        (Nat.le_refl b) (Nat.le_of_lt hbp) (by omega) hab)
  exact (isP_no_move_to_P hPsrc hmove) hPtgt

theorem encoding_rowstart_diagonal_attack {f : Nat -> Nat -> Nat}
    (hf : Encodes f) :
    ∀ {p r a}, f p r = p -> r < p -> f a a = p -> a <= r -> False := by
  intro p r a hstart hrp hdiag har
  have hap : a < p := by
    have := encoded_gt hf (Nat.le_refl a)
    omega
  have hPsrc : IsP (rowStartPos p r (Nat.le_of_lt hrp)) := by
    simpa [rowStartPos, hstart] using
      (encoded_isP_of_ge hf (Nat.le_of_lt hrp)
        (by rw [hstart]; exact Nat.le_refl p))
  have hPtgt : IsP (lowerSquarePos p a (by omega)) := by
    simpa [lowerSquarePos, hdiag] using
      (encoded_isP_of_ge hf (Nat.le_refl a) (by rw [hdiag]; omega))
  have hmove :
      Move (rowStartPos p r (Nat.le_of_lt hrp))
        (lowerSquarePos p a (by omega)) := by
    simpa [rowStartPos, lowerSquarePos] using
      (move_second_to_diagonal (p := p) (q := p) (a := a) (r := r)
        (Nat.le_of_lt hrp) (Nat.le_refl p) har hap)
  exact (isP_no_move_to_P hPsrc hmove) hPtgt

theorem encoding_diagonal_general_no_attack {f : Nat -> Nat -> Nat}
    (hf : Encodes f) :
    ∀ {i s q}, i < s -> s <= q -> f i i = f q s -> False := by
  intro i s q his hsq heq
  have hsm : s < f q s := encoded_gt hf hsq
  have him : i < f i i := encoded_gt hf (Nat.le_refl i)
  have hPtgt : IsP (lowerSquarePos (f q s) i (by omega)) := by
    simpa [lowerSquarePos, heq] using
      (encoded_isP_of_ge hf (Nat.le_refl i) (by rw [heq]; omega))
  by_cases hmq : f q s < q
  · have hPsrc : IsP (rowStartPos (f q s) s (Nat.le_of_lt hsm)) :=
      encoded_isP_of_lt hf hsq hmq
    have hmove :
        Move (rowStartPos (f q s) s (Nat.le_of_lt hsm))
          (lowerSquarePos (f q s) i (by omega)) := by
      simpa [rowStartPos, lowerSquarePos] using
        (move_second_to_diagonal (p := f q s) (q := f q s) (a := i) (r := s)
          (Nat.le_of_lt hsm) (Nat.le_refl (f q s)) (Nat.le_of_lt his) (by omega))
    exact (isP_no_move_to_P hPsrc hmove) hPtgt
  · have hqm : q <= f q s := Nat.le_of_not_gt hmq
    have hPsrc : IsP (mkPos (f q s) q s hqm hsq) := encoded_isP_of_ge hf hsq hqm
    have hmove :
        Move (mkPos (f q s) q s hqm hsq) (lowerSquarePos (f q s) i (by omega)) := by
      simpa using
        (move_second_to_diagonal (p := f q s) (q := q) (a := i) (r := s)
          hsq hqm (Nat.le_of_lt his) (by omega))
    exact (isP_no_move_to_P hPsrc hmove) hPtgt

theorem encoding_rowstart_no_middle {f : Nat -> Nat -> Nat} (hf : Encodes f) :
    ∀ {p r q}, f p r = p -> r < q -> q < p -> f q r ≠ p := by
  intro p r q hstart hrq hqp hmid
  have hrp : r < p := by omega
  have hPsrc : IsP (rowStartPos p r (Nat.le_of_lt hrp)) := by
    simpa [rowStartPos, hstart] using
      (encoded_isP_of_ge hf (Nat.le_of_lt hrp)
        (by rw [hstart]; exact Nat.le_refl p))
  have hPtgt : IsP (mkPos p q r (Nat.le_of_lt hqp) (Nat.le_of_lt hrq)) := by
    simpa [hmid] using
      (encoded_isP_of_ge hf (Nat.le_of_lt hrq) (by rw [hmid]; omega))
  have hmove :
      Move (rowStartPos p r (Nat.le_of_lt hrp))
        (mkPos p q r (Nat.le_of_lt hqp) (Nat.le_of_lt hrq)) := by
    simpa [rowStartPos] using
      (move_second_to_same_lower (p := p) (q := p) (a := q) (r := r)
        (Nat.le_of_lt hrp) (Nat.le_refl p) (Nat.le_of_lt hrq) hqp)
  exact (isP_no_move_to_P hPsrc hmove) hPtgt

theorem encoding_same_lower_no_repeat {f : Nat -> Nat -> Nat} (hf : Encodes f) :
    ∀ {s t₁ t₂ p},
      s < t₁ -> t₁ < t₂ -> t₂ < p ->
      f t₁ s = p -> f t₂ s = p -> False := by
  intro s t₁ t₂ p hst₁ ht₁t₂ ht₂p ht₁ ht₂
  have hs_le_t₂ : s <= t₂ := by omega
  have ht₂_le_ft₂ : t₂ <= f t₂ s := by
    rw [ht₂]
    exact Nat.le_of_lt ht₂p
  have hPsrc : IsP (mkPos p t₂ s (Nat.le_of_lt ht₂p) (by omega)) := by
    simpa [ht₂] using
      (encoded_isP_of_ge hf hs_le_t₂ ht₂_le_ft₂)
  have ht₁_le_ft₁ : t₁ <= f t₁ s := by
    rw [ht₁]
    omega
  have hPtgt : IsP (mkPos p t₁ s (by omega) (Nat.le_of_lt hst₁)) := by
    simpa [ht₁] using
      (encoded_isP_of_ge hf (Nat.le_of_lt hst₁) ht₁_le_ft₁)
  have hmove :
      Move (mkPos p t₂ s (Nat.le_of_lt ht₂p) (by omega))
        (mkPos p t₁ s (by omega) (Nat.le_of_lt hst₁)) := by
    simpa using
      (move_second_to_same_lower (p := p) (q := t₂) (a := t₁) (r := s)
        (by omega) (Nat.le_of_lt ht₂p) (Nat.le_of_lt hst₁) ht₁t₂)
  exact (isP_no_move_to_P hPsrc hmove) hPtgt

theorem interval_reply_bounds {f : Nat -> Nat -> Nat}
    (hf : Encodes f) (hcomplete : CompleteEncoding f) :
    ∀ {r q p t s},
      s < r -> r < q -> q < t -> t < p ->
      f t s = p ->
      (¬ ∃ b, b < r ∧ f q b = p) ->
      q < f q s ∧ f q s < p := by
  intro r q p t s hsr hrq hqt htp hfts hnotC
  let src := mkPos p t s (by omega) (by omega)
  let opt := mkPos p q s (by omega) (by omega)
  have hPsrc : IsP src := by
    have ht_le_fts : t <= f t s := by
      rw [hfts]
      exact Nat.le_of_lt htp
    simpa [src, hfts] using
      (encoded_isP_of_ge hf (by omega) ht_le_fts)
  have hsrc_to_opt : Move src opt := by
    simpa [src, opt] using
      (move_second_to_same_lower (p := p) (q := t) (a := q) (r := s)
        (by omega) (by omega) (by omega) hqt)
  have hnot_opt : ¬ IsP opt := isP_no_move_to_P hPsrc hsrc_to_opt
  have hopt_pos : 0 < opt.p := by
    dsimp [opt, mkPos]
    omega
  rcases not_isP_has_move_to_P hopt_pos hnot_opt with ⟨y, hyMove, hyP⟩
  cases hyMove with
  | first u hu0 hu =>
      have hup : u < p := by
        simpa [opt, mkPos] using hu
      have hqu : q < u := by
        by_cases hqu : q < u
        · exact hqu
        · have huq : u <= q := Nat.le_of_not_gt hqu
          have hsrcMove : Move src (Pos.firstCut opt u) := by
            have hm : Move src (Pos.firstCut src u) :=
              Move.first src u hu0 hup
            simpa [src, opt, mkPos, Pos.firstCut,
              Nat.min_eq_left huq,
              Nat.min_eq_left (by omega : u <= t)]
              using hm
          exact False.elim ((isP_no_move_to_P hPsrc hsrcMove) hyP)
      have hyGeneral : IsP (mkPos u q s (Nat.le_of_lt hqu) (by omega)) := by
        simpa [opt, mkPos, Pos.firstCut,
          Nat.min_eq_right (Nat.le_of_lt hqu),
          Nat.min_eq_right (by omega : s <= u)]
          using hyP
      have hfqs : f q s = u :=
        hcomplete.2 (p := u) (q := q) (r := s)
          (Nat.le_of_lt hqu) (by omega) hyGeneral
      omega
  | second a ha =>
      have haq : a < q := by
        simpa [opt, mkPos] using ha
      have hsrcMove : Move src (Pos.secondCut opt a (Nat.le_of_lt haq)) := by
        have hat : a < t := by omega
        have hm : Move src (Pos.secondCut src a (Nat.le_of_lt hat)) :=
          Move.second src a hat
        simpa [src, opt, mkPos, Pos.secondCut] using hm
      exact False.elim ((isP_no_move_to_P hPsrc hsrcMove) hyP)
  | third b hb =>
      have hbs : b < s := by
        simpa [opt, mkPos] using hb
      have hyGeneral : IsP (mkPos p q b (by omega) (by omega)) := by
        simpa [opt, mkPos, Pos.thirdCut] using hyP
      have hfqb : f q b = p :=
        hcomplete.2 (p := p) (q := q) (r := b)
          (by omega) (by omega) hyGeneral
      exact False.elim (hnotC ⟨b, by omega, hfqb⟩)

theorem rectangle_to_stolen (p : Nat) (hp : 0 < p) :
    Move (rectanglePos p) (stolenRectanglePos p) := by
  have hb : p - 1 < p := by omega
  have hm : Move (rectanglePos p)
      (Pos.thirdCut (rectanglePos p) (p - 1) (Nat.le_of_lt hb)) :=
    Move.third (rectanglePos p) (p - 1) hb
  simpa [rectanglePos, stolenRectanglePos, lowerSquarePos, mkPos, Pos.thirdCut] using hm

theorem stolen_move_lifts {p : Nat} (hp : 0 < p) {y : Pos} :
    Move (stolenRectanglePos p) y -> Move (rectanglePos p) y := by
  intro h
  cases h with
  | first a ha0 ha =>
      have ha_p : a < p := by
        simpa [stolenRectanglePos, mkPos] using ha
      have ha_le_pred : a <= p - 1 := by omega
      have hm : Move (rectanglePos p) (Pos.firstCut (rectanglePos p) a) :=
        Move.first (rectanglePos p) a ha0 ha_p
      simpa [rectanglePos, stolenRectanglePos, lowerSquarePos, mkPos,
        Pos.firstCut, Nat.min_eq_left (Nat.le_of_lt ha_p), Nat.min_eq_left ha_le_pred]
        using hm
  | second a ha =>
      have ha_p : a < p := by
        simpa [stolenRectanglePos, mkPos] using ha
      have ha_le_pred : a <= p - 1 := by omega
      have hm : Move (rectanglePos p)
          (Pos.secondCut (rectanglePos p) a (Nat.le_of_lt ha_p)) :=
        Move.second (rectanglePos p) a ha_p
      simpa [rectanglePos, stolenRectanglePos, lowerSquarePos, mkPos,
        Pos.secondCut, Nat.min_eq_left (Nat.le_of_lt ha_p), Nat.min_eq_left ha_le_pred]
        using hm
  | third b hb =>
      have hb_pred : b < p - 1 := by
        simpa [stolenRectanglePos, mkPos] using hb
      have hb_rect : b < p := by omega
      have hm : Move (rectanglePos p)
          (Pos.thirdCut (rectanglePos p) b (Nat.le_of_lt hb_rect)) :=
        Move.third (rectanglePos p) b hb_rect
      simpa [rectanglePos, stolenRectanglePos, lowerSquarePos, mkPos, Pos.thirdCut]
        using hm

theorem rectangle_not_isP (p : Nat) (hp : 0 < p) :
    ¬ IsP (rectanglePos p) := by
  intro hrect
  have hsteal : Move (rectanglePos p) (stolenRectanglePos p) :=
    rectangle_to_stolen p hp
  have hnot_stolen : ¬ IsP (stolenRectanglePos p) :=
    isP_no_move_to_P hrect hsteal
  have hpos : 0 < (stolenRectanglePos p).p := by
    simpa [stolenRectanglePos, mkPos] using hp
  rcases not_isP_has_move_to_P hpos hnot_stolen with ⟨y, hyMove, hyP⟩
  have hrectMove : Move (rectanglePos p) y := stolen_move_lifts hp hyMove
  exact (isP_no_move_to_P hrect hrectMove) hyP

theorem encodedValue_complete (hex : EncodedExists) :
    CompleteEncoding (encodedValue hex) := by
  constructor
  · intro p q r h_rp h_pq hP
    have hrq : r <= q := by omega
    have hchosen : EncodedPosition q r (encodedValue hex q r) :=
      encodedValue_encodes hex hrq
    have hthis : EncodedPosition q r p :=
      Or.inl ⟨h_rp, h_pq, hP⟩
    exact encodedPosition_unique hchosen hthis
  · intro p q r h_qp h_rq hP
    have hp_pos : 0 < p := by
      simpa [mkPos] using isP_pos hP
    have h_rp : r < p := by
      by_cases hlt : r < p
      · exact hlt
      · exfalso
        have hge : p <= r := Nat.le_of_not_gt hlt
        have hq_eq : q = p := by omega
        have hr_eq : r = p := by omega
        have hpos_eq : mkPos p q r h_qp h_rq = rectanglePos p := by
          apply Pos.ext <;> simp [mkPos, rectanglePos, lowerSquarePos, hq_eq, hr_eq]
        exact (rectangle_not_isP p hp_pos) (by simpa [hpos_eq] using hP)
    have hchosen : EncodedPosition q r (encodedValue hex q r) :=
      encodedValue_encodes hex h_rq
    have hthis : EncodedPosition q r p :=
      Or.inr ⟨h_rp, h_qp, h_rq, hP⟩
    exact encodedPosition_unique hchosen hthis

theorem opening_cover_of_complete {f : Nat -> Nat -> Nat}
    (hcomplete : CompleteEncoding f) :
    ∀ {p}, 0 < p ->
      (∃ a, a < p ∧ f a a = p) ∨
      (∃ r, r < p ∧ f p r = p) := by
  intro p hp
  have hnot_rect : ¬ IsP (rectanglePos p) := rectangle_not_isP p hp
  have hpos : 0 < (rectanglePos p).p := by
    simpa [rectanglePos, lowerSquarePos, mkPos] using hp
  rcases not_isP_has_move_to_P hpos hnot_rect with ⟨y, hmove, hyP⟩
  cases hmove with
  | first a ha0 ha =>
      have ha_p : a < p := by
        simpa [rectanglePos, lowerSquarePos, mkPos] using ha
      have hyRect : IsP (rectanglePos a) := by
        simpa [rectanglePos, lowerSquarePos, mkPos, Pos.firstCut,
          Nat.min_eq_left (Nat.le_of_lt ha_p)] using hyP
      exact False.elim ((rectangle_not_isP a ha0) hyRect)
  | second a ha =>
      have ha_p : a < p := by
        simpa [rectanglePos, lowerSquarePos, mkPos] using ha
      left
      refine ⟨a, ha_p, ?_⟩
      have hySquare : IsP (lowerSquarePos p a (Nat.le_of_lt ha_p)) := by
        simpa [rectanglePos, lowerSquarePos, mkPos, Pos.secondCut,
          Nat.min_eq_left (Nat.le_of_lt ha_p)] using hyP
      simpa [lowerSquarePos] using
        hcomplete.2 (p := p) (q := a) (r := a)
          (Nat.le_of_lt ha_p) (Nat.le_refl a) hySquare
  | third r hr =>
      right
      refine ⟨r, hr, ?_⟩
      have hyRow : IsP (rowStartPos p r (Nat.le_of_lt hr)) := by
        simpa [rectanglePos, rowStartPos, lowerSquarePos, mkPos, Pos.thirdCut]
          using hyP
      simpa [rowStartPos] using
        hcomplete.2 (p := p) (q := p) (r := r)
          (Nat.le_refl p) (Nat.le_of_lt hr) hyRow

theorem first_cut_P_encodes {p q r u : Nat}
    (hrq : r <= q) (hqp : q <= p)
    (hu0 : 0 < u) (_hup : u < p)
    (hP : IsP (Pos.firstCut (mkPos p q r hqp hrq) u)) :
    EncodedPosition q r u := by
  have hru : r < u := by
    by_cases h : r < u
    · exact h
    · have hur : u <= r := Nat.le_of_not_gt h
      have huq : u <= q := Nat.le_trans hur hrq
      have hrect : IsP (rectanglePos u) := by
        simpa [mkPos, rectanglePos, lowerSquarePos, Pos.firstCut,
          Nat.min_eq_left huq, Nat.min_eq_left hur] using hP
      exact False.elim ((rectangle_not_isP u hu0) hrect)
  by_cases huq_lt : u < q
  · left
    refine ⟨hru, huq_lt, ?_⟩
    have hur_le : r <= u := Nat.le_of_lt hru
    have huq_le : u <= q := Nat.le_of_lt huq_lt
    simpa [mkPos, rowStartPos, Pos.firstCut,
      Nat.min_eq_left huq_le, Nat.min_eq_right hur_le] using hP
  · right
    have hqu : q <= u := Nat.le_of_not_gt huq_lt
    refine ⟨hru, hqu, hrq, ?_⟩
    have hru_le : r <= u := Nat.le_trans hrq hqu
    simpa [mkPos, Pos.firstCut,
      Nat.min_eq_right hqu, Nat.min_eq_right hru_le] using hP

theorem encoded_exists_from_game : EncodedExists := by
  classical
  let P : Nat -> Prop :=
    fun n => ∀ q r, r <= q -> q + r = n -> ∃ p, EncodedPosition q r p
  have hPall : ∀ n, P n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro q r hrq hsum
        let secondBlocker : Nat -> Nat := fun a =>
          if ha : a < q then
            Classical.choose
              (ih (a + Nat.min a r)
                (by
                  have hmin : Nat.min a r <= r := Nat.min_le_right a r
                  omega)
                a (Nat.min a r) (Nat.min_le_left a r) rfl)
          else
            0
        let thirdBlocker : Nat -> Nat := fun b =>
          if hb : b < r then
            Classical.choose
              (ih (q + b)
                (by omega)
                q b (by omega) rfl)
          else
            0
        have second_spec :
            ∀ {a}, a < q ->
              EncodedPosition a (Nat.min a r) (secondBlocker a) := by
          intro a ha
          dsimp [secondBlocker]
          rw [dif_pos ha]
          exact Classical.choose_spec
            (ih (a + Nat.min a r)
              (by
                have hmin : Nat.min a r <= r := Nat.min_le_right a r
                omega)
              a (Nat.min a r) (Nat.min_le_left a r) rfl)
        have third_spec :
            ∀ {b}, b < r -> EncodedPosition q b (thirdBlocker b) := by
          intro b hb
          dsimp [thirdBlocker]
          rw [dif_pos hb]
          exact Classical.choose_spec
            (ih (q + b) (by omega) q b (by omega) rfl)
        let blocked :=
          (List.range q).map secondBlocker ++ (List.range r).map thirdBlocker
        let p := q + blocked.sum + 1
        have hqp : q <= p := by
          dsimp [p]
          omega
        have hp_pos : 0 < p := by
          dsimp [p]
          omega
        have hrp : r < p := by
          dsimp [p]
          omega
        have hp_notmem : p ∉ blocked := by
          intro hmem
          have hle := List.mem_le_sum hmem
          dsimp [p] at hle
          omega
        let x := mkPos p q r hqp hrq
        by_cases hfirst :
            ∃ u, 0 < u ∧ u < p ∧ IsP (Pos.firstCut x u)
        · rcases hfirst with ⟨u, hu0, hup, huP⟩
          refine ⟨u, ?_⟩
          exact first_cut_P_encodes hrq hqp hu0 hup (by simpa [x] using huP)
        · have hxP : IsP x := by
            apply isP_of_no_cut_replies x hp_pos
            · intro a ha0 ha haP
              exact hfirst ⟨a, ha0, ha, haP⟩
            · intro a ha haP
              have haq : a < q := by
                simpa [x, mkPos] using ha
              have hap : a <= p := by omega
              have htarget :
                  IsP (mkPos p a (Nat.min a r) hap
                    (Nat.min_le_left a r)) := by
                simpa [x, mkPos, Pos.secondCut] using haP
              have hthis :
                  EncodedPosition a (Nat.min a r) p := by
                right
                refine ⟨?_, hap, Nat.min_le_left a r, htarget⟩
                have hmin : Nat.min a r <= a := Nat.min_le_left a r
                omega
              have heq : secondBlocker a = p :=
                encodedPosition_unique (second_spec haq) hthis
              have hmem_second : p ∈ (List.range q).map secondBlocker := by
                exact List.mem_map.mpr ⟨a, List.mem_range.mpr haq, heq⟩
              exact hp_notmem (List.mem_append_left _ hmem_second)
            · intro b hb hbP
              have hbr : b < r := by
                simpa [x, mkPos] using hb
              have hbq : b <= q := by omega
              have htarget : IsP (mkPos p q b hqp hbq) := by
                simpa [x, mkPos, Pos.thirdCut] using hbP
              have hthis : EncodedPosition q b p := by
                right
                refine ⟨by omega, hqp, hbq, htarget⟩
              have heq : thirdBlocker b = p :=
                encodedPosition_unique (third_spec hbr) hthis
              have hmem_third : p ∈ (List.range r).map thirdBlocker := by
                exact List.mem_map.mpr ⟨b, List.mem_range.mpr hbr, heq⟩
              exact hp_notmem (List.mem_append_right _ hmem_third)
          refine ⟨p, ?_⟩
          right
          exact ⟨hrp, hqp, hrq, by simpa [x] using hxP⟩
  intro q r hrq
  exact hPall (q + r) q r hrq rfl

end ChompLean
