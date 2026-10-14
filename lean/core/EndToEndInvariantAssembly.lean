import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/-!
An abstract conditional composition interface.

Publication audit clarification (2026-10-13): the carrier types, stage
functions, exactness predicates, winning-move predicate, cost function and
budget are arbitrary supplied data. No concrete Chomp instantiation,
initial exact state, oracle restriction or logarithmic running-time bound
is established here. All exactness implications are explicit hypotheses.

The game-specific work is deliberately visible as fields of
`EndToEndInvariantPortfolio`.  In particular, the theorem does not identify
an exact compact state with an exact next state, and it does not hide either
the new right-boundary history or the winning-move bridge inside a generic
"transition is correct" premise.

The concrete project can instantiate the eight carrier types with its
committed state, left descriptor, row ledger, selector history, decision,
post-commit strip ledger, post-commit histories, and Chomp move.
-/

universe uState uLeft uRow uHist uDecision uNextStrip uNextHist uMove

/--
The smallest arrow-by-arrow interface used by the end-to-end reduction.

The fields named `leftInitializerExact`, `stripHolesPacketsExact`,
`rightBoundaryW2Exact`, and `midpointHostedSelectorExact` are the four open
game-specific macro obligations.  `selectorHistoryExact`,
`committedStateExact`, and `winningMoveExact` make the causal ordering and
the two final bookkeeping arrows explicit.
-/
structure EndToEndInvariantPortfolio
    (State : Type uState)
    (Left : Type uLeft)
    (Row : Type uRow)
    (Hist : Type uHist)
    (Decision : Type uDecision)
    (NextStrip : Type uNextStrip)
    (NextHist : Type uNextHist)
    (Move : Type uMove) where
  initializeLeft : Nat -> State -> Left
  sweepRow : Nat -> State -> Left -> Row
  exposeSelectorHistory : Nat -> State -> Row -> Hist
  selectAndCommitLabel : Nat -> State -> Row -> Hist -> Decision
  advanceStrip : Nat -> State -> Left -> Row -> Hist -> Decision -> NextStrip
  updateRightBoundary :
    Nat -> State -> Row -> Hist -> Decision -> NextStrip -> NextHist
  assembleNextState :
    Nat -> State -> Left -> Row -> Hist -> Decision -> NextStrip ->
      NextHist -> State
  emitWinningMove : Nat -> State -> Decision -> Move

  StateExact : Nat -> State -> Prop
  LeftExact : Nat -> State -> Left -> Prop
  RowExact : Nat -> State -> Left -> Row -> Prop
  HistExact : Nat -> State -> Row -> Hist -> Prop
  DecisionExact : Nat -> State -> Row -> Hist -> Decision -> Prop
  NextStripExact : Nat -> State -> Row -> Decision -> NextStrip -> Prop
  NextHistExact : Nat -> State -> NextStrip -> NextHist -> Prop
  WinningMove : Nat -> Move -> Prop

  /-- Exact causal initialization at the first active left-wing cell. -/
  leftInitializerExact :
    forall u s, StateExact u s ->
      LeftExact u s (initializeLeft u s)

  /-- Exact bounded hole/packet/rail sweep of the current thirty-track row. -/
  stripHolesPacketsExact :
    forall u s left,
      StateExact u s -> LeftExact u s left ->
        RowExact u s left (sweepRow u s left)

  /-- Vertical insertion and the proved causal-depth cut produce exact reads. -/
  selectorHistoryExact :
    forall u s left row,
      StateExact u s -> RowExact u s left row ->
        HistExact u s row (exposeSelectorHistory u s row)

  /-- Complete midpoint/hosted selector, including its residual branch. -/
  midpointHostedSelectorExact :
    forall u s left row hist,
      StateExact u s -> RowExact u s left row -> HistExact u s row hist ->
        DecisionExact u s row hist (selectAndCommitLabel u s row hist)

  /-- Post-commit construction of the next compact strip and bounded tails. -/
  committedStripUpdateExact :
    forall u s left row hist decision,
      StateExact u s -> LeftExact u s left -> RowExact u s left row ->
      HistExact u s row hist -> DecisionExact u s row hist decision ->
        NextStripExact u s row decision
          (advanceStrip u s left row hist decision)

  /-- W2: exact new right root; all other roots are recycled or vertically edited. -/
  rightBoundaryW2Exact :
    forall u s row hist decision nextStrip,
      StateExact u s -> HistExact u s row hist ->
      DecisionExact u s row hist decision ->
      NextStripExact u s row decision nextStrip ->
        NextHistExact u s nextStrip
          (updateRightBoundary u s row hist decision nextStrip)

  /-- No unnamed field remains: the listed exact products form the next state. -/
  committedStateExact :
    forall u s left row hist decision nextStrip nextHist,
      StateExact u s -> LeftExact u s left -> RowExact u s left row ->
      HistExact u s row hist -> DecisionExact u s row hist decision ->
      NextStripExact u s row decision nextStrip ->
      NextHistExact u s nextStrip nextHist ->
        StateExact (u + 1)
          (assembleNextState u s left row hist decision nextStrip nextHist)

  /-- The exact range/blocker decision carries the data needed for a move to P. -/
  winningMoveExact :
    forall u s row hist decision,
      StateExact u s -> DecisionExact u s row hist decision ->
        WinningMove u (emitWinningMove u s decision)

  /-- Concrete implementations instantiate this with the charged work of one step. -/
  stepCost : Nat -> Nat
  logBudget : Nat -> Nat
  stepCostWithinLogBudget : forall u, stepCost u <= logBudget u

/--
The conjunction of the portfolio fields closes every intermediate arrow of
one logical step.  This is intentionally stronger than a theorem returning
only the next state: it exposes the exactness certificate at every boundary,
so its stated stage certificates can be inspected. The interface does not
restrict how the supplied functions obtain their values; in particular it
does not prohibit truth-table or oracle access.
-/
theorem endToEnd_step_exact
    {State : Type uState}
    {Left : Type uLeft}
    {Row : Type uRow}
    {Hist : Type uHist}
    {Decision : Type uDecision}
    {NextStrip : Type uNextStrip}
    {NextHist : Type uNextHist}
    {Move : Type uMove}
    (p : EndToEndInvariantPortfolio
      State Left Row Hist Decision NextStrip NextHist Move)
    {u : Nat} {s : State}
    (hs : p.StateExact u s) :
    let left := p.initializeLeft u s
    let row := p.sweepRow u s left
    let hist := p.exposeSelectorHistory u s row
    let decision := p.selectAndCommitLabel u s row hist
    let nextStrip := p.advanceStrip u s left row hist decision
    let nextHist := p.updateRightBoundary u s row hist decision nextStrip
    let nextState :=
      p.assembleNextState u s left row hist decision nextStrip nextHist
    p.LeftExact u s left /\
      p.RowExact u s left row /\
      p.HistExact u s row hist /\
      p.DecisionExact u s row hist decision /\
      p.NextStripExact u s row decision nextStrip /\
      p.NextHistExact u s nextStrip nextHist /\
      p.StateExact (u + 1) nextState := by
  dsimp
  have hleft := p.leftInitializerExact u s hs
  have hrow := p.stripHolesPacketsExact u s _ hs hleft
  have hhist := p.selectorHistoryExact u s _ _ hs hrow
  have hdecision :=
    p.midpointHostedSelectorExact u s _ _ _ hs hrow hhist
  have hnextStrip :=
    p.committedStripUpdateExact u s _ _ _ _
      hs hleft hrow hhist hdecision
  have hnextHist :=
    p.rightBoundaryW2Exact u s _ _ _ _
      hs hhist hdecision hnextStrip
  have hnextState :=
    p.committedStateExact u s _ _ _ _ _ _
      hs hleft hrow hhist hdecision hnextStrip hnextHist
  exact
    ⟨hleft, hrow, hhist, hdecision, hnextStrip, hnextHist, hnextState⟩

/-- The same composed step already contains enough certified data to emit P. -/
theorem endToEnd_emits_winning_move
    {State : Type uState}
    {Left : Type uLeft}
    {Row : Type uRow}
    {Hist : Type uHist}
    {Decision : Type uDecision}
    {NextStrip : Type uNextStrip}
    {NextHist : Type uNextHist}
    {Move : Type uMove}
    (p : EndToEndInvariantPortfolio
      State Left Row Hist Decision NextStrip NextHist Move)
    {u : Nat} {s : State}
    (hs : p.StateExact u s) :
    let left := p.initializeLeft u s
    let row := p.sweepRow u s left
    let hist := p.exposeSelectorHistory u s row
    let decision := p.selectAndCommitLabel u s row hist
    p.WinningMove u (p.emitWinningMove u s decision) := by
  dsimp
  have hleft := p.leftInitializerExact u s hs
  have hrow := p.stripHolesPacketsExact u s _ hs hleft
  have hhist := p.selectorHistoryExact u s _ _ hs hrow
  have hdecision :=
    p.midpointHostedSelectorExact u s _ _ _ hs hrow hhist
  exact p.winningMoveExact u s _ _ _ hs hdecision

/-- Projects the assumed cost inequality. `logBudget` is an arbitrary supplied
function; its name does not impose logarithmic growth or a concrete cost model. -/
theorem endToEnd_step_cost_bound
    {State : Type uState}
    {Left : Type uLeft}
    {Row : Type uRow}
    {Hist : Type uHist}
    {Decision : Type uDecision}
    {NextStrip : Type uNextStrip}
    {NextHist : Type uNextHist}
    {Move : Type uMove}
    (p : EndToEndInvariantPortfolio
      State Left Row Hist Decision NextStrip NextHist Move)
    (u : Nat) :
    p.stepCost u <= p.logBudget u :=
  p.stepCostWithinLogBudget u

#print axioms endToEnd_step_exact
#print axioms endToEnd_emits_winning_move
#print axioms endToEnd_step_cost_bound

end ChompLean
