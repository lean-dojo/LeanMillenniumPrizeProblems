import YangMills.OversubtractedFlow

/-!
# Connected multi-insertion flow and exact cumulant link

FHH (80)–(85), (93). Proper insertion bipartitions are counted ONCE by
anchoring original index zero in the left block; the source consequently
has no extra half factor. Both insertion and external Koszul unshuffles
are explicit. Connected multi-insertion amplitudes have zero UV boundary.
Their moments are linked to the SAME G_0=product(single)-hbar F_0, so this
module cannot add an unrelated connected sector to the prescription.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def selectedInsertions (input : List (PositionedInsertion G))
    (s : Finset (Fin input.length)) : List (PositionedInsertion G) :=
  (selectedIndices s).map input.get

def insertionComplement (input : List (PositionedInsertion G))
    (s : Finset (Fin input.length)) : Finset (Fin input.length) := Finset.univ \ s

def insertionUnshuffleSign (input : List (PositionedInsertion G))
    (s : Finset (Fin input.length)) : ℂ :=
  (-1 : ℂ) ^ (∑ i ∈ s, ∑ j ∈ insertionComplement input s,
    if j < i ∧ (input.get i).monomial.parity = true ∧
      (input.get j).monomial.parity = true then 1 else 0)

def insertionListParity (input : List (PositionedInsertion G)) : Bool :=
  decide (inputOddMultiplicity input % 2 = 1)

def insertionPermutationSign (input : List (PositionedInsertion G))
    (permutation : Equiv.Perm (Fin input.length)) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin input.length, ∑ j : Fin input.length,
    if i < j ∧ permutation j < permutation i ∧
      (input.get (permutation i)).monomial.parity = true ∧
      (input.get (permutation j)).monomial.parity = true then 1 else 0)

/-- Canonical orientation of each unordered proper bipartition. -/
def anchoredInsertionSplits (input : List (PositionedInsertion G)) :
    Finset (Finset (Fin input.length)) := by
  classical
  exact (Finset.univ : Finset (Fin input.length)).powerset.filter
    (fun s => s ≠ Finset.univ ∧ ∃ i ∈ s, i.val = 0)

def connectedInsertionSource (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ s ∈ anchoredInsertionSplits input,
    insertionUnshuffleSign input s *
      independentContractionRHS (insertionListParity (selectedInsertions input s))
        (L (selectedInsertions input s))
        (L (selectedInsertions input (insertionComplement input s))) loop Λ UV legs q

def connectedInsertionRHS (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  insertionHomogeneousRHS (L []) (L input) loop Λ UV legs q -
    connectedInsertionSource L input loop Λ UV legs q

/-- A partition is encoded uniquely by sending each index to the least
index of its block. No enumeration-dependent multiplicity is introduced. -/
def canonicalInsertionPartitions (n : ℕ) : Finset (Fin n → Fin n) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i, f i ≤ i ∧ f (f i) = f i)

def partitionBlock (input : List (PositionedInsertion G))
    (partition : Fin input.length → Fin input.length) (block : Fin input.length) :
    List (PositionedInsertion G) :=
  selectedInsertions input (Finset.univ.filter (fun i => partition i = block))

def partitionRoots {n : ℕ} (partition : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => partition i = i)

def partitionKoszulSign (input : List (PositionedInsertion G))
    (partition : Fin input.length → Fin input.length) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin input.length, ∑ j : Fin input.length,
    if i < j ∧ partition j < partition i ∧ (input.get i).monomial.parity = true ∧
      (input.get j).monomial.parity = true then 1 else 0)

def partitionConnectedProduct (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) (partition : Fin input.length → Fin input.length) :
    FlowFamily G :=
  ((selectedIndices (partitionRoots partition)).map
    (fun block => L (partitionBlock input partition block))).foldl flowProduct flowUnit

/-- Source (85): a block partition contributes (-hbar)^(n-numberOfBlocks).
The whole coefficient is a finite exact hbar Cauchy product. -/
def connectedMoment (L : InsertedFlowFamily G) (input : List (PositionedInsertion G)) :
    FlowFamily G :=
  fun loop Λ UV legs q => ∑ p ∈ canonicalInsertionPartitions input.length,
    let shift := input.length - (partitionRoots p).card
    if shift ≤ loop then
      partitionKoszulSign input p * (-1 : ℂ) ^ shift *
        partitionConnectedProduct L input p (loop - shift) Λ UV legs q
    else 0

/-- The connected hierarchy is fixed by actual equations, and its moment
is constrained to be the previously constructed SAME oversubtracted G_0. -/
structure ConnectedInsertionFlowConditions (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) : Prop where
  graded_external : ∀ input loop Λ UV legs q (permutation : Equiv.Perm (Fin legs.length)),
    input ≠ [] →
    L input loop Λ UV (permutedLegs legs permutation) (permutedMomenta legs permutation q) =
      permutationSign legs permutation * L input loop Λ UV legs q
  graded_insertions : ∀ input loop Λ UV legs q (permutation : Equiv.Perm (Fin input.length)),
    L (List.ofFn (fun i => input.get (permutation i))) loop Λ UV legs q =
      insertionPermutationSign input permutation * L input loop Λ UV legs q
  ultraviolet : ∀ input loop UV, 2 ≤ input.length → 0 < UV → L input loop UV UV = 0
  smooth : ∀ input loop Λ UV legs, input ≠ [] → 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (L input loop Λ UV legs)
  scale_jet_continuous : ∀ input loop UV legs
      (directions : List (Fin legs.length × Fin 4)) q, input ≠ [] →
    ContinuousOn (fun Λ : ℝ => momentumJet directions (L input loop Λ UV legs) q)
      (Set.Ioc 0 UV)
  loop_integrable : ∀ input loop Λ UV legs q, input ≠ [] → 0 < Λ → Λ < UV →
    Integrable (linearFlowIntegrand (L input) loop Λ UV legs q)
  source_integrable : ∀ input s loop Λ UV legs q, s ∈ anchoredInsertionSplits input →
    0 < Λ → Λ < UV → Integrable
      (independentContractionIntegrand (insertionListParity (selectedInsertions input s))
        (L (selectedInsertions input s))
        (L (selectedInsertions input (insertionComplement input s))) loop Λ UV legs q)
  flow : ∀ input loop Λ UV legs q, input ≠ [] → 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => L input loop scale UV legs q)
      (connectedInsertionRHS L input loop Λ UV legs q) Λ
  moment_same : ∀ input loop Λ UV legs q, input ≠ [] → 0 < Λ → Λ ≤ UV →
    connectedMoment L input loop Λ UV legs q =
      disconnectedFunctional L F 0 input loop Λ UV legs q
  translation : ∀ input y loop Λ UV legs q, input ≠ [] →
    L input loop Λ UV legs q =
      Complex.exp (-Complex.I * (euclideanPair y (∑ i : Fin legs.length, q i) : ℂ)) *
        L (shiftInsertions input y) loop Λ UV legs q

/-- Connected normalization carries hbar^(1-s); the graph grading therefore
has the crucial +2(s-1) term for s insertions. Negative powers are zero. -/
structure CoupledConnectedInsertionFlowConditions (L : ℝ → InsertedFlowFamily G)
    (F : ℝ → OversubtractedFamily G) : Prop where
  per_coupling : ∀ g, ConnectedInsertionFlowConditions (L g) (F g)
  joint_smooth : ∀ input loop Λ UV legs, input ≠ [] → 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (fun gq : ℝ × (Fin legs.length → Spacetime) =>
      L gq.1 input loop Λ UV legs gq.2)
  graph_grading : ∀ g input loop Λ UV legs q, input ≠ [] →
    L g input loop Λ UV legs q =
      if (input.map (fun a => a.monomial.legs.length)).sum ≤
          legs.length + 2 * loop + 2 * (input.length - 1) then
        (g : ℂ) ^ (legs.length + 2 * loop + 2 * (input.length - 1) -
          (input.map (fun a => a.monomial.legs.length)).sum) *
            L 1 input loop Λ UV legs q
      else 0

end YangMills.PerturbativeFlow
