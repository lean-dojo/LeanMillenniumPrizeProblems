import Problems.YangMills.PerturbativeFlow

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Ordered composite projectors and regulated OPE extraction

The coefficient projector is Fröb--Holland (1603.08012), eq.(4.1).
Finite local monomials use the actual fields/antifields and their fixed
engineering dimensions; odd jet generators have multiplicity at most one.
The OPE recursion is eqs.(5.5)--(5.7), at IR scale mu rather than zero.
This module does not let a candidate assign OPE coefficients independently
of the insertion amplitudes. Flow and boundary conditions fixing those
amplitudes are separate, concrete obligations.
-/
noncomputable section
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative

variable {G : CompactSimpleGaugeGroup}

abbrev JetVariable (G : CompactSimpleGaugeGroup) := ExternalLeg G × (Fin 4 → ℕ)
abbrev LocalMonomial (G : CompactSimpleGaugeGroup) := JetVariable G →₀ ℕ

def JetVariable.dimension (v : JetVariable G) : ℕ :=
  ExternalLeg.dimension v.1 + ∑ μ : Fin 4, v.2 μ

def LocalMonomial.dimension (m : LocalMonomial G) : ℕ :=
  m.sum (fun v n => n * JetVariable.dimension v)

/-- Exterior-algebra nilpotence, not an arbitrary label restriction. -/
def LocalMonomial.Admissible (m : LocalMonomial G) : Prop :=
  ∀ v, ExternalLeg.parity v.1 = true → m v ≤ 1

def jetCode (v : JetVariable G) : ℕ := by
  classical
  letI : Encodable (ExternalLeg G) := Fintype.toEncodable _
  exact Encodable.encode v

def isBasicJet (v : JetVariable G) : Bool := v.1.isLeft

theorem external_dimension_pos (k : ExternalLeg G) : 0 < ExternalLeg.dimension k := by
  cases k with
  | inl k => cases k <;> norm_num [ExternalLeg.dimension, BasicField.dimension]
  | inr k => cases k <;> norm_num [ExternalLeg.dimension, BasicField.dimension]

theorem jet_dimension_pos (v : JetVariable G) : 0 < JetVariable.dimension v := by
  have h := external_dimension_pos v.1
  unfold JetVariable.dimension
  omega

/-- A fixed order of generators, with basic fields before antifields as in
(4.1). Encoding orders jets within each block; odd reordering is not free. -/
def LocalMonomial.orderedJets (m : LocalMonomial G) : List (JetVariable G) :=
  let raw := (m.support.toList.mergeSort (fun a b => jetCode a ≤ jetCode b)).flatMap
    (fun v => List.replicate (m v) v)
  raw.filter isBasicJet ++ raw.filter (fun v => !isBasicJet v)

def LocalMonomial.legs (m : LocalMonomial G) : List (ExternalLeg G) :=
  m.orderedJets.map Prod.fst

def LocalMonomial.jetAt (m : LocalMonomial G) (i : Fin m.legs.length) : JetVariable G :=
  m.orderedJets.get ⟨i.val, by simpa [LocalMonomial.legs] using i.isLt⟩

/-- One derivative direction for every momentum multiindex entry. -/
def LocalMonomial.momentumDirections (m : LocalMonomial G) :
    List (Fin m.legs.length × Fin 4) :=
  (List.finRange m.legs.length).flatMap fun i =>
    (orderedMultiindex (m.jetAt i).2).map (fun μ => (i, μ))

def LocalMonomial.momentumFactorial (m : LocalMonomial G) : ℕ :=
  (m.orderedJets.map (fun v => ∏ μ : Fin 4, Nat.factorial (v.2 μ))).prod

def LocalMonomial.multiplicityFactorial (m : LocalMonomial G) : ℕ :=
  m.prod (fun _ n => Nat.factorial n)

/-- The field/antifield functional derivatives are already represented by
selecting the ordered amplitude component. Momentum derivatives are actual
iterated Frechet derivatives. Tuple q contains *all* external momenta;
insertions do not satisfy an overall momentum-conservation constraint. -/
def extractCoefficient (m : LocalMonomial G) (A : OrderedAmplitude G)
    (q : Fin m.legs.length → Spacetime) : ℂ :=
  (Complex.I ^ m.momentumDirections.length / (m.momentumFactorial : ℂ)) *
    iteratedFDeriv ℝ m.momentumDirections.length (A m.legs) q
      (fun i => Pi.single (m.momentumDirections.get i).1
        (Pi.single (m.momentumDirections.get i).2 1))

/-- Explicit finite jet set sufficient for degree at most D. -/
def jetsThrough (G : CompactSimpleGaugeGroup) (D : ℕ) : Finset (JetVariable G) := by
  classical
  exact (Finset.univ : Finset (ExternalLeg G)).biUnion fun k =>
    (Finset.univ : Finset (Fin 4 → Fin (D + 1))).image fun d => (k, fun μ => (d μ).val)

/-- Exactly the admissible monomials of degree strictly below D, enumerated
through a finite box before filtering by the actual weighted degree. -/
def monomialsBelow (G : CompactSimpleGaugeGroup) (D : ℕ) : Finset (LocalMonomial G) := by
  classical
  let S := jetsThrough G D
  let box : Finset (LocalMonomial G) :=
    (Finset.univ : Finset ({v // v ∈ S} → Fin (D + 1))).image fun f =>
      Finsupp.onFinset S (fun v => if h : v ∈ S then (f ⟨v, h⟩).val else 0)
        (by intro v hv; by_contra h; exact hv (by simp [h]))
  exact box.filter (fun m => m.Admissible ∧ m.dimension < D)

set_option maxHeartbeats 1200000 in
/-- The finite box omits no admissible monomial of the required degree.
This is important: an incomplete list would weaken the OPE subtraction. -/
theorem mem_monomialsBelow_iff (D : ℕ) (m : LocalMonomial G) :
    m ∈ monomialsBelow G D ↔ m.Admissible ∧ m.dimension < D := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hm
    have hterm (v : JetVariable G) (hv : v ∈ m.support) :
        m v * JetVariable.dimension v ≤ m.dimension := by
      change m v * JetVariable.dimension v ≤
        ∑ a ∈ m.support, m a * JetVariable.dimension a
      exact Finset.single_le_sum (f := fun a => m a * JetVariable.dimension a)
        (fun _ _ => Nat.zero_le _) hv
    have hexponent (v : JetVariable G) : m v ≤ m.dimension := by
      by_cases hv : v ∈ m.support
      · have hpos : 1 ≤ JetVariable.dimension v := jet_dimension_pos v
        have hmul := Nat.mul_le_mul_left (m v) hpos
        simpa using hmul.trans (hterm v hv)
      · simp [Finsupp.notMem_support_iff.mp hv]
    have hsupport : m.support ⊆ jetsThrough G D := by
      intro v hv
      have hn : 1 ≤ m v := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hdim : JetVariable.dimension v < D := by
        have hmul := Nat.mul_le_mul_right (JetVariable.dimension v) hn
        have hle : JetVariable.dimension v ≤ m.dimension := by
          simpa using hmul.trans (hterm v hv)
        exact hle.trans_lt hm.2
      have hd (μ : Fin 4) : v.2 μ < D + 1 := by
        have hsum : v.2 μ ≤ ∑ ν : Fin 4, v.2 ν :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
        unfold JetVariable.dimension at hdim
        omega
      apply Finset.mem_biUnion.mpr
      refine ⟨v.1, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
      refine ⟨(fun μ => (⟨v.2 μ, hd μ⟩ : Fin (D + 1))), Finset.mem_univ _, ?_⟩
      rfl
    let S := jetsThrough G D
    let f : {v // v ∈ S} → Fin (D + 1) :=
      fun v => ⟨m v.val, (hexponent v.val).trans_lt (Nat.lt_succ_of_lt hm.2)⟩
    unfold monomialsBelow
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨f, Finset.mem_univ _, ?_⟩, hm⟩
    ext v
    by_cases hv : v ∈ S
    · have hv' : v ∈ jetsThrough G D := hv
      simp [Finsupp.onFinset_apply, hv', f]
    · have hz : m v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hsupport h))
      have hv' : v ∉ jetsThrough G D := hv
      simp [Finsupp.onFinset_apply, hv', hz]

theorem dimension_lt_of_mem_monomialsBelow {D : ℕ} {m : LocalMonomial G}
    (h : m ∈ monomialsBelow G D) : m.dimension < D := by
  classical
  exact (Finset.mem_filter.mp h).2.2

/-- Actual insertion locations, with no synthetic coefficients attached. -/
structure PositionedInsertion (G : CompactSimpleGaugeGroup) where
  monomial : LocalMonomial G
  position : Spacetime

abbrev InsertedFlowFamily (G : CompactSimpleGaugeGroup) :=
  List (PositionedInsertion G) → FlowFamily G

abbrev OversubtractedFamily (G : CompactSimpleGaugeGroup) :=
  ℕ → List (PositionedInsertion G) → FlowFamily G

/-- Exact graded Leibniz product of ordered external coefficients. -/
def amplitudeProduct (A B : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => ∑ s : Finset (Fin legs.length),
    splitSign legs s *
      A (selectedLegs legs s) (selectedMomenta legs s q) *
      B (selectedLegs legs (complementIndices legs s))
        (selectedMomenta legs (complementIndices legs s) q)

/-- Cauchy product in loop order (formal hbar), with the actual graded
external-derivative Leibniz rule at each coefficient. -/
def flowProduct (A B : FlowFamily G) : FlowFamily G :=
  fun loop Λ Λ0 legs q => ∑ r ∈ Finset.range (loop + 1),
    amplitudeProduct (A r Λ Λ0) (B (loop - r) Λ Λ0) legs q

def flowUnit : FlowFamily G := fun loop _ _ legs _ =>
  if loop = 0 ∧ legs = [] then 1 else 0

def singleInsertionProduct (L : InsertedFlowFamily G) :
    List (PositionedInsertion G) → FlowFamily G
  | [] => flowUnit
  | a :: rest => flowProduct (L [a]) (singleInsertionProduct L rest)

/-- Equation (4.5): the formal hbar shifts the coefficient of F down one
loop order; it is not multiplication by an arbitrary numerical constant. -/
def disconnectedFunctional (L : InsertedFlowFamily G) (F : OversubtractedFamily G)
    (D : ℕ) (input : List (PositionedInsertion G)) : FlowFamily G :=
  fun loop Λ Λ0 legs q =>
    singleInsertionProduct L input loop Λ Λ0 legs q -
      if loop = 0 then 0 else F D input (loop - 1) Λ Λ0 legs q

/-- A nonempty insertion cluster carries its actual final point, which fixes
where the output insertion in the triangular extraction is evaluated. -/
structure InsertionCluster (G : CompactSimpleGaugeGroup) where
  initial : List (PositionedInsertion G)
  last : PositionedInsertion G

def InsertionCluster.insertions (input : InsertionCluster G) : List (PositionedInsertion G) :=
  input.initial ++ [input.last]

/-- Equations (5.5)--(5.7), performed coefficientwise in hbar. The recursive
sum is finite and only lower engineering degrees appear. No coefficient
family is supplied as witness data. The IR argument is the positive mu. -/
def regulatedOPECoefficient (L : InsertedFlowFamily G) (F : OversubtractedFamily G)
    (μ Λ0 : ℝ) (input : InsertionCluster G) (loop : ℕ) (output : LocalMonomial G) : ℂ := by
  classical
  let whole := disconnectedFunctional L F 0 input.insertions
  exact if output = 0 then whole loop μ Λ0 [] (fun i => Fin.elim0 i)
    else if ¬ output.Admissible then 0
    else extractCoefficient output
      (fun legs q => whole loop μ Λ0 legs q -
        ∑ c ∈ (monomialsBelow G output.dimension).attach,
          ∑ r ∈ Finset.range (loop + 1),
            regulatedOPECoefficient L F μ Λ0 input r c.val *
              L [⟨c.val, input.last.position⟩] (loop - r) μ Λ0 legs q)
      0
termination_by output.dimension
decreasing_by
  exact dimension_lt_of_mem_monomialsBelow c.property

/-- The extracted coefficient of the identity is literally the full
zero-external-leg functional at the positive renormalization scale. -/
theorem regulatedOPECoefficient_identity (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) (μ Λ0 : ℝ) (input : InsertionCluster G) (loop : ℕ) :
    regulatedOPECoefficient L F μ Λ0 input loop 0 =
      disconnectedFunctional L F 0 input.insertions loop μ Λ0 [] (fun i => Fin.elim0 i) := by
  rw [regulatedOPECoefficient]
  simp

/-- A genuine coefficientwise UV limit. An arbitrary proposed limiting
coefficient is accepted only with convergence to the fixed extraction. -/
def IsUltravioletOPECoefficient (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) (μ : ℝ) (input : InsertionCluster G)
    (loop : ℕ) (output : LocalMonomial G) (value : ℂ) : Prop :=
  0 < μ ∧ Filter.Tendsto
    (fun Λ0 : ℝ => regulatedOPECoefficient L F μ Λ0 input loop output)
    Filter.atTop (nhds value)

/-- Project canonical potential jets into the same elementary gauge-field
jet labels, discarding only the separate coupling-power variable. -/
def potentialMonomialToLocal (m : PotentialVariable G →₀ ℕ) : LocalMonomial G :=
  m.sum (fun v n => match v with
    | .inl _ => 0
    | .inr (d, μ, a) => Finsupp.single (.inl (.gauge μ a), d) n)

/-- Conversion to the normalized monomial basis dual to (4.1). Repeated
bosonic jets carry the multiplicity factorial; the original polynomial is
not changed or silently replaced by its normalized basis representative. -/
def normalizedPotentialExpansion (P : PotentialPolynomial G) (g : ℝ) :
    LocalMonomial G →₀ ℂ :=
  P.sum (fun m c => Finsupp.single (potentialMonomialToLocal m)
    ((c : ℂ) * (g : ℂ) ^ m (.inl ()) *
      ((potentialMonomialToLocal m).multiplicityFactorial : ℂ)))

/-- All source-observable insertions use the actual bracket-dependent
classical substitution already used in the same group's YM vertices. -/
def normalizedObservableExpansion {B : InvariantForm G} (e : ColorFrame B)
    (p : CurvatureJetPolynomial G) (g : ℝ) : LocalMonomial G →₀ ℂ :=
  normalizedPotentialExpansion (classicalInsertionPolynomial e p) g

/-- Finite multilinear insertion expansion. This applies equally to the
fixed stress polynomial and to classicalInsertionPolynomial(e,p). -/
def polynomialInsertionValue (value : List (PositionedInsertion G) → ℂ) (g : ℝ) :
    List (PotentialPolynomial G × Spacetime) → List (PositionedInsertion G) → ℂ
  | [], accumulated => value accumulated
  | (P, x) :: rest, accumulated =>
      (normalizedPotentialExpansion P g).sum (fun m a =>
        a * polynomialInsertionValue value g rest (accumulated ++ [⟨m, x⟩]))

def polynomialInsertionFlow (L : InsertedFlowFamily G) (g : ℝ)
    (input : List (PotentialPolynomial G × Spacetime)) : FlowFamily G :=
  fun loop Λ Λ0 legs q => polynomialInsertionValue
    (fun labels => L labels loop Λ Λ0 legs q) g input []

/-- Regulated coefficients for actual group-dependent polynomial inputs;
the output is a normalized elementary jet monomial. Cohomological descent
and finite renormalization subsequently transport this output basis. -/
def regulatedPolynomialOPECoefficient (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) (g μ Λ0 : ℝ)
    (initial : List (PotentialPolynomial G × Spacetime))
    (last : PotentialPolynomial G × Spacetime) (loop : ℕ)
    (output : LocalMonomial G) : ℂ :=
  (normalizedPotentialExpansion last.1 g).sum (fun m a =>
    a * polynomialInsertionValue (fun preceding =>
      regulatedOPECoefficient L F μ Λ0 ⟨preceding, ⟨m, last.2⟩⟩ loop output)
      g initial [])

/-- Smoothness and fixed single-insertion boundary projectors (4.2).
Only admissible supermonomials are normalized: an odd square is zero,
so giving it a Kronecker normalization would force 0=1. -/
structure SingleInsertionBoundaryConditions (L : InsertedFlowFamily G) (μ : ℝ) : Prop where
  scale_positive : 0 < μ
  smooth : ∀ input loop Λ Λ0, 0 < Λ → Λ ≤ Λ0 → ∀ legs,
    ContDiff ℝ ∞ (L input loop Λ Λ0 legs)
  /-- Momentum jets extend continuously to the actual UV boundary, so
  irrelevant endpoint values cannot be disconnected from the interior flow. -/
  scale_jet_continuous : ∀ input loop Λ0 legs
      (directions : List (Fin legs.length × Fin 4)) q,
    ContinuousOn (fun scale : ℝ => momentumJet directions (L input loop scale Λ0 legs) q)
      (Set.Ioc 0 Λ0)
  invalid : ∀ A, ¬ A.Admissible → ∀ x loop Λ Λ0 legs q,
    L [⟨A, x⟩] loop Λ Λ0 legs q = 0
  normalized : ∀ A B : LocalMonomial G, A.Admissible → B.Admissible →
    B.dimension ≤ A.dimension → ∀ loop Λ0, μ ≤ Λ0 →
      extractCoefficient B (L [⟨A, 0⟩] loop μ Λ0) 0 =
        if A = B ∧ loop = 0 then 1 else 0
  irrelevant : ∀ A B : LocalMonomial G, A.Admissible → B.Admissible →
    A.dimension < B.dimension → ∀ loop Λ0, μ ≤ Λ0 →
      ∀ q : Fin B.legs.length → Spacetime,
        extractCoefficient B (L [⟨A, 0⟩] loop Λ0 Λ0) q = 0

/-- Shift all insertion points by the specified vector. -/
def shiftInsertions (input : List (PositionedInsertion G)) (y : Spacetime) :
    List (PositionedInsertion G) := input.map (fun a => ⟨a.monomial, a.position - y⟩)

def InsertionCluster.atOrigin (input : InsertionCluster G) : List (PositionedInsertion G) :=
  shiftInsertions input.insertions input.last.position

/-- Exact oversubtraction boundary projectors (4.4). The final insertion
is shifted to the origin as stipulated by the primary definition. -/
structure OversubtractionBoundaryConditions (F : OversubtractedFamily G) (μ : ℝ) : Prop where
  scale_positive : 0 < μ
  smooth : ∀ D input loop Λ Λ0, 0 < Λ → Λ ≤ Λ0 → ∀ legs,
    ContDiff ℝ ∞ (F D input loop Λ Λ0 legs)
  scale_jet_continuous : ∀ D input loop Λ0 legs
      (directions : List (Fin legs.length × Fin 4)) q,
    ContinuousOn (fun scale : ℝ => momentumJet directions (F D input loop scale Λ0 legs) q)
      (Set.Ioc 0 Λ0)
  low : ∀ D (input : InsertionCluster G) (B : LocalMonomial G), B.Admissible →
    B.dimension < D → ∀ loop Λ0, μ ≤ Λ0 →
      extractCoefficient B (F D input.atOrigin loop μ Λ0) 0 = 0
  high : ∀ D (input : InsertionCluster G) (B : LocalMonomial G), B.Admissible →
    D ≤ B.dimension → ∀ loop Λ0, μ ≤ Λ0 → ∀ q : Fin B.legs.length → Spacetime,
      extractCoefficient B (F D input.atOrigin loop Λ0 Λ0) q = 0
  translation : ∀ D input y loop Λ Λ0 legs q,
    F D input loop Λ Λ0 legs q =
      Complex.exp (-Complex.I * (euclideanPair y (∑ i : Fin legs.length, q i) : ℂ)) *
        F D (shiftInsertions input y) loop Λ Λ0 legs q

end YangMills.PerturbativeFlow
