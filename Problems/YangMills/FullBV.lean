import Problems.YangMills.PerturbativeFlow
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Finprod

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Concrete complex BV jets, same-action densities and local functionals.
No master equation, Ward restoration or quotient bracket descent is assumed. -/
noncomputable section
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}
abbrev Multiindex := Fin 4 → ℕ
structure Jet (G : CompactSimpleGaugeGroup) where
  field : ExternalLeg G
  derivative : Multiindex
  deriving DecidableEq
abbrev EvenJet (G : CompactSimpleGaugeGroup) := {j : Jet G // j.field.parity = false}
abbrev OddJet (G : CompactSimpleGaugeGroup) := {j : Jet G // j.field.parity = true}
abbrev JetAlgebra (G : CompactSimpleGaugeGroup) :=
  TensorProduct ℂ (MvPolynomial (EvenJet G) ℂ)
    (ExteriorAlgebra ℂ (OddJet G →₀ ℂ))
def evenJet (j : EvenJet G) : JetAlgebra G :=
  TensorProduct.tmul ℂ (MvPolynomial.X j) 1
def oddJet (j : OddJet G) : JetAlgebra G :=
  TensorProduct.tmul ℂ 1 (ExteriorAlgebra.ι ℂ (Finsupp.single j 1))
/-- Canonical left Grassmann derivative: exterior contraction by coordinate
evaluation, hence the anticommuting signs are fixed by the algebra. -/
def oddPartial (j : OddJet G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  TensorProduct.map LinearMap.id
    (CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply j))

def evenPartial (j : EvenJet G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  TensorProduct.map (MvPolynomial.pderiv j).toLinearMap LinearMap.id

@[simp] theorem oddPartial_oddJet (i j : OddJet G) :
    oddPartial i (oddJet j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [oddPartial, oddJet, CliffordAlgebra.contractLeft_ι,
      Algebra.TensorProduct.one_def]
  · simp [oddPartial, oddJet, CliffordAlgebra.contractLeft_ι,
      Finsupp.lapply_apply, h]

@[simp] theorem evenPartial_evenJet (i j : EvenJet G) :
    evenPartial i (evenJet j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [evenPartial, evenJet, MvPolynomial.pderiv_X,
      Algebra.TensorProduct.one_def]
  · simp [evenPartial, evenJet, MvPolynomial.pderiv_X, h]

abbrev JetIndex (G : CompactSimpleGaugeGroup) := EvenJet G ⊕ OddJet G

def leftPartial : JetIndex G → JetAlgebra G →ₗ[ℂ] JetAlgebra G
  | .inl j => evenPartial j
  | .inr j => oddPartial j

/-- Ordered external differentiation; the first listed leg differentiates
first. This is the convention used by the ordered amplitude flow. -/
def externalDerivative : List (JetIndex G) → JetAlgebra G →ₗ[ℂ] JetAlgebra G
  | [] => LinearMap.id
  | j :: js => (externalDerivative js).comp (leftPartial j)

def oddAugmentation : ExteriorAlgebra ℂ (OddJet G →₀ ℂ) →ₐ[ℂ] ℂ :=
  ExteriorAlgebra.lift ℂ ⟨0, by intro m; simp⟩

/-- Evaluate every gauge/auxiliary/ghost jet at zero. -/
def augmentation : JetAlgebra G →ₗ[ℂ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun p e => MvPolynomial.eval (fun _ => 0) p * oddAugmentation e)
    (by intro p q e; simp [add_mul])
    (by intro r p e; simp [mul_assoc])
    (by intro p e f; simp [mul_add])
    (by intro r p e; simp [mul_left_comm]))

/-- Amputated ordered external coefficient, including even-variable factorials
and odd-variable signs. It is extracted from the same actual jet polynomial. -/
def externalCoefficient (w : List (JetIndex G)) (P : JetAlgebra G) : ℂ :=
  augmentation (externalDerivative w P)

/-- A fully specified coordinate differential for polynomial jets. Its
summands are fixed partials, not freely supplied maps on observables. Finite
partial support is proved below, excluding infinite-support totalization. -/
def coordinateDifferential (evenImage : EvenJet G → JetAlgebra G)
    (oddImage : OddJet G → JetAlgebra G) (P : JetAlgebra G) : JetAlgebra G :=
  (∑ᶠ j : EvenJet G, evenImage j * evenPartial j P) +
    ∑ᶠ j : OddJet G, oddImage j * oddPartial j P

theorem exteriorPartials_finite (e : ExteriorAlgebra ℂ (OddJet G →₀ ℂ)) :
    ∃ S : Finset (OddJet G), ∀ j ∉ S,
      CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply j) e = 0 := by
  classical
  induction e using CliffordAlgebra.left_induction with
  | algebraMap r =>
      exact ⟨∅, by intro j hj; simp⟩
  | add x y hx hy =>
      obtain ⟨S, hS⟩ := hx
      obtain ⟨T, hT⟩ := hy
      refine ⟨S ∪ T, ?_⟩
      intro j hj
      have hj' := Finset.notMem_union.mp hj
      simp [hS j hj'.1, hT j hj'.2]
  | ι_mul e v he =>
      obtain ⟨S, hS⟩ := he
      refine ⟨v.support ∪ S, ?_⟩
      intro j hj
      have hj' := Finset.notMem_union.mp hj
      have hv : v j = 0 := Finsupp.notMem_support_iff.mp hj'.1
      simp [CliffordAlgebra.contractLeft_ι_mul, hv, hS j hj'.2]

theorem oddPartials_finite (P : JetAlgebra G) :
    ∃ S : Finset (OddJet G), ∀ j ∉ S, oddPartial j P = 0 := by
  classical
  induction P using TensorProduct.induction_on with
  | zero => exact ⟨∅, by intro j hj; simp⟩
  | tmul p e =>
      obtain ⟨S, hS⟩ := exteriorPartials_finite e
      refine ⟨S, ?_⟩
      intro j hj
      simp [oddPartial, hS j hj]
  | add P Q hP hQ =>
      obtain ⟨S, hS⟩ := hP
      obtain ⟨T, hT⟩ := hQ
      refine ⟨S ∪ T, ?_⟩
      intro j hj
      have hj' := Finset.notMem_union.mp hj
      simp [hS j hj'.1, hT j hj'.2]

theorem evenPartials_finite (P : JetAlgebra G) :
    ∃ S : Finset (EvenJet G), ∀ j ∉ S, evenPartial j P = 0 := by
  classical
  induction P using TensorProduct.induction_on with
  | zero => exact ⟨∅, by intro j hj; simp⟩
  | tmul p e =>
      refine ⟨p.vars, ?_⟩
      intro j hj
      simp [evenPartial, MvPolynomial.pderiv_eq_zero_of_notMem_vars hj]
  | add P Q hP hQ =>
      obtain ⟨S, hS⟩ := hP
      obtain ⟨T, hT⟩ := hQ
      refine ⟨S ∪ T, ?_⟩
      intro j hj
      have hj' := Finset.notMem_union.mp hj
      simp [hS j hj'.1, hT j hj'.2]

theorem evenSummands_finite (E : EvenJet G → JetAlgebra G) (P : JetAlgebra G) :
    (Function.support (fun j => E j * evenPartial j P)).Finite := by
  classical
  obtain ⟨S, hS⟩ := evenPartials_finite P
  refine S.finite_toSet.subset ?_
  intro j hj
  by_contra h
  change E j * evenPartial j P ≠ 0 at hj
  exact hj (by rw [hS j h, mul_zero])

theorem oddSummands_finite (O : OddJet G → JetAlgebra G) (P : JetAlgebra G) :
    (Function.support (fun j => O j * oddPartial j P)).Finite := by
  classical
  obtain ⟨S, hS⟩ := oddPartials_finite P
  refine S.finite_toSet.subset ?_
  intro j hj
  by_contra h
  change O j * oddPartial j P ≠ 0 at hj
  exact hj (by rw [hS j h, mul_zero])

theorem coordinateDifferential_add (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (P Q : JetAlgebra G) :
    coordinateDifferential E O (P + Q) =
      coordinateDifferential E O P + coordinateDifferential E O Q := by
  simp only [coordinateDifferential, map_add, mul_add]
  rw [finsum_add_distrib (evenSummands_finite E P) (evenSummands_finite E Q),
    finsum_add_distrib (oddSummands_finite O P) (oddSummands_finite O Q)]
  abel

theorem coordinateDifferential_smul (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (r : ℂ) (P : JetAlgebra G) :
    coordinateDifferential E O (r • P) = r • coordinateDifferential E O P := by
  simp only [coordinateDifferential, map_smul, mul_smul_comm]
  rw [← smul_finsum' r (evenSummands_finite E P),
    ← smul_finsum' r (oddSummands_finite O P), smul_add]

def coordinateDifferentialLinear (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := coordinateDifferential E O
  map_add' := coordinateDifferential_add E O
  map_smul' := coordinateDifferential_smul E O

@[simp] theorem oddPartial_evenJet (i : OddJet G) (j : EvenJet G) :
    oddPartial i (evenJet j) = 0 := by
  simp [oddPartial, evenJet]

@[simp] theorem evenPartial_oddJet (i : EvenJet G) (j : OddJet G) :
    evenPartial i (oddJet j) = 0 := by
  simp [evenPartial, oddJet]

theorem coordinateDifferential_evenJet (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (j : EvenJet G) :
    coordinateDifferential E O (evenJet j) = E j := by
  classical
  simp only [coordinateDifferential, evenPartial_evenJet, oddPartial_evenJet,
    mul_zero, finsum_zero, add_zero, mul_ite, mul_one]
  rw [finsum_eq_single _ j (by intro i hi; simp [hi])]
  simp

theorem coordinateDifferential_oddJet (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (j : OddJet G) :
    coordinateDifferential E O (oddJet j) = O j := by
  classical
  simp only [coordinateDifferential, evenPartial_oddJet, oddPartial_oddJet,
    mul_zero, finsum_zero, zero_add, mul_ite, mul_one]
  rw [finsum_eq_single _ j (by intro i hi; simp [hi])]
  simp

def Jet.shift (mu : Fin 4) (j : Jet G) : Jet G :=
  ⟨j.field, j.derivative + Pi.single mu 1⟩

def evenShift (mu : Fin 4) (j : EvenJet G) : EvenJet G :=
  ⟨j.val.shift mu, j.property⟩

def oddShift (mu : Fin 4) (j : OddJet G) : OddJet G :=
  ⟨j.val.shift mu, j.property⟩

def totalDerivative (mu : Fin 4) (P : JetAlgebra G) : JetAlgebra G :=
  coordinateDifferential (fun j => evenJet (evenShift mu j))
    (fun j => oddJet (oddShift mu j)) P

theorem totalDerivative_add (mu : Fin 4) (P Q : JetAlgebra G) :
    totalDerivative mu (P + Q) = totalDerivative mu P + totalDerivative mu Q :=
  coordinateDifferential_add _ _ _ _

theorem totalDerivative_smul (mu : Fin 4) (r : ℂ) (P : JetAlgebra G) :
    totalDerivative mu (r • P) = r • totalDerivative mu P :=
  coordinateDifferential_smul _ _ _ _

def derivativeList (alpha : Multiindex) : List (Fin 4) :=
  (List.finRange 4).flatMap (fun mu => List.replicate (alpha mu) mu)

def totalDerivatives (alpha : Multiindex) (P : JetAlgebra G) : JetAlgebra G :=
  (derivativeList alpha).foldr totalDerivative P

theorem totalDerivatives_add (alpha : Multiindex) (P Q : JetAlgebra G) :
    totalDerivatives alpha (P + Q) = totalDerivatives alpha P + totalDerivatives alpha Q := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldr_cons, ih] using totalDerivative_add a _ _

theorem totalDerivatives_smul (alpha : Multiindex) (r : ℂ) (P : JetAlgebra G) :
    totalDerivatives alpha (r • P) = r • totalDerivatives alpha P := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldr_cons, ih] using totalDerivative_smul a r _

def parity : JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  TensorProduct.map LinearMap.id CliffordAlgebra.involute.toLinearMap

/-- Every extended field, including antifields, has its algebraically fixed
commuting or anticommuting generator according to the flow's actual parity. -/
def jet (j : Jet G) : JetAlgebra G :=
  if h : j.field.parity = true then oddJet ⟨j, h⟩ else
    evenJet ⟨j, by cases hp : j.field.parity <;> simp_all⟩

def leftPartialJet (j : Jet G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  if h : j.field.parity = true then oddPartial ⟨j, h⟩ else
    evenPartial ⟨j, by cases hp : j.field.parity <;> simp_all⟩

/-- Right differentiation is obtained from canonical left differentiation,
with the parity of the remaining polynomial, not an assumed sign parameter. -/
def rightPartialJet (j : Jet G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  if j.field.parity then parity.comp (leftPartialJet j) else leftPartialJet j

theorem jetPartials_finite (P : JetAlgebra G) :
    ∃ S : Finset (Jet G), ∀ j ∉ S, leftPartialJet j P = 0 := by
  classical
  obtain ⟨E, hE⟩ := evenPartials_finite P
  obtain ⟨O, hO⟩ := oddPartials_finite P
  refine ⟨E.image Subtype.val ∪ O.image Subtype.val, ?_⟩
  intro j hj
  by_cases h : j.field.parity = true
  · have hn : (⟨j, h⟩ : OddJet G) ∉ O := by
      intro hm
      exact hj (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, h⟩, hm, rfl⟩))
    simpa [leftPartialJet, h] using hO ⟨j, h⟩ hn
  · have hf : j.field.parity = false := by cases hp : j.field.parity <;> simp_all
    have hn : (⟨j, hf⟩ : EvenJet G) ∉ E := by
      intro hm
      exact hj (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨j, hf⟩, hm, rfl⟩))
    simpa [leftPartialJet, h] using hE ⟨j, hf⟩ hn

theorem jetPartialsSupport_finite (P : JetAlgebra G) :
    (Function.support (fun j : Jet G => leftPartialJet j P)).Finite := by
  classical
  obtain ⟨S, hS⟩ := jetPartials_finite P
  refine S.finite_toSet.subset ?_
  intro j hj
  by_contra hn
  exact hj (hS j hn)

/-- The actual nonzero jet partial support of P, not an arbitrary dictionary
chosen by a proof author. -/
def jetSupport (P : JetAlgebra G) : Finset (Jet G) :=
  (jetPartialsSupport_finite P).toFinset

@[simp] theorem mem_jetSupport (P : JetAlgebra G) (j : Jet G) :
    j ∈ jetSupport P ↔ leftPartialJet j P ≠ 0 := by
  simp [jetSupport]

def externalJetDerivative : List (Jet G) → JetAlgebra G →ₗ[ℂ] JetAlgebra G
  | [] => LinearMap.id
  | j :: js => (externalJetDerivative js).comp (leftPartialJet j)

def jetMomentumPhase (j : Jet G) (p : Spacetime) : ℂ :=
  ∏ mu : Fin 4, (-Complex.I * (p mu : ℂ)) ^ j.derivative mu

/-- Ordered local momentum amplitude extracted from P's actual jet
coefficients. Every assignment is from P's finite nonzero derivative support.
Left Grassmann signs and even factorials come from canonical partials. -/
def densityAmplitude (P : JetAlgebra G) : OrderedAmplitude G :=
  fun legs q =>
    ∑ assignment : Fin legs.length → {j : Jet G // j ∈ jetSupport P},
      if ∀ i : Fin legs.length, (assignment i).val.field = legs.get i then
        augmentation (externalJetDerivative
          (List.ofFn (fun i => (assignment i).val)) P) *
          ∏ i : Fin legs.length, jetMomentumPhase (assignment i).val (q i)
      else 0

theorem leftPartialJet_jet (i j : Jet G) :
    leftPartialJet i (jet j) = if i = j then 1 else 0 := by
  classical
  by_cases hi : i.field.parity = true <;> by_cases hj : j.field.parity = true
  · simp [leftPartialJet, jet, hi, hj, Subtype.ext_iff]
  · have hn : i ≠ j := by intro he; subst j; exact hj hi
    simp [leftPartialJet, jet, hi, hj, hn]
  · have hn : i ≠ j := by intro he; subst j; exact hi hj
    simp [leftPartialJet, jet, hi, hj, hn]
  · simp [leftPartialJet, jet, hi, hj, Subtype.ext_iff]

@[simp] theorem jetSupport_jet (j : Jet G) : jetSupport (jet j) = {j} := by
  classical
  ext i
  simp [mem_jetSupport, leftPartialJet_jet]

@[simp] theorem densityAmplitude_zero : densityAmplitude (0 : JetAlgebra G) = 0 := by
  funext legs q
  simp [densityAmplitude]

@[simp] theorem totalDerivative_zero (mu : Fin 4) :
    totalDerivative mu (0 : JetAlgebra G) = 0 := by
  simp [totalDerivative, coordinateDifferential]

@[simp] theorem totalDerivatives_zeroInput (alpha : Multiindex) :
    totalDerivatives alpha (0 : JetAlgebra G) = 0 := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

def monomial (legs : List (LocalVertexLeg G)) : JetAlgebra G :=
  (legs.map (fun k => jet ⟨k.field, fun mu => k.derivatives.count mu⟩)).prod

def densityOfVertex (g : ℝ) (v : LocalVertex G) : JetAlgebra G :=
  (v.coefficient * (g : ℂ) ^ v.couplingOrder) • monomial v.legs

def densityOfVertices (g : ℝ) (vertices : List (LocalVertex G)) : JetAlgebra G :=
  (vertices.map (densityOfVertex g)).sum

/-- The same explicit free BV action used to derive the flow's free Ward
operator, now as an actual complex superjet polynomial. -/
def freeActionDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  densityOfVertices 0 (freeActionVertices G)

def interactionDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  densityOfVertices g (physicalActionVertices e ++ antifieldActionVertices e)

/-- The action's color tensors, ghost terms, shifted B and antifield couplings
are all inherited from the same fixed vertex lists used by the coefficient flow. -/
def masterActionDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  freeActionDensity G + interactionDensity e g

/-- Every classical curvature-jet polynomial is inserted through the same
actual-G canonical/source normalization already used by the flow. The
invariance and cocycle correspondence proofs are separate supporting facts. -/
def classicalInsertionDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : CurvatureJetPolynomial G) : JetAlgebra G :=
  densityOfVertices g ((observableMonomials e P).map (fun m =>
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) }))

def derivativeOrder (alpha : Multiindex) : ℕ := ∑ mu : Fin 4, alpha mu

/-- Euler variational derivative with left Grassmann convention. Each
polynomial has only finitely many nonzero jet partials. -/
def leftEuler (field : ExternalLeg G) (P : JetAlgebra G) : JetAlgebra G :=
  ∑ᶠ alpha : Multiindex, ((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (leftPartialJet ⟨field, alpha⟩ P)

def rightEuler (field : ExternalLeg G) (P : JetAlgebra G) : JetAlgebra G :=
  ∑ᶠ alpha : Multiindex, ((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ P)

theorem leftEulerSummands_finite (field : ExternalLeg G) (P : JetAlgebra G) :
    (Function.support (fun alpha : Multiindex =>
      ((-1 : ℂ) ^ derivativeOrder alpha) •
        totalDerivatives alpha (leftPartialJet ⟨field, alpha⟩ P))).Finite := by
  classical
  obtain ⟨S, hS⟩ := jetPartials_finite P
  refine (S.image Jet.derivative).finite_toSet.subset ?_
  intro alpha hmem
  by_contra hn
  have hj : (⟨field, alpha⟩ : Jet G) ∉ S := by
    intro hm
    exact hn (Finset.mem_image.mpr ⟨⟨field, alpha⟩, hm, rfl⟩)
  change ((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (leftPartialJet ⟨field, alpha⟩ P) ≠ 0 at hmem
  exact hmem (by simp [hS _ hj])

theorem rightEulerSummands_finite (field : ExternalLeg G) (P : JetAlgebra G) :
    (Function.support (fun alpha : Multiindex =>
      ((-1 : ℂ) ^ derivativeOrder alpha) •
        totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ P))).Finite := by
  classical
  obtain ⟨S, hS⟩ := jetPartials_finite P
  refine (S.image Jet.derivative).finite_toSet.subset ?_
  intro alpha hmem
  by_contra hn
  have hj : (⟨field, alpha⟩ : Jet G) ∉ S := by
    intro hm
    exact hn (Finset.mem_image.mpr ⟨⟨field, alpha⟩, hm, rfl⟩)
  have hz : rightPartialJet ⟨field, alpha⟩ P = 0 := by
    by_cases hp : field.parity = true
    · simp [rightPartialJet, hp, hS _ hj]
    · simp [rightPartialJet, hp, hS _ hj]
  change ((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ P) ≠ 0 at hmem
  exact hmem (by simp [hz])

theorem leftEuler_add (field : ExternalLeg G) (P Q : JetAlgebra G) :
    leftEuler field (P + Q) = leftEuler field P + leftEuler field Q := by
  simp only [leftEuler, map_add, totalDerivatives_add, smul_add]
  exact finsum_add_distrib (leftEulerSummands_finite field P)
    (leftEulerSummands_finite field Q)

theorem rightEuler_add (field : ExternalLeg G) (P Q : JetAlgebra G) :
    rightEuler field (P + Q) = rightEuler field P + rightEuler field Q := by
  simp only [rightEuler, map_add, totalDerivatives_add, smul_add]
  exact finsum_add_distrib (rightEulerSummands_finite field P)
    (rightEulerSummands_finite field Q)

theorem leftEuler_smul (field : ExternalLeg G) (r : ℂ) (P : JetAlgebra G) :
    leftEuler field (r • P) = r • leftEuler field P := by
  simp only [leftEuler, map_smul, totalDerivatives_smul, smul_comm (_ : ℂ) r]
  exact (smul_finsum' r (leftEulerSummands_finite field P)).symm

theorem rightEuler_smul (field : ExternalLeg G) (r : ℂ) (P : JetAlgebra G) :
    rightEuler field (r • P) = r • rightEuler field P := by
  simp only [rightEuler, map_smul, totalDerivatives_smul, smul_comm (_ : ℂ) r]
  exact (smul_finsum' r (rightEulerSummands_finite field P)).symm

def leftEulerLinear (field : ExternalLeg G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := leftEuler field
  map_add' := leftEuler_add field
  map_smul' := leftEuler_smul field

def rightEulerLinear (field : ExternalLeg G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := rightEuler field
  map_add' := rightEuler_add field
  map_smul' := rightEuler_smul field

/-- The fixed odd BV antibracket on polynomial densities, before passing to
local functionals modulo total divergences. It includes every basic species. -/
def densityBracket (P Q : JetAlgebra G) : JetAlgebra G :=
  ∑ K : BasicField G,
    (rightEuler (.inl K) P * leftEuler (.inr K) Q -
      rightEuler (.inr K) P * leftEuler (.inl K) Q)

def divergences (G : CompactSimpleGaugeGroup) : Submodule ℂ (JetAlgebra G) :=
  Submodule.span ℂ (Set.range (fun p : Fin 4 × JetAlgebra G =>
    totalDerivative p.1 p.2))

abbrev LocalFunctional (G : CompactSimpleGaugeGroup) := JetAlgebra G ⧸ divergences G

def localClass (P : JetAlgebra G) : LocalFunctional G := (divergences G).mkQ P

theorem totalDerivative_class_zero (mu : Fin 4) (P : JetAlgebra G) :
    localClass (totalDerivative mu P) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (divergences G)).mpr
  exact Submodule.subset_span ⟨(mu, P), rfl⟩

/-- Concrete graph of the induced BV bracket. The descent and uniqueness
theorems must establish that it is the graph of a function; they are not
assumptions packaged as free meaning fields. -/
def bracketGraph (P Q R : LocalFunctional G) : Prop :=
  ∃ p q : JetAlgebra G,
    localClass p = P ∧ localClass q = Q ∧ localClass (densityBracket p q) = R

def masterAction {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : LocalFunctional G :=
  localClass (masterActionDensity e g)

/-- A fixed classical master-equation proposition about the same action;
its proof requires BV descent and the actual-G Jacobi identities. -/
def ClassicalMasterEquation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : Prop :=
  localClass (densityBracket (masterActionDensity e g) (masterActionDensity e g)) = 0

def freeSTDensity (G : CompactSimpleGaugeGroup) (P : JetAlgebra G) : JetAlgebra G :=
  densityBracket (freeActionDensity G) P

def classicalSTDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : JetAlgebra G :=
  densityBracket (masterActionDensity e g) P

/-- The BV Hamiltonian characteristic on an undifferentiated field or
antifield. These images are extracted from S itself, never supplied freely. -/
def stCharacteristic (S : JetAlgebra G) : ExternalLeg G → JetAlgebra G
  | .inl K => -rightEuler (.inr K) S
  | .inr K => rightEuler (.inl K) S

/-- Evolutionary prolongation on POINTWISE local insertions. Unlike the
integrated BV bracket, this retains all derivative descendants of P(x). -/
def localST (S P : JetAlgebra G) : JetAlgebra G :=
  coordinateDifferential
    (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field))
    (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field)) P

def freeLocalSTDensity (G : CompactSimpleGaugeGroup) (P : JetAlgebra G) : JetAlgebra G :=
  localST (freeActionDensity G) P

def classicalLocalSTDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : JetAlgebra G :=
  localST (masterActionDensity e g) P

def LocalClassicalCocycle {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : Prop := classicalLocalSTDensity e g P = 0

def LocalClassicalCohomologous {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P Q : JetAlgebra G) : Prop :=
  ∃ R : JetAlgebra G, P - Q = classicalLocalSTDensity e g R

theorem localST_evenJet (S : JetAlgebra G) (j : EvenJet G) :
    localST S (evenJet j) =
      totalDerivatives j.val.derivative (stCharacteristic S j.val.field) :=
  coordinateDifferential_evenJet _ _ _

theorem localST_oddJet (S : JetAlgebra G) (j : OddJet G) :
    localST S (oddJet j) =
      totalDerivatives j.val.derivative (stCharacteristic S j.val.field) :=
  coordinateDifferential_oddJet _ _ _

def ClassicalCocycle {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : Prop := localClass (classicalSTDensity e g P) = 0

/-- Equality up to a classical BV-exact term and a total divergence. This is
a fixed relation on densities; establishing the cohomology equivalence uses
the master-equation and quotient-descent supporting theorems. -/
def ClassicalCohomologous {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P Q : JetAlgebra G) : Prop :=
  ∃ R : JetAlgebra G,
    localClass (P - Q) = localClass (classicalSTDensity e g R)


/-- The full graded Leibniz identity for canonical exterior contraction. -/
theorem contraction_product (d : Module.Dual ℂ (OddJet G →₀ ℂ))
    (u v : ExteriorAlgebra ℂ (OddJet G →₀ ℂ)) :
    CliffordAlgebra.contractLeft (Q := 0) d (u * v) =
      CliffordAlgebra.contractLeft d u * v +
        CliffordAlgebra.involute u * CliffordAlgebra.contractLeft d v := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [CliffordAlgebra.contractLeft_algebraMap_mul]
  | add u w hu hw =>
      simp only [add_mul, map_add, hu, hw]
      abel
  | ι_mul u a hu =>
      simp only [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, hu,
        map_mul, CliffordAlgebra.involute_ι]
      simp only [mul_add, sub_mul, smul_mul_assoc,
        neg_mul, mul_assoc]
      noncomm_ring

theorem oddPartial_mul (j : OddJet G) (P Q : JetAlgebra G) :
    oddPartial j (P * Q) = oddPartial j P * Q + parity P * oddPartial j Q := by
  induction P using TensorProduct.induction_on with
  | zero => simp [parity]
  | add P R hP hR =>
      simp only [add_mul, map_add, hP, hR]
      abel
  | tmul p u =>
      induction Q using TensorProduct.induction_on with
      | zero => simp
      | add Q R hQ hR =>
          simp only [mul_add, map_add, hQ, hR]
          abel
      | tmul q v =>
          simp [oddPartial, parity, Algebra.TensorProduct.tmul_mul_tmul,
            contraction_product, TensorProduct.tmul_add]

theorem evenPartial_mul (j : EvenJet G) (P Q : JetAlgebra G) :
    evenPartial j (P * Q) = evenPartial j P * Q + P * evenPartial j Q := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P R hP hR =>
      simp only [add_mul, map_add, hP, hR]
      abel
  | tmul p u =>
      induction Q using TensorProduct.induction_on with
      | zero => simp
      | add Q R hQ hR =>
          simp only [mul_add, map_add, hQ, hR]
          abel
      | tmul q v =>
          have h : MvPolynomial.pderiv j (p * q) =
              MvPolynomial.pderiv j p * q + p * MvPolynomial.pderiv j q := by
            simpa only [smul_eq_mul, mul_comm, add_comm] using
              (MvPolynomial.pderiv j).leibniz p q
          simp [evenPartial, Algebra.TensorProduct.tmul_mul_tmul, h,
            TensorProduct.add_tmul]



end YangMills.FullBV
