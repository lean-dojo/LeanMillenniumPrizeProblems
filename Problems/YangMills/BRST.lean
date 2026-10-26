import Problems.YangMills.Renormalization
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.MvPolynomial.PDeriv

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed classical ghost algebra and BRST signs

The coefficient algebra is an exterior algebra, not commuting scalar ghosts.
The quadratic ghost BRST generator uses the actual Lie bracket of G.
The degree-one Chevalley--Eilenberg differential squares to zero by Jacobi.
This is the ghost part of the classical BRST differential only; it does not
claim quantum Ward restoration, a jet-algebra differential or a BV quotient.

Real Lie-algebra convention: sc = -g [c,c]/2. Complex hermitian-generator
conventions insert i consistently in both bracket and action.
-/
noncomputable section
namespace YangMills.Perturbative.BRST

variable {G : CompactSimpleGaugeGroup}

abbrev GhostAlgebra (G : CompactSimpleGaugeGroup) :=
  ExteriorAlgebra ℝ (Fin G.dimension →₀ ℝ)

def ghost (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) : GhostAlgebra G :=
  ExteriorAlgebra.ι ℝ (Finsupp.single a 1)

theorem ghost_sq_zero (a : Fin G.dimension) : ghost G a * ghost G a = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem ghost_anticommute (a b : Fin G.dimension) :
    ghost G a * ghost G b + ghost G b * ghost G a = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

/-- Components of sc are fixed by the actual color bracket, including the
factor 1/2 necessitated by summing ordered color pairs. -/
def ghostVariation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) : GhostAlgebra G :=
  ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    (-(g / 2) * structureConstant e a b c) • (ghost G b * ghost G c)

@[simp] theorem ghostVariation_zero {B : InvariantForm G} (e : ColorFrame B)
    (a : Fin G.dimension) : ghostVariation e 0 a = 0 := by
  simp [ghostVariation]

/-- CE differential of a linear ghost observable, with the BRST sign. -/
def differentialOne (f : G.Algebra →ₗ[ℝ] ℝ) (x y : G.Algebra) : ℝ :=
  -f ⁅x, y⁆

/-- The next CE differential, explicitly fixing all three alternating signs.
Its inputs need not be arbitrary predicates or chosen differentials. -/
def differentialTwo (f : G.Algebra → G.Algebra → ℝ)
    (x y z : G.Algebra) : ℝ :=
  -f ⁅x, y⁆ z + f ⁅x, z⁆ y - f ⁅y, z⁆ x

theorem differentialOne_self (f : G.Algebra →ₗ[ℝ] ℝ) (x : G.Algebra) :
    differentialOne f x x = 0 := by
  simp [differentialOne]

/-- The cubic nilpotency equation of the ghost differential is a theorem
of the same G's Jacobi identity, rather than an assumed BRST axiom. -/
theorem differential_square_zero (f : G.Algebra →ₗ[ℝ] ℝ)
    (x y z : G.Algebra) :
    differentialTwo (differentialOne f) x y z = 0 := by
  have hxy : ⁅⁅x, z⁆, y⁆ = -⁅y, ⁅x, z⁆⁆ := (lie_skew _ _).symm
  have hyz : ⁅⁅y, z⁆, x⁆ = -⁅x, ⁅y, z⁆⁆ := (lie_skew _ _).symm
  simp only [differentialTwo, differentialOne, neg_neg]
  rw [hxy, hyz, map_neg, map_neg, lie_lie, map_sub]
  ring

/-- Ordinary jet multiindices; derivatives commute on the formal jet algebra. -/
abbrev Multiindex := Fin 4 → ℕ

inductive EvenJet (G : CompactSimpleGaugeGroup)
  | gauge (mu : Fin 4) (color : Fin G.dimension) (derivative : Multiindex)
  | auxiliary (color : Fin G.dimension) (derivative : Multiindex)
  deriving DecidableEq

inductive OddJet (G : CompactSimpleGaugeGroup)
  | ghost (color : Fin G.dimension) (derivative : Multiindex)
  | antighost (color : Fin G.dimension) (derivative : Multiindex)
  deriving DecidableEq

/-- The full antifield-free local super-polynomial algebra: commuting gauge/B
jets tensored with exterior ghost/antighost jets. Ghosts are not assigned
commuting numerical values. -/
abbrev JetAlgebra (G : CompactSimpleGaugeGroup) :=
  TensorProduct ℝ (MvPolynomial (EvenJet G) ℝ)
    (ExteriorAlgebra ℝ (OddJet G →₀ ℝ))

def evenJet (j : EvenJet G) : JetAlgebra G :=
  TensorProduct.tmul ℝ (MvPolynomial.X j) 1

def oddJet (j : OddJet G) : JetAlgebra G :=
  TensorProduct.tmul ℝ 1 (ExteriorAlgebra.ι ℝ (Finsupp.single j 1))

theorem oddJet_sq_zero (j : OddJet G) : oddJet j * oddJet j = 0 := by
  simp [oddJet, Algebra.TensorProduct.tmul_mul_tmul]

/-- BRST generator images in the real bracket convention before the auxiliary
B field redefinition: sA=Dc, sc=-g[c,c]/2, scbar=B, sB=0.
This fixes the images, but is not yet an extension to a graded derivation of
the jet algebra. Such an extension must commute with total jet derivatives. -/
def basicVariation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    BasicField G → JetAlgebra G
  | .gauge mu a =>
      oddJet (.ghost a (Pi.single mu 1)) +
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (g * structureConstant e a b c) •
          (evenJet (.gauge mu b 0) * oddJet (.ghost c 0))
  | .ghost a =>
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (-(g / 2) * structureConstant e a b c) •
          (oddJet (.ghost b 0) * oddJet (.ghost c 0))
  | .antighost a => evenJet (.auxiliary a 0)
  | .auxiliary _ => 0

@[simp] theorem basicVariation_auxiliary {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) : basicVariation e g (.auxiliary a) = 0 := rfl

@[simp] theorem basicVariation_antighost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    basicVariation e g (.antighost a) = evenJet (.auxiliary a 0) := rfl

/-- Canonical left Grassmann derivative: exterior contraction by coordinate
evaluation, hence the anticommuting signs are fixed by the algebra. -/
def oddPartial (j : OddJet G) : JetAlgebra G →ₗ[ℝ] JetAlgebra G :=
  TensorProduct.map LinearMap.id
    (CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply j))

def evenPartial (j : EvenJet G) : JetAlgebra G →ₗ[ℝ] JetAlgebra G :=
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

def leftPartial : JetIndex G → JetAlgebra G →ₗ[ℝ] JetAlgebra G
  | .inl j => evenPartial j
  | .inr j => oddPartial j

/-- Ordered external differentiation; the first listed leg differentiates
first. This is the convention used by the ordered amplitude flow. -/
def externalDerivative : List (JetIndex G) → JetAlgebra G →ₗ[ℝ] JetAlgebra G
  | [] => LinearMap.id
  | j :: js => (externalDerivative js).comp (leftPartial j)

def oddAugmentation : ExteriorAlgebra ℝ (OddJet G →₀ ℝ) →ₐ[ℝ] ℝ :=
  ExteriorAlgebra.lift ℝ ⟨0, by intro m; simp⟩

/-- Evaluate every gauge/auxiliary/ghost jet at zero. -/
def augmentation : JetAlgebra G →ₗ[ℝ] ℝ :=
  TensorProduct.lift (LinearMap.mk₂ ℝ
    (fun p e => MvPolynomial.eval (fun _ => 0) p * oddAugmentation e)
    (by intro p q e; simp [add_mul])
    (by intro r p e; simp [mul_assoc])
    (by intro p e f; simp [mul_add])
    (by intro r p e; simp [mul_left_comm]))

/-- Amputated ordered external coefficient, including even-variable factorials
and odd-variable signs. It is extracted from the same actual jet polynomial. -/
def externalCoefficient (w : List (JetIndex G)) (P : JetAlgebra G) : ℝ :=
  augmentation (externalDerivative w P)

/-- A fully specified coordinate differential for polynomial jets. Its
summands are fixed partials, not freely supplied maps on observables. Finite
partial support is proved below, excluding infinite-support totalization. -/
def coordinateDifferential (evenImage : EvenJet G → JetAlgebra G)
    (oddImage : OddJet G → JetAlgebra G) (P : JetAlgebra G) : JetAlgebra G :=
  (∑ᶠ j : EvenJet G, evenImage j * evenPartial j P) +
    ∑ᶠ j : OddJet G, oddImage j * oddPartial j P

theorem exteriorPartials_finite (e : ExteriorAlgebra ℝ (OddJet G →₀ ℝ)) :
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
    (O : OddJet G → JetAlgebra G) (r : ℝ) (P : JetAlgebra G) :
    coordinateDifferential E O (r • P) = r • coordinateDifferential E O P := by
  simp only [coordinateDifferential, map_smul, mul_smul_comm]
  rw [← smul_finsum' r (evenSummands_finite E P),
    ← smul_finsum' r (oddSummands_finite O P), smul_add]

def coordinateDifferentialLinear (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) : JetAlgebra G →ₗ[ℝ] JetAlgebra G where
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

def EvenJet.shift (mu : Fin 4) : EvenJet G → EvenJet G
  | .gauge nu a alpha => .gauge nu a (alpha + Pi.single mu 1)
  | .auxiliary a alpha => .auxiliary a (alpha + Pi.single mu 1)

def OddJet.shift (mu : Fin 4) : OddJet G → OddJet G
  | .ghost a alpha => .ghost a (alpha + Pi.single mu 1)
  | .antighost a alpha => .antighost a (alpha + Pi.single mu 1)

/-- Concrete total jet derivative, obtained from the fixed coordinate partials. -/
def totalDerivative (mu : Fin 4) (P : JetAlgebra G) : JetAlgebra G :=
  coordinateDifferential (fun j => evenJet (j.shift mu))
    (fun j => oddJet (j.shift mu)) P

def derivativeList (alpha : Multiindex) : List (Fin 4) :=
  (List.finRange 4).flatMap (fun mu => List.replicate (alpha mu) mu)

def totalDerivatives (alpha : Multiindex) (P : JetAlgebra G) : JetAlgebra G :=
  (derivativeList alpha).foldr totalDerivative P

def evenVariation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    EvenJet G → JetAlgebra G
  | .gauge mu a alpha => totalDerivatives alpha (basicVariation e g (.gauge mu a))
  | .auxiliary a alpha => totalDerivatives alpha (basicVariation e g (.auxiliary a))

def oddVariation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    OddJet G → JetAlgebra G
  | .ghost a alpha => totalDerivatives alpha (basicVariation e g (.ghost a))
  | .antighost a alpha => totalDerivatives alpha (basicVariation e g (.antighost a))

/-- Fixed antifield-free classical BRST extension on every superjet polynomial.
All sums have finite support by the partial-support lemmas above. The graded
Leibniz, derivative-commutation and full nilpotency equivalences remain to prove. -/
def classicalBRST {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : JetAlgebra G :=
  coordinateDifferential (evenVariation e g) (oddVariation e g) P

def parity : JetAlgebra G →ₗ[ℝ] JetAlgebra G :=
  TensorProduct.map LinearMap.id CliffordAlgebra.involute.toLinearMap

/-- The full graded Leibniz identity for canonical exterior contraction. -/
theorem contraction_product (d : Module.Dual ℝ (OddJet G →₀ ℝ))
    (u v : ExteriorAlgebra ℝ (OddJet G →₀ ℝ)) :
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

@[simp] theorem totalDerivative_evenJet (mu : Fin 4) (j : EvenJet G) :
    totalDerivative mu (evenJet j) = evenJet (j.shift mu) :=
  coordinateDifferential_evenJet _ _ _

@[simp] theorem totalDerivative_oddJet (mu : Fin 4) (j : OddJet G) :
    totalDerivative mu (oddJet j) = oddJet (j.shift mu) :=
  coordinateDifferential_oddJet _ _ _

@[simp] theorem totalDerivatives_zero (P : JetAlgebra G) : totalDerivatives 0 P = P := by
  simp [totalDerivatives, derivativeList, List.finRange_succ]

theorem classicalBRST_evenJet {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (j : EvenJet G) : classicalBRST e g (evenJet j) = evenVariation e g j :=
  coordinateDifferential_evenJet _ _ _

theorem classicalBRST_oddJet {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (j : OddJet G) : classicalBRST e g (oddJet j) = oddVariation e g j :=
  coordinateDifferential_oddJet _ _ _

end YangMills.Perturbative.BRST
