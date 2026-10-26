import Problems.YangMills.QuantumObservableLift
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Defs

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Actual generated-Q formal quantum cohomology in engineering filtration

Scalar formal power series encode ALL hbar orders. Every finite row is an
actual admissible field/antifield monomial with fixed engineering, ghost and
parity bounds. Matrix entries are the same QuantumWardLimit coefficients;
their ordinary formal multiplication is proved to be the exact loop Cauchy
convolution. No differential, cohomology relation or null sector is selected
independently of Q.

The ghost -1 odd slice through degree d maps to ghost zero even through d+1,
then to ghost one odd through d+2. Q.Filtered proves the finite middle slice
omits no nonzero term, while actual Q.Nilpotent proves exact implies closed.
We quotient the cocycles by this actual image. A compatible observable lift
supplies an actual class, with support controlled by its intrinsic dimension.
There is no classical/quantum bijection or physical Hilbert null assertion.
-/
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
namespace FilteredQuantum
variable {G : CompactSimpleGaugeGroup}
abbrev Scalar := PowerSeries ℂ

@[irreducible] def rows (G : CompactSimpleGaugeGroup) (d : ℕ) (ghost : ℤ) (parity : Bool) :
    Finset (LocalMonomial G) := by
  classical
  exact (monomialsBelow G (d+1)).filter fun A => A.ghostNumber = ghost ∧ A.parity = parity

structure Row (G : CompactSimpleGaugeGroup) (d : ℕ) (ghost : ℤ) (parity : Bool) where
  val : LocalMonomial G
  property : val ∈ rows G d ghost parity

def rowEquiv (d : ℕ) (ghost : ℤ) (parity : Bool) :
    Row G d ghost parity ≃ ↥(rows G d ghost parity) where
  toFun A := ⟨A.val, A.property⟩
  invFun A := { val := A.1, property := by exact A.2 }
  left_inv := by intro A; cases A; rfl
  right_inv := by intro A; cases A; rfl

instance rowFintype (d : ℕ) (ghost : ℤ) (parity : Bool) : Fintype (Row G d ghost parity) :=
  letI := Finset.fintypeCoeSort (rows G d ghost parity)
  Fintype.ofEquiv ↥(rows G d ghost parity) (rowEquiv d ghost parity).symm

lemma sum_rows {M : Type*} [AddCommMonoid M]
    (d : ℕ) (ghost : ℤ) (parity : Bool) (F : LocalMonomial G → M) :
    (∑ A : Row G d ghost parity, F A.val) = ∑ A ∈ rows G d ghost parity, F A := by
  classical
  letI := Finset.fintypeCoeSort (rows G d ghost parity)
  rw [← (rowEquiv (G := G) d ghost parity).symm.sum_comp (fun A => F A.val)]
  exact Finset.sum_coe_sort _ F

lemma mem_rows (d : ℕ) (ghost : ℤ) (parity : Bool) (A : LocalMonomial G) :
    A ∈ rows G d ghost parity ↔ A.Admissible ∧ A.dimension ≤ d ∧
      A.ghostNumber = ghost ∧ A.parity = parity := by
  classical
  simp only [rows, Finset.mem_filter, mem_monomialsBelow_iff, Nat.lt_succ_iff]
  tauto

def series (Q : QuantumWardLimit G) (g : ℝ) (A B : LocalMonomial G) : Scalar :=
  PowerSeries.mk (fun loop => Q.coefficient g loop A B)

lemma series_support (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (g : ℝ) (A B : LocalMonomial G) (ha : A.Admissible) (nz : series Q g A B ≠ 0) :
    B.Admissible ∧ B.dimension ≤ A.dimension+1 ∧
      B.ghostNumber = A.ghostNumber+1 ∧ B.parity = !A.parity := by
  have hn : ∃ loop, Q.coefficient g loop A B ≠ 0 := by
    by_contra! hn
    apply nz
    apply PowerSeries.ext
    intro loop
    simpa only [series, PowerSeries.coeff_mk, map_zero] using hn loop
  obtain ⟨loop, hn⟩ := hn
  exact filtered g loop A B ha hn

lemma series_convolution (Q : QuantumWardLimit G) (g : ℝ) (A B C : LocalMonomial G) (loop : ℕ) :
    PowerSeries.coeff loop (series Q g A B * series Q g B C) =
      ∑ l : Fin (loop+1), Q.coefficient g l.val A B * Q.coefficient g (loop-l.val) B C := by
  rw [PowerSeries.coeff_mul]
  simp only [series, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- All degree-allowed intermediates are retained; outputs are not projected
back to the original degree, so this is genuine rectangular nilpotence. -/
lemma full_composition_zero (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (A C : LocalMonomial G)
    (ha : A.Admissible) (hc : C.Admissible) :
    (∑ B ∈ monomialsBelow G (A.dimension+2), series Q g A B * series Q g B C) = 0 := by
  classical
  by_cases bound : C.dimension ≤ A.dimension+2
  · apply PowerSeries.ext
    intro loop
    simp only [map_sum, series_convolution, map_zero]
    exact nilpotent g A C loop ha hc bound
  · apply Finset.sum_eq_zero
    intro B hb
    by_cases first : series Q g A B = 0
    · simp [first]
    by_cases second : series Q g B C = 0
    · simp [second]
    have hs := series_support Q filtered g A B ha first
    have ht := series_support Q filtered g B C hs.1 second
    omega

/-- The relevant finite middle slice is complete because actual Q support
fixes its degree, ghost number and parity. -/
lemma sliced_composition_zero (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) (ghost : ℤ) (parity : Bool)
    (A : Row G d ghost parity) (C : Row G (d+2) (ghost+2) parity) :
    (∑ B ∈ rows G (d+1) (ghost+1) (!parity), series Q g A.val B * series Q g B C.val) = 0 := by
  classical
  have ha := (mem_rows (G := G) d ghost parity A.val).mp A.property
  have hc := (mem_rows (G := G) (d+2) (ghost+2) parity C.val).mp C.property
  let S := rows G (d+1) (ghost+1) (!parity)
  let T := monomialsBelow G (A.val.dimension+2)
  let F := fun B => series Q g A.val B * series Q g B C.val
  have smallS : (∑ B ∈ S, F B) = ∑ B ∈ S ∪ T, F B := by
    apply Finset.sum_subset Finset.subset_union_left
    intro B _hb outside
    by_cases hz : series Q g A.val B = 0
    · simp [F, hz]
    have hs := series_support Q filtered g A.val B ha.1 hz
    exfalso
    apply outside
    apply (mem_rows (G := G) (d+1) (ghost+1) (!parity) B).mpr
    exact ⟨hs.1, by omega, hs.2.2.1.trans (congrArg (fun z : ℤ => z+1) ha.2.2.1),
      hs.2.2.2.trans (congrArg Bool.not ha.2.2.2)⟩
  have smallT : (∑ B ∈ T, F B) = ∑ B ∈ S ∪ T, F B := by
    apply Finset.sum_subset Finset.subset_union_right
    intro B _hb outside
    by_cases hz : series Q g A.val B = 0
    · simp [F, hz]
    have hs := series_support Q filtered g A.val B ha.1 hz
    exfalso
    apply outside
    exact (mem_monomialsBelow_iff (G := G) _ _).mpr ⟨hs.1, by omega⟩
  exact smallS.trans (smallT.symm.trans (full_composition_zero Q filtered nilpotent g A.val C.val ha.1 hc.1))

abbrev Vector (G : CompactSimpleGaugeGroup) (d : ℕ) (ghost : ℤ) (parity : Bool) :=
  Row G d ghost parity → Scalar

/-- Column=input, row=output; the entries are the SAME generated Q's full
formal hbar series, not independently supplied cochain maps. -/
def matrix (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) (ghost : ℤ) (parity : Bool) :
    Matrix (Row G (d+1) (ghost+1) (!parity)) (Row G d ghost parity) Scalar :=
  fun B A => series Q g A.val B.val

def differential (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) (ghost : ℤ) (parity : Bool) :
    Vector G d ghost parity →ₗ[Scalar] Vector G (d+1) (ghost+1) (!parity) :=
  (matrix Q g d ghost parity).mulVecLin

def incomingMatrix (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Matrix (Row G (d+1) 0 false) (Row G d (-1) true) Scalar :=
  fun B A => series Q g A.val B.val

def outgoingMatrix (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Matrix (Row G (d+2) 1 true) (Row G (d+1) 0 false) Scalar :=
  fun C B => series Q g B.val C.val

def incoming (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Vector G d (-1) true →ₗ[Scalar] Vector G (d+1) 0 false :=
  (incomingMatrix Q g d).mulVecLin

def outgoing (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Vector G (d+1) 0 false →ₗ[Scalar] Vector G (d+2) 1 true :=
  (outgoingMatrix Q g d).mulVecLin

theorem matrix_square_zero (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) :
    outgoingMatrix Q g d * incomingMatrix Q g d = 0 := by
  classical
  apply Matrix.ext
  intro C A
  simp only [Matrix.mul_apply, incomingMatrix, outgoingMatrix, Matrix.zero_apply]
  simp_rw [mul_comm (series Q g _ C.val)]
  rw [sum_rows (d+1) 0 false (fun B => series Q g A.val B * series Q g B C.val)]
  have hz := sliced_composition_zero Q filtered nilpotent g d (-1) true A
    (show Row G (d+2) ((-1 : ℤ)+2) true from C)
  simpa only [Int.reduceNeg, Int.reduceAdd, Bool.not_true] using hz

theorem differential_comp_zero (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) :
    (outgoing Q g d).comp (incoming Q g d) = 0 := by
  unfold incoming outgoing
  rw [← Matrix.mulVecLin_mul, matrix_square_zero Q filtered nilpotent]
  simp

theorem range_le_ker (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) :
    LinearMap.range (incoming Q g d) ≤ LinearMap.ker (outgoing Q g d) :=
  LinearMap.range_le_ker_iff.mpr (differential_comp_zero Q filtered nilpotent g d)

def cocycles (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Submodule Scalar (Vector G (d+1) 0 false) := LinearMap.ker (outgoing Q g d)

def exactInside (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :
    Submodule Scalar (cocycles Q g d) :=
  (LinearMap.range (incoming Q g d)).comap (cocycles Q g d).subtype

/-- Full formal hbar ghost-zero cohomology at engineering bound d+1.
No classical/quantum bijection or physical Hilbert null identification occurs. -/
def H0 (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) :=
  (cocycles Q g d) ⧸ exactInside Q g d

def boundaryCocycle (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) (v : Vector G d (-1) true) :
    cocycles Q g d :=
  ⟨incoming Q g d v, range_le_ker Q filtered nilpotent g d ⟨v, rfl⟩⟩

theorem boundaryCocycle_class_zero (Q : QuantumWardLimit G) (filtered : Q.Filtered)
    (nilpotent : Q.Nilpotent) (g : ℝ) (d : ℕ) (v : Vector G d (-1) true) :
    (exactInside Q g d).mkQ (boundaryCocycle Q filtered nilpotent g d v) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (exactInside Q g d)).mpr
  exact ⟨v, rfl⟩

/-- Corrected physical representative as a formal vector in the actual
engineering slice. The bound will be used to prove no support is discarded. -/
def liftVector (lift : QuantumObservableLift G) (g : ℝ) (p : InvariantInsertionLabel G)
    (d : ℕ) : Vector G (d+1) 0 false :=
  fun A => PowerSeries.mk (fun loop => lift.physicalCoefficient g p loop A.val)

lemma lift_convolution (Q : QuantumWardLimit G) (lift : QuantumObservableLift G)
    (g : ℝ) (p : InvariantInsertionLabel G) (A C : LocalMonomial G) (loop : ℕ) :
    PowerSeries.coeff loop
      (PowerSeries.mk (fun l => lift.physicalCoefficient g p l A) * series Q g A C) =
      ∑ l : Fin (loop+1), lift.physicalCoefficient g p l.val A *
        Q.coefficient g (loop-l.val) A C := by
  rw [PowerSeries.coeff_mul]
  simp only [series, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma lift_full_cocycle {B : InvariantForm G} {e : YangMills.Perturbative.ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (g : ℝ) (p : InvariantInsertionLabel G) (loop : ℕ) (C : LocalMonomial G)
    (hc : C.Admissible) :
    (∑ l : Fin (loop+1), (lift.physicalCoefficient g p l.val).sum (fun A c =>
      c * Q.coefficient g (loop-l.val) A C)) = 0 := by
  by_cases bound : C.dimension ≤ intrinsicEngineeringDimension p + 1
  · exact compatible.cocycle g p loop C hc bound
  · apply Finset.sum_eq_zero
    intro l _hl
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro A ha
    have hs := compatible.physical_support g p l.val A (Finsupp.mem_support_iff.mp ha)
    have zero : Q.coefficient g (loop-l.val) A C = 0 := by
      by_contra hn
      have ht := compatible.ward_filtered g (loop-l.val) A C hs.1 hn
      omega
    simp [zero]

theorem liftVector_closed {B : InvariantForm G} {e : YangMills.Perturbative.ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (g : ℝ) (p : InvariantInsertionLabel G) (d : ℕ)
    (bound : intrinsicEngineeringDimension p ≤ d+1) :
    outgoing Q g d (liftVector lift g p d) = 0 := by
  classical
  funext C
  apply PowerSeries.ext
  intro loop
  change PowerSeries.coeff loop
    (∑ A : Row G (d+1) 0 false, series Q g A.val C.val *
      PowerSeries.mk (fun l => lift.physicalCoefficient g p l A.val)) = 0
  rw [map_sum]
  simp_rw [mul_comm (series Q g _ C.val), lift_convolution]
  rw [sum_rows (d+1) 0 false (fun A => ∑ l : Fin (loop+1),
    lift.physicalCoefficient g p l.val A * Q.coefficient g (loop-l.val) A C.val)]
  rw [Finset.sum_comm]
  have haC := (mem_rows (G := G) (d+2) 1 true C.val).mp C.property
  have single (l : Fin (loop+1)) :
      (∑ A ∈ rows G (d+1) 0 false, lift.physicalCoefficient g p l.val A *
        Q.coefficient g (loop-l.val) A C.val) =
      (lift.physicalCoefficient g p l.val).sum (fun A c => c * Q.coefficient g (loop-l.val) A C.val) := by
    symm
    apply Finset.sum_subset
    · intro A ha
      have hs := compatible.physical_support g p l.val A (Finsupp.mem_support_iff.mp ha)
      exact (mem_rows (G := G) (d+1) 0 false A).mpr ⟨hs.1, hs.2.1.trans bound, hs.2.2⟩
    · intro A _ha outside
      simp only [Finsupp.notMem_support_iff.mp outside, zero_mul]
  simp_rw [single]
  exact lift_full_cocycle compatible g p loop C.val haC.1

def liftCocycle {B : InvariantForm G} {e : YangMills.Perturbative.ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (g : ℝ) (p : InvariantInsertionLabel G) (d : ℕ)
    (bound : intrinsicEngineeringDimension p ≤ d+1) : cocycles Q g d :=
  ⟨liftVector lift g p d, liftVector_closed compatible g p d bound⟩

/-- The existing quantum lift now has an actual ghost-zero cohomology class;
no classical/quantum injectivity or surjectivity is asserted. -/
def liftClass {B : InvariantForm G} {e : YangMills.Perturbative.ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (g : ℝ) (p : InvariantInsertionLabel G) (d : ℕ)
    (bound : intrinsicEngineeringDimension p ≤ d+1) : H0 Q g d :=
  (exactInside Q g d).mkQ (liftCocycle compatible g p d bound)

end FilteredQuantum
end YangMills.PerturbativeFlow
