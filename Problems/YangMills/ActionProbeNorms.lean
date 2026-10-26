import Problems.YangMills.ActionGhostAmplitude
import Problems.YangMills.KineticProbeValues
import Problems.YangMills.ActionProbeSupport
import Problems.YangMills.ProbeCalculus
import Problems.YangMills.CubicProbeValues
import Problems.YangMills.QuarticProbeValues

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace YangMills.WardAction
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The fixed ghost vertex contains the actual G structure constants. -/
theorem ghostVertex_probe {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) :
    referenceTensor e .ghostVertex (a,b,c) =
      -Complex.I * (structureConstant e a b c : ℂ) := by
  unfold referenceTensor probeTensor
  have he : (fun q => basisAmplitude e Sector.ghostVertex
      (probeLegs Sector.ghostVertex (a,b,c))
      (conservingMomenta (probeLegs Sector.ghostVertex (a,b,c)) q)) =
      fun q : Fin 3 → Spacetime =>
        (structureConstant e a b c : ℂ) * (-Complex.I * (q 0 0 : ℂ)) := by
    funext q
    change basisAmplitude e .ghostVertex
      [.inl (.antighost a), .inl (.gauge 0 b), .inl (.ghost c)] _ = _
    rw [ghostVertex_amplitude]
    simp [conservingMomenta, probeLegs]
  rw [he]
  simp [probeDirections, momentumJet]
  let L : (Fin 3 → Spacetime) →L[ℝ] ℂ :=
    ((structureConstant e a b c : ℂ) * -Complex.I) •
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj 0 : (Fin 3 → Spacetime) →L[ℝ] Spacetime)))
  have hL : (fun q : Fin 3 → Spacetime =>
      -((structureConstant e a b c : ℂ) * (Complex.I * (q 0 0 : ℂ)))) = L := by
    funext q
    simp [L]
    ring
  rw [hL, L.fderiv]
  simp [L, mul_comm, probeLegs, ContinuousLinearMap.proj]

def momentumCoordinate (n : ℕ) (i : Fin n) (μ : Fin 4) :
    (Fin n → Spacetime) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin n → Spacetime) →L[ℝ] Spacetime))

/-- Fixed transverse/massless quadratic source tensor in the dependent-last
momentum convention. -/
def kineticBilinear (transverse : Bool) :
    (Fin 2 → Spacetime) →L[ℝ] (Fin 2 → Spacetime) →L[ℝ] ℂ :=
  ∑ μ : Fin 4, if transverse && decide (μ = 1) then 0 else
    (momentumCoordinate 2 0 μ).smulRight (momentumCoordinate 2 0 μ)

theorem ghostKinetic_probe {B : InvariantForm G} (e : ColorFrame B)
    (a : Fin G.dimension) : referenceTensor e .ghostKinetic a = 2 := by
  unfold referenceTensor probeTensor
  have he : (fun q => basisAmplitude e .ghostKinetic
      (probeLegs .ghostKinetic a) (conservingMomenta (probeLegs .ghostKinetic a) q)) =
      fun q : Fin 2 → Spacetime => kineticBilinear false q q := by
    funext q
    change basisAmplitude e .ghostKinetic [.inl (.antighost a), .inl (.ghost a)] _ = _
    change Fin 2 → Spacetime at q
    rw [ghostKinetic_amplitude]
    simp [probeLegs, conservingMomenta, kineticBilinear, momentumCoordinate, ContinuousLinearMap.proj_apply, Finset.sum_filter, Fin.sum_univ_succ]
    try ring
  rw [he]
  simp [probeDirections, momentumJet]
  change iteratedFDeriv ℝ 2 (fun q : Fin 2 → Spacetime => kineticBilinear false q q) 0
    (fun i => Pi.single (List.replicate 2 ((0 : Fin 2), (0 : Fin 4)))[i.val].1
      (Pi.single (List.replicate 2 ((0 : Fin 2), (0 : Fin 4)))[i.val].2 1)) = 2
  simp only [List.getElem_replicate]
  rw [iterated_two_quadratic (kineticBilinear false) 0]
  norm_num [kineticBilinear, momentumCoordinate, ContinuousLinearMap.proj,
    Pi.single_apply, Fin.ext_iff, Finset.sum_filter, Fin.sum_univ_four]

theorem gluonKinetic_probe {B : InvariantForm G} (e : ColorFrame B)
    (a : Fin G.dimension) : referenceTensor e .gluonKinetic a = 2 := by
  unfold referenceTensor probeTensor
  have he : (fun q => basisAmplitude e .gluonKinetic
      (probeLegs .gluonKinetic a) (conservingMomenta (probeLegs .gluonKinetic a) q)) =
      fun q : Fin 2 → Spacetime => kineticBilinear true q q := by
    funext q
    change basisAmplitude e .gluonKinetic [.inl (.gauge 1 a), .inl (.gauge 1 a)] _ = _
    change Fin 2 → Spacetime at q
    rw [gluonKinetic_amplitude]
    simp [probeLegs, conservingMomenta, kineticBilinear, momentumCoordinate, ContinuousLinearMap.proj_apply, Finset.sum_filter, Fin.sum_univ_succ]
    try ring
  rw [he]
  simp [probeDirections, momentumJet]
  change iteratedFDeriv ℝ 2 (fun q : Fin 2 → Spacetime => kineticBilinear true q q) 0
    (fun i => Pi.single (List.replicate 2 ((0 : Fin 2), (0 : Fin 4)))[i.val].1
      (Pi.single (List.replicate 2 ((0 : Fin 2), (0 : Fin 4)))[i.val].2 1)) = 2
  simp only [List.getElem_replicate]
  rw [iterated_two_quadratic (kineticBilinear true) 0]
  norm_num [kineticBilinear, momentumCoordinate, ContinuousLinearMap.proj,
    Pi.single_apply, Fin.ext_iff, Finset.sum_filter, Fin.sum_univ_four]


theorem gluonKinetic_norm_pos {B : InvariantForm G} (e : ColorFrame B) :
    0 < tensorNorm (referenceTensor e .gluonKinetic) := by
  obtain ⟨a,b,c,_⟩ := structureConstant_exists_ne_zero e
  apply tensorNorm_pos
  exact ⟨a, by rw [gluonKinetic_probe]; norm_num⟩

theorem ghostKinetic_norm_pos {B : InvariantForm G} (e : ColorFrame B) :
    0 < tensorNorm (referenceTensor e .ghostKinetic) := by
  obtain ⟨a,b,c,_⟩ := structureConstant_exists_ne_zero e
  apply tensorNorm_pos
  exact ⟨a, by rw [ghostKinetic_probe]; norm_num⟩

theorem ghostVertex_norm_pos {B : InvariantForm G} (e : ColorFrame B) :
    0 < tensorNorm (referenceTensor e .ghostVertex) := by
  obtain ⟨a,b,c,h⟩ := structureConstant_exists_ne_zero e
  apply tensorNorm_pos
  refine ⟨(a,b,c), ?_⟩
  rw [ghostVertex_probe]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr h)


theorem cubic_probe {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) : referenceTensor e .cubic (a,b,c) =
      Complex.I * (structureConstant e a b c : ℂ) := by
  let L : (Fin 3 → Spacetime) →L[ℝ] ℂ :=
    (Complex.I * (structureConstant e a b c : ℂ)) •
      (momentumCoordinate 3 0 0 + (2 : ℂ) • momentumCoordinate 3 1 0)
  unfold referenceTensor probeTensor
  have he : (fun q => basisAmplitude e .cubic
      (probeLegs .cubic (a,b,c)) (conservingMomenta (probeLegs .cubic (a,b,c)) q)) = L := by
    funext q
    change Fin 3 → Spacetime at q
    change basisAmplitude e .cubic
      [.inl (.gauge 0 a), .inl (.gauge 1 b), .inl (.gauge 1 c)] _ = _
    rw [cubic_amplitude]
    simp [probeLegs, conservingMomenta, L, momentumCoordinate,
      ContinuousLinearMap.proj, Finset.sum_filter, Fin.sum_univ_three]
    ring
  rw [he]
  simp [probeDirections, momentumJet, L.fderiv]
  simp [L, momentumCoordinate, ContinuousLinearMap.proj, probeLegs]

theorem cubic_norm_pos {B : InvariantForm G} (e : ColorFrame B) :
    0 < tensorNorm (referenceTensor e .cubic) := by
  obtain ⟨a,b,c,h⟩ := structureConstant_exists_ne_zero e
  apply tensorNorm_pos
  refine ⟨(a,b,c), ?_⟩
  rw [cubic_probe]
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h)


theorem quartic_probe {B : InvariantForm G} (e : ColorFrame B)
    (a b : Fin G.dimension) : referenceTensor e .quartic (a,b) =
      2 * (fourColor B (e.basis a) (e.basis b) (e.basis a) (e.basis b) : ℂ) := by
  simp [referenceTensor, probeTensor, probeDirections, momentumJet, probeLegs,
    quartic_amplitude]

theorem quartic_norm_pos {B : InvariantForm G} (e : ColorFrame B) :
    0 < tensorNorm (referenceTensor e .quartic) := by
  obtain ⟨a,b,h⟩ := fourColor_basis_positive e
  apply tensorNorm_pos
  refine ⟨(a,b), ?_⟩
  rw [quartic_probe]
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt h))

/-- Every reference denominator is strictly positive for the ACTUAL group
and invariant form. No candidate or scheme chooses this nondegeneracy. -/
theorem fixed_probeNondegenerate {B : InvariantForm G} (e : ColorFrame B) :
    FixedProbeNondegenerate e := by
  intro s
  cases s with
  | gluonKinetic => exact ne_of_gt (gluonKinetic_norm_pos e)
  | ghostKinetic => exact ne_of_gt (ghostKinetic_norm_pos e)
  | cubic => exact ne_of_gt (cubic_norm_pos e)
  | ghostVertex => exact ne_of_gt (ghostVertex_norm_pos e)
  | quartic => exact ne_of_gt (quartic_norm_pos e)

/-- Equality of every physical local jet determines the five advertised
coordinates unconditionally: both source-support and denominator properties
are now theorems of the fixed actual-G action. -/
theorem PhysicalActionDecomposition.coordinates_fixed {B : InvariantForm G}
    (e : ColorFrame B) (F : OrderedAmplitude G) (z : Sector → ℝ)
    (h : PhysicalActionDecomposition e F z) (s : Sector) :
    coordinate e s F = z s :=
  PhysicalActionDecomposition.coordinates e F z h
    (fixed_crossSectorSupport e) (fixed_probeNondegenerate e) s

/-- A full multiplicative physical-sector jet decomposition fixes every
coefficient of the actual projected normalization series. This is only a
conditional recovery theorem; raw finite-cutoff Ward closure is not imposed. -/
theorem normalizationSeries_eq_of_decomposition {B : InvariantForm G}
    (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ)
    (z : Sector → Series)
    (h : ∀ n, PhysicalActionDecomposition e (uvActionCoefficient A μ Λ0 n)
      (fun s => if couplingOffset s ≤ n then
        PowerSeries.coeff (n - couplingOffset s) (z s) else 0)) (s : Sector) :
    normalizationSeries e A μ Λ0 s = z s := by
  ext k
  simp only [normalizationSeries, PowerSeries.coeff_mk]
  have hh := PhysicalActionDecomposition.coordinates_fixed e _ _
    (h (k + couplingOffset s)) s
  have hk : couplingOffset s ≤ k + couplingOffset s := Nat.le_add_left _ _
  simpa only [if_pos hk, Nat.add_sub_cancel_right] using hh

end YangMills.WardAction
