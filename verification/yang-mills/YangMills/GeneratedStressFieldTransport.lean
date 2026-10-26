import YangMills.FilteredQuantumRGReduction
import YangMills.GeneratedMixingMeaning

noncomputable section
open scoped BigOperators
namespace YangMills.FilteredRG
variable {G : CompactSimpleGaugeGroup} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Q : WightmanData H} {C : RenormalizedCompositeMap Q G}
  {m : ℕ} {labels : Fin m → PerturbativeFlow.InvariantInsertionLabel G}
  {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
  {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}

/-- The actual label transport acts on every finite SAME-C field combination,
not just on a new independently chosen family of basis operators. -/
theorem Realizes.combination {F : Frame labels reference betaSeries gammaSeries}
    (hF : Realizes (C := C) F) (t : ℝ) (ht : 0 ≤ t)
    (a : Fin m → ℂ) (f : TestFunction) (v : Q.domain) :
    (∑ i, a i • C.field reference (labels i) f v) =
      ∑ j, (F.transport t a j) • C.field (runningScale reference t) (labels j) f v := by
  classical
  simp_rw [hF t ht]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [linearEquiv_apply_sum, Finset.sum_smul]

/-- PhysicalBinding is an equality of the actual same-domain stress field
with its finite source dictionary, after clearing the positive coupling pole. -/
theorem dictionary_field_binding (dict : PerturbativeFlow.StressSourceDictionary G)
    (T : StressTensorData Q G C) (h : dict.PhysicalBinding T) (mu nu : Fin 4)
    (f : TestFunction) (v : Q.domain) :
    ((T.coupling.val ^ 2 : ℝ) : ℂ) • T.field mu nu f v =
      ∑ i, (dict.exactRegular T.coupling.val mu nu i : ℂ) •
        C.field T.scale (dict.label i) f v := by
  have eq := congrArg (C.fieldLabelLinearMap T.scale) (h mu nu)
  simp only [map_smul, map_sum] at eq
  have point := congrArg (fun A : TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain => A f v) eq
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, RCLike.real_smul_eq_coe_smul]
    using point

/-- The same physical stress at every running scale follows from the actual
reference dictionary, actual SAME-C transport and transported numerator.
It is not an independent prediction supplied at each scale. -/
theorem GeneratedStressFamily.field_transport
    {form : InvariantForm G} {e : Perturbative.ColorFrame form}
    {S : PerturbativeFlow.FixedFlowSystem e}
    {family : PerturbativeFlow.LocalWardFlowFamily S}
    (A : GeneratedStressFamily family labels)
    (F : Frame labels S.referenceScale betaSeries gammaSeries)
    (T : StressTensorData Q G C)
    (href : T.scale = S.referenceScale)
    (hg : T.coupling.val = F.running.coupling 0)
    (hbind : (A.dictionary S.referenceScale).PhysicalBinding T)
    (htransport : Realizes (C := C) F)
    (hnum : ∀ mu nu t, 0 ≤ t →
      ((F.running.coupling 0 ^ 2 : ℝ) : ℂ) •
        (fun i => (A.exactRegular (runningScale S.referenceScale t)
          (F.running.coupling t) mu nu i : ℂ)) =
      ((F.running.coupling t ^ 2 : ℝ) : ℂ) •
        F.transport t (fun i => (A.exactRegular S.referenceScale
          (F.running.coupling 0) mu nu i : ℂ)))
    (t : ℝ) (ht : 0 ≤ t) (mu nu : Fin 4) (f : TestFunction) (v : Q.domain) :
    T.field mu nu f v =
      (((F.running.coupling t)⁻¹ ^ 2 : ℝ) : ℂ) •
        ∑ i, (A.exactRegular (runningScale S.referenceScale t)
          (F.running.coupling t) mu nu i : ℂ) •
          C.field (runningScale S.referenceScale t) (labels i) f v := by
  classical
  have hb := dictionary_field_binding (A.dictionary S.referenceScale) T hbind mu nu f v
  change ((T.coupling.val ^ 2 : ℝ) : ℂ) • T.field mu nu f v =
    ∑ i, (A.exactRegular S.referenceScale T.coupling.val mu nu i : ℂ) •
      C.field T.scale (labels i) f v at hb
  rw [href, hg, htransport.combination t ht] at hb
  let E : (Fin m → ℂ) →ₗ[ℂ] Q.domain :=
    { toFun := fun a => ∑ i, a i •
        C.field (runningScale S.referenceScale t) (labels i) f v
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [smul_smul, Finset.smul_sum] }
  have hn := congrArg E (hnum mu nu t ht)
  rw [map_smul, map_smul] at hn
  change ((F.running.coupling 0 ^ 2 : ℝ) : ℂ) •
      (∑ i, (A.exactRegular (runningScale S.referenceScale t)
        (F.running.coupling t) mu nu i : ℂ) •
          C.field (runningScale S.referenceScale t) (labels i) f v) =
    ((F.running.coupling t ^ 2 : ℝ) : ℂ) •
      (∑ i, (F.transport t (fun j =>
        (A.exactRegular S.referenceScale (F.running.coupling 0) mu nu j : ℂ)) i) •
          C.field (runningScale S.referenceScale t) (labels i) f v) at hn
  have h0 : ((F.running.coupling 0 ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (ne_of_gt F.running.initial_positive)
  have ht0 : F.running.coupling t ≠ 0 := ne_of_gt (F.running.positive t ht)
  apply (smul_right_injective (M := Q.domain) h0)
  dsimp only
  rw [smul_smul, mul_comm, ← smul_smul, hn, smul_smul, ← hb, smul_smul]
  have cancel : (((F.running.coupling t)⁻¹ ^ 2 : ℝ) : ℂ) *
      ((F.running.coupling t ^ 2 : ℝ) : ℂ) = 1 := by
    norm_cast
    field_simp
  rw [cancel, one_mul]

/-- Redundancy check on the assembled SAME-stress RG conditions: the
operator transport conclusion is already forced by their dictionary data. -/
theorem GeneratedStressFamily.SameStressRG.field_derived
    {form : InvariantForm G} {e : Perturbative.ColorFrame form}
    {S : PerturbativeFlow.FixedFlowSystem e}
    {family : PerturbativeFlow.LocalWardFlowFamily S}
    {A : GeneratedStressFamily family labels}
    {F : Frame labels S.referenceScale betaSeries gammaSeries}
    {T : StressTensorData Q G C} (h : A.SameStressRG F T) :
    ∀ t : ℝ, 0 ≤ t → ∀ mu nu f v,
      T.field mu nu f v =
        (((F.running.coupling t)⁻¹ ^ 2 : ℝ) : ℂ) •
          ∑ i, (A.exactRegular (runningScale S.referenceScale t)
            (F.running.coupling t) mu nu i : ℂ) •
            C.field (runningScale S.referenceScale t) (labels i) f v :=
  A.field_transport F T h.reference_scale h.coupling h.reference_binding
    h.actual_transport h.numerator_transport

end YangMills.FilteredRG
