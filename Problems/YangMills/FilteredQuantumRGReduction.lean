import Problems.YangMills.FilteredQuantumRG

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.FilteredRG
variable {G : CompactSimpleGaugeGroup} {m : ℕ}
variable {labels : Fin m → PerturbativeFlow.InvariantInsertionLabel G}
variable {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}

/-- An existing homogeneous frame is a special filtered frame with no
explicit subtraction-scale dependence in its exact gamma completion. -/
def Frame.ofHomogeneous (reference : RenormalizationScale)
    (F : RG.Frame labels betaSeries gammaSeries) :
    Frame labels reference betaSeries (fun _ => gammaSeries) where
  running := F.running
  gamma _ g i j := F.gamma g i j
  gamma_smooth i j := ((F.gamma_smooth i j).comp contDiff_snd).contDiffOn
  gamma_jet _ := F.gamma_jet
  transport := F.transport
  initial := F.initial
  filtered t i j higher := F.homogeneous t i j (Ne.symm (Nat.ne_of_lt higher))
  equation := F.equation

lemma linearEquiv_apply_sum (M : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ))
    (v : Fin m → ℂ) (i : Fin m) :
    M v i = ∑ j : Fin m, v j * M (Pi.single j 1) i := by
  nth_rw 1 [pi_eq_sum_univ' v]
  rw [map_sum]
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul]

/-- Numerical engineering weights separate distinct classical grades. -/
def degreeOperator (v : Fin m → ℂ) : Fin m → ℂ :=
  fun i => (OPE.dimension (labels i) : ℂ) * v i

lemma homogeneous_commutes_degree (F : RG.Frame labels betaSeries gammaSeries)
    (t : ℝ) (v : Fin m → ℂ) :
    F.transport t (degreeOperator (labels := labels) v) =
      degreeOperator (labels := labels) (F.transport t v) := by
  ext i
  rw [linearEquiv_apply_sum]
  unfold degreeOperator
  rw [linearEquiv_apply_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases equal : OPE.dimension (labels i) = OPE.dimension (labels j)
  · rw [equal]; ring
  · rw [F.homogeneous t i j equal]
    simp

lemma homogeneous_inverse_commutes_degree (F : RG.Frame labels betaSeries gammaSeries)
    (t : ℝ) (v : Fin m → ℂ) :
    (F.transport t).symm (degreeOperator (labels := labels) v) =
      degreeOperator (labels := labels) ((F.transport t).symm v) := by
  apply (F.transport t).injective
  rw [LinearEquiv.apply_symm_apply,homogeneous_commutes_degree,LinearEquiv.apply_symm_apply]

/-- The inverse transport has the same degree blocks; this is derived from
the existing frame rather than added as a new condition. -/
theorem homogeneous_inverse (F : RG.Frame labels betaSeries gammaSeries)
    (t : ℝ) (i j : Fin m)
    (different : OPE.dimension (labels i) ≠ OPE.dimension (labels j)) :
    (F.transport t).symm (Pi.single j 1) i = 0 := by
  have equal := congrFun (homogeneous_inverse_commutes_degree F t (Pi.single j 1)) i
  have single : degreeOperator (labels := labels) (Pi.single j 1) =
      (OPE.dimension (labels j) : ℂ) • (Pi.single j 1 : Fin m → ℂ) := by
    ext k
    by_cases same : k=j
    · subst k; simp [degreeOperator]
    · simp [degreeOperator,Pi.single_eq_of_ne same]
  rw [single,map_smul] at equal
  change (OPE.dimension (labels j) : ℂ) * _ = (OPE.dimension (labels i) : ℂ) * _ at equal
  have scalars : (OPE.dimension (labels j) : ℂ) ≠ (OPE.dimension (labels i) : ℂ) := by
    exact_mod_cast different.symm
  have product : ((OPE.dimension (labels j) : ℂ) - OPE.dimension (labels i)) *
      (F.transport t).symm (Pi.single j 1) i = 0 := by linear_combination equal
  exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr scalars)

/-- The corrected filtered coefficient formula reduces to the existing
homogeneous formula: all nonzero transport entries have matching degrees. -/
theorem strippedMultiPairing_ofHomogeneous (reference : RenormalizationScale)
    (F : RG.Frame labels betaSeries gammaSeries)
    (coeff : (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (scale : ℝ) (n : ℕ) (inputs : Fin n → Fin m) (last output : Fin m)
    (test : OPE.RelativeTest n) :
    strippedMultiPairing (Frame.ofHomogeneous reference F) coeff scale n inputs last output test =
      RG.multiStrippedPairing F (coeff n) scale inputs last output test := by
  classical
  unfold strippedMultiPairing RG.multiStrippedPairing Frame.ofHomogeneous
  apply Finset.sum_congr rfl
  intro is _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases outdegree : OPE.dimension (labels output) = OPE.dimension (labels k)
  · by_cases lastdegree : OPE.dimension (labels j) = OPE.dimension (labels last)
    · by_cases indegree : ∀ r, OPE.dimension (labels (is r)) = OPE.dimension (labels (inputs r))
      · have sums : (∑ r : Fin n, (OPE.dimension (labels (is r)) : ℤ)) =
            ∑ r : Fin n, (OPE.dimension (labels (inputs r)) : ℤ) :=
          Finset.sum_congr rfl (fun r _ => congrArg (fun d : ℕ => (d : ℤ)) (indegree r))
        rw [sums,outdegree,lastdegree]
        ring
      · obtain ⟨r,hr⟩ := not_forall.mp indegree
        have zero : (∏ r : Fin n, (F.transport (RG.time scale)).symm
            (Pi.single (inputs r) 1) (is r)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ r) (homogeneous_inverse F _ _ _ hr)
        simp only [zero,mul_zero,zero_mul]
    · rw [homogeneous_inverse F _ _ _ lastdegree]
      simp
  · rw [F.homogeneous _ _ _ outdegree]
    simp

lemma homogeneous_rotated_inverse (F : RG.Frame labels betaSeries gammaSeries)
    (W : Wick.LabelRotation labels)
    (rotation_homogeneous : ∀ i j, OPE.dimension (labels i) ≠ OPE.dimension (labels j) →
      W.map (Pi.single j 1) i = 0)
    (t : ℝ) (i j : Fin m) (different : OPE.dimension (labels i) ≠ OPE.dimension (labels j)) :
    (F.transport t).symm (W.map (Pi.single j 1)) i = 0 := by
  rw [linearEquiv_apply_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : OPE.dimension (labels k) = OPE.dimension (labels j)
  · rw [homogeneous_inverse F _ i k (by simpa only [same] using different),mul_zero]
  · rw [rotation_homogeneous k j same,zero_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {C : RenormalizedCompositeMap Q G}

/-- Word normalization also reduces exactly when the actual Wick label map
preserves engineering grades. It introduces no outgoing word factor. -/
theorem strippedVacuumWord_ofHomogeneous {K : OPE.MultiKernels C}
    (V : PhysicalWords.VacuumWordContinuation K) (reference : RenormalizationScale)
    (F : RG.Frame labels betaSeries gammaSeries) (W : Wick.LabelRotation labels)
    (rotation_homogeneous : ∀ i j, OPE.dimension (labels i) ≠ OPE.dimension (labels j) →
      W.map (Pi.single j 1) i = 0)
    (scale : ℝ) (n : ℕ) (inputs : Fin (n+1) → Fin m)
    (test : PhysicalWords.WordTest (n+1)) :
    strippedVacuumWord V (Frame.ofHomogeneous reference F) W scale n inputs test =
      PhysicalWords.strippedVacuumWord V F W reference scale n inputs test := by
  classical
  unfold strippedVacuumWord PhysicalWords.strippedVacuumWord Frame.ofHomogeneous
  apply Finset.sum_congr rfl
  intro indices _
  by_cases same : ∀ r, OPE.dimension (labels (indices r)) = OPE.dimension (labels (inputs r))
  · have sums : (∑ r : Fin (n+1), OPE.dimension (labels (indices r))) =
        ∑ r : Fin (n+1), OPE.dimension (labels (inputs r)) :=
      Finset.sum_congr rfl (fun r _ => same r)
    change _ = _ * (((scale ^ (∑ r : Fin (n+1), OPE.dimension (labels (indices r))) : ℝ) : ℂ)) * _
    rw [sums]
    ring
  · obtain ⟨r,hr⟩ := not_forall.mp same
    have zero : (∏ r : Fin (n+1), (F.transport (RG.time scale)).symm
        (W.map (Pi.single (inputs r) 1)) (indices r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (homogeneous_rotated_inverse F W rotation_homogeneous _ _ _ hr)
    simp only [zero,mul_zero,zero_mul]

end YangMills.FilteredRG
