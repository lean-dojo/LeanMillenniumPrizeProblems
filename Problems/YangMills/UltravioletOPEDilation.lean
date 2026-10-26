import Problems.YangMills.RegulatedOPEDilation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative Filter
variable {G : CompactSimpleGaugeGroup}

/-- A genuine UV limit transports along the same cofinal positive cutoff
change. The limiting coefficient remains fixed by the actual extraction. -/
theorem IsUltravioletOPECoefficient.rescale (a : ℝ) (positive : 0 < a)
    (L : InsertedFlowFamily G) (F : OversubtractedFamily G) (mu : ℝ)
    (input : InsertionCluster G) (loop : ℕ) (output : LocalMonomial G) (value : ℂ)
    (h : IsUltravioletOPECoefficient L F (a*mu) (dilateInsertionCluster a input) loop output value) :
    IsUltravioletOPECoefficient (rescaleInsertedFlow a L) (rescaleOversubtractions a F) mu input loop output
      ((a : ℂ)^((output.dimension : ℤ)-positionedInsertionDegreeSum input.insertions) * value) := by
  refine ⟨(mul_pos_iff_of_pos_left positive).mp h.1, ?_⟩
  have cofinal : Tendsto (fun uv : ℝ => a*uv) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos positive).mpr tendsto_id
  have limit := (h.2.comp cofinal).const_mul
    ((a : ℂ)^((output.dimension : ℤ)-positionedInsertionDegreeSum input.insertions))
  simpa only [regulatedOPECoefficient_rescale a positive] using! limit

end YangMills.PerturbativeFlow
