import Problems.YangMills.LowProjectorAdequacy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma directionalWord_append (left right : List E) (f : E → ℂ) :
    directionalWord (left ++ right) f = directionalWord left (directionalWord right f) := by
  induction left with
  | nil => rfl
  | cons v rest ih => simp only [List.cons_append,directionalWord,ih]

lemma directionalWord_zero (directions : List E) : directionalWord directions (0 : E → ℂ) = 0 := by
  induction directions with
  | nil => rfl
  | cons v rest ih =>
    simp only [directionalWord,ih]
    funext x
    simp only [fderiv_zero,Pi.zero_apply,zero_apply]

variable {G : CompactSimpleGaugeGroup}

/-- Admissible vanishing PDEs generate a genuine differential ideal of
actual smooth momentum jets. Any reordered extension also vanishes. -/
theorem momentumJet_extension_zero (legs : List (ExternalLeg G))
    (directions lower extra : List (Fin legs.length × Fin 4))
    (permutation : directions.Perm (extra ++ lower))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (vanishing : ∀ q, momentumJet lower f q = 0) (q : Fin legs.length → Spacetime) :
    momentumJet directions f q = 0 := by
  rw [momentumJet_perm legs permutation smooth,momentumJet_eq_directionalWord _ _ smooth]
  rw [List.map_append,directionalWord_append]
  have lower_zero : directionalWord
      (lower.map (fun d => (Pi.single d.1 (Pi.single d.2 1) : Fin legs.length → Spacetime))) f = 0 := by
    funext p
    rw [← momentumJet_eq_directionalWord legs lower smooth]
    exact vanishing p
  rw [lower_zero,directionalWord_zero]
  rfl

/-- The actual high-dimensional canonical projector imposes the specified
constant-coefficient PDE at every independent momentum. -/
theorem admissibleHighProjectorAdequacy (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (boundary : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (admissible : (directionMonomial legs directions).Admissible)
    (degree : D < totalDimension legs + directions.length) (q : Fin legs.length → Spacetime) :
    momentumJet directions (A legs) q = 0 := by
  apply (canonicalJetExtraction_zero_iff A smooth graded legs directions q).mp
  exact boundary _ admissible (by rw [directionMonomial_dimension]; exact degree) _

end YangMills.PerturbativeFlow
