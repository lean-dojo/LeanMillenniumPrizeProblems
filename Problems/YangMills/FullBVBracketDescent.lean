import Problems.YangMills.FullBVEulerDivergence
import Problems.YangMills.FullBVEulerParity
import Problems.YangMills.FullBVIntegratedHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem rightEuler_totalDerivative (field : ExternalLeg G) (mu : Fin 4) (P : JetAlgebra G) :
    rightEuler field (totalDerivative mu P) = 0 := by
  rw [rightEuler_eq_parity_leftEuler, leftEuler_totalDerivative]
  cases field.parity <;> simp

def leftEulerFunctional (field : ExternalLeg G) : LocalFunctional G →ₗ[ℂ] JetAlgebra G :=
  (divergences G).liftQ (leftEulerLinear field) (by
    apply Submodule.span_le.mpr
    intro P hP
    obtain ⟨⟨mu,Q⟩,rfl⟩ := hP
    exact leftEuler_totalDerivative field mu Q)

def rightEulerFunctional (field : ExternalLeg G) : LocalFunctional G →ₗ[ℂ] JetAlgebra G :=
  (divergences G).liftQ (rightEulerLinear field) (by
    apply Submodule.span_le.mpr
    intro P hP
    obtain ⟨⟨mu,Q⟩,rfl⟩ := hP
    exact rightEuler_totalDerivative field mu Q)

@[simp] theorem leftEulerFunctional_localClass (field : ExternalLeg G) (P : JetAlgebra G) :
    leftEulerFunctional field (localClass P) = leftEuler field P := rfl

@[simp] theorem rightEulerFunctional_localClass (field : ExternalLeg G) (P : JetAlgebra G) :
    rightEulerFunctional field (localClass P) = rightEuler field P := rfl

/-- The fixed BV operation is now a function of the actual integrated
functionals: Euler kills divergences in BOTH arguments. No bracket witness
or chosen representative supplies its meaning. -/
def functionalBracket (P Q : LocalFunctional G) : LocalFunctional G :=
  localClass (∑ K : BasicField G,
    (rightEulerFunctional (.inl K) P * leftEulerFunctional (.inr K) Q -
      rightEulerFunctional (.inr K) P * leftEulerFunctional (.inl K) Q))

@[simp] theorem functionalBracket_localClass (P Q : JetAlgebra G) :
    functionalBracket (localClass P) (localClass Q) = localClass (densityBracket P Q) := rfl

/-- The earlier concrete graph is exactly this operation, so it cannot
admit several outputs or depend on a representative. -/
theorem bracketGraph_iff (P Q R : LocalFunctional G) :
    bracketGraph P Q R ↔ functionalBracket P Q = R := by
  constructor
  · rintro ⟨p,q,hp,hq,hr⟩
    rw [← hp,← hq,functionalBracket_localClass]
    exact hr
  · intro h
    induction P using Submodule.Quotient.induction_on with
    | _ p =>
      induction Q using Submodule.Quotient.induction_on with
      | _ q => exact ⟨p,q,rfl,rfl,h⟩

theorem bracketGraph_exists_unique (P Q : LocalFunctional G) : ∃! R, bracketGraph P Q R := by
  refine ⟨functionalBracket P Q, (bracketGraph_iff P Q _).mpr rfl, ?_⟩
  intro R hR
  exact ((bracketGraph_iff P Q R).mp hR).symm

end YangMills.FullBV
