import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import YangMills.Spectrum

/-!
# Unbounded Hamiltonians: domains, self-adjointness, and spectrum

A Hamiltonian is not assumed bounded. Its domain is part of the data.
The resolvent below is a bounded two-sided inverse on the entire Hilbert
space; thus the resulting spectrum includes continuous spectrum.
-/

noncomputable section
namespace YangMills

universe u
variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure DenselyDefinedOperator where
  domain : Submodule ℂ H
  toLinearMap : domain →ₗ[ℂ] H
  dense_domain : Dense (domain : Set H)

namespace DenselyDefinedOperator
variable {H}

/-- Equality with the adjoint, expressed through its graph. In particular
this is stronger than symmetry on a common core. The inner product is
conjugate-linear in its first argument. -/
def IsSelfAdjoint (A : DenselyDefinedOperator H) : Prop :=
  ∀ v w : H,
    (∀ u : A.domain, inner ℂ (A.toLinearMap u) v = inner ℂ (u : H) w) ↔
    ∃ hv : v ∈ A.domain, A.toLinearMap ⟨v, hv⟩ = w

/-- The bounded inverse condition for A - zI, including both inverse laws
and the requirement that the inverse lands in the operator domain. -/
def InResolvent (A : DenselyDefinedOperator H) (z : ℂ) : Prop :=
  ∃ R : H →L[ℂ] H, ∃ hR : ∀ v, R v ∈ A.domain,
    (∀ v, A.toLinearMap ⟨R v, hR v⟩ - z • R v = v) ∧
    (∀ u : A.domain, R (A.toLinearMap u - z • (u : H)) = (u : H))

/-- Full complex spectrum, defined from the operator rather than supplied. -/
def spectrum (A : DenselyDefinedOperator H) : Set ℂ :=
  {z | ¬ A.InResolvent z}

/-- The real spectral set used by Jaffe–Witten's gap clause. -/
def realSpectrum (A : DenselyDefinedOperator H) : Set ℝ :=
  {E | (E : ℂ) ∈ A.spectrum}

/-- An eigenvalue is necessarily in the spectrum. This checks that the
resolvent definition cannot erase the vacuum or other eigenstates. -/
theorem eigenvalue_mem_spectrum (A : DenselyDefinedOperator H)
    (z : ℂ) (v : A.domain) (hne : (v : H) ≠ 0)
    (hv : A.toLinearMap v = z • (v : H)) : z ∈ A.spectrum := by
  rintro ⟨R, hR, _, hleft⟩
  have hz := hleft v
  rw [hv, sub_self, map_zero] at hz
  exact hne hz.symm

end DenselyDefinedOperator
end YangMills
