import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SelfAdjoint
import Mathlib.Analysis.Calculus.Deriv.Basic
import Problems.YangMills.Spectrum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Unbounded Hamiltonians: domains, self-adjointness, and spectrum

A Hamiltonian is not assumed bounded. Its domain is part of the data.
The resolvent and full spectrum use Physlib. The adapter theorem below proves
that resolvent membership is exactly the bounded two-sided inverse condition
on the entire space. The domain and adjoint-graph interface remain local;
on complete spaces, the latter is proved equivalent to Physlib self-adjointness.
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

/-- The partial linear map used by Physlib, with exactly the same domain and action. -/
def toLinearPMap (A : DenselyDefinedOperator H) : H →ₗ.[ℂ] H :=
  ⟨A.domain, A.toLinearMap⟩

/-- Equality with the adjoint, expressed through its graph. In particular
this is stronger than symmetry on a common core. The inner product is
conjugate-linear in its first argument. -/
def IsSelfAdjoint (A : DenselyDefinedOperator H) : Prop :=
  ∀ v w : H,
    (∀ u : A.domain, inner ℂ (A.toLinearMap u) v = inner ℂ (u : H) w) ↔
    ∃ hv : v ∈ A.domain, A.toLinearMap ⟨v, hv⟩ = w

/-- On a Hilbert space, the graph condition is exactly Physlib's self-adjointness. -/
theorem isSelfAdjoint_iff [CompleteSpace H] (A : DenselyDefinedOperator H) :
    A.IsSelfAdjoint ↔ _root_.IsSelfAdjoint A.toLinearPMap := by
  have graph_eq (T S : H →ₗ.[ℂ] H) : T.graph = S.graph ↔ T = S := by
    constructor
    · intro h
      exact le_antisymm (LinearPMap.le_graph_iff.mp h.le)
        (LinearPMap.le_graph_iff.mp h.ge)
    · rintro rfl
      rfl
  rw [LinearPMap.isSelfAdjoint_def, ← graph_eq,
    LinearPMap.adjoint_graph_eq_graph_adjoint A.dense_domain]
  simp only [IsSelfAdjoint, Submodule.ext_iff, Submodule.mem_adjoint_iff,
    LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    Prod.forall, forall_exists_index, forall_apply_eq_imp_iff, sub_eq_zero, Subtype.forall]
  rfl

/-- Membership in Physlib's resolvent set of the actual partial operator. -/
def InResolvent (A : DenselyDefinedOperator H) (z : ℂ) : Prop :=
  z ∈ A.toLinearPMap.resolventSet

/-- Physlib's resolvent is equivalent to a bounded two-sided inverse on the
entire Hilbert space, whose range lies in the operator domain. -/
theorem inResolvent_iff (A : DenselyDefinedOperator H) (z : ℂ) :
    A.InResolvent z ↔
      ∃ R : H →L[ℂ] H, ∃ hR : ∀ v, R v ∈ A.domain,
        (∀ v, A.toLinearMap ⟨R v, hR v⟩ - z • R v = v) ∧
        (∀ u : A.domain, R (A.toLinearMap u - z • (u : H)) = (u : H)) := by
  let T := A.toLinearPMap - z • 1
  have hdom : T.domain = A.domain := by simp [T, LinearPMap.sub_domain, toLinearPMap]
  have happ (x : T.domain) : T x = A.toLinearMap ⟨x, hdom ▸ x.property⟩ - z • (x : H) := rfl
  change (T.toFun.ker = ⊥ ∧ T.toFun.range = ⊤ ∧ Continuous T.inverse) ↔ _
  constructor
  · rintro ⟨hinj, hsurj, hcont⟩
    have hidom : T.inverse.domain = ⊤ := LinearPMap.inverse_domain.trans hsurj
    let incl : H →ₗ[ℂ] T.inverse.domain :=
      { toFun := fun x => ⟨x, hidom.symm ▸ Submodule.mem_top⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let R : H →L[ℂ] H :=
      ⟨T.inverse.toFun.comp incl, hcont.comp (continuous_id.subtype_mk _)⟩
    have hR (x : H) : R x ∈ A.domain := by
      rw [← hdom, ← LinearPMap.inverse_range hinj]
      exact ⟨incl x, rfl⟩
    refine ⟨R, hR, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hsurj x
      have hInv : R x = (y : H) := LinearPMap.inverse_apply_eq hinj hy
      simpa only [hInv] using (happ y).symm.trans hy
    · intro x
      exact LinearPMap.inverse_apply_eq hinj (x := ⟨x, hdom.symm ▸ x.property⟩) rfl
  · rintro ⟨R, hR, hright, hleft⟩
    have hinj : T.toFun.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      change T x = 0 at hx
      apply Subtype.ext
      have h := hleft ⟨x, hdom ▸ x.property⟩
      rw [← happ x, hx, map_zero] at h
      exact h.symm
    have hsurj : T.toFun.range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro x
      exact ⟨⟨R x, hdom.symm ▸ hR x⟩, hright x⟩
    refine ⟨hinj, hsurj, ?_⟩
    have heq : (fun x : T.inverse.domain => T.inverse x) =
        (fun x : T.inverse.domain => R (x : H)) := by
      funext x
      exact LinearPMap.inverse_apply_eq hinj
        (x := ⟨R x, hdom.symm ▸ hR x⟩) (hright x)
    rw [show T.inverse.toFun' = (fun x : T.inverse.domain => R (x : H)) from heq]
    exact R.continuous.comp continuous_subtype_val

/-- Physlib's full complex spectrum, including continuous spectrum. -/
def spectrum (A : DenselyDefinedOperator H) : Set ℂ :=
  A.toLinearPMap.spectrum

/-- The real spectral set used by Jaffe–Witten's gap clause. -/
def realSpectrum (A : DenselyDefinedOperator H) : Set ℝ :=
  {E | (E : ℂ) ∈ A.spectrum}

/-- An eigenvalue is necessarily in the spectrum. This checks that the
resolvent definition cannot erase the vacuum or other eigenstates. -/
theorem eigenvalue_mem_spectrum (A : DenselyDefinedOperator H)
    (z : ℂ) (v : A.domain) (hne : (v : H) ≠ 0)
    (hv : A.toLinearMap v = z • (v : H)) : z ∈ A.spectrum := by
  apply A.toLinearPMap.pointSpectrum_subset_spectrum
  intro hker
  have hx : (⟨v, ⟨v.property, Submodule.mem_top⟩⟩ :
      (A.toLinearPMap - z • 1).domain) = 0 :=
    LinearMap.ker_eq_bot'.mp hker _ (by change A.toLinearMap v - z • (v : H) = 0; rw [hv, sub_self])
  exact hne (congrArg Subtype.val hx)

/-- Physlib's spectral theorem applies to the existing Hamiltonian interface. -/
theorem spectrum_real [CompleteSpace H] (A : DenselyDefinedOperator H)
    (h : A.IsSelfAdjoint) : A.spectrum ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real ((A.isSelfAdjoint_iff).mp h)

end DenselyDefinedOperator
end YangMills
