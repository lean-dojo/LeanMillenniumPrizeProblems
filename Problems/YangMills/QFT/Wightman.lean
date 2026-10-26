import Problems.YangMills.QFT.Spacetime
import Problems.YangMills.QFT.Operator
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Concrete bosonic Wightman proof obligations

This file implements the operator formulation of §3 for countably many
finite-component bosonic field multiplets. Gauge-invariant pure Yang–Mills
observables are bosonic. No field is required to be a bounded operator.

`WightmanData` supplies mathematical objects. `WightmanAxioms` supplies proofs
of fixed statements about those objects: there are no `... : Prop` inputs.
The spectral condition is expressed distributionally for translations, with
Fourier kernel exp(-i p·a) and convention U(a) = exp(i P·a).

This is a QFT specification, not yet the Yang–Mills identification of §4.

These local QFT obligations may be replaced by official Physlib APIs if its
development supplies equivalent Wightman and spectral conditions. Completion
of related roadmap items alone is not a proof of equivalence.
-/

noncomputable section
open MeasureTheory
namespace YangMills

universe u
variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- All operator-valued distributions act on the same invariant domain. -/
structure WightmanData where
  domain : Submodule ℂ H
  vacuum : domain
  componentCount : ℕ → ℕ
  field : (Σ n, Fin (componentCount n)) → TestFunction →ₗ[ℂ] domain →ₗ[ℂ] domain
  adjointIndex : (Σ n, Fin (componentCount n)) → (Σ n, Fin (componentCount n))
  unitary : PoincareTransform → H ≃ₗᵢ[ℂ] H
  domainAction : PoincareTransform → domain ≃ₗ[ℂ] domain
  componentAction : (n : ℕ) → PoincareTransform →
    (Fin (componentCount n) → ℂ) ≃ₗ[ℂ] (Fin (componentCount n) → ℂ)
  pullback : PoincareTransform → TestFunction → TestFunction
  conjugateTest : TestFunction → TestFunction
  hamiltonian : DenselyDefinedOperator H

namespace WightmanData
variable {H}

abbrev FieldIndex (Q : WightmanData H) := Σ n, Fin (Q.componentCount n)

/-- All finite products of smeared fields applied to the vacuum, including
 the empty product (the vacuum itself). -/
def word (Q : WightmanData H) : List (Q.FieldIndex × TestFunction) → Q.domain
  | [] => Q.vacuum
  | (i, f) :: rest => Q.field i f (Q.word rest)

def timeTranslation (Q : WightmanData H) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  Q.unitary (PoincareTransform.translate (Pi.single 0 t))

/-- The spectral test kernel, with Minkowski pairing. No unspecified
Fourier-transform or spectral-support predicate is passed to the theory. -/
def spectralKernel (f : TestFunction) (a : Spacetime) : ℂ :=
  ∫ p : Spacetime, Complex.exp (-Complex.I * (minkowski p a : ℂ)) * f p

end WightmanData

/-- Each field is a concrete proposition to prove, not a proposition to choose.
The numbering follows the familiar Wightman organization, with Hamiltonian
clauses separated so the mass gap refers to the same translation dynamics. -/
structure WightmanAxioms (Q : WightmanData H) : Prop where
  /-- Completeness is a required proof, not an unused ambient assumption. -/
  complete : CompleteSpace H
  /-- W0: the physical Hilbert space is separable. -/
  separable : TopologicalSpace.SeparableSpace H
  /-- W0: one common dense invariant domain. Invariance under fields is
  already enforced by the codomain of `field`. -/
  dense_domain : Dense (Q.domain : Set H)
  /-- W0: normalized vacuum. -/
  vacuum_norm : ‖(Q.vacuum : H)‖ = 1
  /-- W1: a genuine, strongly continuous unitary representation. -/
  unitary_identity : ∀ v, Q.unitary PoincareTransform.identity v = v
  unitary_comp : ∀ g h v,
    Q.unitary (g.compose h) v = Q.unitary g (Q.unitary h v)
  strongly_continuous : ∀ v, Continuous (fun g => Q.unitary g v)
  domain_action : ∀ g v, (Q.domainAction g v : H) = Q.unitary g (v : H)
  /-- W1: Poincaré-invariant vacuum and uniqueness of the translation-invariant ray. -/
  vacuum_invariant : ∀ g, Q.unitary g (Q.vacuum : H) = (Q.vacuum : H)
  vacuum_unique : ∀ v : H,
    (∀ a, Q.unitary (PoincareTransform.translate a) v = v) →
      ∃ c : ℂ, v = c • (Q.vacuum : H)
  /-- W2: joint energy-momentum spectrum in the closed forward cone.
  Integrability is explicit because Lean's Bochner integral is totalized.
  A nonintegrable integrand must not make this axiom vacuous. -/
  spectral_integrable : ∀ (f : TestFunction) (v : H),
    Integrable (fun a => WightmanData.spectralKernel f a •
      Q.unitary (PoincareTransform.translate a) v)
  spectral_support : ∀ (f : TestFunction), (∀ p ∈ FutureCone, f p = 0) →
    ∀ v : H, (∫ a : Spacetime, WightmanData.spectralKernel f a •
      Q.unitary (PoincareTransform.translate a) v) = 0
  /-- W3: tempered operator-valued distributions; linearity in the test
  function and vector is enforced by the two linear-map types of `field`. -/
  field_continuous : ∀ i (v : Q.domain),
    Continuous (fun f : TestFunction => (Q.field i f v : H))
  conjugateTest_eq : ∀ f x, Q.conjugateTest f x = star (f x)
  adjoint_involution : ∀ i, Q.adjointIndex (Q.adjointIndex i) = i
  adjoint_relation : ∀ i f (v w : Q.domain),
    inner ℂ (Q.field i f v : H) (w : H) =
      inner ℂ (v : H) (Q.field (Q.adjointIndex i) (Q.conjugateTest f) w : H)
  /-- W4: finite-dimensional component representations and covariance.
  Coefficients are matrix columns: the image of the i-th basis vector. -/
  component_identity : ∀ n v, Q.componentAction n PoincareTransform.identity v = v
  component_comp : ∀ n g h v,
    Q.componentAction n (g.compose h) v =
      Q.componentAction n g (Q.componentAction n h v)
  component_continuous : ∀ n v, Continuous (fun g => Q.componentAction n g v)
  component_translation : ∀ n a v,
    Q.componentAction n (PoincareTransform.translate a) v = v
  pullback_eq : ∀ g f, IsPullback g f (Q.pullback g f)
  covariance : ∀ g n (i : Fin (Q.componentCount n)) f v,
    Q.domainAction g (Q.field ⟨n, i⟩ f v) =
      ∑ j : Fin (Q.componentCount n),
        (Q.componentAction n g (Pi.single i 1) j) •
          Q.field ⟨n, j⟩ (Q.pullback g f) (Q.domainAction g v)
  /-- W5: bosonic local commutativity, on the invariant domain, for
  spacelike-separated closed supports. -/
  locality : ∀ i j f g, TestFunctionsSpacelike f g → ∀ v,
    Q.field i f (Q.field j g v) = Q.field j g (Q.field i f v)
  /-- W6: the vacuum is cyclic for the entire field algebra. -/
  cyclic : Dense
    ((Submodule.span ℂ (Set.range (fun w => (Q.word w : H)))) : Set H)
  /-- H is self-adjoint, including the full adjoint-domain condition. -/
  selfAdjoint : Q.hamiltonian.IsSelfAdjoint
  /-- Exactly the domain of the time-translation generator, not an arbitrary
  restriction or an unrelated positive operator. -/
  generator_domain : ∀ v : H,
    (∃ w : H, HasDerivAt (fun t => Q.timeTranslation t v) w 0) ↔
      v ∈ Q.hamiltonian.domain
  generator_action : ∀ v : Q.hamiltonian.domain,
    HasDerivAt (fun t => Q.timeTranslation t (v : H))
      (Complex.I • Q.hamiltonian.toLinearMap v) 0
  /-- Explicit spectral consequences, kept as checked obligations until
  the relevant unbounded-operator spectral theorems are developed here. -/
  spectrum_real : ∀ z ∈ Q.hamiltonian.spectrum, z.im = 0
  positive_energy : PositiveEnergy Q.hamiltonian.realSpectrum
  vacuum_mem : (Q.vacuum : H) ∈ Q.hamiltonian.domain
  vacuum_zero : Q.hamiltonian.toLinearMap ⟨(Q.vacuum : H), vacuum_mem⟩ = 0

namespace WightmanAxioms
variable {H} {Q : WightmanData H}

/-- The vacuum's spectral energy is derived from the actual Hamiltonian. -/
theorem vacuum_mem_spectrum (h : WightmanAxioms H Q) :
    0 ∈ Q.hamiltonian.realSpectrum := by
  have hne : (Q.vacuum : H) ≠ 0 := by
    intro hz
    have hn := h.vacuum_norm
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  exact Q.hamiltonian.eigenvalue_mem_spectrum 0
    ⟨(Q.vacuum : H), h.vacuum_mem⟩ hne (by simpa using h.vacuum_zero)

/-- The adjoint relation on the common dense domain guarantees
closability of each smeared field: a graph limit above zero is zero.
This is the sequential graph criterion in the ambient Hilbert norm. -/
theorem field_graph_limit_zero (h : WightmanAxioms H Q)
    (i : Q.FieldIndex) (f : TestFunction) (v : ℕ → Q.domain) (w : H)
    (hv : Filter.Tendsto (fun n => (v n : H)) Filter.atTop (nhds 0))
    (hfield : Filter.Tendsto (fun n => (Q.field i f (v n) : H))
      Filter.atTop (nhds w)) : w = 0 := by
  have hclosed : IsClosed {x : H | inner ℂ w x = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (Q.domain : Set H) ⊆ {x : H | inner ℂ w x = 0} := by
    intro x hx
    have hleft := hfield.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    have hright := hv.inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := (Q.field (Q.adjointIndex i) (Q.conjugateTest f) ⟨x, hx⟩ : H)))
    have heq : (fun n => inner ℂ (Q.field i f (v n) : H) x) =
        (fun n => inner ℂ (v n : H)
          (Q.field (Q.adjointIndex i) (Q.conjugateTest f) ⟨x, hx⟩ : H)) :=
      funext (fun n => h.adjoint_relation i f (v n) ⟨x, hx⟩)
    rw [heq] at hleft
    simpa using tendsto_nhds_unique hleft hright
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact hclosed.closure_subset_iff.mpr hsub (h.dense_domain w)

/-- Two admissible Hamiltonians generating the same actual time evolution
have exactly the same domains. This rules out replacing the physical
Hamiltonian by a restriction with a more convenient spectrum. -/
theorem hamiltonian_domain_unique {R : WightmanData H}
    (hQ : WightmanAxioms H Q) (hR : WightmanAxioms H R)
    (hsame : ∀ t v, Q.timeTranslation t v = R.timeTranslation t v) :
    Q.hamiltonian.domain = R.hamiltonian.domain := by
  ext v
  rw [← hQ.generator_domain v, ← hR.generator_domain v]
  simp_rw [hsame]

/-- The action, as well as the full domain, is fixed by time translations.
This is derivative uniqueness, without invoking Stone's existence theorem. -/
theorem hamiltonian_action_unique {R : WightmanData H}
    (hQ : WightmanAxioms H Q) (hR : WightmanAxioms H R)
    (hsame : ∀ t v, Q.timeTranslation t v = R.timeTranslation t v)
    (v : H) (hvQ : v ∈ Q.hamiltonian.domain) (hvR : v ∈ R.hamiltonian.domain) :
    Q.hamiltonian.toLinearMap ⟨v, hvQ⟩ = R.hamiltonian.toLinearMap ⟨v, hvR⟩ := by
  have hderivQ := hQ.generator_action ⟨v, hvQ⟩
  have hderivR := hR.generator_action ⟨v, hvR⟩
  have heq : (fun t => Q.timeTranslation t v) = (fun t => R.timeTranslation t v) :=
    funext (fun t => hsame t v)
  rw [heq] at hderivQ
  have hI := hderivQ.unique hderivR
  have hc := congrArg (fun x : H => (-Complex.I) • x) hI
  simpa [smul_smul] using hc

end WightmanAxioms

/-- A precise necessary QFT-and-gap condition. This deliberately does not
claim to identify the theory as Yang–Mills. The mass uses the actual operator
resolvent; a candidate cannot supply a convenient spectrum by hand. -/
structure GappedWightmanTheory (Q : WightmanData H) : Prop where
  axioms : WightmanAxioms H Q
  massGap : HasPositiveFiniteMass Q.hamiltonian.realSpectrum

end YangMills
