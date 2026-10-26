import Problems.YangMills.WardActionCoordinates
import Mathlib.Data.List.Perm.Basic

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace YangMills.WardAction
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- A nonzero ordered derivative must consume precisely the source fields,
including their Grassmann species. No evaluation in commuting ghosts occurs. -/
theorem localDerivative_support (source : List (LocalVertexLeg G))
    (external : List (ExternalLeg G × Spacetime))
    (h : localMonomialDerivative source external ≠ 0) :
    (source.map LocalVertexLeg.field).Perm (external.map Prod.fst) := by
  induction external generalizing source with
  | nil =>
    cases source with
    | nil => exact .nil
    | cons a rest => exact False.elim (h (by simp [localMonomialDerivative]))
  | cons ep rest ih =>
    rcases ep with ⟨K, p⟩
    simp only [localMonomialDerivative] at h
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases hk : (source.get j).field = K
    · simp only [if_pos hk] at hj
      have hd := (mul_ne_zero_iff.mp hj).2
      have hp := ih _ hd
      have he : source.take j.val ++ source.drop (j.val + 1) = source.eraseIdx j.val :=
        (List.eraseIdx_eq_take_drop_succ source j.val).symm
      rw [he] at hp
      have hh := (List.getElem_cons_eraseIdx_perm (l := source) j.isLt).map
        LocalVertexLeg.field
      simp only [List.map_cons] at hh
      change source[j.val].field = K at hk
      rw [hk] at hh
      exact hh.symm.trans (.cons K hp)
    · exact False.elim (hj (by simp only [if_neg hk]))


def isGhostLeg : ExternalLeg G → Bool
  | .inl (.ghost _) | .inl (.antighost _) => true
  | _ => false

def speciesSignature (fields : List (ExternalLeg G)) : ℕ × ℕ :=
  (fields.length, (fields.filter isGhostLeg).length)

def sectorSignature : Sector → ℕ × ℕ
  | .gluonKinetic => (2, 0)
  | .ghostKinetic => (2, 2)
  | .cubic => (3, 0)
  | .ghostVertex => (3, 2)
  | .quartic => (4, 0)

theorem sectorSignature_injective : Function.Injective sectorSignature := by
  intro s t h
  cases s <;> cases t <;> simp_all [sectorSignature]

theorem probe_signature (s : Sector) (i : ProbeIndex G s) :
    speciesSignature (probeLegs s i) = sectorSignature s := by
  cases s with
  | gluonKinetic => simp [probeLegs, speciesSignature, sectorSignature, isGhostLeg]
  | ghostKinetic => simp [probeLegs, speciesSignature, sectorSignature, isGhostLeg]
  | cubic => rcases i with ⟨a,b,c⟩; simp [probeLegs, speciesSignature, sectorSignature, isGhostLeg]
  | ghostVertex => rcases i with ⟨a,b,c⟩; simp [probeLegs, speciesSignature, sectorSignature, isGhostLeg]
  | quartic => rcases i with ⟨a,b⟩; simp [probeLegs, speciesSignature, sectorSignature, isGhostLeg]

theorem vertex_signature {B : InvariantForm G} (e : ColorFrame B) (s : Sector)
    (v : LocalVertex G) (hv : v ∈ basisVertices e s) :
    speciesSignature (v.legs.map LocalVertexLeg.field) = sectorSignature s := by
  cases s <;>
    simp [basisVertices, gluonKineticVertices, ghostKineticVertices, liftPhysical,
      cubicMonomials, quarticMonomials, ghostMonomials] at hv
  all_goals aesop (add simp [speciesSignature, sectorSignature, isGhostLeg])


theorem speciesSignature_perm {a b : List (ExternalLeg G)} (h : a.Perm b) :
    speciesSignature a = speciesSignature b := by
  exact Prod.ext h.length_eq (h.filter isGhostLeg).length_eq

/-- Every cross-sector amplitude vanishes identically, before taking a
momentum derivative: the actual action monomials have different ordered
field support. This includes gauge/ghost separation at equal arity. -/
theorem basisAmplitude_cross {B : InvariantForm G} (e : ColorFrame B)
    (s t : Sector) (hst : s ≠ t) (i : ProbeIndex G s)
    (q : Fin (probeLegs s i).length → Spacetime) :
    basisAmplitude e t (probeLegs s i) q = 0 := by
  unfold basisAmplitude localPolynomialAmplitude
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  unfold localVertexAmplitude
  suffices localMonomialDerivative v.legs
      (List.ofFn (fun j => ((probeLegs s i).get j, q j))) = 0 by rw [this, mul_zero]
  by_contra h
  have hp := speciesSignature_perm (localDerivative_support _ _ h)
  have he : (List.ofFn (fun j => ((probeLegs s i).get j, q j))).map Prod.fst =
      probeLegs s i := by simp only [List.map_ofFn, Function.comp_def, List.ofFn_get]
  rw [he, vertex_signature e t v hv, probe_signature] at hp
  exact hst (sectorSignature_injective hp.symm)

theorem fixed_crossSectorSupport {B : InvariantForm G} (e : ColorFrame B) :
    CrossSectorSupport e := by
  intro s t hst i
  unfold probeTensor
  have he : (fun q => basisAmplitude e t (probeLegs s i)
      (conservingMomenta (probeLegs s i) q)) = fun _ => 0 := by
    funext q
    exact basisAmplitude_cross e s t hst i _
  rw [he]
  simp [momentumJet]


/-- Nonabelian simplicity makes the actual orthonormal-frame interaction
color tensor nonzero; this excludes a free-color projector. -/
theorem structureConstant_exists_ne_zero {B : InvariantForm G} (e : ColorFrame B) :
    ∃ a b c, structureConstant e a b c ≠ 0 := by
  by_contra h
  push Not at h
  apply LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := G.Algebra)
  refine ⟨fun X Y => ?_⟩
  apply e.basis.repr.injective
  ext c
  simp [bracket_coordinates, h]

theorem bracket_basis_exists_ne_zero {B : InvariantForm G} (e : ColorFrame B) :
    ∃ a b, ⁅e.basis a, e.basis b⁆ ≠ 0 := by
  obtain ⟨a,b,c,h⟩ := structureConstant_exists_ne_zero e
  refine ⟨b,c,fun hc => h ?_⟩
  simp [structureConstant, threeColor, hc]

theorem fourColor_basis_positive {B : InvariantForm G} (e : ColorFrame B) :
    ∃ a b, 0 < fourColor B (e.basis a) (e.basis b) (e.basis a) (e.basis b) := by
  obtain ⟨a,b,h⟩ := bracket_basis_exists_ne_zero e
  exact ⟨a,b,B.positive _ h⟩

end YangMills.WardAction
