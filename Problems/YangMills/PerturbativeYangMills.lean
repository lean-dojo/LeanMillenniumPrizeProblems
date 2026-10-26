import Problems.YangMills.Classical
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed pure Yang--Mills interaction vertices

The interaction is expanded from the actual bracket and invariant form of G.
These are bare local vertices, not freely selected perturbative coefficients.
Gauge fixing here is a possible perturbative presentation; no nonperturbative
construction is required to use this gauge. Ghost contraction signs, all-order
renormalization and the quantum BRST identities are not supplied by this file.
-/
noncomputable section
namespace YangMills.Perturbative

variable {G : CompactSimpleGaugeGroup}

/-- Values and first derivatives of a gauge potential at one point. -/
abbrev FieldJet (G : CompactSimpleGaugeGroup) :=
  (Fin 4 → G.Algebra) × (Fin 4 → Fin 4 → G.Algebra)

/-- The derivative index precedes the potential component. -/
def linearCurvature (j : FieldJet G) (μ ν : Fin 4) : G.Algebra :=
  j.2 μ ν - j.2 ν μ

def nonlinearCurvature (j : FieldJet G) (μ ν : Fin 4) : G.Algebra :=
  ⁅j.1 μ, j.1 ν⁆

/-- Canonical perturbative field normalization F=dA+g[A,A]. -/
def curvature (g : ℝ) (j : FieldJet G) (μ ν : Fin 4) : G.Algebra :=
  linearCurvature j μ ν + g • nonlinearCurvature j μ ν

/-- The action density in canonical field normalization, with all ordered
antisymmetric tensor components summed. -/
def yangMillsDensity (B : InvariantForm G) (g : ℝ) (j : FieldJet G) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (curvature g j μ ν) (curvature g j μ ν)

def quadraticDensity (B : InvariantForm G) (j : FieldJet G) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (linearCurvature j μ ν) (linearCurvature j μ ν)

def cubicDensity (B : InvariantForm G) (j : FieldJet G) : ℝ :=
  (1 / 2 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (linearCurvature j μ ν) (nonlinearCurvature j μ ν)

def quarticDensity (B : InvariantForm G) (j : FieldJet G) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (nonlinearCurvature j μ ν) (nonlinearCurvature j μ ν)

theorem invariantForm_quadratic_expansion (B : InvariantForm G)
    (X Y : G.Algebra) (g : ℝ) :
    B.bilinear (X + g • Y) (X + g • Y) =
      B.bilinear X X + 2 * g * B.bilinear X Y + g ^ 2 * B.bilinear Y Y := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [B.symmetric Y X]
  ring

/-- The vertices are coefficients of the fixed YM action, not a second input
which a proof author could choose independently of G and its curvature. -/
theorem density_expansion (B : InvariantForm G) (g : ℝ) (j : FieldJet G) :
    yangMillsDensity B g j = quadraticDensity B j + g * cubicDensity B j +
      g ^ 2 * quarticDensity B j := by
  unfold yangMillsDensity curvature quadraticDensity cubicDensity quarticDensity
  simp_rw [invariantForm_quadratic_expansion]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

def divergence (j : FieldJet G) : G.Algebra := ∑ μ : Fin 4, j.2 μ μ

/-- Feynman gauge is ξ=1 in this local presentation. -/
def gaugeFixingDensity (B : InvariantForm G) (j : FieldJet G) : ℝ :=
  (1 / 2 : ℝ) * B.bilinear (divergence j) (divergence j)

def gaugeFixedDensity (B : InvariantForm G) (g : ℝ) (j : FieldJet G) : ℝ :=
  yangMillsDensity B g j + gaugeFixingDensity B j

/-- This seed is linear in each of its three external jets. Symmetrization
below is the exact coefficient of one distinct parameter on every leg. -/
def cubicSeed (B : InvariantForm G) (j k l : FieldJet G) : ℝ :=
  (1 / 2 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (linearCurvature j μ ν) ⁅k.1 μ, l.1 ν⁆

def quarticSeed (B : InvariantForm G) (j k l m : FieldJet G) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear ⁅j.1 μ, k.1 ν⁆ ⁅l.1 μ, m.1 ν⁆

def cubicVertex (B : InvariantForm G) (v : Fin 3 → FieldJet G) : ℝ :=
  ∑ π : Equiv.Perm (Fin 3), cubicSeed B (v (π 0)) (v (π 1)) (v (π 2))

def quarticVertex (B : InvariantForm G) (v : Fin 4 → FieldJet G) : ℝ :=
  ∑ π : Equiv.Perm (Fin 4),
    quarticSeed B (v (π 0)) (v (π 1)) (v (π 2)) (v (π 3))

theorem cubicVertex_diagonal (B : InvariantForm G) (j : FieldJet G) :
    cubicVertex B (fun _ => j) = 6 * cubicDensity B j := by
  norm_num [cubicVertex, cubicSeed, cubicDensity, nonlinearCurvature, Fintype.card_perm,
    Nat.factorial_succ]

theorem quarticVertex_diagonal (B : InvariantForm G) (j : FieldJet G) :
    quarticVertex B (fun _ => j) = 24 * quarticDensity B j := by
  norm_num [quarticVertex, quarticSeed, quarticDensity, nonlinearCurvature, Fintype.card_perm,
    Nat.factorial_succ]

/-- Faddeev--Popov bilinear insertion after integration by parts:
(∂μ cbar, ∂μ c + g[Aμ,c]). Anticommutation enters Wick contraction,
not this coefficient of the ordered external legs (cbar,A,c). -/
def ghostKinetic (B : InvariantForm G) (dbar dc : Fin 4 → G.Algebra) : ℝ :=
  ∑ μ : Fin 4, B.bilinear (dbar μ) (dc μ)

def ghostVertex (B : InvariantForm G) (dbar A : Fin 4 → G.Algebra)
    (c : G.Algebra) : ℝ :=
  ∑ μ : Fin 4, B.bilinear (dbar μ) ⁅A μ, c⁆

def ghostDensity (B : InvariantForm G) (g : ℝ)
    (dbar dc A : Fin 4 → G.Algebra) (c : G.Algebra) : ℝ :=
  ∑ μ : Fin 4, B.bilinear (dbar μ) (dc μ + g • ⁅A μ, c⁆)

theorem ghostDensity_expansion (B : InvariantForm G) (g : ℝ)
    (dbar dc A : Fin 4 → G.Algebra) (c : G.Algebra) :
    ghostDensity B g dbar dc A c = ghostKinetic B dbar dc + g * ghostVertex B dbar A c := by
  simp [ghostDensity, ghostKinetic, ghostVertex, map_add, map_smul,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- The actual group color tensors, independent of a matrix representation. -/
def threeColor (B : InvariantForm G) (X Y Z : G.Algebra) : ℝ := B.bilinear X ⁅Y, Z⁆
def fourColor (B : InvariantForm G) (X Y Z W : G.Algebra) : ℝ :=
  B.bilinear ⁅X, Y⁆ ⁅Z, W⁆

theorem threeColor_antisymmetric (B : InvariantForm G) (X Y Z : G.Algebra) :
    threeColor B X Y Z = -threeColor B X Z Y := by
  unfold threeColor
  rw [← map_neg]
  exact congrArg (B.bilinear X) (lie_skew Y Z).symm

/-- Simplicity forces a nonzero interaction color tensor. In particular the
actual group cannot silently become an abelian/free color sector. This alone
does not prove that any quantum theory realizes that interaction. -/
theorem threeColor_nonzero (B : InvariantForm G) :
    ∃ X Y Z : G.Algebra, threeColor B X Y Z ≠ 0 := by
  by_contra h
  push Not at h
  apply LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := G.Algebra)
  refine ⟨fun Y Z => ?_⟩
  by_contra hz
  have hp := B.positive ⁅Y, Z⁆ hz
  have he := h ⁅Y, Z⁆ Y Z
  exact (ne_of_gt hp) he

/-- Canonical normalization A_source=g A. The physical source curvature is
g times dA+g[A,A], not just dA+g[A,A]. -/
def rescaleJet (g : ℝ) (j : FieldJet G) : FieldJet G :=
  (fun μ => g • j.1 μ, fun μ ν => g • j.2 μ ν)

theorem rescaled_curvature (g : ℝ) (j : FieldJet G) (μ ν : Fin 4) :
    curvature 1 (rescaleJet g j) μ ν = g • curvature g j μ ν := by
  simp [curvature, linearCurvature, nonlinearCurvature, rescaleJet,
    smul_sub, smul_add, smul_smul, lie_smul, smul_lie]

def sourceDensity (B : InvariantForm G) (g : ℝ) (j : FieldJet G) : ℝ :=
  (1 / (4 * g ^ 2)) * ∑ μ : Fin 4, ∑ ν : Fin 4,
    B.bilinear (curvature 1 (rescaleJet g j) μ ν) (curvature 1 (rescaleJet g j) μ ν)

theorem sourceDensity_eq_canonical (B : InvariantForm G) (g : ℝ) (hg : g ≠ 0)
    (j : FieldJet G) : sourceDensity B g j = yangMillsDensity B g j := by
  unfold sourceDensity yangMillsDensity
  simp_rw [rescaled_curvature, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [← Finset.mul_sum]
  field_simp

def connectionJet (A : Connection G) (x : Spacetime) : FieldJet G :=
  (A.potential x, fun μ ν => Connection.partialDerivative (fun y => A.potential y ν) μ x)

@[simp] theorem curvature_connectionJet (A : Connection G) (x : Spacetime) (μ ν : Fin 4) :
    curvature 1 (connectionJet A x) μ ν = A.curvature x μ ν := by
  simp [curvature, linearCurvature, nonlinearCurvature, connectionJet, Connection.curvature]

theorem connectionCurvature_skew (A : Connection G) (x : Spacetime) (μ ν : Fin 4) :
    A.curvature x ν μ = -A.curvature x μ ν := by
  unfold Connection.curvature
  rw [← lie_skew (A.potential x ν) (A.potential x μ)]
  abel

theorem symmetric_double_sum (f : Fin 4 → Fin 4 → ℝ)
    (hs : ∀ μ ν, f μ ν = f ν μ) (hd : ∀ μ, f μ μ = 0) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, f μ ν) =
      2 * ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then f μ ν else 0 := by
  have hsplit (μ ν : Fin 4) : f μ ν =
      (if μ < ν then f μ ν else 0) + (if ν < μ then f μ ν else 0) := by
    rcases lt_trichotomy μ ν with h | h | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · subst ν
      simp [hd]
    · simp [h, not_lt_of_ge (le_of_lt h)]
  have hswap : (∑ μ : Fin 4, ∑ ν : Fin 4, if ν < μ then f μ ν else 0) =
      ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then f μ ν else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    rw [hs ν μ]
  calc
    (∑ μ : Fin 4, ∑ ν : Fin 4, f μ ν) =
        ∑ μ : Fin 4, ∑ ν : Fin 4,
          ((if μ < ν then f μ ν else 0) + (if ν < μ then f μ ν else 0)) := by
      simp_rw [← hsplit]
    _ = _ := by simp only [Finset.sum_add_distrib, hswap]; ring

/-- Explicitly exposes the pre-existing half-normalization in Classical:
it sums μ<ν only, whereas the standard component density sums ordered μν.
To match the same coupling g, its invariant form must be doubled; alternatively
its coupling is g/sqrt(2). No equivalence is silently asserted. -/
theorem canonicalDensity_eq_half_oldDensity (B : InvariantForm G)
    (A : Connection G) (x : Spacetime) :
    yangMillsDensity B 1 (connectionJet A x) = (1 / 2 : ℝ) * A.actionDensity B x := by
  unfold yangMillsDensity Connection.actionDensity
  simp only [curvature_connectionJet]
  rw [symmetric_double_sum]
  · ring
  · intro μ ν
    rw [connectionCurvature_skew A x μ ν]
    simp
  · intro μ
    simp [Connection.curvature]

end YangMills.Perturbative
