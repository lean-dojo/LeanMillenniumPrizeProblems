import Problems.YangMills.GeneratedStressNormalization
import Problems.YangMills.RenormalizationGroup

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Zero anomalous dimension of the same physical stress tensor

The regular source-label numerator a has physical label coefficients a/g^2.
With the library's column-label convention Q_mu(v)=Q_muExp(R v), R'=gamma R,
scale independence reads beta d(a/g^2)/dg=gamma(a/g^2). Clearing the pole gives
  g beta a' - 2 beta a = g gamma a.
The exact finite RG transport below uses that SAME common frame, dictionary
and physical stress. It allows quantum scalar mixing and a trace anomaly.
This relation does not authorize freely selected beta/gamma series.
-/
noncomputable section
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The regular numerator as a column in the actual finite label frame. -/
def StressSourceDictionary.regularColumn (dict : StressSourceDictionary G)
    (g : ℝ) (mu nu : Fin 4) : Fin dict.count → ℂ :=
  fun i => (dict.exactRegular g mu nu i : ℂ)

/-- Exact transport, with both powers of g explicit and positive along the
common running trajectory. This is zero anomalous dimension of T, not of
each component of its scale-dependent source-label numerator. -/
structure StressSourceDictionary.RGCovariant (dict : StressSourceDictionary G)
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin dict.count → Fin dict.count → ℂ}
    (F : RG.Frame dict.label betaSeries gammaSeries) : Prop where
  regular_smooth : ∀ mu nu i,
    ContDiff ℝ ∞ (fun g : ℝ => dict.exactRegular g mu nu i)
  transport : ∀ mu nu t, 0 ≤ t →
    ((F.running.coupling 0 ^ 2 : ℝ) : ℂ) •
      dict.regularColumn (F.running.coupling t) mu nu =
    ((F.running.coupling t ^ 2 : ℝ) : ℂ) •
      F.transport t (dict.regularColumn (F.running.coupling 0) mu nu)
  differential : ∀ mu nu t, 0 ≤ t → ∀ i,
    let g := F.running.coupling t
    ((g * F.running.beta g * deriv (fun s : ℝ => dict.exactRegular s mu nu i) g -
      2 * F.running.beta g * dict.exactRegular g mu nu i : ℝ) : ℂ) =
      (g : ℂ) * ∑ j : Fin dict.count,
        F.gamma g i j * (dict.exactRegular g mu nu j : ℂ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {QFT : WightmanData H} {C : RenormalizedCompositeMap QFT G}

/-- The same actual stress operator at any scale of the common RG frame.
Both the running coupling and the correspondence's scale are the ones used
by the physical OPE/stress matching; no second stress tensor is introduced. -/
def StressSourceDictionary.SameStressRG (dict : StressSourceDictionary G)
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin dict.count → Fin dict.count → ℂ}
    (F : RG.Frame dict.label betaSeries gammaSeries) (T : StressTensorData QFT G C) : Prop :=
  dict.PhysicalBinding T ∧ dict.RGCovariant F ∧
  T.coupling.val = F.running.coupling 0 ∧ RG.Realizes F C T.scale ∧
  ∀ t : ℝ, 0 ≤ t → ∀ mu nu f v,
    T.field mu nu f v =
      (((F.running.coupling t)⁻¹ ^ 2 : ℝ) : ℂ) •
        ∑ i : Fin dict.count, (dict.exactRegular (F.running.coupling t) mu nu i : ℂ) •
          C.field ⟨T.scale.val * Real.exp t,
            mul_pos T.scale.property (Real.exp_pos t)⟩ (dict.label i) f v

end YangMills.PerturbativeFlow
