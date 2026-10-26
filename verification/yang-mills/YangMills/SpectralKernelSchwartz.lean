import YangMills.QFT.Wightman
import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# The actual Wightman spectral kernel is a Schwartz Fourier transform

Mathlib uses exp(-2*pi*i*<p,x>). The specified (+---) kernel therefore
is the same transform at eta*a/(2*pi). The canonical PiLp identification
preserves volume, so this identity has no additional volume prefactor.
Pullback along that invertible linear coordinate map preserves the full
Schwartz class. Rapid decay and integrability follow for the actual kernel.
The vector kernel is integrable from strong continuity and unitarity alone,
without assuming the spectral_integrable field of WightmanAxioms.
-/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace YangMills
abbrev EuclideanSpacetime := EuclideanSpace ℝ (Fin 4)

def euclideanCoordinates : EuclideanSpacetime ≃L[ℝ] Spacetime :=
  PiLp.continuousLinearEquiv 2 ℝ _

def metricReflection : Spacetime ≃L[ℝ] Spacetime where
  toFun a i := if i = 0 then a i else -a i
  invFun a i := if i = 0 then a i else -a i
  left_inv := by intro a; ext i; simp; split_ifs <;> simp
  right_inv := by intro a; ext i; simp; split_ifs <;> simp
  map_add' := by intro a b; ext i; simp; split_ifs <;> ring
  map_smul' := by intro c a; ext i; by_cases hi : i = 0 <;> simp [hi]
  continuous_toFun := by
    apply continuous_pi; intro i
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] <;> fun_prop
  continuous_invFun := by
    apply continuous_pi; intro i
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] <;> fun_prop

def spectralFourierCoordinates : Spacetime ≃L[ℝ] EuclideanSpacetime :=
  (metricReflection.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)))).trans
      euclideanCoordinates.symm

def euclideanMomentumTest (f : TestFunction) : SchwartzMap EuclideanSpacetime ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanCoordinates f

lemma spectralFourierCoordinates_inner (p : EuclideanSpacetime) (a : Spacetime) :
    (2 * Real.pi) * inner ℝ p (spectralFourierCoordinates a) = minkowski (euclideanCoordinates p) a := by
  simp only [spectralFourierCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  simp [euclideanCoordinates, metricReflection, PiLp.inner_apply, Fin.sum_univ_succ, minkowski]
  field_simp
  ring

def spectralKernelTest (f : TestFunction) : TestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ spectralFourierCoordinates
    (SchwartzMap.fourierTransformCLM ℂ (euclideanMomentumTest f))

lemma spectralKernel_eq_fourier (f : TestFunction) (a : Spacetime) :
    WightmanData.spectralKernel f a =
      SchwartzMap.fourierTransformCLM ℂ (euclideanMomentumTest f) (spectralFourierCoordinates a) := by
  change _ = 𝓕 (euclideanMomentumTest f : EuclideanSpacetime → ℂ) (spectralFourierCoordinates a)
  rw [Real.fourierIntegral_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 4)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  unfold WightmanData.spectralKernel
  apply integral_congr_ae
  filter_upwards [] with p
  change Complex.exp (-Complex.I * (minkowski p a : ℂ)) * f p =
    Complex.exp ((↑(-2 * Real.pi * inner ℝ (WithLp.toLp 2 p) (spectralFourierCoordinates a)) * Complex.I)) • f p
  rw [show -2 * Real.pi * inner ℝ (WithLp.toLp 2 p) (spectralFourierCoordinates a) =
    -minkowski p a by
      calc
        -2 * Real.pi * inner ℝ (WithLp.toLp 2 p) (spectralFourierCoordinates a) =
            -((2 * Real.pi) * inner ℝ (WithLp.toLp 2 p) (spectralFourierCoordinates a)) := by ring
        _ = -minkowski p a := by
          rw [spectralFourierCoordinates_inner]
          rfl]
  simp only [Complex.ofReal_neg, smul_eq_mul]
  congr 2
  ring

lemma spectralKernelTest_apply (f : TestFunction) (a : Spacetime) :
    spectralKernelTest f a = WightmanData.spectralKernel f a :=
  (spectralKernel_eq_fourier f a).symm

theorem spectralKernel_integrable (f : TestFunction) :
    Integrable (WightmanData.spectralKernel f) := by
  have h : Integrable (spectralKernelTest f) := (spectralKernelTest f).integrable
  have heq : (spectralKernelTest f : Spacetime → ℂ) = WightmanData.spectralKernel f :=
    funext (spectralKernelTest_apply f)
  rw [← heq]
  exact h

lemma continuous_translate : Continuous PoincareTransform.translate := by
  apply continuous_induced_rng.mpr
  change Continuous (fun a : Spacetime => (a, fun i j : Fin 4 => (Pi.single j 1 : Spacetime) i))
  exact continuous_id.prodMk continuous_const

lemma continuous_spectralOrbit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : WightmanData H) (continuousQ : ∀ v, Continuous (fun g => Q.unitary g v)) (v : H) :
    Continuous (fun a => Q.unitary (PoincareTransform.translate a) v) :=
  (continuousQ v).comp continuous_translate

lemma integrable_spectralVector_of_integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Q : WightmanData H)
    (continuousQ : ∀ v, Continuous (fun g => Q.unitary g v))
    (f : Spacetime → ℂ) (hf : Integrable f) (v : H) :
    Integrable (fun a => f a • Q.unitary (PoincareTransform.translate a) v) := by
  apply (hf.norm.mul_const ‖v‖).mono'
    (hf.aestronglyMeasurable.smul (continuous_spectralOrbit Q continuousQ v).aestronglyMeasurable)
  filter_upwards [] with a
  simp only [norm_smul, LinearIsometryEquiv.norm_map]
  exact le_rfl

/-- Every derivative of the actual spectral kernel has Schwartz decay. -/
theorem spectralKernel_decay (f : TestFunction) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a, ‖a‖ ^ k *
      ‖iteratedFDeriv ℝ n (WightmanData.spectralKernel f) a‖ ≤ C := by
  have heq : (spectralKernelTest f : Spacetime → ℂ) = WightmanData.spectralKernel f :=
    funext (spectralKernelTest_apply f)
  simpa only [heq] using (spectralKernelTest f).decay k n

/-- Thus explicit spectral integrability adds no restriction beyond the
strongly continuous unitary translation action and the fixed Schwartz tests. -/
theorem spectral_integrable_of_strongly_continuous {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Q : WightmanData H)
    (continuousQ : ∀ v, Continuous (fun g => Q.unitary g v)) (f : TestFunction) (v : H) :
    Integrable (fun a => WightmanData.spectralKernel f a •
      Q.unitary (PoincareTransform.translate a) v) :=
  integrable_spectralVector_of_integrable Q continuousQ _ (spectralKernel_integrable f) v

end YangMills
