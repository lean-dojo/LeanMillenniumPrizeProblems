import Problems.NavierStokes.Millennium

/-!
# Why the Navier–Stokes cases are exposed separately

This file is a compiled witness of the reason `Problems/NavierStokes/Millennium.lean` exposes
Fefferman's four cases (A)–(D) as separate propositions and defines no aggregate target: the
disjunction `(A) ∨ (B) ∨ (C) ∨ (D)` is a theorem of classical logic with no fluid dynamics in it.

* If (A) fails, it fails for some viscosity `ν₀` and some admissible initial datum `u₀`.  The zero
  force satisfies Fefferman's force hypotheses (`zero_force_smooth_rapid_decay`), so `u₀` together
  with the zero force witnesses (C) at the viscosity `ν₀`.
* (C) quantifies over every viscosity.  The Navier–Stokes scaling symmetry
  `u(x,t) ↦ b·u(x, b t)`, `p(x,t) ↦ b²·p(x, b t)` transports a global smooth finite-energy solution
  at viscosity `μ` with data `w₀` to one at viscosity `b·μ` with data `b·w₀`, for any `b > 0`.  So a
  breakdown witness at `ν₀` yields one at every `ν > 0`.

Hence `(A) ∨ (C)`, and a fortiori the four-way disjunction, holds by excluded middle.  Everything
below is elementary calculus: the chain rule for a linear change of the time coordinate,
homogeneity of `fderiv` under multiplication by an invertible scalar, `ContDiffOn.comp`, and pulling
a constant out of an integral.

This file is a regression test.  It is expected to keep compiling as long as
`NavierStokesOnR3.SmoothExistence`, `NavierStokesOnR3.Breakdown`,
`NavierStokesPeriodic.SmoothExistence` and `NavierStokesPeriodic.Breakdown` keep their current
shape; if it stops compiling, the shape of the four cases has changed and this argument should be
re-examined.
-/

-- `open` must happen before entering the `Tests.NavierStokes` namespace: inside it, the identifier
-- `NavierStokes` would resolve to `Tests.NavierStokes` rather than to the root namespace.
open NavierStokes NavierStokesOnR3

namespace Tests.NavierStokes.AggregateIsTrivial

/-! ## Time scaling on `ℝ³ × ℝ` and the induced `partial_deriv` rules

Nothing in this section uses a differentiability hypothesis, so the rules also hold where Mathlib's
ambient `fderiv` takes the junk value `0`. -/

/-- Scale the time coordinate by `b`, keeping the three space coordinates. -/
noncomputable def scaleMap (b : ℝ) : Spacetime3 →ₗ[ℝ] Spacetime3 where
  toFun x := EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := 4)
    (fun i => if i = 0 then b * x i else x i)
  map_add' x y := by
    ext i; by_cases h : i = 0 <;> simp [h, mul_add]
  map_smul' c x := by
    ext i
    by_cases h : i = 0
    · simp [h]; ring
    · simp [h]

@[simp] theorem scaleMap_apply (b : ℝ) (x : Spacetime3) (i : Fin 4) :
    scaleMap b x i = if i = 0 then b * x i else x i := by
  simp [scaleMap]

/-- The time scaling as a linear equivalence, for `b ≠ 0`. -/
noncomputable def scaleEquiv (b : ℝ) (hb : b ≠ 0) : Spacetime3 ≃ₗ[ℝ] Spacetime3 where
  toLinearMap := scaleMap b
  invFun := scaleMap b⁻¹
  left_inv x := by
    ext i; by_cases h : i = 0 <;> simp [h, inv_mul_cancel_left₀ hb]
  right_inv x := by
    ext i; by_cases h : i = 0 <;> simp [h, mul_inv_cancel_left₀ hb]

/-- The time scaling as a continuous linear equivalence. -/
noncomputable def scaleCLE (b : ℝ) (hb : b ≠ 0) : Spacetime3 ≃L[ℝ] Spacetime3 :=
  (scaleEquiv b hb).toContinuousLinearEquiv

@[simp] theorem scaleCLE_apply (b : ℝ) (hb : b ≠ 0) (x : Spacetime3) :
    scaleCLE b hb x = scaleMap b x := rfl

/-- The scaling sends the standard time direction to `b` times itself. -/
theorem scaleMap_standard_basis_zero (b : ℝ) :
    scaleMap b (standard_basis (n := 4) 0) = b • standard_basis (n := 4) 0 := by
  ext i; by_cases h : i = 0 <;> simp [h]

/-- The scaling fixes the standard space directions. -/
theorem scaleMap_standard_basis_succ (b : ℝ) (j : Fin 3) :
    scaleMap b (standard_basis (n := 4) j.succ) = standard_basis (n := 4) j.succ := by
  ext i
  by_cases h : i = 0
  · subst h; simp [(Fin.succ_ne_zero j).symm]
  · simp [h]

/-- Time partial derivative under time scaling: no differentiability hypothesis. -/
theorem partial_deriv_comp_scale_time (b : ℝ) (hb : b ≠ 0) (f : Spacetime3 → ℝ)
    (x : Spacetime3) :
    partial_deriv (n := 4) 0 (fun y => f (scaleMap b y)) x
      = b * partial_deriv (n := 4) 0 f (scaleMap b x) := by
  have hcomp : (fun y => f (scaleMap b y)) = f ∘ (scaleCLE b hb) := rfl
  rw [partial_deriv, hcomp, (scaleCLE b hb).comp_right_fderiv]
  simp [partial_deriv, scaleMap_standard_basis_zero b, ← smul_eq_mul]

/-- Space partial derivatives are unchanged by time scaling. -/
theorem partial_deriv_comp_scale_space (b : ℝ) (hb : b ≠ 0) (j : Fin 3) (f : Spacetime3 → ℝ)
    (x : Spacetime3) :
    partial_deriv (n := 4) j.succ (fun y => f (scaleMap b y)) x
      = partial_deriv (n := 4) j.succ f (scaleMap b x) := by
  have hcomp : (fun y => f (scaleMap b y)) = f ∘ (scaleCLE b hb) := rfl
  rw [partial_deriv, hcomp, (scaleCLE b hb).comp_right_fderiv]
  simp [partial_deriv, scaleMap_standard_basis_succ b j]

/-- Constant multiples pass through `partial_deriv`, again with no differentiability hypothesis
(the constant is invertible, so both sides degenerate to the same junk value). -/
theorem partial_deriv_const_mul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (i : Fin n)
    (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) :
    partial_deriv (n := n) i (fun y => c * f y) x = c * partial_deriv (n := n) i f x := by
  letI : Invertible c := invertibleOfNonzero hc
  have h : (fun y => c * f y) = c • f := by funext y; simp [Pi.smul_apply, smul_eq_mul]
  rw [partial_deriv, h, fderiv_const_smul_of_invertible (f := f) (c := c)]
  simp [partial_deriv, smul_eq_mul]

/-- Iterated partial derivatives are homogeneous in the same junk-safe way. -/
theorem iterated_partial_deriv_const_mul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (α : List (Fin n))
    (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) :
    iterated_partial_deriv (n := n) α (fun y => c * f y) x
      = c * iterated_partial_deriv (n := n) α f x := by
  induction α generalizing x with
  | nil => rfl
  | cons i rest ih =>
      show partial_deriv i (fun y => iterated_partial_deriv rest (fun z => c * f z) y) x = _
      have hfun : (fun y => iterated_partial_deriv (n := n) rest (fun z => c * f z) y)
          = fun y => c * iterated_partial_deriv (n := n) rest f y := by
        funext y; exact ih y
      rw [hfun, partial_deriv_const_mul c hc]
      rfl

/-! ## Transport of data -/

/-- Rescaled initial data. -/
noncomputable def scaledInitial (c : ℝ) (u₀ : InitialVelocity) : InitialVelocity :=
  fun x => c • u₀ x

theorem scaledInitial_divergence_free (c : ℝ) (hc : c ≠ 0) {u₀ : InitialVelocity}
    (h : DivergenceFreeInitial u₀) : DivergenceFreeInitial (scaledInitial c u₀) := by
  intro x
  have : ∀ i : Fin 3, partial_deriv (n := 3) i (fun y => scaledInitial c u₀ y i) x
      = c * partial_deriv (n := 3) i (fun y => u₀ y i) x := by
    intro i
    have hfun : (fun y => scaledInitial c u₀ y i) = fun y => c * u₀ y i := by
      funext y; simp [scaledInitial]
    rw [hfun, partial_deriv_const_mul c hc]
  simp only [this, ← Finset.mul_sum, h x, mul_zero]

theorem scaledInitial_smooth_rapid_decay (c : ℝ) (hc : 0 < c) {u₀ : InitialVelocity}
    (h : SmoothRapidDecayInitial u₀) : SmoothRapidDecayInitial (scaledInitial c u₀) := by
  obtain ⟨hsmooth, hdecay⟩ := h
  refine ⟨hsmooth.const_smul c, ?_⟩
  intro α K
  obtain ⟨C, hC, hbound⟩ := hdecay α K
  refine ⟨c * C, by positivity, ?_⟩
  intro x
  have hvec : spatial_derivative_vector (scaledInitial c u₀) α x
      = c • spatial_derivative_vector u₀ α x := by
    ext i
    have hfun : (fun y => scaledInitial c u₀ y i) = fun y => c * u₀ y i := by
      funext y; simp [scaledInitial]
    simp only [spatial_derivative_vector, EuclideanCoordinateSpace.of_fun_apply, hfun,
      iterated_partial_deriv_const_mul c hc.ne', PiLp.smul_apply, smul_eq_mul]
  rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hbound x) hc.le

/-! ## Transport of solutions -/

/-- The rescaled velocity field `b · v(x, b t)`. -/
noncomputable def scaledVelocity (b : ℝ) (v : VelocityField 3) : VelocityField 3 :=
  fun x => b • v (scaleMap b x)

/-- The rescaled pressure field `b² · q(x, b t)`. -/
noncomputable def scaledPressure (b : ℝ) (q : PressureField 3) : PressureField 3 :=
  fun x => b ^ 2 * q (scaleMap b x)

theorem scaleMap_spacetime_point (b t : ℝ) (x : Space3) :
    scaleMap b (spacetime_point t x) = spacetime_point (b * t) x := by
  ext i
  by_cases h : i = 0 <;> simp [h, spacetime_point]

/-- Scaling by `b > 0` preserves the closed half-space `t ≥ 0`. -/
theorem scaleMap_mem_global {b : ℝ} (hb : 0 < b) {x : Spacetime3}
    (hx : x ∈ global_spacetime_domain 3) : scaleMap b x ∈ global_spacetime_domain 3 := by
  simpa [global_spacetime_domain] using mul_nonneg hb.le hx

/-- Scaling by `b > 0` preserves the open half-space `t > 0` on which the equations are imposed. -/
theorem scaleMap_mem_interior {b : ℝ} (hb : 0 < b) {x : Spacetime3}
    (hx : x ∈ interior_spacetime_domain 3) : scaleMap b x ∈ interior_spacetime_domain 3 := by
  simpa [interior_spacetime_domain] using mul_pos hb hx

theorem scaledVelocity_smooth {b : ℝ} (hb : 0 < b) {v : VelocityField 3}
    (h : velocity_smooth_on_global_spacetime_domain v) :
    velocity_smooth_on_global_spacetime_domain (scaledVelocity b v) := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v (scaleMap b x)) (global_spacetime_domain 3) :=
    h.comp ((scaleCLE b hb.ne').contDiff.contDiffOn) fun x hx => scaleMap_mem_global hb hx
  exact hcomp.const_smul b

theorem scaledPressure_smooth {b : ℝ} (hb : 0 < b) {q : PressureField 3}
    (h : pressure_smooth_on_global_spacetime_domain q) :
    pressure_smooth_on_global_spacetime_domain (scaledPressure b q) := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => q (scaleMap b x)) (global_spacetime_domain 3) :=
    h.comp ((scaleCLE b hb.ne').contDiff.contDiffOn) fun x hx => scaleMap_mem_global hb hx
  exact hcomp.const_smul (b ^ 2)

/-- First space derivative of the rescaled velocity. -/
theorem partial_deriv_scaledVelocity_space {b : ℝ} (hb : b ≠ 0) (v : VelocityField 3) (i j : Fin 3)
    (x : Spacetime3) :
    partial_deriv (n := 4) j.succ (fun y => scaledVelocity b v y i) x
      = b * partial_deriv (n := 4) j.succ (fun y => v y i) (scaleMap b x) := by
  have hfun : (fun y => scaledVelocity b v y i) = fun y => b * v (scaleMap b y) i := by
    funext y; simp [scaledVelocity]
  rw [hfun, partial_deriv_const_mul b hb]
  exact congrArg (fun r => b * r)
    (show partial_deriv (n := 4) j.succ (fun y => v (scaleMap b y) i) x
        = partial_deriv (n := 4) j.succ (fun y => v y i) (scaleMap b x) from
      partial_deriv_comp_scale_space b hb j (fun z => v z i) x)

/-- Time derivative of the rescaled velocity picks up `b²`. -/
theorem partial_deriv_scaledVelocity_time {b : ℝ} (hb : b ≠ 0) (v : VelocityField 3) (i : Fin 3)
    (x : Spacetime3) :
    partial_deriv (n := 4) 0 (fun y => scaledVelocity b v y i) x
      = b ^ 2 * partial_deriv (n := 4) 0 (fun y => v y i) (scaleMap b x) := by
  have hfun : (fun y => scaledVelocity b v y i) = fun y => b * v (scaleMap b y) i := by
    funext y; simp [scaledVelocity]
  rw [hfun, partial_deriv_const_mul b hb,
    show partial_deriv (n := 4) 0 (fun y => v (scaleMap b y) i) x
        = b * partial_deriv (n := 4) 0 (fun y => v y i) (scaleMap b x) from
      partial_deriv_comp_scale_time b hb (fun z => v z i) x]
  ring

/-- Divergence of the rescaled velocity. -/
theorem divergence_scaledVelocity {b : ℝ} (hb : b ≠ 0) (v : VelocityField 3) (x : Spacetime3) :
    divergence (scaledVelocity b v) x = b * divergence v (scaleMap b x) := by
  simp only [divergence, partial_deriv_scaledVelocity_space hb, ← Finset.mul_sum]

/-- Scalar form of the pressure-gradient transport. -/
theorem partial_deriv_scaledPressure {b : ℝ} (hb : b ≠ 0) (q : PressureField 3) (i : Fin 3)
    (x : Spacetime3) :
    partial_deriv (n := 4) i.succ (scaledPressure b q) x
      = b ^ 2 * partial_deriv (n := 4) i.succ q (scaleMap b x) := by
  rw [show (scaledPressure b q) = (fun y => b ^ 2 * q (scaleMap b y)) from rfl,
    partial_deriv_const_mul (b ^ 2) (pow_ne_zero 2 hb)]
  exact congrArg (fun r => b ^ 2 * r)
    (show partial_deriv (n := 4) i.succ (fun y => q (scaleMap b y)) x
        = partial_deriv (n := 4) i.succ q (scaleMap b x) from
      partial_deriv_comp_scale_space b hb i q x)

@[simp] theorem scaledVelocity_apply (b : ℝ) (v : VelocityField 3) (x : Spacetime3) (i : Fin 3) :
    scaledVelocity b v x i = b * v (scaleMap b x) i := by
  simp [scaledVelocity]

/-- The outer step of the second space derivative, in the shape `simp` produces. -/
theorem partial_deriv_outer_scaledVelocity {b : ℝ} (hb : b ≠ 0) (v : VelocityField 3) (i j : Fin 3)
    (x : Spacetime3) :
    partial_deriv (n := 4) j.succ
        (fun y => b * partial_deriv (n := 4) j.succ (fun z => v z i) (scaleMap b y)) x
      = b * partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => v z i) y) (scaleMap b x) := by
  rw [partial_deriv_const_mul b hb]
  exact congrArg (fun r => b * r)
    (show partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => v z i) (scaleMap b y)) x
        = partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => v z i) y) (scaleMap b x) from
      partial_deriv_comp_scale_space b hb j
        (fun w => partial_deriv (n := 4) j.succ (fun z => v z i) w) x)

/--
**Time-scaling transport.**  A global smooth finite-energy solution at viscosity `μ` with data `w₀`
yields one at viscosity `b * μ` with data `b • w₀`, for any `b > 0`.  This is the classical
Navier–Stokes scaling symmetry `u(x,t) ↦ b u(x, b t)`, `p ↦ b² p(x, b t)`; it is elementary
calculus and contains no PDE content.
-/
theorem transport {b μ ν₀ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hν₀ : 0 < ν₀) (hvisc : b * μ = ν₀)
    {w₀ u₀ : InitialVelocity} (hw₀ : DivergenceFreeInitial w₀) (hu₀ : DivergenceFreeInitial u₀)
    (hdata : ∀ x, b • w₀ x = u₀ x)
    (sol : GlobalSmoothSolution (equations μ hμ w₀ hw₀ (fun _ => 0)))
    (hfe : FiniteEnergy sol.velocity) :
    ∃ sol' : GlobalSmoothSolution (equations ν₀ hν₀ u₀ hu₀ (fun _ => 0)),
      FiniteEnergy sol'.velocity := by
  have hb' : b ≠ 0 := hb.ne'
  obtain ⟨⟨v, q, hmom0, hinc0, hinit0⟩, hsv, hsq⟩ := sol
  simp only [equations] at hmom0 hinc0 hinit0
  refine ⟨⟨⟨scaledVelocity b v, scaledPressure b q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · -- momentum equation on `t > 0`
    intro x hx
    have hmom := hmom0 (scaleMap b x) (scaleMap_mem_interior hb hx)
    ext i
    have hi := congrArg (fun w : Space3 => w i) hmom
    simp only [material_derivative, viscous_term, pressure_gradient, equations,
      EuclideanCoordinateSpace.of_fun_apply, PiLp.add_apply, add_zero] at hi ⊢
    simp only [partial_deriv_scaledVelocity_time hb' v i,
      partial_deriv_scaledVelocity_space hb' v i,
      partial_deriv_outer_scaledVelocity hb' v i,
      partial_deriv_scaledPressure hb' q i]
    simp only [scaledVelocity_apply]
    have hsum : (∑ j : Fin 3, b * v (scaleMap b x) j *
          (b * partial_deriv (n := 4) j.succ (fun y => v y i) (scaleMap b x)))
        = b ^ 2 * ∑ j : Fin 3, v (scaleMap b x) j *
          partial_deriv (n := 4) j.succ (fun y => v y i) (scaleMap b x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlap : (∑ j : Fin 3, b * partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => v z i) y) (scaleMap b x))
        = b * ∑ j : Fin 3, partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => v z i) y) (scaleMap b x) := by
      rw [Finset.mul_sum]
    rw [hsum, hlap, ← hvisc]
    linear_combination (b ^ 2) * hi
  · -- incompressibility on `t > 0`
    intro x hx
    have h := hinc0 (scaleMap b x) (scaleMap_mem_interior hb hx)
    have hd : divergence (scaledVelocity b v) x = b * divergence v (scaleMap b x) :=
      divergence_scaledVelocity hb' v x
    simp only [divergence_free_at] at h ⊢
    rw [hd, h, mul_zero]
  · -- initial condition
    intro x
    have h := hinit0 x
    show scaledVelocity b v (spacetime_point 0 x) = u₀ x
    rw [← hdata x]
    simp only [scaledVelocity, scaleMap_spacetime_point, mul_zero]
    exact congrArg (fun w : Space3 => b • w) h
  · exact scaledVelocity_smooth hb hsv
  · exact scaledPressure_smooth hb hsq
  · -- bounded energy
    obtain ⟨C, hC, hbound⟩ := hfe
    refine ⟨b ^ 2 * C, by positivity, ?_⟩
    intro t ht
    obtain ⟨hint, hlt⟩ := hbound (b * t) (mul_nonneg hb.le ht)
    have hfun : (fun x : Space3 => ∑ i : Fin 3,
          (scaledVelocity b v (spacetime_point t x) i) ^ 2)
        = fun x : Space3 => b ^ 2 * ∑ i : Fin 3, (v (spacetime_point (b * t) x) i) ^ 2 := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp [scaledVelocity, scaleMap_spacetime_point, mul_pow]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hint.const_mul _
    · have henergy : energy_integral (scaledVelocity b v) t
          = b ^ 2 * energy_integral v (b * t) := by
        simp only [energy_integral]
        rw [show (fun x : Space3 => ∑ i : Fin 3,
            (scaledVelocity b v (spacetime_point t x) i) ^ 2)
            = fun x : Space3 => b ^ 2 * ∑ i : Fin 3,
              (v (spacetime_point (b * t) x) i) ^ 2 from hfun]
        exact MeasureTheory.integral_const_mul _ _
      rw [henergy]
      exact mul_lt_mul_of_pos_left hlt (by positivity)

/-! ## The disjunction of Fefferman's cases is a theorem of classical logic -/

/-- Fefferman (A) at a fixed viscosity. -/
def SmoothExistenceAt (ν : ℝ) (ν_pos : ν > 0) : Prop :=
  ∀ (u₀ : InitialVelocity), SmoothRapidDecayInitial u₀ →
    ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
        SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity

/-- Fefferman (C) at a fixed viscosity. -/
def BreakdownAt (ν : ℝ) (ν_pos : ν > 0) : Prop :=
  ∃ (u₀ : InitialVelocity) (f : SpacetimeForce),
    SmoothRapidDecayInitial u₀ ∧ DivergenceFreeInitial u₀ ∧ SmoothRapidDecayForce f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun x => f x)),
              SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity)

theorem smoothExistence_iff :
    SmoothExistence ↔ ∀ ν (ν_pos : ν > 0), SmoothExistenceAt ν ν_pos := Iff.rfl

theorem breakdown_iff : Breakdown ↔ ∀ ν (ν_pos : ν > 0), BreakdownAt ν ν_pos := Iff.rfl

/-- The zero-force step (issue #5): at a fixed viscosity, `¬(A at ν) → (C at ν)`, because the zero
force is admissible (`zero_force_smooth_rapid_decay`). -/
theorem breakdownAt_of_not_smoothExistenceAt (ν : ℝ) (ν_pos : ν > 0) :
    ¬ SmoothExistenceAt ν ν_pos → BreakdownAt ν ν_pos := by
  classical
  intro hA
  by_contra hC
  apply hA
  intro u₀ h4 hdiv
  by_contra hno
  apply hC
  exact ⟨u₀, fun _ => 0, h4, hdiv, zero_force_smooth_rapid_decay, fun _ => hno⟩

/-- The scaling step.  If some admissible datum `u₀` has no global smooth finite-energy zero-force
solution at viscosity `ν₀`, then `(ν/ν₀) • u₀` with the zero force witnesses (C) at every viscosity
`ν > 0`: a solution at `ν` would transport back to one at `ν₀` with data `u₀`. -/
theorem breakdown_witness {ν₀ : ℝ} (hν₀ : ν₀ > 0) {u₀ : InitialVelocity}
    (h4 : SmoothRapidDecayInitial u₀) (hdiv₀ : DivergenceFreeInitial u₀)
    (hno : ¬ ∃ sol : GlobalSmoothSolution (equations ν₀ hν₀ u₀ hdiv₀ (fun _ => 0)),
        SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity)
    (ν : ℝ) (hν : ν > 0) :
    ∃ (w₀ : InitialVelocity) (f : SpacetimeForce),
      SmoothRapidDecayInitial w₀ ∧ DivergenceFreeInitial w₀ ∧ SmoothRapidDecayForce f ∧
        ∀ hdiv : DivergenceFreeInitial w₀,
          ¬ (∃ sol : GlobalSmoothSolution (equations ν hν w₀ hdiv (fun x => f x)),
                SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity) := by
  have hc : 0 < ν / ν₀ := div_pos hν hν₀
  refine ⟨scaledInitial (ν / ν₀) u₀, fun _ => 0,
    scaledInitial_smooth_rapid_decay _ hc h4,
    scaledInitial_divergence_free _ hc.ne' hdiv₀,
    zero_force_smooth_rapid_decay, ?_⟩
  intro hdiv hsol
  obtain ⟨sol, _, hfe⟩ := hsol
  apply hno
  obtain ⟨sol', hfe'⟩ :=
    transport (b := ν₀ / ν) (μ := ν) (ν₀ := ν₀) (div_pos hν₀ hν) hν hν₀
      (by field_simp) hdiv hdiv₀
      (fun x => by
        have hcoef : (ν₀ / ν) * (ν / ν₀) = 1 := by field_simp
        calc (ν₀ / ν) • scaledInitial (ν / ν₀) u₀ x
            = ((ν₀ / ν) * (ν / ν₀)) • u₀ x := smul_smul _ _ _
          _ = u₀ x := by rw [hcoef, one_smul])
      sol hfe
  exact ⟨sol', GlobalSmoothSolution.smooth_fields sol', hfe'⟩

/-- Zero-force step and scaling step together: failure of (A) at one viscosity gives (C) at every
viscosity. -/
theorem breakdownAt_of_not_smoothExistenceAt_at_all {ν₀ : ℝ} (hν₀ : ν₀ > 0)
    (hA : ¬ SmoothExistenceAt ν₀ hν₀) (ν : ℝ) (hν : ν > 0) : BreakdownAt ν hν := by
  classical
  have hex : ∃ (u₀ : InitialVelocity) (_ : SmoothRapidDecayInitial u₀)
      (hdiv₀ : DivergenceFreeInitial u₀),
      ¬ ∃ sol : GlobalSmoothSolution (equations ν₀ hν₀ u₀ hdiv₀ (fun _ => 0)),
          SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity := by
    by_contra h
    push Not at h
    exact hA fun u₀ h4 hdiv => h u₀ h4 hdiv
  obtain ⟨u₀, h4, hdiv₀, hno⟩ := hex
  exact breakdown_witness hν₀ h4 hdiv₀ hno ν hν

/-- **(A) or (C) holds, by classical logic alone.** -/
theorem whole_space_disjunction :
    MillenniumNavierStokes.FeffermanA ∨ MillenniumNavierStokes.FeffermanC := by
  classical
  by_cases hA : MillenniumNavierStokes.FeffermanA
  · exact Or.inl hA
  · refine Or.inr ?_
    have hex : ∃ (ν₀ : ℝ) (hν₀ : ν₀ > 0), ¬ SmoothExistenceAt ν₀ hν₀ := by
      by_contra h
      push Not at h
      exact hA fun ν hν => h ν hν
    obtain ⟨ν₀, hν₀, hnot⟩ := hex
    intro ν hν
    exact breakdownAt_of_not_smoothExistenceAt_at_all hν₀ hnot ν hν

/-- **The four-way disjunction of Fefferman's cases is a theorem.**  This is why it is not a
target. -/
theorem fefferman_disjunction :
    MillenniumNavierStokes.FeffermanA ∨ MillenniumNavierStokes.FeffermanB ∨
      MillenniumNavierStokes.FeffermanC ∨ MillenniumNavierStokes.FeffermanD := by
  rcases whole_space_disjunction with hA | hC
  · exact Or.inl hA
  · exact Or.inr (Or.inr (Or.inl hC))

end Tests.NavierStokes.AggregateIsTrivial
