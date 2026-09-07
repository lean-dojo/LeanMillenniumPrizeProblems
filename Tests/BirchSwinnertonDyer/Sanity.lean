import Problems.BirchSwinnertonDyer.Millennium

/-!
# Birch and Swinnerton-Dyer: sanity checks

Compiled checks accompanying the 2026-09-07 review.  Everything here is a positive fact about the
formalization; the axiom guards make sure no `sorry` leaks into the supporting theory (the only
declaration allowed to use `sorryAx` is the prize placeholder).
-/

open MillenniumBirchSwinnertonDyer Filter Topology Polynomial

namespace Tests.BirchSwinnertonDyer

/-! ## Axiom audit -/

/-- info: 'MillenniumBirchSwinnertonDyer.LSeriesData.l_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LSeriesData.l_unique

/-- info: 'MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank

/-- info: 'MillenniumBirchSwinnertonDyer.HasseWeilLSeriesData.analytic_order_hasse_weil_lseries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasseWeilLSeriesData.analytic_order_hasse_weil_lseries_eq

/-- info: 'MillenniumBirchSwinnertonDyer.ClayShortIntegralModel.weierstrass_bad_prime_iff_clay_bad_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayShortIntegralModel.weierstrass_bad_prime_iff_clay_bad_prime

/-- info: 'MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clay_prize_birch_swinnerton_dyer

/-! ## The Mordell–Weil group is an additive group and the rank is an `ℕ∞` -/

noncomputable example (W : WeierstrassCurve ℚ) : AddCommGroup W.toProjective.Point := inferInstance
noncomputable example (W : WeierstrassCurve ℚ) : ℕ∞ := WeierstrassCurve.rank W

/-! ## Bad-prime local factor uses the nonsingular-point count `q - #W_ns(𝔽_q)` -/

example {R : Type} [CommRing R] (W : WeierstrassCurve R) (h : ¬ W.IsElliptic) :
    W.local_euler_factor_polynomial =
      1 - (Cardinal.toNat (Cardinal.mk R) - W.num_points : ℤ) • (X : ℤ[X]) := by
  simp [WeierstrassCurve.local_euler_factor_polynomial, h]

/-! ## Completed L-series data is at least as available as ordinary data -/

variable {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}

/-- Every ordinary continuation gives completed data with completion factor `1`. -/
def completedOfOrdinary (d : LSeriesData W hΔ) : CompletedLSeriesData W hΔ :=
  { d with
    lstar := d.L
    analytic_star := d.analytic
    completion_factor := fun _ => 1
    completion_factor_analytic := analyticAt_const
    completion_factor_ne_zero := one_ne_zero
    lstar_eq := Filter.Eventually.of_forall fun z => by simp }

/-- The completed leading coefficient is unique (so `CompletedLeadingCoeff` is a function). -/
theorem leading_coeff_unique (data : CompletedLSeriesData W hΔ) {c₁ c₂ : ℂ}
    (h₁ : CompletedLeadingCoeff data c₁) (h₂ : CompletedLeadingCoeff data c₂) : c₁ = c₂ := by
  obtain ⟨n₁, hn₁, g₁, hg₁, _, he₁, rfl⟩ := h₁
  obtain ⟨n₂, hn₂, g₂, hg₂, _, he₂, rfl⟩ := h₂
  have hn : n₁ = n₂ := by exact_mod_cast hn₁.trans hn₂.symm
  subst hn
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), g₁ z = g₂ z := by
    have h := (he₁.and he₂).filter_mono (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
    filter_upwards [h, self_mem_nhdsWithin] with z hz hz1
    have hpow : (z - 1) ^ n₁ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz1)
    have := hz.1.symm.trans hz.2
    simp only [smul_eq_mul] at this
    exact mul_left_cancel₀ hpow this
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg₂.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- The order of vanishing of `L*` at `1` agrees with that of `L` (positive content of the
completed data). -/
example (d : LSeriesData W hΔ) :
    analyticOrderAt (completedOfOrdinary d).lstar 1 = analyticOrderAt d.L 1 :=
  (completedOfOrdinary d).order_lstar_eq

end Tests.BirchSwinnertonDyer
