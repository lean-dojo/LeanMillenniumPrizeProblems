import Problems.YangMills.InsertionEquationDilation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

/-- Scalar formal loop multiplication, at fixed UV and other parameters.
The coefficient is independent of the differentiated flow scale. -/
def scalarConvolution (c : ℕ → ℂ) (F : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ r ∈ Finset.range (loop+1), c r * F (loop-r) Λ UV legs q

private lemma sum_three_rotate {I J K : Type*} [Fintype I] [Fintype J]
    (s : Finset K) (f : I → J → K → ℂ) :
    (∑ i, ∑ j, ∑ k ∈ s, f i j k) = ∑ k ∈ s, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k ∈ s, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma truncated_triangle_exchange (n : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ l ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n-l+1), f l r) =
      ∑ r ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n-r+1), f l r := by
  have extend (l : ℕ) (hl : l < n+1) (g : ℕ → ℂ) :
      (∑ r ∈ Finset.range (n-l+1), g r) =
        ∑ r ∈ Finset.range (n+1), if l+r ≤ n then g r else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_range,Finset.mem_filter]
    omega
  calc
    _ = ∑ l ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n+1),
          if l+r ≤ n then f l r else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact extend l (Finset.mem_range.mp hl) _
    _ = ∑ r ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
          if l+r ≤ n then f l r else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simpa only [Nat.add_comm] using (extend r (Finset.mem_range.mp hr) (fun l => f l r)).symm

lemma quadraticSplit_scalarConvolution_right (c : ℕ → ℂ) (L F : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    quadraticSplit L (scalarConvolution c F) loop leftLoop Λ UV legs q s =
      ∑ r ∈ Finset.range (loop-leftLoop+1),
        c r * quadraticSplit L F (loop-r) leftLoop Λ UV legs q s := by
  simp only [quadraticSplit,scalarConvolution]
  simp_rw [Finset.mul_sum]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro N _
  have sub : loop-leftLoop-r = loop-r-leftLoop := by omega
  rw [sub]
  ring

lemma quadraticFlowRHS_scalarConvolution_right (c : ℕ → ℂ) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quadraticFlowRHS L (scalarConvolution c F) loop Λ UV legs q =
      ∑ r ∈ Finset.range (loop+1), c r * quadraticFlowRHS L F (loop-r) Λ UV legs q := by
  unfold quadraticFlowRHS
  simp_rw [quadraticSplit_scalarConvolution_right]
  rw [Fin.sum_univ_eq_sum_range (fun l => ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    ∑ r ∈ Finset.range (loop-l+1), c r * quadraticSplit L F (loop-r) l Λ UV legs q s) (loop+1)]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin legs.length)).powerset)]
  rw [truncated_triangle_exchange]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun l => ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    c r * quadraticSplit L F (loop-r) l Λ UV legs q s) (loop-r+1)]

lemma linearFlowIntegrand_scalarConvolution (c : ℕ → ℂ) (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (scalarConvolution c F) loop Λ UV legs q p =
      ∑ r ∈ Finset.range (loop+1), c r * linearFlowIntegrand F (loop-r) Λ UV legs q p := by
  cases loop with
  | zero => simp [linearFlowIntegrand]
  | succ n =>
    have main : linearFlowIntegrand (scalarConvolution c F) (n+1) Λ UV legs q p =
        ∑ r ∈ Finset.range (n+1), c r * linearFlowIntegrand F (n+1-r) Λ UV legs q p := by
      calc
        _ = ∑ r ∈ Finset.range (n+1), c r *
            ((∑ M : BasicField G, ∑ N : BasicField G,
              (basicDerivativeCovariance Λ M N (-p) : ℂ) *
                F (n-r) Λ UV (.inl M :: .inl N :: legs)
                  (prependMomenta (.inl M) p (prependMomenta (.inl N) (-p) q))) /
              (2 * Real.pi : ℂ)^4) := by
          simp only [linearFlowIntegrand,show n+1 ≠ 0 by omega,if_false,Nat.add_sub_cancel,
            scalarConvolution]
          simp_rw [Finset.mul_sum]
          rw [sum_three_rotate,Finset.sum_div]
          apply Finset.sum_congr rfl
          intro r _
          rw [← mul_div_assoc]
          congr 1
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro M _
          apply Finset.sum_congr rfl
          intro N _
          ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          have nonzero : n+1-r ≠ 0 := by have := Finset.mem_range.mp hr; omega
          simp only [linearFlowIntegrand,nonzero,if_false]
          have sub : n+1-r-1 = n-r := by omega
          rw [sub]
    rw [Finset.sum_range_succ]
    simpa only [Nat.sub_self,linearFlowIntegrand,if_true,mul_zero,add_zero] using main

/-- Actual Lebesgue integrability is preserved, rather than inferred from
Lean's totalized integral. Only the finitely used lower loop orders occur. -/
theorem linearFlowIntegrand_scalarConvolution_integrable (c : ℕ → ℂ) (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ k ≤ loop, Integrable (linearFlowIntegrand F k Λ UV legs q)) :
    Integrable (linearFlowIntegrand (scalarConvolution c F) loop Λ UV legs q) := by
  have eq : linearFlowIntegrand (scalarConvolution c F) loop Λ UV legs q =
      fun p => ∑ r ∈ Finset.range (loop+1), c r * linearFlowIntegrand F (loop-r) Λ UV legs q p := by
    funext p
    exact linearFlowIntegrand_scalarConvolution c F loop Λ UV legs q p
  rw [eq]
  apply integrable_finsetSum
  intro r _
  exact (integrable (loop-r) (Nat.sub_le _ _)).const_mul (c r)

lemma linearFlowRHS_scalarConvolution (c : ℕ → ℂ) (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ k ≤ loop, Integrable (linearFlowIntegrand F k Λ UV legs q)) :
    linearFlowRHS (scalarConvolution c F) loop Λ UV legs q =
      ∑ r ∈ Finset.range (loop+1), c r * linearFlowRHS F (loop-r) Λ UV legs q := by
  unfold linearFlowRHS
  simp_rw [linearFlowIntegrand_scalarConvolution]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro r _
    exact (integrable (loop-r) (Nat.sub_le _ _)).const_mul (c r)

theorem insertionHomogeneousRHS_scalarConvolution_right (c : ℕ → ℂ) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ k ≤ loop, Integrable (linearFlowIntegrand F k Λ UV legs q)) :
    insertionHomogeneousRHS L (scalarConvolution c F) loop Λ UV legs q =
      ∑ r ∈ Finset.range (loop+1), c r * insertionHomogeneousRHS L F (loop-r) Λ UV legs q := by
  unfold insertionHomogeneousRHS
  rw [linearFlowRHS_scalarConvolution c F loop Λ UV legs q integrable,
    quadraticFlowRHS_scalarConvolution_right]
  simp_rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- A finite sum of actual inserted families, with no additional kernels. -/
def finiteFlowSum {ι : Type*} (s : Finset ι) (F : ι → FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ i ∈ s, F i loop Λ UV legs q

lemma linearFlowIntegrand_finiteFlowSum {ι : Type*} (s : Finset ι) (F : ι → FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (finiteFlowSum s F) loop Λ UV legs q p =
      ∑ i ∈ s, linearFlowIntegrand (F i) loop Λ UV legs q p := by
  unfold linearFlowIntegrand
  by_cases zero : loop=0
  · simp only [zero,if_true,Finset.sum_const_zero]
  · simp only [zero,if_false,finiteFlowSum]
    simp_rw [Finset.mul_sum]
    rw [sum_three_rotate,Finset.sum_div]

theorem linearFlowIntegrand_finiteFlowSum_integrable {ι : Type*}
    (s : Finset ι) (F : ι → FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ i ∈ s, Integrable (linearFlowIntegrand (F i) loop Λ UV legs q)) :
    Integrable (linearFlowIntegrand (finiteFlowSum s F) loop Λ UV legs q) := by
  have eq : linearFlowIntegrand (finiteFlowSum s F) loop Λ UV legs q =
      fun p => ∑ i ∈ s, linearFlowIntegrand (F i) loop Λ UV legs q p := by
    funext p
    exact linearFlowIntegrand_finiteFlowSum s F loop Λ UV legs q p
  rw [eq]
  exact integrable_finsetSum s integrable

lemma linearFlowRHS_finiteFlowSum {ι : Type*} (s : Finset ι) (F : ι → FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ i ∈ s, Integrable (linearFlowIntegrand (F i) loop Λ UV legs q)) :
    linearFlowRHS (finiteFlowSum s F) loop Λ UV legs q =
      ∑ i ∈ s, linearFlowRHS (F i) loop Λ UV legs q := by
  unfold linearFlowRHS
  simp_rw [linearFlowIntegrand_finiteFlowSum]
  exact integral_finsetSum s integrable

lemma quadraticSplit_finiteFlowSum_right {ι : Type*} (s : Finset ι) (F : ι → FlowFamily G)
    (L : FlowFamily G) (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (t : Finset (Fin legs.length)) :
    quadraticSplit L (finiteFlowSum s F) loop leftLoop Λ UV legs q t =
      ∑ i ∈ s, quadraticSplit L (F i) loop leftLoop Λ UV legs q t := by
  simp only [quadraticSplit,finiteFlowSum]
  simp_rw [Finset.mul_sum]
  rw [sum_three_rotate]

lemma quadraticFlowRHS_finiteFlowSum_right {ι : Type*} (s : Finset ι) (F : ι → FlowFamily G)
    (L : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    quadraticFlowRHS L (finiteFlowSum s F) loop Λ UV legs q =
      ∑ i ∈ s, quadraticFlowRHS L (F i) loop Λ UV legs q := by
  unfold quadraticFlowRHS
  simp_rw [quadraticSplit_finiteFlowSum_right]
  calc
    _ = ∑ l : Fin (loop+1), ∑ i ∈ s,
        ∑ t ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
          quadraticSplit L (F i) loop l.val Λ UV legs q t := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem insertionHomogeneousRHS_finiteFlowSum_right {ι : Type*}
    (s : Finset ι) (F : ι → FlowFamily G) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (integrable : ∀ i ∈ s, Integrable (linearFlowIntegrand (F i) loop Λ UV legs q)) :
    insertionHomogeneousRHS L (finiteFlowSum s F) loop Λ UV legs q =
      ∑ i ∈ s, insertionHomogeneousRHS L (F i) loop Λ UV legs q := by
  unfold insertionHomogeneousRHS
  rw [linearFlowRHS_finiteFlowSum s F loop Λ UV legs q integrable,
    quadraticFlowRHS_finiteFlowSum_right]
  rw [Finset.mul_sum,Finset.sum_sub_distrib]

end YangMills.PerturbativeFlow
