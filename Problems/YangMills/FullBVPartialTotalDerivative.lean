import Problems.YangMills.FullBVTotalDerivativeParity
import Problems.YangMills.FullBVActionParity

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem Jet.shift_injective (mu : Fin 4) : Function.Injective (Jet.shift (G := G) mu) := by
  intro j k h
  apply Jet.eq_of_coordinates
  · have hf : (j.shift mu).field = (k.shift mu).field := congrArg (fun x : Jet G => x.field) h
    exact hf
  · have hd := congrArg (fun x : Jet G => x.derivative) h
    change j.derivative + Pi.single mu 1 = k.derivative + Pi.single mu 1 at hd
    exact add_right_cancel hd

/-- The actual graded partial/ordinary derivative commutator as a linear
operator on full local insertions. -/
def partialDerivativeCommutator (j : Jet G) (mu : Fin 4) :
    JetAlgebra G →ₗ[ℂ] JetAlgebra G :=
  (leftPartialJet j).comp (totalDerivativeLinear mu) -
    (totalDerivativeLinear mu).comp (leftPartialJet j)

theorem partialDerivativeCommutator_jet (j k : Jet G) (mu : Fin 4) :
    partialDerivativeCommutator j mu (jet k) = if j = k.shift mu then 1 else 0 := by
  classical
  change leftPartialJet j (totalDerivative mu (jet k)) -
    totalDerivative mu (leftPartialJet j (jet k)) = _
  rw [totalDerivative_jet, leftPartialJet_jet, leftPartialJet_jet]
  by_cases h : j = k <;> simp [h, totalDerivative_one]

/-- This commutator has the same graded Leibniz sign as the original jet
partial. The statement follows from both actual product rules and D parity. -/
theorem partialDerivativeCommutator_mul_jet (j k : Jet G) (mu : Fin 4) (P : JetAlgebra G) :
    partialDerivativeCommutator j mu (P * jet k) =
      partialDerivativeCommutator j mu P * jet k +
        (if j.field.parity then parity P else P) * partialDerivativeCommutator j mu (jet k) := by
  classical
  change leftPartialJet j (totalDerivative mu (P * jet k)) -
    totalDerivative mu (leftPartialJet j (P * jet k)) =
    (leftPartialJet j (totalDerivative mu P) - totalDerivative mu (leftPartialJet j P)) * jet k +
    (if j.field.parity then parity P else P) *
      (leftPartialJet j (totalDerivative mu (jet k)) - totalDerivative mu (leftPartialJet j (jet k)))
  rw [totalDerivative_mul, map_add, leftPartialJet_mul, leftPartialJet_mul,
    leftPartialJet_mul, totalDerivative_add, totalDerivative_mul, totalDerivative_mul]
  cases hj : j.field.parity <;>
    simp only [hj, Bool.false_eq_true, if_true, if_false, totalDerivative_parity,
      add_mul, mul_add, sub_mul, mul_sub]
  all_goals abel

/-- Differentiating a total derivative at a shifted jet adds exactly its
predecessor partial; all ghost/antifield signs are the actual algebra's. -/
theorem leftPartialJet_totalDerivative_shift (k : Jet G) (mu : Fin 4) (P : JetAlgebra G) :
    leftPartialJet (k.shift mu) (totalDerivative mu P) =
      totalDerivative mu (leftPartialJet (k.shift mu) P) + leftPartialJet k P := by
  classical
  have identity : partialDerivativeCommutator (k.shift mu) mu P = leftPartialJet k P := by
    induction P using polynomial_induction_jet with
    | zero => simp
    | one =>
        change leftPartialJet _ (totalDerivative mu 1) - totalDerivative mu (leftPartialJet _ 1) = _
        simp [leftPartialJet_one, totalDerivative_one]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | smul c P hP => simp only [map_smul, hP]
    | mul P j hP =>
        rw [partialDerivativeCommutator_mul_jet, hP, partialDerivativeCommutator_jet,
          leftPartialJet_mul, leftPartialJet_jet]
        have heq : (k.shift mu = j.shift mu) ↔ k = j := (Jet.shift_injective mu).eq_iff
        simp only [heq]
        rfl
  change leftPartialJet _ (totalDerivative mu P) - totalDerivative mu (leftPartialJet _ P) = _ at identity
  have result : leftPartialJet (k.shift mu) (totalDerivative mu P) =
      leftPartialJet k P + totalDerivative mu (leftPartialJet (k.shift mu) P) :=
    sub_eq_iff_eq_add.mp identity
  exact result.trans (add_comm _ _)

/-- At jet order zero in this direction there is no predecessor term. -/
theorem leftPartialJet_totalDerivative_zero (j : Jet G) (mu : Fin 4)
    (hj : j.derivative mu = 0) (P : JetAlgebra G) :
    leftPartialJet j (totalDerivative mu P) = totalDerivative mu (leftPartialJet j P) := by
  classical
  have different (k : Jet G) : j ≠ k.shift mu := by
    intro h
    have hc := congrArg (fun x : Jet G => x.derivative mu) h
    simp only [Jet.shift, Pi.add_apply, Pi.single_eq_same, hj] at hc
    omega
  have identity : partialDerivativeCommutator j mu P = 0 := by
    induction P using polynomial_induction_jet with
    | zero => simp
    | one =>
        change leftPartialJet _ (totalDerivative mu 1) - totalDerivative mu (leftPartialJet _ 1) = _
        simp [leftPartialJet_one, totalDerivative_one]
    | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
    | smul c P hP => simp only [map_smul, hP, smul_zero]
    | mul P k hP =>
        rw [partialDerivativeCommutator_mul_jet, hP, partialDerivativeCommutator_jet]
        simp only [different k, if_false, zero_mul, mul_zero, add_zero]
  exact sub_eq_zero.mp identity

/-- The unique actual multiindex predecessor when one derivative is present. -/
def Jet.unshift (mu : Fin 4) (j : Jet G) : Jet G :=
  ⟨j.field,j.derivative - Pi.single mu 1⟩

theorem Jet.unshift_shift (j : Jet G) (mu : Fin 4) (positive : 0 < j.derivative mu) :
    (j.unshift mu).shift mu = j := by
  apply Jet.eq_of_coordinates (j := (j.unshift mu).shift mu) (k := j)
  · rfl
  funext nu
  by_cases h : mu = nu
  · subst nu
    simp only [Jet.unshift, Jet.shift, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    omega
  · simp [Jet.unshift, Jet.shift, Pi.sub_apply, Pi.add_apply, Pi.single_apply, h]

theorem leftPartialJet_totalDerivative (j : Jet G) (mu : Fin 4) (P : JetAlgebra G) :
    leftPartialJet j (totalDerivative mu P) = totalDerivative mu (leftPartialJet j P) +
      if 0 < j.derivative mu then leftPartialJet (j.unshift mu) P else 0 := by
  classical
  by_cases h : 0 < j.derivative mu
  · simpa only [j.unshift_shift mu h, if_pos h] using
      leftPartialJet_totalDerivative_shift (j.unshift mu) mu P
  · rw [leftPartialJet_totalDerivative_zero j mu (by omega), if_neg h, add_zero]

end YangMills.FullBV
