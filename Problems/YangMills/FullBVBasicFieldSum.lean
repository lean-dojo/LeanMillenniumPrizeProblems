import Problems.YangMills.FullBVPhysicalActionInvariance

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private def basicFieldSumEquiv (G : CompactSimpleGaugeGroup) : BasicField G ≃
    (Fin 4 × Fin G.dimension) ⊕ (Fin G.dimension ⊕ (Fin G.dimension ⊕ Fin G.dimension)) where
  toFun
    | .gauge mu a => .inl (mu,a)
    | .antighost a => .inr (.inl a)
    | .ghost a => .inr (.inr (.inl a))
    | .auxiliary a => .inr (.inr (.inr a))
  invFun
    | .inl (mu,a) => .gauge mu a
    | .inr (.inl a) => .antighost a
    | .inr (.inr (.inl a)) => .ghost a
    | .inr (.inr (.inr a)) => .auxiliary a
  left_inv K := by cases K <;> rfl
  right_inv K := by rcases K with ⟨mu,a⟩ | (a | (a | a)) <;> rfl

/-- Exact decomposition of a sum over all four actual basic-field species. -/
theorem sum_basicField_components {M : Type*} [AddCommMonoid M] (F : BasicField G → M) :
    (∑ K : BasicField G, F K) =
      (∑ mu : Fin 4, ∑ a : Fin G.dimension, F (.gauge mu a)) +
      (∑ a : Fin G.dimension, F (.antighost a)) +
      (∑ a : Fin G.dimension, F (.ghost a)) +
      (∑ a : Fin G.dimension, F (.auxiliary a)) := by
  have h := Fintype.sum_equiv (basicFieldSumEquiv G) F
    (fun x => F ((basicFieldSumEquiv G).symm x))
    (fun K => congrArg F ((basicFieldSumEquiv G).symm_apply_apply K).symm)
  rw [h]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, basicFieldSumEquiv,
    Equiv.coe_fn_symm_mk]
  abel

end YangMills.FullBV
