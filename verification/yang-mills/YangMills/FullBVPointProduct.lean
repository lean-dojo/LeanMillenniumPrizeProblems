import YangMills.FullBVShiftedNilpotency
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem finsum_postmul_delta {I : Type*} [DecidableEq I]
    (f : I → JetAlgebra G) (hf : (Function.support f).Finite)
    (Q R : JetAlgebra G) (k : I) :
    (∑ᶠ i, (f i * Q + if i = k then R else 0)) = (∑ᶠ i, f i) * Q + R := by
  have h1 := hf.subset (Function.support_mul_subset_left f (fun _ => Q))
  have h2 : (Function.support (fun i => if i = k then R else 0)).Finite := by
    apply (Set.finite_singleton k).subset
    intro i hi
    by_contra hn
    exact hi (by simp_all)
  rw [finsum_add_distrib h1 h2, ← finsum_mul' f Q hf]
  congr 1
  rw [finsum_eq_single _ k (by intro i hi; simp [hi])]
  simp

/-- Exact right-generator product rule before moving its Hamiltonian image
past the preceding polynomial. It uses finite supports, including zero
divisors in the exterior algebra. -/
theorem coordinateDifferential_mul_evenJet (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (P : JetAlgebra G) (k : EvenJet G) :
    coordinateDifferential E O (P * evenJet k) =
      coordinateDifferential E O P * evenJet k + E k * P := by
  classical
  have he (i : EvenJet G) : E i * evenPartial i (P * evenJet k) =
      (E i * evenPartial i P) * evenJet k + if i = k then E k * P else 0 := by
    rw [evenPartial_mul, evenPartial_evenJet]
    by_cases h : i = k <;> simp [h, mul_add, mul_assoc]
  have ho (i : OddJet G) : O i * oddPartial i (P * evenJet k) =
      (O i * oddPartial i P) * evenJet k := by
    simp [oddPartial_mul, mul_assoc]
  simp only [coordinateDifferential, he, ho]
  rw [finsum_postmul_delta _ (evenSummands_finite E P),
    ← finsum_mul' _ _ (oddSummands_finite O P)]
  noncomm_ring

theorem coordinateDifferential_mul_oddJet (E : EvenJet G → JetAlgebra G)
    (O : OddJet G → JetAlgebra G) (P : JetAlgebra G) (k : OddJet G) :
    coordinateDifferential E O (P * oddJet k) =
      coordinateDifferential E O P * oddJet k + O k * parity P := by
  classical
  have he (i : EvenJet G) : E i * evenPartial i (P * oddJet k) =
      (E i * evenPartial i P) * oddJet k := by
    simp [evenPartial_mul, mul_assoc]
  have ho (i : OddJet G) : O i * oddPartial i (P * oddJet k) =
      (O i * oddPartial i P) * oddJet k + if i = k then O k * parity P else 0 := by
    rw [oddPartial_mul, oddPartial_oddJet]
    by_cases h : i = k <;> simp [h, mul_add, mul_assoc]
  simp only [coordinateDifferential, he, ho]
  rw [finsum_postmul_delta _ (oddSummands_finite O P),
    ← finsum_mul' _ _ (evenSummands_finite E P)]
  noncomm_ring

/-- Fixed pointwise quadratic ST formula. The second image is retained in
its actual left placement, so no unproved graded-commutation rule is hidden. -/
theorem localST_mul_jet (S P : JetAlgebra G) (k : Jet G) :
    localST S (P * jet k) = localST S P * jet k +
      prolongedST S k * (if k.field.parity then parity P else P) := by
  by_cases hk : k.field.parity = true
  · simpa only [jet, hk, dif_pos, if_pos, prolongedST, localST] using
      coordinateDifferential_mul_oddJet
        (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field))
        (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field)) P ⟨k, hk⟩
  · simpa only [jet, hk, dif_neg, if_neg, prolongedST, localST] using
      coordinateDifferential_mul_evenJet
        (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field))
        (fun j => totalDerivatives j.val.derivative (stCharacteristic S j.val.field)) P
          ⟨k, by cases h : k.field.parity <;> simp_all⟩

end YangMills.FullBV
