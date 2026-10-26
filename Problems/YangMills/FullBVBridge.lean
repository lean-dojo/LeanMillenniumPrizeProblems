import Problems.YangMills.FullBV

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Algebraic presentation bridges for fixed BV density amplitudes. -/
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem polynomialPartials_commute {E : Type*} (i j : E) (p : MvPolynomial E ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  by_cases h : i = j
  · subst j; rfl
  · induction p using MvPolynomial.induction_on' with
    | monomial m c =>
        simp [MvPolynomial.pderiv_monomial, h, Ne.symm h, tsub_right_comm,
          mul_assoc, mul_comm, mul_left_comm]
    | add p q hp hq => simp [hp, hq]

theorem evenPartials_commute (i j : EvenJet G) (P : JetAlgebra G) :
    evenPartial i (evenPartial j P) = evenPartial j (evenPartial i P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | tmul p e => simp [evenPartial, polynomialPartials_commute]

theorem evenOddPartials_commute (i : EvenJet G) (j : OddJet G) (P : JetAlgebra G) :
    evenPartial i (oddPartial j P) = oddPartial j (evenPartial i P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | tmul p e => simp [evenPartial, oddPartial]

theorem oddPartials_anticommute (i j : OddJet G) (P : JetAlgebra G) :
    oddPartial i (oddPartial j P) = -oddPartial j (oddPartial i P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, neg_add]
  | tmul p e =>
      simp only [oddPartial, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [CliffordAlgebra.contractLeft_comm]
      exact TensorProduct.tmul_neg _ _

theorem jetPartials_commute (i j : Jet G) (P : JetAlgebra G) :
    leftPartialJet i (leftPartialJet j P) =
      if i.field.parity = true ∧ j.field.parity = true then
        -leftPartialJet j (leftPartialJet i P)
      else leftPartialJet j (leftPartialJet i P) := by
  classical
  by_cases hi : i.field.parity = true <;> by_cases hj : j.field.parity = true
  · simpa only [leftPartialJet, hi, hj, Bool.false_eq_true, dite_true, and_self, if_true] using
      oddPartials_anticommute ⟨i, hi⟩ ⟨j, hj⟩ P
  · simpa only [leftPartialJet, hi, hj, Bool.false_eq_true, dite_true, dite_false, and_false, if_false] using
      (evenOddPartials_commute ⟨j, by cases hp : j.field.parity <;> simp_all⟩ ⟨i, hi⟩ P).symm
  · simpa only [leftPartialJet, hi, hj, Bool.false_eq_true, dite_true, dite_false, false_and, if_false] using
      evenOddPartials_commute ⟨i, by cases hp : i.field.parity <;> simp_all⟩ ⟨j, hj⟩ P
  · simpa only [leftPartialJet, hi, hj, Bool.false_eq_true, dite_false, false_and, if_false] using
      evenPartials_commute ⟨i, by cases hp : i.field.parity <;> simp_all⟩
        ⟨j, by cases hp : j.field.parity <;> simp_all⟩ P

theorem jetPartial_zero_preserved (i j : Jet G) (P : JetAlgebra G)
    (h : leftPartialJet i P = 0) :
    leftPartialJet i (leftPartialJet j P) = 0 := by
  rw [jetPartials_commute, h]
  split <;> simp

theorem jetSupport_partial_subset (j : Jet G) (P : JetAlgebra G) :
    jetSupport (leftPartialJet j P) ⊆ jetSupport P := by
  intro i hi
  rw [mem_jetSupport] at hi ⊢
  by_contra hz
  exact hi (jetPartial_zero_preserved i j P hz)

theorem jetSupport_externalDerivative_subset (w : List (Jet G)) (P : JetAlgebra G) :
    jetSupport (externalJetDerivative w P) ⊆ jetSupport P := by
  induction w generalizing P with
  | nil => exact fun _ h => h
  | cons j js ih =>
      exact (ih (leftPartialJet j P)).trans (jetSupport_partial_subset j P)

theorem externalDerivative_zero_of_outside (w : List (Jet G)) (P : JetAlgebra G)
    (j : Jet G) (hj : j ∈ w) (hout : j ∉ jetSupport P) :
    externalJetDerivative w P = 0 := by
  induction w generalizing P with
  | nil => simp at hj
  | cons k ks ih =>
      rcases List.mem_cons.mp hj with he | htail
      · subst k
        have hz : leftPartialJet j P = 0 := by simpa using hout
        simp [externalJetDerivative, hz]
      · have hn : j ∉ jetSupport (leftPartialJet k P) :=
          fun hm => hout (jetSupport_partial_subset k P hm)
        simpa [externalJetDerivative] using ih (leftPartialJet k P) htail hn

open YangMills.PerturbativeFlow YangMills.Perturbative

def amplitudeTerm (P : JetAlgebra G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (a : Fin legs.length → Jet G) : ℂ :=
  if ∀ i, (a i).field = legs.get i then
    augmentation (externalJetDerivative (List.ofFn a) P) *
      ∏ i : Fin legs.length, jetMomentumPhase (a i) (q i)
  else 0

def amplitudeOn (S : Finset (Jet G)) (P : JetAlgebra G) : OrderedAmplitude G :=
  fun legs q => ∑ a : Fin legs.length → {j : Jet G // j ∈ S},
    amplitudeTerm P legs q (fun i => (a i).val)

theorem densityAmplitude_eq_amplitudeOn (P : JetAlgebra G) :
    densityAmplitude P = amplitudeOn (jetSupport P) P := rfl

theorem amplitudeTerm_zero_of_outside (P : JetAlgebra G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (a : Fin legs.length → Jet G)
    (i : Fin legs.length) (hi : a i ∉ jetSupport P) :
    amplitudeTerm P legs q a = 0 := by
  have hz := externalDerivative_zero_of_outside (List.ofFn a) P (a i)
    (List.mem_ofFn.mpr ⟨i, rfl⟩) hi
  simp [amplitudeTerm, hz]

theorem amplitudeOn_mono (S T : Finset (Jet G)) (hST : S ⊆ T)
    (P : JetAlgebra G) (hP : jetSupport P ⊆ S) :
    amplitudeOn S P = amplitudeOn T P := by
  classical
  funext legs q
  let e : (Fin legs.length → {j : Jet G // j ∈ S}) →
      (Fin legs.length → {j : Jet G // j ∈ T}) :=
    fun a i => ⟨(a i).val, hST (a i).property⟩
  have he : Function.Injective e := by
    intro a b hab
    funext i
    exact Subtype.ext (congrArg (fun f => (f i).val) hab)
  apply Fintype.sum_of_injective e he
  · intro a hnot
    have hex : ∃ i, (a i).val ∉ S := by
      by_contra hn
      push Not at hn
      apply hnot
      exact ⟨fun i => ⟨(a i).val, hn i⟩, by funext i; rfl⟩
    obtain ⟨i, hi⟩ := hex
    exact amplitudeTerm_zero_of_outside P legs q _ i (fun hm => hi (hP hm))
  · intro a
    rfl

theorem amplitudeOn_add (S : Finset (Jet G)) (P Q : JetAlgebra G) :
    amplitudeOn S (P + Q) = amplitudeOn S P + amplitudeOn S Q := by
  classical
  funext legs q
  simp only [amplitudeOn, amplitudeTerm, map_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  split <;> simp [add_mul]

theorem jetSupport_add_subset (P Q : JetAlgebra G) :
    jetSupport (P + Q) ⊆ jetSupport P ∪ jetSupport Q := by
  classical
  intro j hj
  by_contra hn
  have hn' := Finset.notMem_union.mp hn
  have hp : leftPartialJet j P = 0 := by simpa using hn'.1
  have hq : leftPartialJet j Q = 0 := by simpa using hn'.2
  rw [mem_jetSupport] at hj
  exact hj (by simp [hp, hq])

theorem densityAmplitude_add (P Q : JetAlgebra G) :
    densityAmplitude (P + Q) = densityAmplitude P + densityAmplitude Q := by
  classical
  let S := jetSupport P ∪ jetSupport Q
  have hPQ : amplitudeOn (jetSupport (P + Q)) (P + Q) = amplitudeOn S (P + Q) :=
    amplitudeOn_mono _ _ (jetSupport_add_subset P Q) _ (fun _ h => h)
  have hP : amplitudeOn (jetSupport P) P = amplitudeOn S P :=
    amplitudeOn_mono _ _ Finset.subset_union_left _ (fun _ h => h)
  have hQ : amplitudeOn (jetSupport Q) Q = amplitudeOn S Q :=
    amplitudeOn_mono _ _ Finset.subset_union_right _ (fun _ h => h)
  rw [densityAmplitude_eq_amplitudeOn, hPQ, amplitudeOn_add, ← hP, ← hQ]
  rfl

theorem amplitudeOn_smul (S : Finset (Jet G)) (r : ℂ) (P : JetAlgebra G) :
    amplitudeOn S (r • P) = r • amplitudeOn S P := by
  classical
  funext legs q
  simp only [amplitudeOn, amplitudeTerm, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split <;> simp [mul_assoc]

theorem jetSupport_smul_subset (r : ℂ) (P : JetAlgebra G) :
    jetSupport (r • P) ⊆ jetSupport P := by
  intro j hj
  by_contra hn
  have hp : leftPartialJet j P = 0 := by simpa using hn
  rw [mem_jetSupport] at hj
  exact hj (by simp [hp])

theorem densityAmplitude_smul (r : ℂ) (P : JetAlgebra G) :
    densityAmplitude (r • P) = r • densityAmplitude P := by
  rw [densityAmplitude_eq_amplitudeOn,
    amplitudeOn_mono _ _ (jetSupport_smul_subset r P) _ (fun _ h => h),
    amplitudeOn_smul]
  rfl

def densityAmplitudeLinear : JetAlgebra G →ₗ[ℂ] OrderedAmplitude G where
  toFun := densityAmplitude
  map_add' := densityAmplitude_add
  map_smul' := densityAmplitude_smul

def momentumDerivative (K : ExternalLeg G) (p : Spacetime) (P : JetAlgebra G) :
    JetAlgebra G :=
  ∑ j ∈ jetSupport P,
    if j.field = K then jetMomentumPhase j p • leftPartialJet j P else 0

theorem momentumDerivative_jet (K : ExternalLeg G) (p : Spacetime) (j : Jet G) :
    momentumDerivative K p (jet j) =
      if j.field = K then jetMomentumPhase j p • (1 : JetAlgebra G) else 0 := by
  classical
  simp [momentumDerivative, leftPartialJet_jet]

theorem amplitudeOn_partial (S : Finset (Jet G)) (P : JetAlgebra G)
    (hP : jetSupport P ⊆ S) (j : Jet G) :
    amplitudeOn S (leftPartialJet j P) = densityAmplitude (leftPartialJet j P) := by
  exact (amplitudeOn_mono _ _ ((jetSupport_partial_subset j P).trans hP)
    _ (fun _ h => h)).symm

theorem finite_sum_fin_cons {A : Type*} [Fintype A] (n : ℕ)
    (f : (Fin (n + 1) → A) → ℂ) :
    (∑ a, f a) = ∑ x : A, ∑ tail : Fin n → A, f (Fin.cons x tail) := by
  classical
  calc
    _ = ∑ p : A × (Fin n → A), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm
        _ _ (by intro a; exact congrArg f ((Fin.consEquiv (fun _ : Fin (n + 1) => A)).apply_symm_apply a).symm)
    _ = _ := Fintype.sum_prod_type _

set_option maxHeartbeats 1200000 in
theorem amplitudeTerm_cons (P : JetAlgebra G) (K : ExternalLeg G)
    (legs : List (ExternalLeg G)) (q : Fin (K :: legs).length → Spacetime)
    (j : Jet G) (a : Fin legs.length → Jet G) :
    amplitudeTerm P (K :: legs) q (Fin.cons j a) =
      if j.field = K then jetMomentumPhase j (q ⟨0, by simp⟩) *
        amplitudeTerm (leftPartialJet j P) legs (fun i => q i.succ) a else 0 := by
  classical
  simp only [amplitudeTerm, List.length_cons, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, List.get_cons_zero,
    List.ofFn_succ, externalJetDerivative, LinearMap.comp_apply,
    Fin.prod_univ_succ]
  by_cases h : j.field = K <;> by_cases ht : ∀ i : Fin legs.length, (a i).field = legs.get i
  all_goals simp [h, ht, mul_assoc, mul_comm]

theorem amplitudeOn_cons (S : Finset (Jet G)) (P : JetAlgebra G) (K : ExternalLeg G)
    (legs : List (ExternalLeg G)) (q : Fin (K :: legs).length → Spacetime) :
    amplitudeOn S P (K :: legs) q =
      ∑ j : {j : Jet G // j ∈ S},
        if j.val.field = K then jetMomentumPhase j.val (q ⟨0, by simp⟩) *
          amplitudeOn S (leftPartialJet j.val P) legs (fun i => q i.succ) else 0 := by
  classical
  unfold amplitudeOn
  change (∑ a : Fin (legs.length + 1) → {j : Jet G // j ∈ S},
    amplitudeTerm P (K :: legs) q (fun i => (a i).val)) = _
  rw [finite_sum_fin_cons legs.length]
  apply Finset.sum_congr rfl
  intro j hj
  have heq (a : Fin legs.length → {j : Jet G // j ∈ S}) :
      (fun i => ((Fin.cons j a : Fin (legs.length + 1) → {j : Jet G // j ∈ S}) i).val) =
        (Fin.cons j.val (fun i => (a i).val) : Fin (legs.length + 1) → Jet G) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  have hterms : (∑ tail : Fin legs.length → {j : Jet G // j ∈ S},
      amplitudeTerm P (K :: legs) q (fun i => ((Fin.cons j tail : Fin (legs.length + 1) → {j : Jet G // j ∈ S}) i).val)) =
      ∑ tail : Fin legs.length → {j : Jet G // j ∈ S},
        if j.val.field = K then jetMomentumPhase j.val (q ⟨0, by simp⟩) *
          amplitudeTerm (leftPartialJet j.val P) legs (fun i => q i.succ)
            (fun i => (tail i).val) else 0 := by
    apply Finset.sum_congr rfl
    intro tail htail
    exact (congrArg (amplitudeTerm P (K :: legs) q) (heq tail)).trans
      (amplitudeTerm_cons P K legs q j.val _)
  rw [hterms]
  by_cases h : j.val.field = K
  · simp only [h, if_true]
    rw [Finset.mul_sum]
  · simp [h]

theorem densityAmplitude_cons (P : JetAlgebra G) (K : ExternalLeg G)
    (legs : List (ExternalLeg G)) (q : Fin (K :: legs).length → Spacetime) :
    densityAmplitude P (K :: legs) q =
      ∑ j : {j : Jet G // j ∈ jetSupport P},
        if j.val.field = K then jetMomentumPhase j.val (q ⟨0, by simp⟩) *
          densityAmplitude (leftPartialJet j.val P) legs (fun i => q i.succ) else 0 := by
  rw [densityAmplitude_eq_amplitudeOn, amplitudeOn_cons]
  apply Finset.sum_congr rfl
  intro j hj
  rw [amplitudeOn_partial _ _ (fun _ h => h)]

theorem densityAmplitude_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G) :
    densityAmplitude (∑ i ∈ s, P i) = ∑ i ∈ s, densityAmplitude (P i) :=
  map_sum densityAmplitudeLinear P s

theorem densityAmplitude_cons_derivative (P : JetAlgebra G) (K : ExternalLeg G)
    (legs : List (ExternalLeg G)) (q : Fin (K :: legs).length → Spacetime) :
    densityAmplitude P (K :: legs) q =
      densityAmplitude (momentumDerivative K (q ⟨0, by simp⟩) P)
        legs (fun i => q i.succ) := by
  classical
  rw [densityAmplitude_cons]
  simp [momentumDerivative, densityAmplitude_sum, densityAmplitude_smul, apply_ite,
    ite_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_attach (jetSupport P) (fun j : Jet G =>
    if j.field = K then jetMomentumPhase j (q ⟨0, by simp⟩) *
      densityAmplitude (leftPartialJet j P) legs (fun i => q i.succ) else (0 : ℂ))

theorem momentumDerivative_eq_sum (K : ExternalLeg G) (p : Spacetime)
    (P : JetAlgebra G) (S : Finset (Jet G)) (hP : jetSupport P ⊆ S) :
    momentumDerivative K p P =
      ∑ j ∈ S, if j.field = K then jetMomentumPhase j p • leftPartialJet j P else 0 := by
  classical
  apply Finset.sum_subset hP
  intro j hj hn
  have hz : leftPartialJet j P = 0 := by simpa using hn
  simp [hz]

theorem leftPartialJet_mul (j : Jet G) (P Q : JetAlgebra G) :
    leftPartialJet j (P * Q) = leftPartialJet j P * Q +
      (if j.field.parity then parity P else P) * leftPartialJet j Q := by
  by_cases h : j.field.parity = true
  · simpa [leftPartialJet, h] using oddPartial_mul ⟨j, h⟩ P Q
  · simpa [leftPartialJet, h] using
      evenPartial_mul ⟨j, by cases hp : j.field.parity <;> simp_all⟩ P Q

theorem jetSupport_mul_subset (P Q : JetAlgebra G) :
    jetSupport (P * Q) ⊆ jetSupport P ∪ jetSupport Q := by
  classical
  intro j hj
  by_contra hn
  have hn' := Finset.notMem_union.mp hn
  have hp : leftPartialJet j P = 0 := by simpa using hn'.1
  have hq : leftPartialJet j Q = 0 := by simpa using hn'.2
  rw [mem_jetSupport] at hj
  exact hj (by simp [leftPartialJet_mul, hp, hq])

theorem momentumDerivative_mul (K : ExternalLeg G) (p : Spacetime)
    (P Q : JetAlgebra G) :
    momentumDerivative K p (P * Q) = momentumDerivative K p P * Q +
      (if K.parity then parity P else P) * momentumDerivative K p Q := by
  classical
  let S := jetSupport P ∪ jetSupport Q
  rw [momentumDerivative_eq_sum K p (P * Q) S (jetSupport_mul_subset P Q),
    momentumDerivative_eq_sum K p P S Finset.subset_union_left,
    momentumDerivative_eq_sum K p Q S Finset.subset_union_right]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j.field = K
  · simp [h, leftPartialJet_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  · simp [h]

theorem parity_jet (j : Jet G) :
    parity (jet j) = if j.field.parity then -jet j else jet j := by
  by_cases h : j.field.parity = true
  · simp [jet, h, parity, oddJet, CliffordAlgebra.involute_ι,
      TensorProduct.tmul_neg]
  · simp [jet, h, parity, evenJet]

theorem augmentation_one : augmentation (1 : JetAlgebra G) = 1 := by
  simp [augmentation, Algebra.TensorProduct.one_def]

theorem augmentation_mul (P Q : JetAlgebra G) :
    augmentation (P * Q) = augmentation P * augmentation Q := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P R hP hR => simp only [add_mul, map_add, hP, hR]
  | tmul p u =>
      induction Q using TensorProduct.induction_on with
      | zero => simp
      | add Q R hQ hR => simp only [mul_add, map_add, hQ, hR]
      | tmul q v =>
          simp only [augmentation, Algebra.TensorProduct.tmul_mul_tmul,
            TensorProduct.lift.tmul, LinearMap.mk₂_apply, map_mul]
          ring

theorem augmentation_jet (j : Jet G) : augmentation (jet j) = 0 := by
  by_cases h : j.field.parity = true
  · simp [jet, h, augmentation, oddJet, oddAugmentation]
  · simp [jet, h, augmentation, evenJet]

theorem augmentation_monomial (source : List (LocalVertexLeg G)) :
    augmentation (monomial source) = if source.length = 0 then 1 else 0 := by
  cases source with
  | nil => simpa [monomial] using augmentation_one (G := G)
  | cons k source => simp [monomial, augmentation_mul, augmentation_jet]

theorem densityAmplitude_nil (P : JetAlgebra G) (q : Fin 0 → Spacetime) :
    densityAmplitude P [] q = augmentation P := by
  classical
  simp [densityAmplitude, externalJetDerivative]

def vertexJet (k : LocalVertexLeg G) : Jet G :=
  ⟨k.field, fun mu => k.derivatives.count mu⟩

theorem vertexJet_phase (k : LocalVertexLeg G) (p : Spacetime) :
    jetMomentumPhase (vertexJet k) p =
      (k.derivatives.map (fun mu => -Complex.I * (p mu : ℂ))).prod := by
  unfold jetMomentumPhase vertexJet
  dsimp
  induction k.derivatives with
  | nil => simp
  | cons a ds ih =>
      simp only [List.count_cons, pow_add, Finset.prod_mul_distrib]
      simp only [neg_mul] at ih ⊢
      simp [ih, mul_comm]

theorem monomial_cons (k : LocalVertexLeg G) (source : List (LocalVertexLeg G)) :
    monomial (k :: source) = jet (vertexJet k) * monomial source := rfl

def crossingSign (K : ExternalLeg G) (k : LocalVertexLeg G) : ℂ :=
  if K.parity = true ∧ k.field.parity = true then -1 else 1

def wordMomentumDerivative (K : ExternalLeg G) (p : Spacetime) :
    List (LocalVertexLeg G) → JetAlgebra G
  | [] => 0
  | k :: source =>
      (if k.field = K then jetMomentumPhase (vertexJet k) p • monomial source else 0) +
      crossingSign K k • (jet (vertexJet k) * wordMomentumDerivative K p source)

theorem leftPartialJet_one (j : Jet G) : leftPartialJet j (1 : JetAlgebra G) = 0 := by
  by_cases h : j.field.parity = true
  · simp [leftPartialJet, h, oddPartial, Algebra.TensorProduct.one_def]
  · simp [leftPartialJet, h, evenPartial, Algebra.TensorProduct.one_def]

theorem momentumDerivative_one (K : ExternalLeg G) (p : Spacetime) :
    momentumDerivative K p (1 : JetAlgebra G) = 0 := by
  classical
  simp [momentumDerivative, leftPartialJet_one]

theorem momentumDerivative_monomial (K : ExternalLeg G) (p : Spacetime)
    (source : List (LocalVertexLeg G)) :
    momentumDerivative K p (monomial source) = wordMomentumDerivative K p source := by
  classical
  induction source with
  | nil =>
      simpa [monomial, wordMomentumDerivative] using momentumDerivative_one K p
  | cons k source ih =>
      rw [monomial_cons, momentumDerivative_mul, momentumDerivative_jet, ih]
      by_cases hK : K.parity = true <;> by_cases hk : k.field.parity = true
      all_goals
        simp [wordMomentumDerivative, crossingSign, hK, hk, vertexJet,
          parity_jet, ite_mul, smul_mul_assoc]
      all_goals
        change -(jet (vertexJet k)) * wordMomentumDerivative K p source =
          (-1 : ℂ) • (jet (vertexJet k) * wordMomentumDerivative K p source)
        calc
          _ = -(jet (vertexJet k) * wordMomentumDerivative K p source) :=
            neg_mul (jet (vertexJet k)) (wordMomentumDerivative K p source)
          _ = _ := (neg_one_smul ℂ
            (jet (vertexJet k) * wordMomentumDerivative K p source)).symm

def prefixSign (K : ExternalLeg G) (source : List (LocalVertexLeg G)) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (if K.parity then ((source.take n).filter (fun k => k.field.parity)).length else 0)

theorem prefixSign_zero (K : ExternalLeg G) (source : List (LocalVertexLeg G)) :
    prefixSign K source 0 = 1 := by simp [prefixSign]

theorem prefixSign_cons_succ (K : ExternalLeg G) (k : LocalVertexLeg G)
    (source : List (LocalVertexLeg G)) (n : ℕ) :
    prefixSign K (k :: source) (n + 1) = crossingSign K k * prefixSign K source n := by
  by_cases hK : K.parity = true <;> by_cases hk : k.field.parity = true
  all_goals simp [prefixSign, crossingSign, hK, hk, List.take_succ_cons, pow_succ]

def positionalWordDerivative (K : ExternalLeg G) (p : Spacetime)
    (source : List (LocalVertexLeg G)) : JetAlgebra G :=
  ∑ i : Fin source.length,
    if (source.get i).field = K then
      (prefixSign K source i.val * jetMomentumPhase (vertexJet (source.get i)) p) •
        monomial (source.take i.val ++ source.drop (i.val + 1))
    else 0

theorem wordMomentumDerivative_positional (K : ExternalLeg G) (p : Spacetime)
    (source : List (LocalVertexLeg G)) :
    wordMomentumDerivative K p source = positionalWordDerivative K p source := by
  classical
  induction source with
  | nil => simp [wordMomentumDerivative, positionalWordDerivative]
  | cons k source ih =>
      rw [wordMomentumDerivative, ih]
      unfold positionalWordDerivative
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, Fin.val_zero, prefixSign_zero, one_mul,
        List.take_zero, List.nil_append]
      congr 1
      rw [Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Fin.val_succ, prefixSign_cons_succ,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append, monomial_cons]
      by_cases h : source[i.val].field = K
      · simp [h, mul_smul_comm, smul_smul, mul_assoc]
      · simp [h]

set_option maxHeartbeats 1200000 in
theorem densityAmplitude_monomial (source : List (LocalVertexLeg G))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    densityAmplitude (monomial source) legs q =
      localMonomialDerivative source (List.ofFn (fun i => (legs.get i, q i))) := by
  classical
  induction legs generalizing source with
  | nil =>
      rw [densityAmplitude_nil, augmentation_monomial]
      cases source <;> simp [localMonomialDerivative]
  | cons K legs ih =>
      rw [densityAmplitude_cons_derivative, momentumDerivative_monomial,
        wordMomentumDerivative_positional]
      unfold positionalWordDerivative
      rw [densityAmplitude_sum]
      simp only [List.length_cons, List.ofFn_succ, List.get_cons_zero,
        localMonomialDerivative]
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [List.get_eq_getElem]
      by_cases h : source[i.val].field = K
      · simp only [h, if_true, densityAmplitude_smul, Pi.smul_apply, smul_eq_mul]
        rw [ih, vertexJet_phase]
        rfl
      · simp [h]

theorem densityAmplitude_vertex (v : LocalVertex G) (g : ℝ) :
    densityAmplitude (densityOfVertex g v) = localVertexAmplitude v g := by
  funext legs q
  rw [densityOfVertex, densityAmplitude_smul]
  change (v.coefficient * (g : ℂ) ^ v.couplingOrder) *
    densityAmplitude (monomial v.legs) legs q = _
  rw [densityAmplitude_monomial]
  rfl

theorem densityAmplitude_vertices (vertices : List (LocalVertex G)) (g : ℝ) :
    densityAmplitude (densityOfVertices g vertices) = localPolynomialAmplitude vertices g := by
  induction vertices with
  | nil =>
      funext legs q
      simp [densityOfVertices, localPolynomialAmplitude]
  | cons v vs ih =>
      rw [densityOfVertices, List.map_cons, List.sum_cons, densityAmplitude_add,
        densityAmplitude_vertex]
      change localVertexAmplitude v g + densityAmplitude (densityOfVertices g vs) = _
      rw [ih]
      rfl


theorem densityAmplitude_freeAction (G : CompactSimpleGaugeGroup) :
    densityAmplitude (freeActionDensity G) = freeVertexAmplitude G :=
  densityAmplitude_vertices _ _

theorem densityAmplitude_interaction {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityAmplitude (interactionDensity e g) = treeVertexAmplitude e g :=
  densityAmplitude_vertices _ _

theorem densityAmplitude_masterAction {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityAmplitude (masterActionDensity e g) =
      freeVertexAmplitude G + treeVertexAmplitude e g := by
  rw [masterActionDensity, densityAmplitude_add,
    densityAmplitude_freeAction, densityAmplitude_interaction]

theorem localST_add (S P Q : JetAlgebra G) :
    localST S (P + Q) = localST S P + localST S Q :=
  coordinateDifferential_add _ _ _ _

theorem localST_smul (S P : JetAlgebra G) (r : ℂ) :
    localST S (r • P) = r • localST S P :=
  coordinateDifferential_smul _ _ _ _

theorem localST_jet (S : JetAlgebra G) (j : Jet G) :
    localST S (jet j) =
      totalDerivatives j.derivative (stCharacteristic S j.field) := by
  by_cases h : j.field.parity = true
  · simpa [jet, h] using localST_oddJet S ⟨j, h⟩
  · simpa [jet, h] using localST_evenJet S
      ⟨j, by cases hp : j.field.parity <;> simp_all⟩

end YangMills.FullBV
