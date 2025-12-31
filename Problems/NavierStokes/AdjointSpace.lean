-- code adapted from SciLean.Analysis.AdjointSpace
-- we give full credit to the authors of SciLean
import Problems.NavierStokes.Imports

open ComplexConjugate RCLike
/--
This is almost `InnerProductSpace` but we do not require that norm originates from the inner product.

The reason for this class it to be able to have inner product on spaces line `ℝ×ℝ` and `ι → ℝ`
as they are by default equiped by max norm which is not compatible with inner product. -/
class AdjointSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] extends
  NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- Norm induced by inner is topologicaly equivalent to the given norm -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    c > 0 ∧ d > 0 ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (inner x x)) ∧ (re (inner x x) ≤ d • ‖x‖^2)
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

attribute [instance low] AdjointSpace.toNormedSpace AdjointSpace.toInner

/-! ### Properties of inner product spaces -/

namespace AdjointSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [AdjointSpace 𝕜 E]
variable [NormedAddCommGroup F] [AdjointSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y
local notation "‖" x "‖₂²" => @inner 𝕜 E _ x x

local notation "IK" => @RCLike.I 𝕜 _

local postfix:90 "†" => starRingEnd _

  -- `InnerProductSpace.norm_sq_eq_inner` was removed/renamed in recent mathlib versions.

open RCLike ComplexConjugate InnerProductSpace

section BasicProperties

@[simp mid+1]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ := by rw[conj_symm]

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw[← conj_symm]; simp only [conj_trivial]

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

@[simp mid+1]
theorem inner_self_im (x : E) : RCLike.im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]; simp

theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by rw[add_left]

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]
  simp only [inner_conj_symm]

theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ := by rw [smul_left]

theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _

theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_ofReal, Algebra.smul_def]

theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_symm]

theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _

theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]

/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps!]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _


/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum (sesqFormOfInner (𝕜 := 𝕜) (E := E) x) _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (LinearMap.flip sesqFormOfInner x) _ _

@[simp mid+1]
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]

theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]

@[simp mid+1]
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, RingHom.map_zero]

theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ := by
  have ⟨c,d,hc,_,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
  have ⟨h'',_⟩ := h x
  apply le_trans _ h''
  positivity

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x

@[simp mid+1]
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im _)

@[simp mid+1]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  constructor
  · have ⟨c,d,hc,_,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have ⟨h,_⟩ := h x
    intro h'; simp[h'] at h
    have : ‖x‖^2 ≤ 0 := by nlinarith
    have : ‖x‖ ≤ 0 := by nlinarith
    simp_all only [gt_iff_lt, smul_eq_mul, norm_le_zero_iff]
  · simp_all only [inner_zero_right, map_zero, le_refl, implies_true]

theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
  @inner_self_nonpos ℝ F _ _ _ x

@[simp mid+1]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (inner_self_nonpos (𝕜:=𝕜)).1
    simp only [h, map_zero, le_refl]
  · simp_all only [inner_zero_right, implies_true]

theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]


@[simp mid+1]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

@[simp mid+1]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

-- Porting note: removed `simp` because it can prove it using `inner_conj_symm`
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

variable (𝕜)

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_right, sub_eq_zero, h (x - y)]

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero, h (x - y)]




/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp mid+1]
theorem innerₛₗ_apply_coe (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/-- The inner product as a bilinear map in the real case. -/
noncomputable
def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ

@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w



----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
variable
  {X} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace 𝕜 (E i)]

instance : AdjointSpace 𝕜 𝕜 where
  inner_top_equiv_norm := by
    apply Exists.intro 1
    apply Exists.intro 1
    simp [norm_sq_eq_def]
  conj_symm := by simp[mul_comm]
  add_left := by
    intro x y z
    simp [mul_add, add_mul, mul_assoc]
  smul_left := by
    intro x y r
    simp [mul_assoc, mul_left_comm, mul_comm]

instance : Inner 𝕜 Unit where
  inner _ _ := 0

instance : AdjointSpace 𝕜 Unit where
  inner_top_equiv_norm := by
    apply Exists.intro 1
    apply Exists.intro 1
    simp[Inner.inner]
  conj_symm := by simp[Inner.inner]
  add_left := by simp[Inner.inner]
  smul_left := by simp[Inner.inner]

instance : AdjointSpace 𝕜 (X×Y) where
  inner := fun (x,y) (x',y') => ⟪x,x'⟫_𝕜 + ⟪y,y'⟫_𝕜
  inner_top_equiv_norm := by
    have ⟨cx, dx, hcx, hdx, hx⟩ := inner_top_equiv_norm (𝕜 := 𝕜) (E := X)
    have ⟨cy, dy, hcy, hdy, hy⟩ := inner_top_equiv_norm (𝕜 := 𝕜) (E := Y)
    refine ⟨min cx cy, dx + dy, lt_min hcx hcy, add_pos hdx hdy, ?_⟩
    rintro ⟨x, y⟩
    have hx' := hx x
    have hy' := hy y
    have hx_low : cx * ‖x‖ ^ 2 ≤ re ⟪x, x⟫_𝕜 := by
      simpa [smul_eq_mul] using hx'.1
    have hx_up : re ⟪x, x⟫_𝕜 ≤ dx * ‖x‖ ^ 2 := by
      simpa [smul_eq_mul] using hx'.2
    have hy_low : cy * ‖y‖ ^ 2 ≤ re ⟪y, y⟫_𝕜 := by
      simpa [smul_eq_mul] using hy'.1
    have hy_up : re ⟪y, y⟫_𝕜 ≤ dy * ‖y‖ ^ 2 := by
      simpa [smul_eq_mul] using hy'.2
    constructor
    · -- lower bound
      have hx_nonneg : 0 ≤ re ⟪x, x⟫_𝕜 := by
        have hx_sq : 0 ≤ (‖x‖ ^ 2 : ℝ) := by
          simpa [pow_two] using mul_nonneg (norm_nonneg x) (norm_nonneg x)
        have : 0 ≤ cx * ‖x‖ ^ 2 := mul_nonneg (le_of_lt hcx) hx_sq
        exact le_trans this hx_low
      have hy_nonneg : 0 ≤ re ⟪y, y⟫_𝕜 := by
        have hy_sq : 0 ≤ (‖y‖ ^ 2 : ℝ) := by
          simpa [pow_two] using mul_nonneg (norm_nonneg y) (norm_nonneg y)
        have : 0 ≤ cy * ‖y‖ ^ 2 := mul_nonneg (le_of_lt hcy) hy_sq
        exact le_trans this hy_low
      -- Split on which component attains the max norm on the product.
      by_cases hxy : ‖x‖ ≤ ‖y‖
      · have hnorm : ‖(x, y)‖ = ‖y‖ := by
          simpa [Prod.norm_mk, max_eq_right hxy]
        have hmin_le : min cx cy ≤ cy := min_le_right _ _
        have hmul : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ cy * ‖y‖ ^ 2 := by
          have hy_sq : 0 ≤ (‖y‖ ^ 2 : ℝ) := by
            simpa [pow_two] using mul_nonneg (norm_nonneg y) (norm_nonneg y)
          simpa [hnorm] using mul_le_mul_of_nonneg_right hmin_le hy_sq
        have hle : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ re ⟪y, y⟫_𝕜 := le_trans hmul hy_low
        have hle' : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ re ⟪x, x⟫_𝕜 + re ⟪y, y⟫_𝕜 :=
          le_trans hle (le_add_of_nonneg_left hx_nonneg)
        simpa [inner, map_add, hnorm] using hle'
      · have hyx : ‖y‖ ≤ ‖x‖ := le_of_not_ge hxy
        have hnorm : ‖(x, y)‖ = ‖x‖ := by
          simpa [Prod.norm_mk, max_eq_left hyx]
        have hmin_le : min cx cy ≤ cx := min_le_left _ _
        have hmul : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ cx * ‖x‖ ^ 2 := by
          have hx_sq : 0 ≤ (‖x‖ ^ 2 : ℝ) := by
            simpa [pow_two] using mul_nonneg (norm_nonneg x) (norm_nonneg x)
          simpa [hnorm] using mul_le_mul_of_nonneg_right hmin_le hx_sq
        have hle : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ re ⟪x, x⟫_𝕜 := le_trans hmul hx_low
        have hle' : (min cx cy) * ‖(x, y)‖ ^ 2 ≤ re ⟪x, x⟫_𝕜 + re ⟪y, y⟫_𝕜 :=
          le_trans hle (le_add_of_nonneg_right hy_nonneg)
        simpa [inner, map_add, hnorm] using hle'
    · -- upper bound
      have hnorm_x : ‖x‖ ≤ ‖(x, y)‖ := by
        simpa [Prod.norm_mk] using le_max_left ‖x‖ ‖y‖
      have hnorm_y : ‖y‖ ≤ ‖(x, y)‖ := by
        simpa [Prod.norm_mk] using le_max_right ‖x‖ ‖y‖
      have hx_sq : ‖x‖ ^ 2 ≤ ‖(x, y)‖ ^ 2 := by
        simpa [pow_two] using
          mul_le_mul hnorm_x hnorm_x (norm_nonneg x) (norm_nonneg (x, y))
      have hy_sq : ‖y‖ ^ 2 ≤ ‖(x, y)‖ ^ 2 := by
        simpa [pow_two] using
          mul_le_mul hnorm_y hnorm_y (norm_nonneg y) (norm_nonneg (x, y))
      have hx_le : re ⟪x, x⟫_𝕜 ≤ dx * ‖(x, y)‖ ^ 2 :=
        le_trans hx_up (mul_le_mul_of_nonneg_left hx_sq (le_of_lt hdx))
      have hy_le : re ⟪y, y⟫_𝕜 ≤ dy * ‖(x, y)‖ ^ 2 :=
        le_trans hy_up (mul_le_mul_of_nonneg_left hy_sq (le_of_lt hdy))
      have hsum : re ⟪x, x⟫_𝕜 + re ⟪y, y⟫_𝕜 ≤ dx * ‖(x, y)‖ ^ 2 + dy * ‖(x, y)‖ ^ 2 :=
        add_le_add hx_le hy_le
      have : re (⟪x, x⟫_𝕜 + ⟪y, y⟫_𝕜) ≤ (dx + dy) * ‖(x, y)‖ ^ 2 := by
        have hfactor : dx * ‖(x, y)‖ ^ 2 + dy * ‖(x, y)‖ ^ 2 = (dx + dy) * ‖(x, y)‖ ^ 2 := by ring
        exact
          le_trans (by simpa [map_add] using hsum) (le_of_eq hfactor)
      simpa [inner, map_add] using this
  conj_symm := by simp
  add_left := by simp[inner_add_left]; intros; ac_rfl
  smul_left := by simp[inner_smul_left,mul_add]

open Classical in
instance : AdjointSpace 𝕜 ((i : ι) → E i) where
  inner := fun x y => ∑ i, ⟪x i, y i⟫_𝕜
  inner_top_equiv_norm := by
    classical
    -- Choose comparison constants for each component space.
    choose c d hc hd hcd using
      (fun i : ι => (inner_top_equiv_norm (𝕜 := 𝕜) (E := E i)))
    let cset : Finset ℝ := (Finset.univ : Finset ι).image c
    by_cases hne : cset.Nonempty
    · -- Nonempty index set.
      let c0 : ℝ := cset.min' hne
      let d0 : ℝ := ∑ i : ι, d i
      refine ⟨c0, d0, ?_, ?_, ?_⟩
      · -- `c0 > 0`
        have hc0mem : c0 ∈ cset := Finset.min'_mem cset hne
        rcases Finset.mem_image.1 hc0mem with ⟨i, _hi, hiEq⟩
        simpa [hiEq] using hc i
      · -- `d0 > 0`
        -- Extract an index from `cset.Nonempty`, hence from `ι`, and use positivity of one summand.
        rcases hne with ⟨v, hv⟩
        rcases Finset.mem_image.1 hv with ⟨i0, _hi0, rfl⟩
        have hdi0 : 0 < d i0 := hd i0
        have hle : d i0 ≤ ∑ i : ι, d i := by
          refine Finset.single_le_sum (s := Finset.univ) (f := fun i : ι => d i) ?_ (Finset.mem_univ i0)
          intro i _hi
          exact le_of_lt (hd i)
        exact lt_of_lt_of_le hdi0 hle
      · intro x
        constructor
        · -- lower bound
          have hc0_pos : 0 < c0 := by
            have hc0mem : c0 ∈ cset := Finset.min'_mem cset hne
            rcases Finset.mem_image.1 hc0mem with ⟨i, _hi, hiEq⟩
            simpa [hiEq] using hc i
          have hc0_nonneg : 0 ≤ c0 := le_of_lt hc0_pos
          -- `c0 ≤ c i` for all `i` (since `c0` is the minimum of the image).
          have hc0_le : ∀ i : ι, c0 ≤ c i := by
            intro i
            have hleast : IsLeast (↑cset : Set ℝ) c0 := Finset.isLeast_min' cset hne
            have hi : c i ∈ cset := Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
            exact hleast.2 (by simpa using hi)
          -- `‖x‖^2 ≤ ∑ i, ‖x i‖^2` (a maximum coordinate exists in the finite sup norm).
          have hnorm_sq : ‖x‖ ^ 2 ≤ ∑ i : ι, ‖x i‖ ^ 2 := by
            by_cases hx0 : ‖x‖ = 0
            ·
              have hnonneg : 0 ≤ ∑ i : ι, ‖x i‖ ^ 2 := by
                refine Finset.sum_nonneg ?_
                intro i _hi
                simpa [pow_two] using mul_nonneg (norm_nonneg (x i)) (norm_nonneg (x i))
              simpa [hx0] using hnonneg
            · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
              have hnot : ¬ (∀ i : ι, ‖x i‖ < ‖x‖) := by
                intro hall
                have : ‖x‖ < ‖x‖ := (pi_norm_lt_iff (x := x) (r := ‖x‖) hxpos).2 hall
                exact lt_irrefl _ this
              rcases not_forall.1 hnot with ⟨i0, hi0⟩
              have hi0' : ‖x‖ ≤ ‖x i0‖ := le_of_not_gt hi0
              have hi0'' : ‖x i0‖ ≤ ‖x‖ := norm_le_pi_norm (f := x) i0
              have hEq : ‖x i0‖ = ‖x‖ := le_antisymm hi0'' hi0'
              have hterm : ‖x‖ ^ 2 ≤ ∑ i : ι, ‖x i‖ ^ 2 := by
                -- `‖x‖^2 = ‖x i0‖^2` and the sum contains that term.
                have hnonneg : ∀ i : ι, 0 ≤ (‖x i‖ ^ 2 : ℝ) := by
                  intro i
                  simpa [pow_two] using mul_nonneg (norm_nonneg (x i)) (norm_nonneg (x i))
                have hle' : ‖x i0‖ ^ 2 ≤ ∑ i : ι, ‖x i‖ ^ 2 :=
                  Finset.single_le_sum (s := Finset.univ) (f := fun i : ι => ‖x i‖ ^ 2)
                    (fun i _hi => hnonneg i) (Finset.mem_univ i0)
                simpa [hEq] using hle'
              exact hterm
          -- Lift componentwise inequalities and sum.
          have hsum :
              c0 * (∑ i : ι, ‖x i‖ ^ 2) ≤ ∑ i : ι, re ⟪x i, x i⟫_𝕜 := by
            -- Compare each coordinate using `c0 ≤ c i`.
            have hcoord :
                ∀ i : ι, c0 * ‖x i‖ ^ 2 ≤ re ⟪x i, x i⟫_𝕜 := by
              intro i
              have hx_sq_nonneg : 0 ≤ (‖x i‖ ^ 2 : ℝ) := by
                simpa [pow_two] using mul_nonneg (norm_nonneg (x i)) (norm_nonneg (x i))
              have hmul : c0 * ‖x i‖ ^ 2 ≤ c i * ‖x i‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (hc0_le i) hx_sq_nonneg
              have hci_low : c i * ‖x i‖ ^ 2 ≤ re ⟪x i, x i⟫_𝕜 := by
                simpa [smul_eq_mul] using (hcd i (x i)).1
              exact le_trans hmul hci_low
            -- Sum the inequalities.
            simpa [Finset.mul_sum] using (Finset.sum_le_sum fun i _hi => hcoord i)
          -- Combine `‖x‖^2 ≤ ∑ ‖x i‖^2` with the summed inequalities.
          have hmain :
              c0 * ‖x‖ ^ 2 ≤ ∑ i : ι, re ⟪x i, x i⟫_𝕜 :=
            le_trans (mul_le_mul_of_nonneg_left hnorm_sq hc0_nonneg) hsum
          -- Rewrite `re (inner x x)` as a sum of real parts.
          have hre :
              re (∑ i : ι, ⟪x i, x i⟫_𝕜) = ∑ i : ι, re ⟪x i, x i⟫_𝕜 := by
            simpa using (map_sum (RCLike.re : 𝕜 →+ ℝ) (fun i : ι => ⟪x i, x i⟫_𝕜) Finset.univ)
          simpa [inner, smul_eq_mul, hre] using hmain
        · -- upper bound
          -- Bound each coordinate by `‖x‖` and sum.
          have hx_sq_le : ∀ i : ι, ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
            intro i
            have hni : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm (f := x) i
            simpa [pow_two] using
              mul_le_mul hni hni (norm_nonneg (x i)) (norm_nonneg x)
          have hcoord :
              ∀ i : ι, re ⟪x i, x i⟫_𝕜 ≤ d i * ‖x‖ ^ 2 := by
            intro i
            have hdi_up : re ⟪x i, x i⟫_𝕜 ≤ d i * ‖x i‖ ^ 2 := by
              simpa [smul_eq_mul] using (hcd i (x i)).2
            have hmul : d i * ‖x i‖ ^ 2 ≤ d i * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_left (hx_sq_le i) (le_of_lt (hd i))
            exact le_trans hdi_up hmul
          have hsum :
              (∑ i : ι, re ⟪x i, x i⟫_𝕜) ≤ (∑ i : ι, d i) * ‖x‖ ^ 2 := by
            -- Sum the bounds and factor out `‖x‖^2`.
            have : (∑ i : ι, re ⟪x i, x i⟫_𝕜) ≤ ∑ i : ι, d i * ‖x‖ ^ 2 :=
              Finset.sum_le_sum fun i _hi => hcoord i
            -- `∑ i, d i * t = (∑ i, d i) * t`.
            simpa [Finset.sum_mul] using this
          have hre :
              re (∑ i : ι, ⟪x i, x i⟫_𝕜) = ∑ i : ι, re ⟪x i, x i⟫_𝕜 := by
            simpa using (map_sum (RCLike.re : 𝕜 →+ ℝ) (fun i : ι => ⟪x i, x i⟫_𝕜) Finset.univ)
          simpa [inner, smul_eq_mul, d0, hre] using hsum
    · -- Empty index set: everything is zero, so any positive constants work.
      refine ⟨1, 1, by positivity, by positivity, ?_⟩
      intro x
      have huniv : (Finset.univ : Finset ι) = ∅ := by
        classical
        by_contra huniv_ne
        have huniv_nonempty : (Finset.univ : Finset ι).Nonempty :=
          Finset.nonempty_iff_ne_empty.2 huniv_ne
        have : cset.Nonempty := by
          simpa [cset] using huniv_nonempty.image c
        exact hne this
      have hnorm : ‖x‖ = 0 := by
        -- For an empty index set, the `L^∞` norm is `0`.
        simpa [Pi.norm_def, huniv]
      constructor <;> simp [inner, smul_eq_mul, huniv, hnorm]
  conj_symm := by simp
  add_left := by simp[inner_add_left,Finset.sum_add_distrib]
  smul_left := by simp[inner_smul_left,Finset.mul_sum]


theorem inner_prod_split (x y : X×Y) : ⟪x,y⟫_𝕜 = ⟪x.1,y.1⟫_𝕜 + ⟪x.2,y.2⟫_𝕜 := by rfl

theorem inner_forall_split (f g : (i : ι) → E i) :
    ⟪f,g⟫_𝕜 = ∑ i, ⟪f i, g i⟫_𝕜 := by rfl
