import YangMills.CompositeExtraction

/-!
# Fixed transverse Taylor projection for pair Ward contact anomalies

This is the local projection of the regulated pair kernel in FHH (340),
(346). For the explicit inverse Fourier phase exp(-i(x-y)p), an ordinary
p^w Taylor monomial transforms to i^|w| times the ordinary derivative of
delta. The phase is therefore explicit (the printed first line of (346)
omits it, despite the displayed Fourier convention and derivative notation).
The kernel argument is the raw momentum kernel, WITHOUT the measure
(2*pi)^(-4); that factor belongs to the inverse Fourier integral only.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

abbrev ContactDerivativeIndex := Fin 4 → ℕ

def ContactDerivativeIndex.order (w : ContactDerivativeIndex) : ℕ := ∑ μ : Fin 4, w μ

def ContactDerivativeIndex.factorial (w : ContactDerivativeIndex) : ℕ :=
  ∏ μ : Fin 4, Nat.factorial (w μ)

/-- Fixed coordinate ordering for the actual iterated Frechet derivative. -/
def ContactDerivativeIndex.directions (w : ContactDerivativeIndex) : List Spacetime :=
  (List.ofFn (fun μ : Fin 4 => μ)).flatMap
    (fun μ => List.replicate (w μ) (Pi.single μ 1))

theorem ContactDerivativeIndex.directions_length (w : ContactDerivativeIndex) :
    w.directions.length = w.order := by
  simp [ContactDerivativeIndex.directions, ContactDerivativeIndex.order, Fin.sum_univ_succ]

/-- Contact channels obey |w|+3≤[A]+[B]. In particular no spurious
zero-order channel is admitted when the dimension sum is smaller than 3. -/
def contactDerivativeIndices (A B : LocalMonomial G) : Finset ContactDerivativeIndex := by
  classical
  exact ((Finset.univ : Finset (Fin 4 → Fin (A.dimension + B.dimension + 1))).image
    (fun f μ => (f μ).val)).filter
    (fun w => w.order + 3 ≤ A.dimension + B.dimension)

/-- Fixed transverse Taylor coefficient in front of ordinary ∂_x^w delta.
No independently chosen local-contact coefficient occurs in this projection. -/
def contactTaylorCoefficient (kernel : Spacetime → ℂ) (w : ContactDerivativeIndex) : ℂ :=
  Complex.I ^ w.order * (w.factorial : ℂ)⁻¹ *
    iteratedFDeriv ℝ w.order kernel 0 (fun i => w.directions.get (Fin.cast w.directions_length.symm i))

/-- All four-component multiindices of total order at most r. -/
def contactMultiIndicesUpTo (r : ℕ) : Finset ContactDerivativeIndex := by
  classical
  exact ((Finset.univ : Finset (Fin 4 → Fin (r + 1))).image
    (fun f μ => (f μ).val)).filter (fun w => w.order ≤ r)

/-- Ordinary momentum partial derivative in a fixed coordinate order. -/
def contactMomentumPartial (kernel : Spacetime → ℂ) (w : ContactDerivativeIndex) : ℂ :=
  iteratedFDeriv ℝ w.order kernel 0
    (fun i => w.directions.get (Fin.cast w.directions_length.symm i))

/-- First-centered normalform of the FINITE p-Taylor polynomial, including
external right-branch momentum k. With r=x-y the original partition has
exp(-ir p) exp(+ir k), so p=κ+k. This is the coefficient of ordinary
∂_x^alpha delta AFTER this polynomial shift. Using the unshifted scalar
Taylor coefficient above would omit Leibniz terms from exp(+ir k).
The input is one ordered external partition's raw kernel; k varies with the
partition and therefore cannot be inserted after summing all partitions.
-/
def centeredContactTaylorCoefficient (kernel : Spacetime → ℂ) (r : ℕ)
    (rightMomentum : Spacetime) (alpha : ContactDerivativeIndex) : ℂ :=
  Complex.I ^ alpha.order * (alpha.factorial : ℂ)⁻¹ *
    ∑ nu ∈ contactMultiIndicesUpTo r,
      if alpha.order + nu.order ≤ r then
        (nu.factorial : ℂ)⁻¹ *
          (∏ μ : Fin 4, (rightMomentum μ : ℂ) ^ nu μ) *
            contactMomentumPartial kernel (alpha + nu)
      else 0

/-- Source-fixed engineering degree available to the output insertion. -/
def contactOutputBound (A B : LocalMonomial G) (w : ContactDerivativeIndex) : ℕ :=
  A.dimension + B.dimension - 3 - w.order

end YangMills.PerturbativeFlow
