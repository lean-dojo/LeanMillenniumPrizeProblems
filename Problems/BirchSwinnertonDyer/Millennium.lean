import Problems.BirchSwinnertonDyer.Mordellweil

namespace MilleniumBirchSwinnertonDyer

open Complex
open EllipticCurveDef

/-!
# Birch and Swinnerton-Dyer Conjecture

This file is an attempt to formalize the statement of the Birch and Swinnerton-Dyer conjecture atleats my understanding. Please take a look at Mordeweil.lean for the definitions of the terms used in this file and there are a bunch of sorries in that file as even the definitions are hard for me to formalize.

The BSD conjecture relates the rank of an elliptic curve E over a number field K to
the order of the zero of its L-function at s = 1, and provides a formula for the leading
coefficient of the Taylor expansion of the L-function at this point.

## My Explanation

The Birch and Swinnerton-Dyer (BSD) conjecture concerns the relationship between:
1. The algebra: How many rational solutions an elliptic curve has
2. The analysis: How a special function (L-function) associated with the curve behaves

Imagine we have an equation like y² = x³ + ax + b with rational coefficients.
The BSD conjecture tells us:
- If we want to know how many "independent" rational solutions exist (the rank)
- We can study how many times the L-function equals zero at a specific point (s=1)

Now my understanding is that the conjecture has two main parts:

1. **Rank Equals Vanishing Order**:
   The rank of the Mordell-Weil group E(K) equals the order of vanishing of L(E,s) at s=1.
   - If the L-function is non-zero at s=1, then E has finitely many rational points
   - If L(E,1) = 0, the curve has infinitely many rational points
   - If L(E,s) has a zero of order r at s=1, the rank of E(K) is r

2. **Leading Coefficient Formula**:
   The leading coefficient in the Taylor expansion of L(E,s) at s=1 is given by:

   L^(r)(E,1)/r! = (Ω_E · Reg_E · #Sha(E) · ∏c_p) / (#E(K)_tors²)

   where:
   - Ω_E: The real period (related to the volume of the real or complex manifold)
   - Reg_E: The regulator (determinant of height pairings between generators)
   - #Sha(E): Size of the Tate-Shafarevich group (obstructions to the local-global principle)
   - c_p: Tamagawa numbers (local factors at bad reduction primes)
   - #E(K)_tors: Size of the torsion subgroup (points of finite order)

## Main Definitions

Imported from Mordellweil.lean:
* `EllipticCurve`: Definition of an elliptic curve using a Weierstrass model
* `MordellWeilGroup`: The group of K-rational points on an elliptic curve
* `torsion_subgroup`: The subgroup of points with finite order
* `torsion_order`: The order of the torsion subgroup
* `rank`: The rank of the Mordell-Weil group
* `L_function`: The Hasse-Weil L-function of the elliptic curve
* `L_function_order_at_one`: The order of zero of the L-function at s = 1
* `Sha`: The Tate-Shafarevich group of an elliptic curve
* `regulator`: The regulator of an elliptic curve
* `period`: The real period of an elliptic curve
* `tamagawa_number`: The Tamagawa number at a prime p

## Main Statements

* `BSD_rank_conjecture`: Rank equals order of zero of L-function at s = 1
* `BSD_leading_coefficient`: Formula for the leading coefficient of the Taylor expansion

## References

* Birch, B. J.; Swinnerton-Dyer, H. P. F. (1965). "Notes on elliptic curves. II".
  J. Reine Angew. Math. 218: 79–108. doi:10.1515/crll.1965.218.79
* Wiles, Andrew (2006). "The Birch and Swinnerton-Dyer conjecture". In Carlson, James;
  Jaffe, Arthur; Wiles, Andrew (eds.). The Millennium prize problems. American Mathematical Society.
-/

-- Number field over which we work
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]

-- An elliptic curve over a number field
variable (E : EllipticCurve K)

/-- The first part of the Birch and Swinnerton-Dyer conjecture:
    The rank of the Mordell-Weil group equals the order of the zero of the L-function at s = 1 -/
def BSD_rank_conjecture (E : EllipticCurve K) : Prop :=
    E.rank = L_function_order_at_one E

/-- The second part of the Birch and Swinnerton-Dyer conjecture:
    Formula for the leading coefficient in the Taylor expansion of the L-function at s = 1 -/
def BSD_leading_coefficient (E : EllipticCurve K) : Prop :=
    L_function_leading_coefficient E =
      (Sha_order E * period E * regulator E * tamagawa_product E) /
      (E.torsion_order ^ 2)

end MilleniumBirchSwinnertonDyer
