import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain
import Mathlib.Analysis.InnerProductSpace.PiL2

open EuclideanSpace MeasureTheory Order NavierStokes

def Torus3 : Type := Euc ℝ 3  -- With the understanding that points are identified modulo 1

-- Provide the necessary instances for the torus
-- All added to be sorries for now as there is no definition of the torus in Lean and the Torus3 type is not defined
-- Plus we could just put Euc R 3 directly everywhere instead of Torus3 but then we just have to add comments everywhere for Euc R 3 has to be have points modulo 1
-- So we just define Torus3 as Euc R 3 and add the necessary instances for it but added sorries for now
instance : AddCommGroup Torus3 := sorry
instance : NormedAddCommGroup Torus3 := sorry
instance : InnerProductSpace ℝ Torus3 := sorry
instance : MeasurableSpace Torus3 := sorry
instance : BorelSpace Torus3 := sorry
instance : Inhabited Torus3 := sorry
instance : MeasureSpace Torus3 := sorry
