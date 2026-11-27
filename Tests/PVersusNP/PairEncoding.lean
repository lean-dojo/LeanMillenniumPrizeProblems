import Problems.PVersusNP.Millennium

/-! Behavior checks for the tagged input/certificate boundary in the Cook-style encoding. -/

namespace Tests.PVersusNP

open Millennium

private abbrev boolStrings := fin_encoding_string Bool
private abbrev encodedPair := pair_encoding boolStrings boolStrings

example : encodedPair.decode [Sum.inr none] = some ([], []) := rfl
example : encodedPair.decode [Sum.inl true, Sum.inr none, Sum.inr (some false)] =
    some ([true], [false]) := rfl

example : encodedPair.decode [Sum.inl true] = none := rfl
example : encodedPair.decode [Sum.inr none, Sum.inr none] = none := rfl
example : encodedPair.decode [Sum.inr (some true), Sum.inr none] = none := rfl
example : encodedPair.decode [Sum.inr none, Sum.inl true] = none := rfl

end Tests.PVersusNP
