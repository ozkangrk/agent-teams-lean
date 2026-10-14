import FormalConjectures.OEIS.«70823»
open OeisA70823
have hd14 : numDigitsBase10 (a 14) = 216 := by decide
have hd15 : numDigitsBase10 (a 15) = 349 := by decide
have pow349 : (10:Nat) ^ 349 = 10 ^ 256 * 10 ^ 93 := by decide
have h16 : a 16 = (((OeisA70823.a 15 * (10:Nat) ^ 216 + OeisA70823.a 14 : ℤ) - (OeisA70823.a 14 * (10:Nat) ^ 256 * (10:Nat) ^ 93 + OeisA70823.a 15 : ℤ)).natAbs) := by
  rw [show (16:Nat) = 13 + 3 from by omega, a, concatenate, concatenate, hd14, hd15, pow349]
  rfl
example : numDigitsBase10 (a 16) = 565 := by
  rw [show (16:Nat) = 13 + 3 from by omega, a, concatenate, concatenate, hd14, hd15, pow349]
  decide
