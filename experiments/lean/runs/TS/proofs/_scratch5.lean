import FormalConjectures.OEIS.«70823»

-- step 1: direct kernel decides for small levels
example : OeisA70823.numDigitsBase10 (OeisA70823.a 14) = 216 := by decide
example : OeisA70823.numDigitsBase10 (OeisA70823.a 15) = 349 := by decide
example : OeisA70823.a 15 % 169 = 4 := by decide
