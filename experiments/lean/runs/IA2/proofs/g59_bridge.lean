import FormalConjectures.WrittenOnTheWallII.GraphConjecture59
open SimpleGraph

-- numeric bridge: F² < R*B implies F < ⌈√(R*B)⌉ (all in ℝ)
private lemma bridge (R B F : ℕ) (hRB : 0 < R * B) (h : (F : ℝ) ^ 2 < (R : ℝ) * (B : ℝ)) :
    (F : ℝ) < (⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ : ℝ) := by
  have hz : (F : ℤ) < ⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ := by
    rw [Int.lt_ceil]
    rw [Real.lt_sqrt (by positivity)]
    exact h
  exact_mod_cast hz

-- and the reverse usage: from ⌈√(R*B)⌉ ≤ F and F² < R*B derive False
private lemma contradiction (R B F : ℕ) (h : (⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ : ℝ) ≤ (F : ℝ))
    (hsq : (F : ℝ) ^ 2 < (R : ℝ) * (B : ℝ)) : False := by
  have h1 : (F : ℝ) < (⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ : ℝ) := by
    have hz : (F : ℤ) < ⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ := by
      rw [Int.lt_ceil]
      rw [Real.lt_sqrt (by positivity)]
      exact hsq
    exact_mod_cast hz
  linarith

-- sanity: sqrt 36
example : Real.sqrt 36 = 6 := by norm_num
