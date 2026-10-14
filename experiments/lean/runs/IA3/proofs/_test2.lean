import FormalConjectures.OEIS.«112970»

/-! probes -/

example (k : ℕ) (h : 0 < k) : 1 < 2 ^ k := Nat.one_lt_two_pow h

example (n : ℕ) : n % 3 < 3 := Nat.mod_lt n (y := 3) (by norm_num)
