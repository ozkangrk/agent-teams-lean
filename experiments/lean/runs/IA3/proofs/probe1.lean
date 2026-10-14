import FormalConjecturesUtil

example (a b : ℕ) (h : 13 * a ∣ 13 * b) : a ∣ b :=
  Nat.dvd_of_mul_dvd_mul_left (k := 13) (by norm_num) h
