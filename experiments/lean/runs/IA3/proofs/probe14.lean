import Mathlib
open Finset Nat
example (n : ℕ) (m : ℕ) (h3 : 3 ≤ m) :
    1 * (m / 1) + ((m - 1) * (m / (m - 1)) + (m * (m / m) + 5)) + 1 ≤ m * m := by
  have hm0 : 0 < m := by omega
  trace_state
  rw [Nat.div_one, Nat.div_self hm0]
  trace_state
  sorry
