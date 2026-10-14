import FormalConjectures.OEIS.«113250»

/-!
Proof of the A113250 conjecture: odd-indexed terms of the sequence are perfect squares,
via the closed form `a n = 4 ^ n * q n` with `q` 6-periodic.
-/

open OeisA113250

namespace A113250Aux

/-- Periodic factor: `a n = 4 ^ n * q n` with `q` 6-periodic. -/
def q : ℕ → ℤ := fun n =>
  match n % 6 with
  | 0 => -1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => -1
  | _ => 4

theorem q_mod (n : ℕ) : q n = q (n % 6) := by
  simp only [q, Nat.mod_mod]

theorem q_add_mod (n j : ℕ) : q (n + j) = q ((n % 6 + j) % 6) := by
  rw [q_mod, Nat.mod_add_mod]

theorem q_add4 (n : ℕ) : q (n + 4) + q (n + 3) = q (n + 1) + q n := by
  have key : ∀ k : ℕ, k < 6 → q ((k + 4) % 6) + q ((k + 3) % 6) = q ((k + 1) % 6) + q k := by
    intro k hk
    interval_cases k
    all_goals rfl
  rw [q_add_mod n 4, q_add_mod n 3, q_add_mod n 1, q_mod n]
  exact key (n % 6) (Nat.mod_lt _ (by norm_num))

theorem closed_form (n : ℕ) : a n = 4 ^ n * q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      all_goals rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have ha : a (m + 4) = -4 * a (m + 3) + 64 * a (m + 1) + 256 * a m := rfl
      rw [ha, ih (m + 3) (by omega), ih (m + 1) (by omega), ih m (by omega)]
      have h4' : q (m + 4) = q (m + 1) + q m - q (m + 3) := by
        have h := q_add4 m
        omega
      rw [h4']
      rw [pow_add, pow_add, pow_add]
      ring

theorem isSquare_4mul (n : ℕ) (c : ℤ) (hc : c = 1 ∨ c = 4) :
    IsSquare (4 ^ (2 * n + 1) * c) := by
  rcases hc with rfl | rfl
  · refine ⟨4 ^ n * 2, ?_⟩
    rw [show 2 * n = n * 2 from Nat.mul_comm 2 n, pow_add, pow_one, pow_mul]
    ring
  · refine ⟨4 ^ n * 4, ?_⟩
    rw [show 2 * n = n * 2 from Nat.mul_comm 2 n, pow_add, pow_one, pow_mul]
    ring

end A113250Aux

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [A113250Aux.closed_form]
  have hc : (2 * n + 1) % 6 = 1 ∨ (2 * n + 1) % 6 = 3 ∨ (2 * n + 1) % 6 = 5 := by omega
  rcases hc with h | h | h <;> rw [A113250Aux.q_mod, h]
  · exact A113250Aux.isSquare_4mul n _ (Or.inl rfl)
  · exact A113250Aux.isSquare_4mul n _ (Or.inl rfl)
  · exact A113250Aux.isSquare_4mul n _ (Or.inr rfl)
