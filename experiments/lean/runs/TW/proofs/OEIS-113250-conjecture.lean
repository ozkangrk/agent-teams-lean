import FormalConjectures.OEIS.«113250»

open OeisA113250

private def u : ℕ → ℤ
  | 0 => 2
  | 1 => 8
  | n + 2 => -4 * u (n + 1) - 16 * u n

private theorem u_eq (n : ℕ) : u (n + 2) = -4 * u (n + 1) - 16 * u n := rfl

private theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n := rfl

-- odd-index subsequence: a(2n+7) = 4096 * a(2n+1)
private theorem c_rec (n : ℕ) : a (2 * n + 7) = 4096 * a (2 * n + 1) := by
  have e1 : a (2 * n + 5) = -4 * a (2 * n + 4) + 64 * a (2 * n + 2) + 256 * a (2 * n + 1) :=
    a_rec (2 * n + 1)
  have e2 : a (2 * n + 6) = -4 * a (2 * n + 5) + 64 * a (2 * n + 3) + 256 * a (2 * n + 2) :=
    a_rec (2 * n + 2)
  have e3 : a (2 * n + 7) = -4 * a (2 * n + 6) + 64 * a (2 * n + 4) + 256 * a (2 * n + 3) :=
    a_rec (2 * n + 3)
  linear_combination 16 * e1 - 4 * e2 + e3

-- squares of u satisfy the same order-3 recurrence
private theorem uu_rec (n : ℕ) :
    u (n + 3) * u (n + 3) = 4096 * (u n * u n) := by
  have h2 := u_eq n
  have h3 := u_eq (n + 1)
  rw [h3, h2]
  ring

private theorem key : ∀ n : ℕ, a (2 * n + 1) = u n * u n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 =>
      have h0 : a (2 * k + 1) = u k * u k := ih k (by omega)
      have h1 : a (2 * (k + 1) + 1) = u (k + 1) * u (k + 1) := ih (k + 1) (by omega)
      have h2 : a (2 * (k + 2) + 1) = u (k + 2) * u (k + 2) := ih (k + 2) (by omega)
      have e1 : 2 * k + 7 = 2 * (k + 3) + 1 := by omega
      have hc := c_rec k
      rw [e1] at hc
      rw [hc, h0, uu_rec k]

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := fun n => ⟨u n, key n⟩
