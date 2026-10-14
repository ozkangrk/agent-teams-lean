import FormalConjectures.OEIS.«100434»
set_option maxHeartbeats 2000000

namespace OeisA100434

private lemma cR (N : ℕ) : c (N + 4) = -6 * c (N + 2) - c N := rfl

private lemma aR (N : ℕ) : a (N + 4) = -6 * a (N + 2) - a N := rfl

private lemma bR (m : ℕ) : b (m + 4) = -6 * b (m + 2) - b m := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have h0 : (m + 4) % 2 = 0 := by omega
    have h1 : (m + 2) % 2 = 0 := by omega
    simp only [b, if_pos h0, if_pos h1, if_pos hm]
    have hc := cR (m + 1)
    linarith
  · have h0 : ¬ ((m + 4) % 2 = 0) := by omega
    have h1 : ¬ ((m + 2) % 2 = 0) := by omega
    have h2 : ¬ (m % 2 = 0) := by omega
    simp only [b, if_neg h0, if_neg h1, if_neg h2]
    have hc := cR (m - 1)
    rw [show m + 4 - 1 = m - 1 + 4 from by omega, show m + 2 - 1 = m - 1 + 2 from by omega]
    linarith

private lemma gR (m : ℕ) : g (m + 4) = -6 * g (m + 2) - g m := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have h0 : (m + 4) % 2 = 0 := by omega
    have h1 : (m + 2) % 2 = 0 := by omega
    simp only [g, if_pos h0, if_pos h1, if_pos hm]
    ring
  · have h0 : ¬ ((m + 4) % 2 = 0) := by omega
    have h1 : ¬ ((m + 2) % 2 = 0) := by omega
    have h2 : ¬ (m % 2 = 0) := by omega
    simp only [g, if_neg h0, if_neg h1, if_neg h2]
    have hc := cR m
    linarith

private lemma zero_of_R (u : ℕ → ℤ) (hR : ∀ m, u (m + 4) = -6 * u (m + 2) - u m)
    (h0 : u 0 = 0) (h1 : u 1 = 0) (h2 : u 2 = 0) (h3 : u 3 = 0) : ∀ n, u n = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · have hRk := hR k
      have hk2 : k + 2 < k + 1 + 1 + 1 + 1 := by omega
      have hk0 : k < k + 1 + 1 + 1 + 1 := by omega
      have e1 := ih (k + 2) hk2
      have e2 := ih k hk0
      rw [show k + 1 + 1 + 1 + 1 = k + 4 from by omega] at hRk ⊢
      rw [hRk, e1, e2]
      ring

private lemma dR (N : ℕ) : d (N + 4) = -6 * d (N + 2) - d N := rfl

private lemma d_even : ∀ n, 2 ∣ d n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | k
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨-5, rfl⟩
    · exact ⟨-12, rfl⟩
    · have hRk := dR k
      rw [show k + 1 + 1 + 1 + 1 = k + 4 from by omega] at hRk ⊢
      obtain ⟨z2, hz2⟩ := ih (k + 2) (by omega)
      obtain ⟨z0, hz0⟩ := ih k (by omega)
      rw [hRk, hz2, hz0]
      exact ⟨-6 * z2 - z0, by ring⟩

private lemma half_of (x y : ℤ) (h : x = 2 * y) : x / 2 = y := by
  rw [h]; omega

private lemma eR (m : ℕ) : e (m + 4) = -6 * e (m + 2) - e m := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have h0 : (m + 4) % 2 = 0 := by omega
    have h1 : (m + 2) % 2 = 0 := by omega
    simp only [e, if_pos h0, if_pos h1, if_pos hm]
    obtain ⟨z2, hz2⟩ := d_even (m + 2)
    obtain ⟨z0, hz0⟩ := d_even m
    have hRk := dR m
    have hA : d (m + 2) / 2 = z2 := half_of _ _ hz2
    have hB : d m / 2 = z0 := half_of _ _ hz0
    have hC : d (m + 4) / 2 = -6 * z2 - z0 := by rw [hRk]; omega
    omega
  · have h0 : ¬ ((m + 4) % 2 = 0) := by omega
    have h1 : ¬ ((m + 2) % 2 = 0) := by omega
    have h2 : ¬ (m % 2 = 0) := by omega
    simp only [e, if_neg h0, if_neg h1, if_neg h2]
    rw [show m + 4 - 1 = m - 1 + 4 from by omega, show m + 2 - 1 = m - 1 + 2 from by omega]
    obtain ⟨z2, hz2⟩ := d_even (m - 1 + 2)
    obtain ⟨z0, hz0⟩ := d_even (m - 1)
    have hRk := dR (m - 1)
    have hA : d (m - 1 + 2) / 2 = z2 := half_of _ _ hz2
    have hB : d (m - 1) / 2 = z0 := half_of _ _ hz0
    have hC : d (m - 1 + 4) / 2 = -6 * z2 - z0 := by rw [hRk]; omega
    omega

private lemma fR (m : ℕ) : f (m + 4) = -6 * f (m + 2) - f m := by
  simp only [f]
  rw [show (m + 4) / 2 = m / 2 + 2 from by omega, show (m + 2) / 2 = m / 2 + 1 from by omega]
  rw [show 2 * (m / 2 + 2) + 1 = 2 * (m / 2) + 5 from by ring,
    show 2 * (m / 2 + 1) + 1 = 2 * (m / 2) + 3 from by ring]
  obtain ⟨z2, hz2⟩ := d_even (2 * (m / 2) + 3)
  obtain ⟨z0, hz0⟩ := d_even (2 * (m / 2) + 1)
  have hRk : d (2 * (m / 2) + 5) = -6 * d (2 * (m / 2) + 3) - d (2 * (m / 2) + 1) :=
    dR (2 * (m / 2) + 1)
  have hA : d (2 * (m / 2) + 3) / 2 = z2 := half_of _ _ hz2
  have hB : d (2 * (m / 2) + 1) / 2 = z0 := half_of _ _ hz0
  have hC : d (2 * (m / 2) + 5) / 2 = -6 * z2 - z0 := by rw [hRk]; omega
  omega

end OeisA100434

open OeisA100434

theorem swarm_proof : type_of% @OeisA100434.conjecture2 := by
  intro n
  have hz := OeisA100434.zero_of_R (fun m => OeisA100434.b m - (OeisA100434.e m + OeisA100434.f m))
    (fun m => by rw [OeisA100434.bR, OeisA100434.eR, OeisA100434.fR]; ring)
    (by decide) (by decide) (by decide) (by decide) n
  linarith
