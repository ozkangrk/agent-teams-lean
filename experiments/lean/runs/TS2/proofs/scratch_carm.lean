import FormalConjectures.OEIS.«237271»
import FormalConjecturesForMathlib.NumberTheory.Carmichael

open Nat List Finset

namespace OeisA237271

lemma mem_zip_of_consecutive {l : List ℕ} (h : l.SortedLT) {x y : ℕ} (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x < y) (hnb : ∀ z ∈ l, z ≤ x ∨ y ≤ z) : (x, y) ∈ l.zip l.tail := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hall, ht⟩ := h
    rcases hx with rfl | hx
    · rcases t with _ | b s
      · rcases hy with rfl | hy
        · simp at hy
        · simp at hy
      · have hyb : y = b := by
          rcases hy with rfl | hy'
          · rfl
          · rcases Nat.lt_trichotomy y b with h1 | h1 | h1
            · exfalso; rcases hnb b (by simp) with hb | hb
              · have hab : a < b := hall b (by simp); omega
              · omega
            · exact h1
            · exfalso; rcases hnb y (by simp) with hy2 | hy2
              · have hay : a < y := hall y (by simp); omega
              · omega
        rw [cons_cons, zip_cons_cons]
        exact Or.inl (by simp [hyb])
    · rcases hy with rfl | hy
      · have hay : a < y := hall y hy; omega
      · rcases t with _ | b s
        · cases hx
        · rw [cons_cons, zip_cons_cons]
          exact Or.inr (ih ht (by simpa using hx) (by simpa using hy) hxy
            (fun z hz => hnb z (by simp [hz])))

theorem swarm_proof : ∀ (k : ℕ), IsCarmichael k → 3 ≤ a k := by
  intro k hk
  obtain ⟨_, hnp, hk1⟩ := hk 1 (by norm_num) (by simp)
  -- k is odd
  have hcop : k.Coprime (k - 1) := Nat.coprime_of_dvd (by
    intro p hp hp1 hp2
    exact absurd (Nat.eq_one_of_dvd (Nat.dvd_sub' hp1 hp2) : p = 1)
      (hp.ne_one rfl) |>.elim
  obtain ⟨hprob, _, _⟩ : FermatPsp k (k - 1) := hk (k - 1) (by omega) hcop
  have hkodd : k % 2 = 1 := by
    rcases Nat.even_or_odd k with heven | hodd
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      have hpow2 : (m + 1) * (m + 1) = (m + 2) * m + 1 := by ring_nf
      have hmod2 : Nat.ModEq (m + 2) ((m + 1) ^ 2) 1 := by
        show (m + 2) ∣ (m + 1) ^ 2 - 1
        rw [pow_two, hpow2]
        have h' : (m + 2) * m + 1 - 1 = (m + 2) * m := by omega
        rw [h']; exact ⟨m, rfl⟩
      have hem : m % 2 = 0 := by omega
      have hexp : m + 1 = 2 * (m / 2) + 1 := by omega
      have hsplit : (m + 1) ^ (m + 1) = ((m + 1) ^ 2) ^ (m / 2) * (m + 1) := by
        rw [hexp, pow_succ, pow_mul, pow_one]
      have hf : Nat.ModEq (m + 2) ((m + 1) ^ (m + 1)) (m + 1) := by
        rw [hsplit]
        exact (hmod2.pow (m / 2)).mul (Nat.ModEq.refl (m + 2) (m + 1)) |>.trans (by
          simp)
      have hf2 : Nat.ModEq (m + 2) ((m + 1) ^ (m + 1)) 1 :=
        (Nat.modEq_of_dvd hprob)
      have : Nat.ModEq (m + 2) (m + 1) 1 := hf.symm.trans hf2
      have hdvd2 : (m + 2) ∣ (m + 1) - 1 := this
      obtain ⟨d, hd⟩ := hdvd2
      rcases d with _ | d
      · omega
      · have : m + 1 - 1 = m := by omega
        omega
    · exact hodd
  sorry

end OeisA237271
