import FormalConjectures.OEIS.«3625»
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open Polynomial OeisA3625

theorem root1 {p : ℕ} (hp : Fact p.Prime) (a : (ZMod p)[X]) (ha : a.natDegree = 1) :
    ∃ x : ZMod p, a.eval x = 0 := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hc1 : a.coeff 1 ≠ 0 := by
    have h := Polynomial.leadingCoeff_ne_zero.mpr ha0
    rwa [Polynomial.leadingCoeff, ha] at h
  refine ⟨-(a.coeff 0) / (a.coeff 1), ?_⟩
  rw [Polynomial.eval_eq_sum_range, ha, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, pow_one]
  field_simp
  ring

-- natDegree 2 and eval unfolding
theorem deg2 (p : ℕ) [Fact p.Prime] : (X ^ 2 + X + C 2 : (ZMod p)[X]).natDegree = 2 := by
  have h1 : (X + C 2 : (ZMod p)[X]).natDegree = 1 := Polynomial.natDegree_X_add_C _
  have h2 : (X ^ 2 : (ZMod p)[X]).natDegree = 2 := Polynomial.natDegree_X_pow 2
  have : (X ^ 2 + X + C 2 : (ZMod p)[X]) = X ^ 2 + (X + C 2) := by ring
  rw [this, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact h2
  · rw [h1, h2]; decide

theorem ev (p : ℕ) (x : ZMod p) :
    (X ^ 2 + X + C 2 : (ZMod p)[X]).eval x = x * x + x + 2 := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  ring


theorem htri {q : ℕ} [Fact q.Prime] (a : ℤ) :
    legendreSym q a = 0 ∨ legendreSym q a = 1 ∨ legendreSym q a = -1 := by
  by_cases h0 : (a : ZMod q) = 0
  · exact Or.inl ((legendreSym.eq_zero_iff q a).mpr h0)
  · by_cases hs : IsSquare (a : ZMod q)
    · exact Or.inr (Or.inl ((legendreSym.eq_one_iff q h0).mpr hs))
    · exact Or.inr (Or.inr ((legendreSym.eq_neg_one_iff q).mpr hs))

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  have hpF : Fact p.Prime := Fact.mk hp
  have hdeg := deg2 p
  -- Step A
  have hA1 : (∀ x : ZMod p, x * x + x + 2 ≠ 0) → Irreducible (X ^ 2 + X + C 2 : (ZMod p)[X]) := by
    intro hnr
    have hq0 : (X ^ 2 + X + C 2 : (ZMod p)[X]) ≠ 0 := by
      intro h; rw [h] at hdeg; exact absurd hdeg (by simp)
    have hq_notunit : ¬ IsUnit (X ^ 2 + X + C 2 : (ZMod p)[X]) := by
      intro hu
      obtain ⟨r, _hr, hrC⟩ := Polynomial.isUnit_iff.mp hu
      rw [← hrC, Polynomial.natDegree_C] at hdeg
      exact absurd hdeg (by decide)
    refine ⟨hq_notunit, fun a b hab => ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have ha0 : ∀ a : (ZMod p)[X], ¬IsUnit a → a ≠ 0 → 1 ≤ a.natDegree := by
      intro a hna ha0
      by_contra hc
      have hn0 : a.natDegree = 0 := Nat.le_zero.mp (Nat.not_lt.mp hc)
      have hdeq : a.degree = 0 := by
        rw [Polynomial.degree_eq_natDegree ha0, hn0]
        rfl
      exact hna ((Polynomial.isUnit_iff_degree_eq_zero).mpr hdeq)
    have ha0' : a ≠ 0 := by intro h; rw [h, zero_mul] at hab; exact hq0 hab
    have hb0' : b ≠ 0 := by intro h; rw [h, mul_zero] at hab; exact hq0 hab
    have ha1 := ha0 a hna ha0'
    have hb1 := ha0 b hnb hb0'
    have hnd : 2 = a.natDegree + b.natDegree := by
      have h := Polynomial.natDegree_mul (p := a) (q := b) ha0' hb0'
      rw [← hab, hdeg] at h
      exact h
    obtain ⟨r, hroot⟩ := root1 hpF a (by omega)
    exact hnr r (by
      have he := ev p r
      rw [← he, hab, Polynomial.eval_mul, hroot, zero_mul])
  have hA2 : (∃ x : ZMod p, x * x + x + 2 = 0) → ¬ Irreducible (X ^ 2 + X + C 2 : (ZMod p)[X]) := by
    rintro ⟨x, hx⟩ hirr
    have hdvd : (X - C x) ∣ (X ^ 2 + X + C 2 : (ZMod p)[X]) := by
      rw [Polynomial.dvd_iff_isRoot]
      show (X ^ 2 + X + C 2 : (ZMod p)[X]).eval x = 0
      rw [ev]
      exact hx
    obtain ⟨g, hg⟩ := hdvd
    rcases hirr.isUnit_or_isUnit hg with hu | hu
    · exfalso
      obtain ⟨r, _hr, hrC⟩ := Polynomial.isUnit_iff.mp hu
      have hthis := Polynomial.natDegree_X_sub_C x
      rw [← hrC] at hthis
      rw [Polynomial.natDegree_C] at hthis
      exact absurd hthis (by decide)
    · exfalso
      obtain ⟨r, _hr, hrC⟩ := Polynomial.isUnit_iff.mp hu
      have hq0 : (X ^ 2 + X + C 2 : (ZMod p)[X]) ≠ 0 := by
        intro h; rw [h] at hdeg; exact absurd hdeg (by simp)
      have hx0 : (X - C x : (ZMod p)[X]) ≠ 0 := by
        intro h
        have hthis := Polynomial.natDegree_X_sub_C x
        rw [h] at hthis
        exact absurd hthis (by simp)
      have hg0 : g ≠ 0 := by
        intro h; rw [h, mul_zero] at hg; exact hq0 hg
      have hnd : 2 = (X - C x : (ZMod p)[X]).natDegree + g.natDegree := by
        have h := Polynomial.natDegree_mul (p := X - C x) (q := g) hx0 hg0
        rw [← hg, hdeg] at h
        exact h
      rw [Polynomial.natDegree_X_sub_C] at hnd
      rw [← hrC, Polynomial.natDegree_C] at hnd
      omega
  have hA : ¬ Irreducible (X ^ 2 + X + C 2 : (ZMod p)[X]) ↔ ∃ x : ZMod p, x * x + x + 2 = 0 := by
    constructor
    · intro hni
      by_contra hnr
      exact hni (hA1 (fun x hx => hnr ⟨x, hx⟩))
    · exact hA2

  -- Step B: p ≠ 2: root ↔ IsSquare (−7)
  have hB : p ≠ 2 → ((∃ x : ZMod p, x * x + x + 2 = 0) ↔ IsSquare (-(7 : ZMod p))) := by
    intro hp2
    have hp1lt : 1 < p := hp.one_lt
    have hp4ne : p ≠ 4 := fun h => absurd (h ▸ hp) (by decide)
    have h2n : (2 : ZMod p) ≠ 0 := by
      intro h
      have hd : (p:ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by push_cast; exact h)
      have hd2 : p ∣ 2 := (Int.natCast_dvd_natCast).mp hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd2
      omega
    have h4n : (4 : ZMod p) ≠ 0 := by
      intro h
      have hd : (p:ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 p).mp (by push_cast; exact h)
      have hd2 : p ∣ 4 := (Int.natCast_dvd_natCast).mp hd
      have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hd2
      have hp4ne : p ≠ 4 := fun hh => absurd (hh ▸ hp) (by decide)
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 by omega) with hh | hh | hh
      · omega
      · rw [hh] at hd2
        exact absurd hd2 (by decide)
      · omega
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨2 * x + 1, ?_⟩
      have h4 : (2 * x + 1) * (2 * x + 1) = 4 * (x * x + x + 2) - 7 := by ring
      rw [hx, mul_zero, zero_sub] at h4
      exact h4.symm
    · rintro ⟨y, hy⟩
      have h2x : 2 * ((y - 1) / 2) = y - 1 := by field_simp
      have h2x1 : 2 * ((y - 1) / 2) + 1 = y := by rw [h2x]; ring
      refine ⟨(y - 1) / 2, ?_⟩
      have hcalc : 4 * (((y - 1) / 2) * ((y - 1) / 2) + (y - 1) / 2 + 2)
          = (2 * ((y - 1) / 2) + 1) * (2 * ((y - 1) / 2) + 1) + 7 := by ring
      have hyy : y * y = -(7 : ZMod p) := hy.symm
      rw [h2x1, hyy] at hcalc
      have hzero : 4 * (((y - 1) / 2) * ((y - 1) / 2) + (y - 1) / 2 + 2) = 0 := by
        rw [hcalc]; ring
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h h4n
      · exact h
  -- Step C: legendre chain for p ≠ 2, p ≠ 7
  have hC : p ≠ 2 → p ≠ 7 →
      (IsSquare (-(7 : ZMod p)) ↔ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)) := by
    intro hp2 hp7
    haveI hF7 : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hp1lt : 1 < p := hp.one_lt
    -- bridges with explicit binder
    have hbr : ∀ a : ℤ, ((a : ZMod p) ≠ 0) →
        (IsSquare ((a : ZMod p)) ↔ legendreSym p a = 1) := fun a ha => (legendreSym.eq_one_iff p ha).symm
    have hbr7 : ∀ a : ℤ, ((a : ZMod 7) ≠ 0) →
        (IsSquare ((a : ZMod 7)) ↔ legendreSym 7 a = 1) := fun a ha => (legendreSym.eq_one_iff 7 ha).symm
    -- nonzero facts
    have h7ne : ((p : ℤ) : ZMod 7) ≠ 0 := by
      intro h
      have hd : (7:ℤ) ∣ (p:ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) 7).mp h
      have hd2 : 7 ∣ p := (Int.natCast_dvd_natCast).mp hd
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp hd2
      omega
    have hm7ne : (Int.cast (-(7:ℤ)) : ZMod p) ≠ 0 := by
      intro h
      have hd : (p:ℤ) ∣ (-(7:ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(7:ℤ)) p).mp h
      have hd2 : (p:ℤ) ∣ 7 := by
        rcases hd with ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        linarith [hk]
      have hd3 : p ∣ 7 := (Int.natCast_dvd_natCast).mp hd2
      have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd3
      omega
    have hcast7 : ((p : ℤ) : ZMod 7) = ((p % 7 : ℕ) : ZMod 7) := by
      norm_num [Int.natCast_mod, Nat.add_mul_mod_self_left]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      have := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      omega
    -- cast bridge
    have hcc : (Int.cast (-(7 : ℤ)) : ZMod p) = -(7 : ZMod p) := by push_cast; norm_num
    have hcast : IsSquare (-(7 : ZMod p)) ↔ IsSquare ((Int.cast (-(7:ℤ)) : ZMod p)) := by
      rw [hcc]
    -- QR chain
    have hls : legendreSym p (-(7:ℤ)) = legendreSym 7 (p : ℤ) := by
      rw [show (-(7:ℤ)) = -1 * ((7:Nat) : ℤ) from by norm_num, legendreSym.mul, legendreSym.at_neg_one hp2]
      rcases hp4 with h4 | h4
      · have hc4 : ZMod.χ₄ (p : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four h4
        have hd2 := Nat.div_add_mod p 2
        have hd4 := Nat.div_add_mod p 4
        have hw : ∀ q : ℕ, q % 4 = 1 → (-1:ℤ) ^ (q / 2 * (7 / 2 : ℕ)) = 1 := by
          intro q hq
          rw [show (7:ℕ) / 2 = 3 from by norm_num,
            show q / 2 * 3 = 2 * (3 * (q / 4)) from by omega, pow_mul]
          norm_num
        have hexp : (-1:ℤ) ^ (p / 2 * (7 / 2 : ℕ)) = 1 := hw p h4
        have hqr := legendreSym.quadratic_reciprocity (p := p) (q := 7) (by omega) (by decide) hp7
        rw [hexp] at hqr
        rw [hc4, one_mul]
        rcases htri (q := 7) (p : ℤ) with h0 | h1 | hm1
        · rw [h0, zero_mul] at hqr; norm_num at hqr
        · rw [h1, one_mul] at hqr; rw [h1]; exact hqr
        · rw [hm1] at hqr; rw [hm1]; linear_combination (-1) * hqr
      · have hc4 : ZMod.χ₄ (p : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four h4
        have hd2 := Nat.div_add_mod p 2
        have hd4 := Nat.div_add_mod p 4
        have hw : ∀ q : ℕ, q % 4 = 3 → (-1:ℤ) ^ (q / 2 * (7 / 2 : ℕ)) = -1 := by
          intro q hq
          rw [show (7:ℕ) / 2 = 3 from by norm_num,
            show q / 2 * 3 = 2 * (3 * (q / 4) + 1) + 1 from by omega, pow_add, pow_mul]
          norm_num
        have hexp : (-1:ℤ) ^ (p / 2 * (7 / 2 : ℕ)) = -1 := hw p h4
        have hqr := legendreSym.quadratic_reciprocity (p := p) (q := 7) (by omega) (by decide) hp7
        rw [hexp] at hqr
        rw [hc4, neg_one_mul]
        rcases htri (q := 7) (p : ℤ) with h0 | h1 | hm1
        · rw [h0, zero_mul] at hqr; norm_num at hqr
        · rw [h1, one_mul] at hqr; rw [h1]; linear_combination (-1) * hqr
        · rw [hm1] at hqr; rw [hm1]; linear_combination hqr
    -- final assembly
    have hne3 : ∀ x : ZMod 7, ((3:Nat) : ZMod 7) ≠ x * x := by
      intro x hcon
      have hvm : ZMod.val (x * x) = (ZMod.val x * ZMod.val x) % 7 := ZMod.val_mul x x
      have hv3 : ZMod.val ((3:Nat) : ZMod 7) = 3 % 7 := ZMod.val_natCast 7 3
      have hcc := congrArg ZMod.val hcon
      rw [hvm, hv3] at hcc
      have key : ∀ v : ℕ, v < 7 → (v * v) % 7 ≠ 3 := by
        intro v hv7
        rcases v with _ | _ | _ | _ | _ | _ | - | _ <;> omega
      exact key (ZMod.val x) (ZMod.val_lt x) (by omega)
    have hne5 : ∀ x : ZMod 7, ((5:Nat) : ZMod 7) ≠ x * x := by
      intro x hcon
      have hvm : ZMod.val (x * x) = (ZMod.val x * ZMod.val x) % 7 := ZMod.val_mul x x
      have hv5 : ZMod.val ((5:Nat) : ZMod 7) = 5 % 7 := ZMod.val_natCast 7 5
      have hcc := congrArg ZMod.val hcon
      rw [hvm, hv5] at hcc
      have key : ∀ v : ℕ, v < 7 → (v * v) % 7 ≠ 5 := by
        intro v hv7
        rcases v with _ | _ | _ | _ | _ | _ | - | _ <;> omega
      exact key (ZMod.val x) (ZMod.val_lt x) (by omega)
    have hne6 : ∀ x : ZMod 7, ((6:Nat) : ZMod 7) ≠ x * x := by
      intro x hcon
      have hvm : ZMod.val (x * x) = (ZMod.val x * ZMod.val x) % 7 := ZMod.val_mul x x
      have hv6 : ZMod.val ((6:Nat) : ZMod 7) = 6 % 7 := ZMod.val_natCast 7 6
      have hcc := congrArg ZMod.val hcon
      rw [hvm, hv6] at hcc
      have key : ∀ v : ℕ, v < 7 → (v * v) % 7 ≠ 6 := by
        intro v hv7
        rcases v with _ | _ | _ | _ | _ | _ | - | _ <;> omega
      exact key (ZMod.val x) (ZMod.val_lt x) (by omega)
    have hs1 : IsSquare ((1:Nat) : ZMod 7) := ⟨((1:Nat) : ZMod 7), rfl⟩
    have hs2 : IsSquare ((2:Nat) : ZMod 7) := ⟨((3:Nat) : ZMod 7), rfl⟩
    have hs4 : IsSquare ((4:Nat) : ZMod 7) := ⟨((2:Nat) : ZMod 7), rfl⟩
    constructor
    · intro hsqr
      have h1 : legendreSym p (-(7:ℤ)) = 1 := (hbr (-(7:ℤ)) hm7ne).mp ((hcast.mp hsqr))
      have h2 : legendreSym 7 (p : ℤ) = 1 := by rw [← hls, h1]
      have h3 : IsSquare ((p : ℤ) : ZMod 7) := (hbr7 (p : ℤ) h7ne).mpr h2
      rw [hcast7] at h3
      rcases (show p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 by omega) with h | h | h | h | h | h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) (by
          intro hd
          exact hp7 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp hd).symm)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exfalso
        rw [h] at h3
        rcases h3 with ⟨x, hx⟩
        exact hne3 x hx
      · exact Or.inr (Or.inr h)
      · exfalso
        rw [h] at h3
        rcases h3 with ⟨x, hx⟩
        exact hne5 x hx
      · exfalso
        rw [h] at h3
        rcases h3 with ⟨x, hx⟩
        exact hne6 x hx
    · rintro (h | h | h)
      all_goals
        have h3 : IsSquare ((p : ℤ) : ZMod 7) := by
          rw [hcast7, h]
          first
          | exact hs1
          | exact hs2
          | exact hs4
        have h2 : legendreSym 7 (p : ℤ) = 1 := (hbr7 (p : ℤ) h7ne).mp h3
        have h1 : legendreSym p (-(7:ℤ)) = 1 := by rw [hls, h2]
        exact hcast.mpr ((hbr (-(7:ℤ)) hm7ne).mpr h1)
  -- Final assembly
  by_cases hp2 : p = 2
  · subst hp2
    constructor
    · rintro ⟨_, (h | h | h)⟩ <;> norm_num at h
    · intro hirr
      exact absurd hirr (hA2 ⟨0, by rfl⟩)
  · by_cases hp7 : p = 7
    · subst hp7
      constructor
      · rintro ⟨_, (h | h | h)⟩ <;> norm_num at h
      · intro hirr
        exact absurd hirr (hA2 ⟨3, by rfl⟩)
    · constructor
      · rintro ⟨hpr, (h | h | h)⟩
        all_goals
          refine hA1 (fun x hx => ?_)
          have hsq : IsSquare (-(7 : ZMod p)) := (hB hp2).mp ⟨x, hx⟩
          have hs7 := (hC hp2 hp7).mp hsq
          rcases (show p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6
          · exact absurd ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm hp7
          · exact absurd h1 (by omega)
          · omega
          · omega
          · omega
          · omega
          · omega
      · intro hirr
        refine ⟨hp, ?_⟩
        have hnroot : ¬ (∃ x : ZMod p, x * x + x + 2 = 0) := fun hr => hA2 hr hirr
        have hnsq : ¬ IsSquare (-(7 : ZMod p)) := fun hs => hnroot ((hB hp2).mpr hs)
        rcases (show p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6
        · exact absurd ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm hp7
        · exact absurd ((hC hp2 hp7).mpr (Or.inl h1)) hnsq
        · exact absurd ((hC hp2 hp7).mpr (Or.inr (Or.inl h2))) hnsq
        · exact Or.inl h3
        · exact absurd ((hC hp2 hp7).mpr (Or.inr (Or.inr h4))) hnsq
        · exact Or.inr (Or.inl h5)
        · exact Or.inr (Or.inr h6)

