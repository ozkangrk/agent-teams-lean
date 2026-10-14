import FormalConjectures.OEIS.«3625»
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open Polynomial

-- names probe
example : ∀ (p : ℕ) [inst : Fact p.Prime] (a : ℤ), (legendreSym p a = 0) ↔ ((a : ZMod p) = 0) := legendreSym.eq_zero_iff
example (p : ℕ) [Fact p.Prime] (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := legendreSym.mul
example (p : ℕ) [Fact p.Prime] {a : ℤ} (h : ((a : ZMod p)) ≠ 0) : legendreSym p a = 1 ↔ IsSquare ((a : ZMod p)) := legendreSym.eq_one_iff h
example (p : ℕ) [Fact p.Prime] {a : ℤ} (h : ((a : ZMod p)) ≠ 0) : legendreSym p a ^ 2 = 1 := legendreSym.sq_one h
example : (2 : ℕ) ≠ 2 → True := fun _ => trivial

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
example (hp1 : p % 4 = 1) (hq1 : q ≠ 2) : IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q) :=
  ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp1 hq1
example (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (hpq : p ≠ q) : IsSquare (q : ZMod p) ↔ ¬ IsSquare (p : ZMod q) :=
  ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp3 hq3 hpq

example (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p) = p := ZMod.card p
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : IsSquare (-1 : ZMod p) ↔ Fintype.card (ZMod p) % 4 ≠ 3 := FiniteField.isSquare_neg_one_iff

example (a n : ℕ) : ((a % n : ℕ) : ZMod n) = a := ZMod.natCast_mod a n
example (a n : ℕ) : (a : ZMod n).val = a % n := ZMod.val_natCast a n
example (n : ℕ) [Fact n.Prime] (a b : ZMod n) : (a * b).val = (a.val * b.val) % n := ZMod.val_mul a b
example (hp : p.Prime) : p = 2 ∨ p.Odd := Nat.Prime.eq_two_or_odd hp
example (x : ℤ) (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := (sq_eq_one_iff x).mp h
example (n : ℤ) (a : ℤ) (hn : n ≠ 0) : ((a : ℤ) : ZMod n) = 0 ↔ (n : ℤ) ∣ a := ZMod.intCast_zmod_eq_zero_iff_dvd

-- polynomial names
example {F : Type*} [Field F] (x : F) : (X - C x).degree = 1 := Polynomial.degree_X_sub_C x
example {F : Type*} [Field F] (f : F[X]) : IsUnit f ↔ f.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero
example {F : Type*} [Field F] (f : F[X]) : ¬ Irreducible f ↔ ∃ a b, f = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := Polynomial.not_irreducible_iff
example {F : Type*} [Field F] (f : F[X]) (x : F) : (X - C x) ∣ f ↔ f.IsRoot x := Polynomial.dvd_iff_isRoot
example {F : Type*} [Field F] (x : F) (hx : x ^ 2 + x + 2 = 0) :
    (X - C x) * (X - C (-(x + 1))) = X ^ 2 + X + (2 : F) := by
  have h1 : (X - C x) * (X - C (-(x + 1))) = X ^ 2 + X - (C x * C x + C x) := by
    simp only [map_neg, map_add]
    ring
  rw [h1]
  have hC : C x * C x + C x = C (x * x + x) := by push_cast; ring
  rw [hC]
  have hxx : x * x + x = -(2 : F) := by linarith [show x * x = x ^ 2 from rfl, hx]
  rw [hxx]
  simp
