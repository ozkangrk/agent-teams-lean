import FormalConjectures.OEIS.«237271»
import FormalConjectures.Wikipedia.AgohGiuga

open Nat Finset List

#check @List.countP_cons
#check @Finset.sort_sorted
#check @Finset.sort_nodup
#check @Nat.minFac_prime
#check @Nat.minFac_dvd
#check @Nat.minFac_le_of_dvd
#check @Nat.Prime.eq_two_or_odd
#check @Nat.mul_div_cancel'
#check @Nat.coprime_one_right
#check @Nat.Squarefree
#check @Nat.squarefree_iff_prime_squarefree
#check @korselts_criterion
#check @Nat.FermatPsp
example (k : Nat) (hk : k ≠ 0) : 1 ∈ OeisA237271.sortedDivisorsList k := by
  rw [OeisA237271.sortedDivisorsList]
  exact (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨one_dvd k, hk⟩)
example (k : Nat) (hk : k ≠ 0) : OeisA237271.a k = 1 + ((OeisA237271.sortedDivisorsList k).zip (OeisA237271.sortedDivisorsList k).tail).countP (fun pr => Odd pr.2 ∧ pr.2 ≥ 2 * pr.1) := rfl
