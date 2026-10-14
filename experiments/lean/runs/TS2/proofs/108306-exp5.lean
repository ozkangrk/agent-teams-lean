
import FormalConjectures.OEIS.«108306»
open OeisA108306

example (F : (n : Nat) → ((m : Nat) → m < n → Nat) → Nat) (n : Nat) :
    Nat.strongRecOn (n + 1) F = F (n + 1) (fun m _ => Nat.strongRecOn m F) := by
  unfold Nat.strongRecOn
  rw [WellFounded.fix_eq]

example (F : (n : Nat) → ((m : Nat) → m < n → Nat) → Nat) (n : Nat) :
    Nat.strongRecOn n F = F n (fun m _ => Nat.strongRecOn m F) := by
  unfold Nat.strongRecOn
  exact WellFounded.fix_eq _ _ n
