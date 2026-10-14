
#print Nat.strongRecOn
#check @WellFounded.fix_eq
example (F : ∀ n, (∀ m, m < n → ℕ) → ℕ) (n : ℕ) :
    Nat.strongRecOn (n + 1) F = F (n + 1) (fun m _ => Nat.strongRecOn m F) := by
  simp only [Nat.strongRecOn, WellFounded.fix_eq]
