import FormalConjectures.OEIS.«70823»
#check @Nat.Coprime.mul
#check @Nat.Coprime.pow_left
#check @Nat.Coprime.pow_right
#check @Nat.Coprime.dvd_of_dvd_mul_right
example : Squarefree 10 := by decide
example (p : ℕ) (hsq : Squarefree p) : True := by
  have := hsq
  trivial
#check fun (hsq : Squarefree 5) (hp : Nat.Prime 5) (h : (5:Nat) ^ 2 ∣ 5) => hsq hp h
example : OeisA70823.a 12 % 83 = 0 := by decide
example : OeisA70823.a 20 % 169 = 0 := by decide
