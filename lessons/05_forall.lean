import Mathlib.Data.Nat.Basic

example : ∀ n : ℕ, n = n := by
    intro n
    rfl

example (h : ∀ n : ℕ, n = n) :  5 = 5 := by
    exact h 5

example : ∀ n : Nat, n = n → n = n := by
    intro n hn
    exact hn

example : ∀ a b : Nat, a = b → b = a := by
    intro a b h
    exact h.symm

example (h : ∀ n : Nat, n = n → n = n) : 7 = 7 := by
    exact h 7 rfl

example : ∀ a b : Nat, a = b → a = a := by
    intro a b h
    rfl

example (h : ∀ a b : Nat, a = b → b = a) : ∀ n : Nat, n = n := by
    intro n
    exact h n n rfl

example (P Q : Nat → Prop) :
    (∀ n : Nat, P n → Q n) → (∀ n : Nat, P n) → ∀ n : Nat, Q n := by
    intro hPQ hP n
    exact hPQ n (hP n)

example (P Q : Nat → Prop) :
    (∀ n : Nat, P n → Q n) → (∀ n : Nat, P n) → ∀ n : Nat, Q n := by
    intro hPQ hP n
    have hp : P n := hP n
    have hq : Q n := hPQ n hp
    exact hq
