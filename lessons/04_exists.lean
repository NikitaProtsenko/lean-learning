/-
Exists.intro witness proof
-/
theorem exists_ex1 : ∃ n : Nat, n = 3 := by
    exact Exists.intro 3 rfl

theorem exists_ex2 : ∃ n : Nat, n + 1 = 1 := by
    exact Exists.intro 0 rfl

/-
`trivial` is a tactic that solves goals that are immediately provable
-/
theorem exists_ex3 : (∃ n : Nat, n = 3) → True := by
    intro h
    cases h with
    | intro n hn =>
        trivial

theorem exists_ex3' : (∃ n : Nat, n = 3) → True := by
    intro h
    cases h with
    | intro n hn =>
        exact True.intro

theorem exists_ex4 : (∃ n : Nat, n = 3) → 3 = 3 := by
    intro h
    cases h with
    | intro n hn =>
        rfl

theorem exists_ex5 :
    (∃ n : Nat, n = 3) → ∃ m : Nat, m = 3 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro 3 rfl

theorem exists_ex6 :
    (∃ n : Nat, n = 3) → ∃ m : Nat, 3 = m := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro 3 rfl

theorem exists_ex7 :
    (∃ n : Nat, n = 3) → ∃ m : Nat, m = 3 ∧ m = 3 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro n (And.intro hn hn)

/-
(∃ n : Nat, n = 0 ∨ n = 1) → True
-/
theorem exists_or_ex1 :
    (∃ n : Nat, n = 0 ∨ n = 1) → True := by
    intro h
    cases h with
    | intro n hn =>
        exact True.intro

/-
(∃ n : Nat, n = 0 ∨ n = 1) → ∃ m : Nat, m = 1 ∨ m = 0
-/
theorem exists_or_ex2 :
    (∃ n : Nat, n = 0 ∨ n = 1) → ∃ m : Nat, m = 1 ∨ m = 0 := by
    intro h
    cases h with
    | intro n hn =>
        cases hn with
        | inl h0 =>
            exact Exists.intro n (Or.inr h0)
        | inr h1 =>
            exact Exists.intro n (Or.inl h1)

/-
(∃ n : Nat, n = 2) → ∃ m : Nat, m = 2 ∧ m + 1 = 3
-/
theorem exists_and_ex1 :
    (∃ n : Nat, n = 2) → ∃ m : Nat, m = 2 ∧ m + 1 = 3 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro n (And.intro hn (by rw [hn]))


/-
∃ n : Nat, n = 5
-/
theorem ex_exists_01 : ∃ n : Nat, n = 5 := by
    exact Exists.intro 5 rfl

/-
∃ n : Nat, n + 2 = 4
-/
theorem ex_exists_02 : ∃ n : Nat, n + 2 = 4 := by
    exact Exists.intro 2 rfl

/-
(∃ n : Nat, n = 7) → True
-/
theorem ex_exists_03 : (∃ n : Nat, n = 7) → True := by
    intro h
    cases h with
    | intro n hn =>
        exact True.intro

theorem ex_exists_03' : (∃ n : Nat, n = 7) → True := by
    intro h
    trivial

/-
(∃ n : Nat, n = 3) → ∃ m : Nat, m = 3
-/

theorem ex_exists_04 : (∃ n : Nat, n = 3) → ∃ m : Nat, m = 3 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro n hn

theorem ex_exists_04' : (∃ n : Nat, n = 3) → ∃ m : Nat, m = 3 := by
    intro h
    trivial

/-
(∃ n : Nat, n = 2) → ∃ m : Nat, m = 2 ∧ m = 2
-/
theorem ex_exists_05 :
    (∃ n : Nat, n = 2) → ∃ m : Nat, m = 2 ∧ m = 2 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro n (And.intro hn hn)

/-
(∃ n : Nat, n = 0 ∨ n = 1) → ∃ m : Nat, m = 1 ∨ m = 0
-/
theorem ex_exists_06 :
    (∃ n : Nat, n = 0 ∨ n = 1) → ∃ m : Nat, m = 1 ∨ m = 0 := by
    intro h
    cases h with
    | intro n hn =>
        cases hn with
        | inl n0 => exact Exists.intro n (Or.inr n0)
        | inr n1 => exact Exists.intro n (Or.inl n1)

/-
(∃ n : Nat, n = 4) → ∃ m : Nat, m + 1 = 5
-/
theorem ex_exists_07 :
    (∃ n : Nat, n = 4) → ∃ m : Nat, m + 1 = 5 := by
    intro h
    cases h with
    | intro n hn =>
        exact Exists.intro n (by rw [hn])

/-
∃ n : Nat, ∃ m : Nat, n = 1 ∧ m = 2
-/
theorem ex_exists_08 : ∃ n : Nat, ∃ m : Nat, n = 1 ∧ m = 2 := by
    exact Exists.intro 1 (Exists.intro 2 (And.intro rfl rfl))
