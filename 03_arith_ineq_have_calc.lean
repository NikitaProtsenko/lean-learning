
namespace hcExamples
/-
show
“Перепишу/уточню текущую цель”

show ... from ... (было в 02_nat_induction)
“вот выражение этого типа”
-/

/-
have
“Докажу сейчас вспомогательный факт и сохраню его”
    have h : A := by
    ...
    После этого есть h : A.
-/

theorem have_ex1 (a : Nat) : a + 0 = a := by
    have h : a + 0 = a := by
        exact Nat.add_zero a
    exact h

/-
calc
позволяет писать доказательство как цепочку равенств или неравенств.

theorem calc_ex0 (a b : Nat) : a + b = b + a := by
    calc
        a + b = b + a := Nat.add_comm a b
-/

theorem calc_ex1 (a : Nat) : a + 0 = a := by
    calc
        a + 0 = a := Nat.add_zero a

/-
"_"
Означает:
“левая часть берётся из предыдущей строки”

-/
theorem calc_ex2 (a b c : Nat) : a + (b + c) = b + (a + c) := by
    calc
        a + (b + c) = (a + b) + c := by
            rw[<-Nat.add_assoc]
        _ = (b + a) + c := by
            rw[Nat.add_comm b a]
        _ = b + (a + c) := by
            rw[Nat.add_assoc]

theorem le_ex1 (n : Nat) : n ≤ n := by
    exact Nat.le_refl n

theorem lt_ex1 (n : Nat) : n < n + 1 := by
    exact Nat.lt_succ_self n

theorem le_ex2 (a b : Nat) : a ≤ a + b := by
    exact Nat.le_add_right a b

theorem le_ex3 (a b c : Nat) : a ≤ a + b + c := by
    rw[Nat.add_assoc a b c]
    exact Nat.le_add_right a (b+c)

/-
theorem le_ex4 (a b c : Nat) : a ≤ a + b + c := by
    have h : a ≤ a + b := by
    ...
Задача
1. Сначала получить промежуточный факт h
2. Потом из него прийти к a ≤ a + b + c
-/

theorem le_ex4 (a b c : Nat) : a ≤ a + b + c := by
    have h1 : a ≤ a + b := by
        exact Nat.le_add_right a b
    rw[Nat.add_assoc a b c]
    have h2 : a + b ≤ a + (b+c) := by
        rw[<-Nat.add_assoc]
        rw[Nat.add_comm (a+b) c]
        exact Nat.le_add_left (a+b) c
    exact Nat.le_trans h1 h2

theorem calc_le1 (a b c : Nat) : a ≤ a + b + c := by
    calc
        a ≤ a + b := by
            exact Nat.le_add_right a b
        _ ≤ a + b + c := by
            exact Nat.le_add_right (a+b) c

theorem lt_ex2 (a b : Nat) : a < a + b + 1 := by
    calc
        a ≤  a + b := by
            exact Nat.le_add_right a b
        _ <  a + b + 1 := by
            rw[Nat.add_succ]
            rw[Nat.add_zero]
            exact Nat.lt_succ_self (a+b)
end hcExamples

namespace hardTask

/-
2^n > n, n ∈ ℕ
-/

def pow2 (n : Nat) : Nat :=
    match n with
    | 0   => 1
    | n+1 => 2 * pow2 n

theorem pow2_gt_n (n : Nat) : pow2 n > n := by
    induction n with
    | zero =>
        rw[pow2]
        exact Nat.zero_lt_one
    | succ n ih =>
        rw[pow2]
        conv =>
            lhs
            rw[show 2 = 1 + 1 from rfl]
            rw[Nat.add_mul]
            rw[Nat.mul_comm 1 (pow2 n)]
            rw[Nat.mul_one]
        have h1 : pow2 n ≥ n + 1 := by
            rw [Nat.add_one]
            exact ih
        have h0 : pow2 n > 0 := by
            exact Nat.lt_of_le_of_lt (Nat.zero_le n) ih
        exact Nat.add_lt_add_of_lt_of_le h1 h0

end hardTask
