import Mathlib.Tactic.Ring

/-
Sum of squares of the first `n` odd numbers:
`1^2 + 3^2 + ... + (2n-1)^2`
-/
def kud_01_03_7_1d (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n + 1 => (2 * n + 1)^2+ kud_01_03_7_1d n
/-
Equivalent form of
`1^2 + 3^2 + ... + (2n-1)^2 = n(4n^2 - 1)/3`,
avoiding division in `Nat`.
-/

theorem kud_01_03_7_1t (n : Nat) :
    3 * kud_01_03_7_1d n + n = 4 * n^3 := by
    induction n with
    | zero =>
        rw [kud_01_03_7_1d]
        rfl
    | succ n ih =>
        rw [kud_01_03_7_1d]
        ring_nf
        have l1 :
            4 + n * 13 + n ^ 2 * 12 + kud_01_03_7_1d n * 3 =
            3 * kud_01_03_7_1d n + n + 4 + n * 12 + n ^ 2 * 12 := by
            ring
        rw[l1]
        rw[ih]
        ring

/-
` 1·2 + 2·3 + 3·4 + ... + (n-1)n`
-/
def kud_01_03_7_2d (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n + 1 => n *(n + 1) + kud_01_03_7_2d n

/-
Equivalent form of
`1·2 + 2·3 + 3·4 + ... + (n-1)·n = (n-1)·n·(n+1)/3`
avoiding division in `Nat`.
-/
theorem kud_01_03_7_2t (n : Nat) :
    3 * kud_01_03_7_2d n + n = n^3 := by
    induction n with
    | zero =>
        rw [kud_01_03_7_2d]
        rfl
    | succ n ih =>
        rw [kud_01_03_7_2d]
        ring_nf
        rw [Nat.mul_comm (kud_01_03_7_2d n)]
        have l1 :
            1 + n * 4 + n ^ 2 * 3 + 3 * kud_01_03_7_2d n =
            3 * kud_01_03_7_2d n + n + 1 + n * 3 + n ^ 2 * 3 := by
            ring
        rw [l1, ih]
        ring
