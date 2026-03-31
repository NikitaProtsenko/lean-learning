/-
Урок 2.
Натуральные числа, арифметика, рекурсивные функции и индукция.
-/

namespace NatExamples
/-

Nat.add_comm
Это готовая теорема (для натуральных чисел):

comm = commutative = коммутативность
означает, что

a + b = b + a
-/

def sumTo : Nat → Nat
    | 0 => 0
    | n + 1 => n + 1 + sumTo n

theorem one_add_eq_succ (n : Nat) : 1 + n = n + 1 := by
    exact Nat.add_comm 1 n


theorem sumTo_succ' (n : Nat) : sumTo (n + 1) = sumTo n + (n + 1) := by
    rw [sumTo]
    exact Nat.add_comm (n + 1) (sumTo n)


theorem ex_nat1 (a b : Nat) : a + b = b + a := by
    exact Nat.add_comm a b

theorem ex_nat2 (a b c : Nat) : (a + b) + c = a + (b + c) := by
    exact Nat.add_assoc a b c

theorem ex_nat3 (a b : Nat) : a + b = b + a := by
    rw [Nat.add_comm a b]

theorem ex_nat4 (a b c : Nat) : a + b + c = a + (b + c) := by
    rw [Nat.add_assoc]

theorem ex_nat5 (a b c : Nat) : a + b + c = b + a + c := by
    rw [Nat.add_comm a b]

theorem ex_nat6 (a b c : Nat) : a + (b + c) = b + (a + c) := by
    rw [Nat.add_comm]
    rw [Nat.add_comm a c]
    rw [Nat.add_assoc]




theorem nat_hw1 (a : Nat) : a + 0 = a := by
    simp

theorem nat_hw2 (a : Nat) : 0 + a = a := by
    simp

theorem nat_hw3 (a b : Nat) : a + b = b + a := by
    rw [Nat.add_comm a b]

theorem nat_hw4 (a b c : Nat) : (a + b) + c = a + (b + c) := by
    rw [Nat.add_assoc a b c]

theorem nat_hw5 (a b c : Nat) : a + (b + c) = b + (a + c) := by
    rw [<- Nat.add_assoc]
    rw [Nat.add_comm a b]
    rw [Nat.add_assoc]

theorem nat_hw6 (a b : Nat) : a * b = b * a := by
    rw [Nat.mul_comm]

end NatExamples


namespace induct0
/-
Шаблон

theorem name (n : Nat) : ... := by
  induction n with
  | zero =>
    ...
  | succ n ih =>
    ...

induction n with --- Начинаем индукцию по n.

| zero =>
Случай n = 0

| succ n ih =>
Случай n + 1

Здесь:
n — предыдущее число
ih = induction hypothesis = индукционное предположение
То есть ih — это то, что уже доказано для n.
-/

/-
simp = simplify = упростить.

Он:

раскрывает простые определения,
использует известные равенства,
приводит цель к более простой форме.
-/

theorem add_zero (n : Nat) : n + 0 = n := by
    induction n with
        | zero =>
            rfl
        | succ n ih =>
            simp

def twice : Nat → Nat
    | 0 => 0
    | n + 1 => twice n + 2

/-
twice_succ можно было решить иначе в одну строку.
Пример для тренировки
-/
theorem twice_succ (n : Nat) : twice (n + 1) = twice n + 2 := by
    induction n with
        | zero => rfl
        | succ n ih => rw [twice]

theorem twice_eq_two_mul (n : Nat) : twice n = 2 * n := by
    induction n with
        | zero => rfl
        | succ n ih =>
            rw [twice]
            rw [Nat.mul_add]
            rw [Nat.mul_one]
            rw [ih]
def pow2 : Nat → Nat
    | 0 => 1
    | n + 1 => 2 * pow2 n

theorem pow2_succ (n : Nat) : pow2 (n + 1) = 2 * pow2 n := by
    rw [pow2]

theorem pow2_pos (n : Nat) : 0 < pow2 n := by
    induction n with
        | zero =>
            rw [pow2]
            simp
        | succ n ih =>
            rw[pow2]
            simp[ih]

theorem add_comm_ind (a b : Nat) : a + b = b + a := by
    induction a with
        | zero =>
            rw[Nat.zero_add]
            rfl
        | succ a ih =>
            rw[Nat.succ_add]
            rw[ih]
            rw[Nat.succ_eq_add_one]
            rfl

theorem indD (n : Nat) : twice n = n + n := by
    induction n with
        | zero =>
            rfl
        | succ n ih =>
            rw[twice]
            rw[ih]
            rw[Nat.add_add_add_comm]

end induct0

/-
Задача. Доказать для всех n∈ℕ
1 + 3 + 5 + ... + (2n - 1) = n^2;
-/

namespace induct1

def left: Nat → Nat
    | 0     => 0
    | n+1   => 2*(n+1)-1 + left n

/-
Можно было записать более "чистую" версию функции, дабы упростить индукцию
def oddSum : Nat → Nat
  | 0 => 0
  | n + 1 => (2 * n + 1) + oddSum n
-/

theorem hardTask1 (n:Nat) : left n = n*n := by
    induction n with
        | zero      => rfl
        | succ n ih =>
            rw[left]
            rw[ih]
            rw[Nat.mul_add]
            rw[Nat.mul_one]
            rw[Nat.add_one_mul_add_one]
            rw[Nat.add_comm]
            rw[Nat.add_assoc]
            rw[Nat.add_assoc]
            rw[Nat.add_left_cancel_iff]
            rw[← Nat.add_assoc]
            rw[Nat.two_mul]
            rfl

end induct1

/-
Задача. Доказать для всех n∈ℕ
1·2+2·5+...+n(3n-1)=n^2(n+1)
-/
namespace induct2

def n3n1 (n: Nat): Nat :=
    match n with
        | 0 => 0
        | n + 1 => (n+1)*(3*n+2) + n3n1 n

/-
Решим грубой силой, т.е. раскроем полностью все выражения
-/
theorem hardTask2 (n : Nat) : n3n1 n = n*n*(n+1) := by
    induction n with
        | zero => rfl
        | succ n ih =>
            rw[n3n1]
            rw[ih]
            conv =>
                rhs
                rw[Nat.add_one_mul_add_one]
            rw[Nat.add_comm]
            simp only[Nat.add_mul, Nat.mul_add]
            simp only [Nat.add_assoc,Nat.add_left_cancel_iff]
            simp[Nat.add_comm]
            rw [Nat.add_assoc]
            conv =>
                rhs
                simp only [<-Nat.add_assoc]
            rw [<-Nat.add_assoc]
            conv =>
                lhs
                rw [Nat.mul_comm n 2]
                rw [show 2 = 1 + 1 from rfl]
                rw [show 3 = 1 + 1 + 1 from rfl]
                simp only [<-Nat.mul_assoc,<-Nat.add_assoc]
                simp only [Nat.add_mul,<-Nat.mul_assoc,<-Nat.add_assoc]
            simp only [Nat.mul_add,Nat.one_mul,Nat.mul_one]
            simp only [Nat.add_mul,<-Nat.add_assoc]
            simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
end induct2
