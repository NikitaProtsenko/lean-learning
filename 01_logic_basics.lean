/-===================-/
/-===== ФУНКЦИИ =====-/
/-===================-/
namespace function
/-Так пишутся функции-/
/-
Шаблон:
def name (arg : Type) : ReturnType := expression
: - "имеет тип"
-/
def double (n:Nat)  : Nat := 2*n
def square (n:Nat)  : Nat := n*n
def add (a b : Nat) : Nat := a+b

/-Вывод значений функции-/
#eval double 10
#eval square 5
#eval add 3 4

/-
def - создает определение
#eval вычисляет результат
Nat - натуральные числа
-/

/-
match
принимаешь аргумент, потом разбираешь его
-/
def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => n

#eval pred 0
#eval pred 7

/-
Уравнения функции
-/
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => n + 1 + sumTo n

#eval sumTo 3


def id_nat : Nat → Nat := fun n => n
#eval id_nat 7

def id_bool : Bool → Bool := fun b => b
#eval id_bool true

end function

/-===================-/
/-===== ТЕОРЕМЫ =====-/
/-===================-/
namespace th
/-
Докажи: если есть P, то есть P.
-/
/-
Prop - тип утверждений
P → P - Если P, то P
intro h - пусть дано доказательство P
exact h - используем его
:= - это "определяется как"
-/
theorem id_example (P:Prop) : P → P := by
  intro h
  exact h

theorem id_example2 (Q : Prop) : Q → Q := by
  intro h
  exact h

theorem id_example3 (Q : Prop) : Q → Q := fun q => q

/-
Доказать что P и Q коммутируют
And.intro - собери ∧
.left, .right = "достань части ∧ "
-/
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact And.intro h.right h.left

/-
Доказать, что из P ∧ Q следует P
-/
theorem and_left (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left

/-
Or.inl h - доказать левую часть
Or.inr h - доказать правую часть

Если у тебя есть доказательство P, то из него можно сделать доказательство P ∨ Q через левую ветку.
Если у тебя есть доказательство Q, то можно сделать P ∨ Q через правую ветку.
-/

theorem or_left (P Q : Prop) : P → P ∨ Q := by
  intro h
  exact Or.inl h

theorem or_right (P Q : Prop) : Q → P ∨ Q := by
  intro h
  exact Or.inr h

/-
intro поочередно берет разбирает стрелки

intro hp (предположим что у нас есть P)
Далее ¬¬P это тоже самое что (P → False) → False
Тогда
intro nothp (предположим, что у нас есть P → False)

hP : P
hNotP : P → False

!! Каждый intro снимает одну внешнюю стрелку. !!
-/

theorem not_not (P : Prop) : P → ¬¬P := by
  intro hp
  intro nothp
  exact nothp hp

/-
rfl работает, когда левая и правая части одинаковы по вычислению.
Примеры:
2 = 2
1 + 1 = 2
n = n
rfl = reflexivity, рефлексивность (всякая вещь равна самой себе)
-/
theorem eq1 (n : Nat) : n = n := by
  rfl

theorem eq2 : 1 + 1 = 2 := by
  rfl

/-
rw = rewrite = переписать.

После intro h
У меня есть h : a = b
Цель: b = a
-/

theorem eq_symm_example (a b : Nat) : a = b → b = a := by
  intro h
  rw [h]


/-
cases разбирает объект по способам, которыми он мог быть построен.
Для P ∨ Q это:
inl — есть P
inr — есть Q
-/

theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

end th


/-===================-/
/-===== ПРИМЕРЫ =====-/
/-===================-/
namespace ex

theorem  ex_eqvH (P : Prop) : P ∨ P → ¬¬ P := by
  intro hp
  cases hp with
  | inl hl =>
  {
    intro hnp
    exact hnp hl
  }
  | inr hr =>
  {
    intro hnp
    exact hnp hr
  }

theorem  ex_qvH1 (P : Prop) : P ∨ P → ¬¬ P := by
  intro hp
  intro hnp
  cases hp with
  | inl hl => exact hnp hl
  | inr hr => exact hnp hr

/-
intro hp : P
Q → Q
intro hq : Q
-/
theorem ex2 (P Q : Prop) : P → Q → Q := by
  intro hp
  intro hq
  exact hq

/-
(P ∧ Q) ∨ (P ∧ R) → P
-/
theorem hard1 (P Q R : Prop) : (P ∧ Q) ∨ (P ∧ R) → P := by
  intro hp
  cases hp with
  | inl h1 => exact And.left h1
  | inr h2 => exact And.left h2

/-
 P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
-/
theorem hard2 (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  cases h with
  | intro  hp hqr =>
    cases hqr with
    | inl hq =>
      exact Or.inl ( And.intro hp hq)
    | inr hr =>
      exact Or.inr (And.intro hp hr)

/-
P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
-/
theorem hard3 (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro h
  cases h with
  | intro hp hqr =>
    cases hqr with
    | intro hq hr => exact And.intro (And.intro hp hq) hr

/-
((P ∧ Q) ∨ (P ∧ R)) ∧ P → P ∧ (Q ∨ R)
-/
theorem hard4 (P Q R : Prop) : ((P ∧ Q) ∨ (P ∧ R)) ∧ P → P ∧ (Q ∨ R) := by
  intro h
  cases h with
  | intro hpqpr hp =>
    cases hpqpr with
    | inl hpq =>
      cases hpq with
        | intro hp' hq => exact And.intro hp' (Or.inl hq)
    | inr hpr =>
      cases hpr with
        | intro hp' hr => exact And.intro hp' (Or.inr hr)


/-
(P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)
-/
theorem hard5 (P Q R S : Prop) :  (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  intro h
  cases h with
  | intro hpq hrs =>
    cases hpq with
    | inl hp =>
      cases hrs with
      | inl hr => exact Or.inl ( And.intro hp hr )
      | inr hs => exact Or.inr (Or.inl (And.intro hp hs) )
    | inr hq =>
      cases hrs with
      | inl hr => exact Or.inr (Or.inr ( Or.inl (And.intro hq hr)))
      | inr hs => exact Or.inr (Or.inr ( Or.inr (And.intro hq hs)))

/-
(P → R) → (Q → R) → P ∨ Q → R
-/
theorem exf (P Q R : Prop) : (P → R) → (Q → R) → P ∨ Q → R := by
  intro hpr
  intro hqr
  intro hpq
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

/-
(P → Q) → ¬Q → ¬P
-/
theorem n3 (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hpq
  intro hnq
  intro hp
  exact hnq (hpq hp)

end ex
