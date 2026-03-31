/-
Lavrov & Maksimova, mathematical logic, sheet 01.
Classical propositional logic exercises.
-/

/-
(P → Q) ∨ (Q → P)
-/
theorem lavrov_mathlog_01_09a (P Q : Prop) : (P → Q) ∨ (Q → P) := by
    classical
    -- consider the cases P and ¬P
    by_cases h : P
    ·   right   -- P
        intro _
        exact h

    ·   left    -- ¬ P
        intro p
        contradiction

/-
(P → Q) ∨ (P → ¬ Q)
-/
theorem lavrov_mathlog_01_09b (P Q : Prop) :
    (P → Q) ∨ (P → ¬ Q) := by
    classical
    by_cases h : Q
    ·   left
        intro _
        exact h

    ·   right
        intro _
        exact h

/-
P → (Q → (P ∧ Q))
-/
theorem lavrov_mathlog_01_09c (P Q : Prop) : P → (Q → (P ∧ Q)) := by
    intro hp hq
    exact And.intro hp hq

/-
(P → Q) → ((Q → R) → (P → R))
-/
theorem lavrov_mathlog_01_09d (P Q R : Prop) : (P → Q) →
    ((Q → R) → (P → R)) := by
    -- P → Q
    intro hpq
    -- Q → R
    intro hqr
    -- P
    intro hp
    exact hqr (hpq hp)

/-
(¬ P → ¬ Q) → (Q → P)
-/
theorem lavrov_mathlog_01_09e (P Q : Prop) :
    (¬ P → ¬ Q) → (Q → P) := by
    -- ¬P → ¬Q
    classical
    intro hnpnq
    intro hq
    by_cases h: P
    ·   exact h
    ·   have hnq : ¬Q := hnpnq h
        contradiction

/-
P → (Q → P)
-/
theorem lavrov_mathlog_01_09f (P Q : Prop) : P → (Q → P) := by
    intro hp _
    exact hp

/-
P ∨ ¬ P
-/
theorem lavrov_mathlog_01_09g (P : Prop) : P ∨ ¬ P := by
    classical
    by_cases h : P
    ·   left
        exact h

    ·   right
        exact h

/-
(P → Q) → ((P → (Q → R)) → (P → R))
-/
theorem lavrov_mathlog_01_09h (P Q R : Prop) :
    (P → Q) → ((P → (Q → R)) → (P → R)) := by
    intro hpq hpqr hp
    -- From hpqr : P → Q → R  and hp : P we get Q → R
    -- From hpq :  P → Q      and hp : P we get Q
    -- Apply the function Q → R to Q
    exact (hpqr hp) (hpq hp)

/-
(P ∧ Q) → P
-/
theorem lavrov_mathlog_01_09i (P Q : Prop) : (P ∧ Q) → P := by
    intro hpq
    cases hpq with
        | intro hp hq => exact hp

/-
(P ∧ Q) → Q
-/
theorem lavrov_mathlog_01_09j (P Q : Prop) : (P ∧ Q) → Q := by
    intro hpq
    cases hpq with
        | intro hp hq => exact hq

/-
P → (P ∨ Q)
-/

theorem lavrov_mathlog_01_09k (P Q : Prop) : P → (P ∨ Q) := by
    intro hp
    exact Or.inl hp

/-
Q → (P ∨ Q)
-/

theorem lavrov_mathlog_01_09l (P Q : Prop) : Q → (P ∨ Q) := by
    intro hq
    exact Or.inr hq

/-
(P → R) → ((Q → R) → ((P ∨ Q) → R))
-/

theorem lavrov_mathlog_01_09m (P Q R : Prop) : (P → R) →
    ((Q → R) → ((P ∨ Q) → R)) := by
    intro hpr hqr hpq
    cases hpq with
        | inl hp => exact hpr hp
        | inr hq => exact hqr hq

/-
(P → Q) → ((P → ¬ Q) → ¬ P)
-/

theorem lavrov_mathlog_01_09n (P Q : Prop) : (P → Q) →
    ((P → ¬ Q) → ¬ P) := by
    intro hpq hpnq hp
    have hnq : ¬ Q := by exact hpnq hp
    have hq  : Q := by exact hpq hp
    contradiction

/-
¬¬ P → P
-/

theorem lavrov_mathlog_01_09o (P : Prop) : ¬¬ P → P := by
    classical
    intro hnnp
    by_cases h : P
    ·   exact h
    ·   contradiction


/-
P → ¬¬ P
-/

theorem lavrov_mathlog_01_09p (P : Prop) : P → ¬¬ P := by
    intro hp
    -- ¬P : P → False
    intro hnp
    exact hnp hp


/-
(¬ Q → ¬ P) → ((¬ Q → P) → Q)
-/

theorem lavrov_mathlog_01_09q (P Q : Prop) :
    (¬ Q → ¬ P) → ((¬ Q → P) → Q) := by
    classical
    intro hnqnp
    intro hnqp
    by_cases h : Q
    ·   exact h
    ·   have hnp : ¬ P := by exact hnqnp h
        have hp : P := by exact hnqp h
        contradiction
/-
(P ∨ P) → P
-/

theorem lavrov_mathlog_01_09r (P : Prop) : (P ∨ P) → P := by
    intro hp
    cases hp with
        | inl h => exact h
        | inr h => exact h

/-
(Q → R) → ((P ∨ Q) → (P ∨ R))
-/

theorem lavrov_mathlog_01_09s (P Q R : Prop) :
    (Q → R) → ((P ∨ Q) → (P ∨ R)) := by
    intro hqr hpq
    cases hpq with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (hqr h)

/-
((P → Q) → P) → P
-/

theorem lavrov_mathlog_01_09t (P Q : Prop) : ((P → Q) → P) → P := by
    classical
    intro hpqp
    by_cases h : P
    ·   exact h
    ·   have hpq : P → Q := by
            intro hp
            contradiction
        exact hpqp hpq

/-
¬ P → (P → Q)
-/

theorem lavrov_mathlog_01_09u (P Q : Prop) : ¬ P → (P → Q) := by
    intro hnp hp
    contradiction
