/-
Lavrov & Maksimova, mathematical logic, sheet 01.

Classical propositional logic exercises.
-/

namespace lavrov_mathlog_2_01_09

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

end lavrov_mathlog_2_01_09

namespace lavrov_mathlog_2_01_15

/-
A ↔ A
-/
theorem lavrov_mathlog_01_15a (A : Prop) : A ↔ A := by
    rfl

/-
A ↔ B → B ↔ A
-/

theorem lavrov_mathlog_01_15b (A B : Prop) : (A ↔ B) → (B ↔ A) := by
    intro hAB
    constructor
    · exact hAB.mpr
    · exact hAB.mp

theorem lavrov_mathlog_01_15b' (A B : Prop) : (A ↔ B) → (B ↔ A) := by
    intro hAB
    exact hAB.symm

/-
((A ↔ B) ∧ (B ↔ C)) → (A ↔ C)
-/

theorem lavrov_mathlog_01_15c (A B C : Prop) :
    ((A ↔ B) ∧ (B ↔ C)) → (A ↔ C) := by
    intro hABBC
    cases hABBC with
    | intro hAB hBC =>
        constructor
        · exact hBC.mp ∘  hAB.mp
        · exact hAB.mpr ∘ hBC.mpr

end lavrov_mathlog_2_01_15

namespace lavrov_mathlog_2_01_16

/-
Prove that from (A1 ↔ A2) AND (B1 ↔ B2) it follows that ...
-/

/-
¬ A1 ↔ ¬ A2
-/

/-
For practice, prove this using  `by_cases`.
(It can be proved without `classical`.)
-/
theorem lavrov_mathlog_2_01_16a' (A1 A2 : Prop) :
    (A1 ↔ A2) → (¬ A1 ↔ ¬ A2) := by
    classical
    intro hA1A2
    constructor
    ·   intro hnA1
        by_cases h : A2
        ·   have hA1 : A1 := by exact hA1A2.mpr h
            contradiction
        ·   exact h
    ·   intro hnA2
        by_cases h : A1
        ·   have hA2 : A2 := by exact hA1A2.mp h
            contradiction
        ·   exact h

theorem lavrov_mathlog_2_01_16a (A1 A2 : Prop) :
    (A1 ↔ A2) → (¬ A1 ↔ ¬ A2) := by
    intro hA1A2
    constructor
    ·   intro hnA1 hA2
        apply hnA1
        exact hA1A2.mpr hA2
    ·   intro hnA2 hA1
        apply hnA2
        exact hA1A2.mp hA1

/-
(A1 ∧ B1) ↔ (A2 ∧ B2)
-/

theorem lavrov_mathlog_2_01_16b (A1 A2 B1 B2 : Prop):
    ((A1 ↔ A2) ∧ (B1 ↔ B2)) → ((A1 ∧ B1) ↔ (A2 ∧ B2)) := by
    intro hA1A2B1B2
    constructor
    ·   intro hA1B1
        cases hA1A2B1B2 with
            | intro hA1A2 hB1B2 =>
                exact And.intro (hA1A2.mp hA1B1.left ) (hB1B2.mp hA1B1.right)
    ·   intro hA2B2
        cases hA1A2B1B2 with
            | intro hA1A2 hB1B2 =>
                exact And.intro (hA1A2.mpr hA2B2.left ) (hB1B2.mpr hA2B2.right)

theorem lavrov_mathlog_2_01_16b' (A1 A2 B1 B2 : Prop):
    ((A1 ↔ A2) ∧ (B1 ↔ B2)) → ((A1 ∧ B1) ↔ (A2 ∧ B2)) := by
    intro hA1A2B1B2
    cases hA1A2B1B2 with
        | intro hA1A2 hB1B2 =>
            constructor
            ·   intro hA1B1
                constructor
                · exact hA1A2.mp hA1B1.left
                · exact hB1B2.mp hA1B1.right
            ·   intro hA2B2
                constructor
                · exact hA1A2.mpr hA2B2.left
                · exact hB1B2.mpr hA2B2.right

/-
(A1 ∨ B1) ↔ (A2 ∨ B2)
-/

theorem lavrov_mathlog_2_01_16c (A1 A2 B1 B2 : Prop):
    ((A1 ↔ A2) ∧ (B1 ↔ B2)) → ((A1 ∨ B1) ↔ (A2 ∨ B2)) := by
    intro hA1A2B1B2
    cases hA1A2B1B2 with
        | intro hA1A2 hB1B2 =>
            constructor
            ·   intro hA1B1
                cases hA1B1 with
                | inl hA1 => exact Or.inl (hA1A2.mp hA1)
                | inr hB1 => exact Or.inr (hB1B2.mp hB1)
            ·   intro hA2B2
                cases hA2B2 with
                | inl hA2 => exact Or.inl (hA1A2.mpr hA2)
                | inr hB2 => exact Or.inr (hB1B2.mpr hB2)

/-
(A1 → B1) ↔ (A2 → B2)
-/

theorem lavrov_mathlog_2_01_16d (A1 A2 B1 B2 : Prop):
    ((A1 ↔ A2) ∧ (B1 ↔ B2)) → ((A1 → B1) ↔ (A2 → B2)) := by
    intro hA1A2B1B2
    cases hA1A2B1B2 with
        | intro hA1A2 hB1B2 =>
            constructor
            ·   intro hA1B1
                intro hA2
                exact hB1B2.mp (hA1B1 (hA1A2.mpr hA2))
            ·   intro hA2B2
                intro hA1
                exact hB1B2.mpr (hA2B2 (hA1A2.mp hA1))
end lavrov_mathlog_2_01_16

namespace lavrov_mathlog_2_01_19

/-
(P ∧ (Q ∧ R)) ↔ ((P ∧ Q) ∧ R)
-/
theorem lavrov_mathlog_2_01_19c (P Q R : Prop):
    (P ∧ (Q ∧ R)) ↔ ((P ∧ Q) ∧ R) := by
    constructor
    ·   intro hPQR
        cases hPQR with
        | intro hP hQR =>
            exact And.intro (And.intro hP hQR.left) hQR.right
    ·   intro hPQR
        cases hPQR with
        | intro hPQ hR =>
            exact And.intro hPQ.left  (And.intro hPQ.right hR)

/-
(P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
-/
theorem lavrov_mathlog_2_01_19d (P Q R : Prop):
    (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
    constructor
    ·   intro hPQR
        cases hPQR with
        | intro hP hQR =>
            cases hQR with
            | inl hQ => exact Or.inl (And.intro hP hQ)
            | inr hR => exact Or.inr (And.intro hP hR)
    ·   intro hPQPR
        cases hPQPR with
        | inl hPQ =>
            constructor
            · exact hPQ.left
            · exact Or.inl hPQ.right
        | inr hPR =>
            constructor
            · exact hPR.left
            · exact Or.inr hPR.right

end lavrov_mathlog_2_01_19
