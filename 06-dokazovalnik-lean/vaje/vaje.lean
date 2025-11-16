-- Strukture:

-- (A x B) ^ C <=> A ^ C x B ^ C
def eksponent (A B C : Type) (f : C → Prod A B) : Prod (C → A) (C → B) :=
  ⟨
    fun c => (f c).fst,
    fun c => (f c).2
  ⟩

def eksponent' (A B C : Type) (f : C → Prod A B) : Prod (C → A) (C → B) :=
  ⟨
   fun c => (f c).1,
   fun c => (f c).snd
  ⟩

def eksponent_prop (A B C : Prop) (f : C → A ∧ B) : (C → A) ∧ (C → B) :=
  ⟨
    fun c => (f c).1,
    fun c => (f c).2
  ⟩

#check And.intro

def eksponent_prop_s_taktikami (A B C : Prop) (f : C → A ∧ B) : (C → A) ∧ (C → B) :=
  by
    apply And.intro
    · intro h
      have h1 := f h
      exact h1.left
    · intro h
      exact (f h).right

-- ------------------------------
-- Logika

#check Iff.intro

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    apply Iff.intro
    · intro h
      apply And.intro
      · exact h.2
      · exact h.1
    · intro h
      apply And.intro
      · exact h.right
      · exact h.left


theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  by
    apply Iff.intro
    · intro h
      apply Or.elim h
      · exact Or.inr
      · exact Or.inl
    · intro h
      apply Or.elim h
      · exact Or.inr
      · exact Or.inl


theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact h.right.left
    · apply And.intro
      · exact h.left
      · exact h.right.right
  · intro h
    apply And.intro
    · exact h.right.left
    · apply And.intro
      · exact h.left
      · exact h.right.right


theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) := by
  apply Iff.intro
  · intro h
    cases h
    · case inl a => exact Or.inr (Or.inl a)
    · case inr bc =>
      cases bc
      · case inl b => exact Or.inl b
      · case inr c =>  exact Or.inr (Or.inr c)
  · intro h
    cases h
    · case inl b => exact Or.inr (Or.inl b)
    · case inr ac =>
      cases ac
      · case inl a => exact Or.inl a
      · case inr c =>  exact Or.inr (Or.inr c)


theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  apply Iff.intro
  · intro h
    cases h.2
    · case inl b => exact Or.inl (And.intro h.1 b)
    · case inr c => exact Or.inr (And.intro h.left c)
  · intro h
    cases h
    · case inl ab =>
      apply And.intro
      · exact ab.left
      · exact Or.inl ab.right
    · case inr ac =>
      apply And.intro
      · exact ac.1
      · exact Or.inr ac.right


theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) := by
  apply Iff.intro
  · intro h
    apply And.intro -- constructor
    · intro hb
      apply h
      left
      assumption
    · intro hc
      apply h
      right
      assumption
  · intro h
    intro hbc
    cases hbc
    · case inl b => exact h.1 b
    · case inr c => exact h.2 c


theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hc
      exact (h hc).1
    · intro hc
      exact (h hc).2
  · intro h
    intro hc
    apply And.intro
    · exact h.1 hc
    · exact h.2 hc


-- ------------------------------
-- Enakosti naravnih števil (z uporabo `calc`)

#check Nat.add_mul

theorem kvadrat_dvoclenika {a b : Nat} : (a + b)^2 = a^2 + 2 * a * b + b^2 :=
  by
    calc
      (a + b)^2
      _ = (a + b) * (a + b) := by rw [Nat.pow_two]
      _ = (a + b) * a + (a + b) * b := by rw [Nat.mul_add]
      _ = a * a + b * a + (a + b) * b := by rw [Nat.add_mul]
      _ = a * a + b * a + (a * b + b * b) := by rw [Nat.add_mul]
      _ = a^2 + b * a + (a * b + b^2) := by rw [← Nat.pow_two, ← Nat.pow_two]
      _ = a^2 + (b * a + (a * b + b^2)) := by rw [Nat.add_assoc]
      _ = a^2 + (a * b + (a * b + b^2)) := by rw [Nat.mul_comm]
      _ = a^2 + (a * b + a * b + b^2) := by rw [Nat.add_assoc]
      _ = a^2 + (2 * (a * b) + b^2) := by rw [← Nat.two_mul]
      _ = a^2 + (2 * a * b + b^2) := by rw [← Nat.mul_assoc]
      _ = a^2 + 2 * a * b + b^2 := by rw [← Nat.add_assoc]


theorem vsota_eksponent_produkta {a b c d : Nat} : (a * b)^(c + d) = (a^c)*(a^d)*(b^c)*(b^d) :=
  by
    calc
      (a * b)^(c + d)
      _ = a^(c + d) * b^(c + d) := by rw [Nat.mul_pow]
      _ = a^c * a^d * (b^c * b^d) := by rw [Nat.pow_add, Nat.pow_add]
      _ = a^c * a^d * b^c * b^d := by rw [← Nat.mul_assoc]
