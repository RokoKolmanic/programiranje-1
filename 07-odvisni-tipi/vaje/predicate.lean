
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

theorem eq1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
    apply Iff.intro
    · intro h
      intro x
      intro px
      apply h
      exact ⟨ x, px ⟩
    · intro h
      intro hn
      obtain ⟨ x, h1⟩ := hn
      specialize h x
      exact h h1


theorem eq2 : (r → ∀ x, p x) ↔ (∀ x, r → p x) := by
  apply Iff.intro
  · intro h
    intro x
    intro h1
    specialize (h h1) x
    exact h
  · intro h h1 x
    specialize h x
    exact h h1


theorem eq3 : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  apply Iff.intro
  · intro h
    obtain ⟨ a, h1 ⟩ := h
    obtain ⟨ x, h2 ⟩ := h1
    exact ⟨x, And.intro a h2⟩
  ·

theorem eq4 : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  sorry

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical
#check Classical.byContradiction
#check Classical.em

theorem eq5 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro notForallPx

    apply Classical.byContradiction
    intro notExistsNotPx
    apply notForallPx
    intro x

    apply Classical.byContradiction
    intro notPx

    apply notExistsNotPx
    exact ⟨ x, notPx ⟩

  · intro h1 h2
    obtain ⟨ x, notPx ⟩ := h1
    have h3 := h2 x
    contradiction


theorem eq6 : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
    apply Iff.intro
    · intro h1 x
      sorry -- cases h1 with
    · intro h1
      have h2 := Classical.em r
      cases h2 with
      | inl r1 => sorry --nadajljujem
