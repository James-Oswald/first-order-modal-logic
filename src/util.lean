
--Quantifier negation rules
theorem forallneg (p : α->Prop) : (¬∀ a : α, p a) <-> (∃ a : α, ¬p a) := by
  apply Iff.intro
  . intro H
    apply Classical.byContradiction
    intro H2
    apply H
    intro a
    apply Classical.byContradiction
    intro H3
    apply H2
    apply Exists.intro a
    assumption
  . intro ⟨w, H⟩ H2
    have H3 := H2 w
    contradiction

theorem existsneg (p : α->Prop) : (¬∃ a : α, p a) <-> (∀ a : α, ¬p a) := by
  apply Iff.intro
  . intros H a H2
    apply H
    apply Exists.intro a
    assumption
  . intros H H2
    have ⟨w, H3⟩ := H2
    have H4 := H w
    contradiction


theorem notimpnot (A B : Prop) : ¬(A -> ¬B) -> A ∧ B := by
  intro H
  apply Classical.byContradiction
  intro H2
  apply H
  intro H3 H4
  have H5 := And.intro H3 H4
  contradiction
