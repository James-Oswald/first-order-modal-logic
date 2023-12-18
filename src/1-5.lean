import src.«1-3»

/-
To solve 1.5.1 need some basic notion of truth over a
propositional modal formulae with respect to a truth functional
definition of the box. This function provides that semantics.
it takes an interpetation (string->Prop), and a truth function for box
(Prop->Prop) and a modal formulae and computes the truth value of the
formulae.
-/
def sat (i : String->Prop) (btf : Prop->Prop) : PMF->Prop
| PMF.atom s => i s
| PMF.not φ => ¬(sat i btf φ)
| PMF.bc φ bc ψ => match bc with
  | BC.and => sat i btf φ ∧ sat i btf ψ
  | BC.or => sat i btf φ ∨ sat i btf ψ
  | BC.implies => sat i btf φ -> sat i btf ψ
  | BC.iff => sat i btf φ <-> sat i btf ψ
| PMF.box φ => btf (sat i btf φ)
| PMF.diamond φ => ¬(btf ¬(sat i btf φ))

/-
A PMF φ is a "thesis under a truth functional box operator"
(is valid) if it is true under all assignments of atoms to truth values.
-/
def thesis (btf : Prop->Prop) (φ : PMF): Prop :=
∀(i : String->Prop), sat i btf φ

/-
Exersize 1.5.1:
There are four truth table definable functions of a single input
1) Show that we can def a truth functional operator □ for which
□P ⊃ P is a thesis but P ⊃ □P is not.
-/
example :
∃(btf : Prop->Prop), (thesis btf (□P ⊃ P)) ∧ ¬(thesis btf (P ⊃ □P)) := by {
  apply Exists.intro (λ_=>False); --The function that always returns false
  simp [thesis];
  apply And.intro;
  intro i;
  simp [sat];
  intro H;
  have H2 := H (λ_=>True); --Countermodel
  simp [sat] at H2;
}

/-
2) Show that if we require ¬□P to be a thesis, no truth functional
operator will do.
-/
example (P : PMF) : ¬∃(btf : Prop->Prop), (thesis btf ¬□P) := by {
  intro H;
  have P : ∀(btf : Prop->Prop), thesis btf ¬□P -> False := by {
    intros btf H2;
    simp [thesis, sat] at H2;
    have H3 := H2 (λ_=>True); --Countermodel
    simp [sat, Not] at H3;
    apply H3;
    sorry
  }
  exact Exists.elim H P;
}
