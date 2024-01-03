import src.«1-3»

/-
To solve 1.5.1 need some basic notion of truth over a
propositional modal formulae with respect to a truth functional
definition of the box. This function provides that semantics.
it takes an interpetation (string->Prop), and a truth function for box
(Prop->Prop) and a modal formulae and computes the truth value of the
formulae.
-/
def sat (i : String->Bool) (btf : Bool->Bool): PMF->Bool
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
def thesis (btf : Bool->Bool) (φ : PMF): Prop :=
∀(i : String->Bool), sat i btf φ

/-
Exersize 1.5.1:
There are four truth table definable functions of a single input
1) Show that we can def a truth functional operator □ for which
□P ⊃ P is a thesis but P ⊃ □P is not.
-/
example:
∃(btf : Bool->Bool), (thesis btf (□P ⊃ P)) ∧ ¬(thesis btf (P ⊃ □P)) := by {
  apply Exists.intro (λ_=>false); --The function that always returns false
  simp [thesis];
  apply And.intro;
  intro i;
  simp [sat];
  intro H;
  have H2 := H (λ_=>true); --Countermodel
  simp [sat] at H2;
}

#check Not

--Partially constructavist Solution
example:
∃(btf : Bool->Bool), (thesis btf (□P ⊃ P)) ∧ ¬(thesis btf (P ⊃ □P)) :=
Exists.intro
  (λ_=>false)
  (And.intro
    (λ _ => by simp [thesis, sat])
    (λ H => by
      simp [thesis] at H
      have H2 := H (λ_=>true)
      simp [sat] at H2;
    )
  )

/-
2) Show that if we ALSO require ¬□P to not be a thesis, no truth functional
operator will do.
-/

/-
I orignally read the question wrong and tried to prove
"There does not exist a truth functional operator btf such that ¬□P is a thesis"
¬∃(btf : Bool->Bool), (thesis btf ¬□P)
but in realty, there does exist a truth functional operator btf such that ¬□P is a thesis,
that being (λ_=>false).
∃(btf : Bool->Bool), (thesis btf ¬□P)
-/
example (P : PMF) : ∃(btf : Bool->Bool), thesis btf ¬□P := by
  exists (λ_=>false)
  simp [thesis, sat]

/-
I read it wrong AGAIN (if forgot the also) and tried to prove
"There does not exist a truth functional operator btf such that ¬□P is not a thesis"
¬∃(btf : Bool->Bool), ¬thesis btf ¬□P
which is logically equivalent to
"For every truth functional operator btf, ¬□P is a thesis"
∀(btf : Bool->Bool), thesis btf ¬□P
but this is obviously false, as we prove below via the counterexample
(λ_=>true)
-/
example (P : PMF) : ¬∀(btf : Bool->Bool), thesis btf ¬□P := by
  simp [thesis, sat]
  intro H
  have H2 := H (λ_=>true) (λ_=>true)
  simp [sat] at H2

/-
For real this time
-/
example (P : PMF) :
¬∃(btf : Bool->Bool), (thesis btf (□P ⊃ P)) ∧ (¬thesis btf (P ⊃ □P)) ∧ (¬thesis btf ¬□P) := by
  intro ⟨w, H⟩
  have ⟨H1, H2, H3⟩ := H
  simp [thesis, sat] at H1 H2 H3
  simp [Not] at H2 H3;
  apply H3
  intro i;
  apply Classical.byContradiction;
  intro H4;
  simp at H4;
  apply H2;
  intro i2 H6;
  have H5 := H1 i H4;
  simp [H5] at H4
  simp [H5, H6, H4]
  --QED What a proof!

/-
Exersize 1.5.2: Suppose every world is accessible to every other world.
Would 1.3 (⋄P ⊃ □⋄P) be valid (a thesis)? Discuss informally.
