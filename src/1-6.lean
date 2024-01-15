
import src.LogicSymbolOverloads
import src.util

inductive PMF where
| Atom : String -> PMF
| And : PMF -> PMF -> PMF
| Or : PMF -> PMF -> PMF
| Not : PMF -> PMF
| Implies : PMF -> PMF -> PMF
| Iff : PMF -> PMF -> PMF
| Box : PMF -> PMF
| Diamond : PMF -> PMF

instance : Land PMF := ⟨PMF.And⟩
instance : Lor PMF := ⟨PMF.Or⟩
instance : Lif PMF := ⟨PMF.Implies⟩
instance : Liff PMF := ⟨PMF.Iff⟩
instance : Lnot PMF := ⟨PMF.Not⟩
instance : Box PMF := ⟨PMF.Box⟩
instance : Diamond PMF := ⟨PMF.Diamond⟩

structure Frame where
  ℐ : Type --possible worlds
  ℛ : ℐ -> ℐ -> Prop -- accessibility relation
  --ℐ_nonempty : Nonempty ℐ --Textbook says this, not sure we will need it

structure Model where
  ℱ : Frame
  𝒯 : ℱ.ℐ -> String -> Prop --Truth at a world


/-
Extension of truth of an atom at world to truth of formulae at a world
Takes a dependent pair of a model and a world and a formula and returns if
the formula is true at the world
Actual use of a dependent sigma pair type: (ℳ : Model) × ℳ.ℱ.ℐ
-/
def val (ℳxℐ : (ℳ : Model) × ℳ.ℱ.ℐ) (ϕ : PMF) : Prop :=
let ℳ := ℳxℐ.fst
let Γ := ℳxℐ.snd
let ℐ := ℳ.ℱ.ℐ
let ℛ := ℳ.ℱ.ℛ
match ϕ with
| PMF.Atom a => ℳ.𝒯 Γ a
| PMF.And φ ψ => val ℳxℐ φ ∧ val ℳxℐ ψ
| PMF.Or φ ψ => val ℳxℐ φ ∨ val ℳxℐ ψ
| PMF.Not φ => ¬val ℳxℐ φ
| PMF.Implies φ ψ => val ℳxℐ φ → val ℳxℐ ψ
| PMF.Iff φ ψ => val ℳxℐ φ ↔ val ℳxℐ ψ
| PMF.Box φ => ∀(Γ' : ℐ), ℛ Γ Γ' → val ⟨ℳ, Γ'⟩ φ
| PMF.Diamond φ => ∃(Γ' : ℐ), ℛ Γ Γ' ∧ val ⟨ℳ, Γ'⟩ φ

#check (ℳ : Model) × ℳ.ℱ.ℐ

instance : Forces ((ℳ : Model) × ℳ.ℱ.ℐ) PMF := ⟨val⟩

--Exersises
/-
1.6.1: Show that at every possible world Γ of a model model
Γ ⊩ (□X ≡ ¬◇¬X) and Γ ⊩ (◇X ≡ ¬□¬X)
-/
example (ℳxℐ : (ℳ : Model) × ℳ.ℱ.ℐ) (X : PMF): ℳxℐ ⊩ □X ≡ ¬⋄¬X := by
  simp [Forces.forces, val]
  apply Iff.intro
  . intro H
    intro ⟨w, H2⟩
    have H3 := H w H2.left
    have H4 := H2.right
    contradiction
  . intros H w1 H2
    apply Classical.byContradiction
    intro H3
    simp [Not] at H
    apply H
    exact ⟨w1, ⟨H2, H3⟩⟩

example (ℳxℐ : (ℳ : Model) × ℳ.ℱ.ℐ) (X : PMF): ℳxℐ ⊩ ⋄X ≡ ¬□¬X := by
  simp [Forces.forces, val]
  apply Iff.intro
  . intro ⟨w, H⟩ H2
    have H3 := H2 w H.left
    have H4 := H.right
    contradiction
  . intros H
    rw [forallneg] at H
    have ⟨w, H2⟩ := H
    exists w
    apply notimpnot
    assumption

/-
Exersize 1.6.2
Show that if a world Γ of a model has no
worlds accessable to it, than at Γ every formula is nec but none are possible
-/
example  (ℳ : Model) (Γ: ℳ.ℱ.ℐ) (ϕ : PMF):
let ℳxℐ : (ℳ : Model) × ℳ.ℱ.ℐ := ⟨ℳ, Γ⟩
(∀(Γ' : ℳ.ℱ.ℐ), ¬ℳ.ℱ.ℛ Γ Γ') -> (ℳxℐ ⊩ □ϕ) ∧ (ℳxℐ ⊩ ¬⋄ϕ) := by
  intros ℳxℐ H
  simp [Forces.forces, val]
  apply And.intro
  case left =>
    intro Γ'' H2
    have := H Γ''
    contradiction
  case right =>
    intro ⟨w, H2⟩
    have := H2.left
    have := H w
    contradiction
