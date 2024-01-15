

import src.«1-6-1»

/-
Example 1.7.1
Ω ⊩ P <- Γ -> Δ ⊩ Q
-/

inductive W1 where
| Γ | Δ | Ω

open W1
def A1: W1 -> W1 -> Prop
| Γ, Δ => True
| Γ, Ω => True
| _, _ => False

def T1 : W1 -> String -> Prop
| Δ, "P" => True
| Ω, "Q" => True
| _ , _ => False

def M1 : Model := ⟨⟨W1, A1⟩, T1⟩
def P : PMF := PMF.Atom "P"
def Q : PMF := PMF.Atom "Q"

example :
(⟨M1, Δ⟩ : MWP) ⊩ P ∨ Q := by
  simp [Forces.forces, val]
  apply Or.intro_left
  simp [M1, T1]
