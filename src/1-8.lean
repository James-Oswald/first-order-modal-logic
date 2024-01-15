
import src.«1-6-1»

def valid (M : Model) (φ : PMF) : Prop := ∀ w : M.ℱ.ℐ, (⟨M, w⟩ : MWP) ⊩ φ

def reflexive (F : Frame) : Prop := ∀ w : F.ℐ, F.ℛ w w
def symmetric (F : Frame) : Prop := ∀ w v : F.ℐ, F.ℛ w v → F.ℛ v w
def transitive (F : Frame) : Prop := ∀ u v w : F.ℐ, F.ℛ u v → F.ℛ v w → F.ℛ u w
def serial (F : Frame) : Prop := ∀ w : F.ℐ, ∃ v : F.ℐ, F.ℛ w v

--Exersizes
/-
1.8.1 Show □P ⊃ ⋄P is valid in all serial models.
-/
example (M : Model) (P : PMF): serial M.ℱ -> valid M (□P ⊃ ⋄P) := by
  intro H
  simp [valid, Forces.forces, val]
  intros w H2
  simp [serial] at H
  have ⟨w2, H3⟩ := H w
  have H4 := H2 w2 H3
  exists w2

/-
1.8.2 Show that a frame is transitive iff every formula of the form
□P ⊃ □□P is valid in it.
-/
example (M : Model) (P : PMF) : transitive M.ℱ ↔ valid M (□P ⊃ □□P) := by
  apply Iff.intro
  . intro H
    simp [valid, Forces.forces, val]
    intros w H2 w2 H3 w3 H4
    simp [transitive] at H
    have H5 := H w w2 w3
    exact H2 w3 (H5 H3 H4)
  . intro H
    simp [valid, Forces.forces, val] at H
    simp [transitive]
    intros w w2 w3 H2 H3
    have H4 := H w
    sorry
