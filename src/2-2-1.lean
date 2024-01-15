
import src.«1-6-1»

def Prefix : Type := List Nat
deriving BEq

instance : Repr Prefix where
  reprPrec
  | σ =>

--A prefixed modal formula
structure pPMF where
  pre : Prefix
  formula : PMF
  expanded : Bool

--Two pPMFs are contradictory if they share a prefix and one is the negation of the other
def pPMF.contradictory (pφ pψ : pPMF) : Bool :=
match pψ with
| ⟨σ, (PMF.Not ψ), _⟩ => σ == pφ.pre && ψ == pφ.formula
| _ => false
||
match pφ with
| ⟨σ, (PMF.Not φ), _⟩ => σ == pψ.pre && φ == pψ.formula
| _ => false

inductive tProof
| conjunct : List pPMF → tProof → tProof
| disjunct : List pPMF → tProof → tProof → tProof


def prove (ϕ : PMF) : Bool := sorry
