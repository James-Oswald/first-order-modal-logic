
--First failed atempt at formalizing the modal tableux method

import src.«1-6-1»

--A prefixed propositional modal formula
structure pPMF where
  --Def 2.2.1 a prefix is a finite sequence of postive integers, we'll do 0 instead of 1
  pref : List Nat
  formula : PMF
deriving BEq

--Two pPMFs are contradictory if they share a prefix and one is the negation of the other
def pPMF.contradictory (pφ pψ : pPMF) : Bool :=
match pψ with
| ⟨σ, (PMF.Not ψ)⟩ => σ == pφ.pref && ψ == pφ.formula
| _ => false
||
match pφ with
| ⟨σ, (PMF.Not φ)⟩ => σ == pψ.pref && φ == pψ.formula
| _ => false

--This does terminiate, but it's we need a proof
partial def pMF.newPrefix (branch : List pPMF) (σ : List Nat) (depth : Nat := 0): List Nat :=
  let newPrefix := σ ++ [depth];
  if branch.any (λ pφ => pφ.pref == newPrefix) then
    pMF.newPrefix branch σ (depth + 1)
  else
    newPrefix

/-
Returns none if any φs will close the branch, otherwise returns the branch with the φs added
Time Complexity: O(n) where n is the length of the branch, since the size of pφs is at most 2
-/
def closes (pφs : List pPMF) (branch : List pPMF) : Bool :=
  pφs.any (λ pφ => branch.any (λ pψ => pφ.contradictory pψ))

mutual
/-
Auxiliary function for that takes a list of pPMFs and a branch
since len(pφs) == 2,
-/
def conjunctiveAux (pφs : List pPMF) (branch : List pPMF) : Bool :=
  closes pφs branch || pφs.any (λ pφ => tableuxAux pφ (branch ++ pφs.erase pφ))

def disjunctiveAux (lefts rights : List pPMF) (branch : List pPMF) : Bool :=
  (closes lefts branch && closes rights branch) ||
  (lefts.any (λ pφ => tableuxAux pφ (branch ++ rights)) &&
   rights.any (λ pψ => tableuxAux pψ (branch ++ lefts)))

--Auxiliary function for that takes a single pPMF and a branch
def tableuxAux (ϕ : pPMF) (branch : List pPMF): Bool :=
match ϕ with
--Conjunctive rules
| ⟨σ, PMF.And φ ψ⟩  => conjunctiveAux [⟨σ, φ⟩, ⟨σ, ψ⟩] branch
| ⟨σ, PMF.Not (PMF.Or φ ψ)⟩ => conjunctiveAux [⟨σ, ¬φ⟩, ⟨σ, ¬ψ⟩] branch
| ⟨σ, PMF.Not (PMF.Implies φ ψ)⟩ => conjunctiveAux [⟨σ, φ⟩, ⟨σ, ¬ψ⟩] branch
| ⟨σ, PMF.Iff φ ψ⟩  => conjunctiveAux [⟨σ, φ ⊃ ψ⟩, ⟨σ, ψ ⊃ φ⟩] branch
--Disjunctive rules
| ⟨σ, PMF.Or φ ψ⟩  => disjunctiveAux [⟨σ, φ⟩] [⟨σ, ψ⟩] branch
| ⟨σ, PMF.Not (PMF.And φ ψ)⟩ => disjunctiveAux [⟨σ, ¬φ⟩] [⟨σ, ¬ψ⟩] branch
| ⟨σ, PMF.Implies φ ψ⟩  => disjunctiveAux [⟨σ, ¬φ⟩] [⟨σ, ψ⟩] branch
| ⟨σ, PMF.Not (PMF.Iff φ ψ)⟩ => disjunctiveAux [⟨σ, ¬(φ ⊃ ψ)⟩] [⟨σ, ¬(ψ ⊃ φ)⟩] branch
--Negation rule
| ⟨σ, PMF.Not (PMF.Not φ)⟩ => tableuxAux ⟨σ, φ⟩ branch
--Possibility rules
| ⟨σ, PMF.Diamond φ⟩  => sorry
| ⟨σ, PMF.Not (PMF.Box φ)⟩ => sorry
--Nessesity rules
| ⟨σ, PMF.Box φ⟩  => sorry
| ⟨σ, PMF.Not (PMF.Diamond φ)⟩ => sorry
--Atomic rule (If we have reached an atom that does not close the branch,
--then the branch is open, and serves as a countermodel)
| ⟨σ, PMF.Atom _⟩ => false
| ⟨σ, PMF.Not (PMF.Atom _)⟩ => false
end
