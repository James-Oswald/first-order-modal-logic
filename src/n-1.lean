--Propositional Tableux

import src.LogicSymbolOverloads

--The inductive type for propositional formulae
inductive PF where
| Atom : String -> PF
| And : PF -> PF -> PF
| Or : PF -> PF -> PF
| Not : PF -> PF
| Implies : PF -> PF -> PF
| Iff : PF -> PF -> PF
deriving BEq

--The following instances are used to overload the logic operators
instance : Land PF := ⟨PF.And⟩
instance : Lor PF := ⟨PF.Or⟩
instance : Lif PF := ⟨PF.Implies⟩
instance : Liff PF := ⟨PF.Iff⟩
instance : Lnot PF := ⟨PF.Not⟩

def sat (v: String->Bool) : PF -> Bool
| (PF.Atom s) => v s
| (PF.And p q) => sat v p && sat v q
| (PF.Or p q) => sat v p || sat v q
| (PF.Not p) => !sat v p
| (PF.Implies p q) => sat v p -> sat v q
| (PF.Iff p q) => sat v p <-> sat v q

def valid (ϕ : PF) : Prop := ∀ (v : String → Bool), sat v ϕ = true

--Two formulae are contradictory if one is the negation of the other
--O(n) on the size of the formulae (due to the == operator)
def contradictory (φ ψ : PF) : Bool :=
match ψ with
| (PF.Not ϕ) => ϕ == φ
| _ => false
||
match φ with
| (PF.Not ϕ)=> ϕ == ψ
| _ => false

--O(n^2) contradiction check on a branch
def branchContradiction (branch : List PF) : Bool :=
branch.any (λ ϕ => branch.any (λ ψ => contradictory ϕ ψ))


--This was a NOT dumb idea, but it was a bad idea
-- def PF.depth : PF -> Nat
-- | (PF.Atom _) => 0
-- | (PF.And p q) => 1 + Nat.max (depth p) (depth q)
-- | (PF.Or p q) => 1 + Nat.max (depth p) (depth q)
-- | (PF.Not p) => 1 + depth p
-- | (PF.Implies p q) => 1 + Nat.max (depth p) (depth q)
-- | (PF.Iff p q) => 1 + Nat.max (depth p) (depth q)

-- def ListPFDepth : List PF -> Nat
-- | [] => 0
-- | h::t => Nat.max h.depth (ListPFDepth t)

-- def tableuxAux (branch : List PF) : Bool :=
-- match branch with
-- | [] => false
-- | h::t =>
--   match h with
--   --Atomic Rules
--   | (PF.Atom _) => branchContradiction branch
--   | (PF.Not (PF.Atom _)) => branchContradiction branch
--   --Conjunctive Rules
--   | (PF.And p q) => tableuxAux (p::q::t)
--   | (PF.Not (PF.Or p q)) => tableuxAux ((PF.Not p)::(PF.Not q)::t)
--   | (PF.Not (PF.Implies p q)) => tableuxAux (p::(PF.Not q)::t)
--   | (PF.Iff p q) => tableuxAux ((PF.Implies p q)::(PF.Implies q p)::t)
--   --Disjunctive Rules
--   | (PF.Or p q) => tableuxAux (p::t) && tableuxAux (q::t)
--   | (PF.Not (PF.And p q)) => tableuxAux ((PF.Not p)::t) && tableuxAux ((PF.Not q)::t)
--   | (PF.Implies p q) => tableuxAux ((PF.Not p)::t) && tableuxAux (q::t)
--   | (PF.Not (PF.Iff p q)) => tableuxAux ((PF.Implies p q)::t) && tableuxAux ((PF.Implies q p)::t)
--   --Negation Rule
--   | (PF.Not (PF.Not p)) => tableuxAux (p::t)


noncomputable def tableuxAux (branch : List PF) : PF -> Bool
--Atomic Rules
| (PF.Atom _) => branchContradiction branch
| (PF.Not (PF.Atom _)) => branchContradiction branch
--Conjunctive Rules
| (PF.And p q) => tableuxAux (p::q::branch) p
| (PF.Not (PF.Or p q)) => tableuxAux ((PF.Not p)::(PF.Not q)::t)
| (PF.Not (PF.Implies p q)) => tableuxAux (p::(PF.Not q)::t)
| (PF.Iff p q) => tableuxAux ((PF.Implies p q)::(PF.Implies q p)::t)
--Disjunctive Rules
| (PF.Or p q) => tableuxAux (p::t) && tableuxAux (q::t)
| (PF.Not (PF.And p q)) => tableuxAux ((PF.Not p)::t) && tableuxAux ((PF.Not q)::t)
| (PF.Implies p q) => tableuxAux ((PF.Not p)::t) && tableuxAux (q::t)
| (PF.Not (PF.Iff p q)) => tableuxAux ((PF.Implies p q)::t) && tableuxAux ((PF.Implies q p)::t)
--Negation Rule
| (PF.Not (PF.Not p)) => tableuxAux (p::t)
