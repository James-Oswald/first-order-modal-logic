import src.LogicSymbolOverloads

--Binary connectives
inductive BC where
| and
| or
| implies
| iff

--Def 1.3.1 Propositional Modal Formulae (PMF)
inductive PMF where
| atom : String -> PMF
| not : PMF -> PMF
| bc : PMF -> BC -> PMF -> PMF
| box : PMF -> PMF
| diamond : PMF -> PMF

--Gives us NICE syntax for all the operators
--See LogicSymbolOverloads.lean for the magic
instance : Land PMF := ⟨(PMF.bc · BC.and ·)⟩
instance : Lor PMF := ⟨(PMF.bc · BC.or ·)⟩
instance : Lif PMF := ⟨(PMF.bc · BC.implies ·)⟩
instance : Liff PMF := ⟨(PMF.bc · BC.iff ·)⟩
instance : Lnot PMF := ⟨PMF.not⟩
instance : Box PMF := ⟨PMF.box⟩
instance : Diamond PMF := ⟨PMF.diamond⟩

--Define P and Q to be propositional atoms
--based off their string reprs
def P : PMF := (PMF.atom "P")
def Q : PMF := (PMF.atom "Q")

--Exersize 1.3.1: Prove that (□P ∧ ⋄Q) ⊃ ⋄(P ∧ Q) is a PMF
--from the definition of a PMF

--Check can do this for us.
#check (□P ∧ ⋄Q) ⊃ ⋄(P ∧ Q)
