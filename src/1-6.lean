
import src.LogicSymbolOverloads


inductive PMF {𝒜 : Type} where
| Atom : 𝒜 -> PMF
| And : PMF -> PMF -> PMF
| Or : PMF -> PMF -> PMF
| Not : PMF -> PMF
| Implies : PMF -> PMF -> PMF
| Iff : PMF -> PMF -> PMF
| Box : PMF -> PMF
| Diamond : PMF -> PMF

instance : Land (@PMF α) := ⟨PMF.And⟩
instance : Lor (@PMF α) := ⟨PMF.Or⟩
instance : Lif (@PMF α) := ⟨PMF.Implies⟩
instance : Liff (@PMF α) := ⟨PMF.Iff⟩
instance : Lnot (@PMF α) := ⟨PMF.Not⟩
instance : Box (@PMF α) := ⟨PMF.Box⟩
instance : Diamond (@PMF α) := ⟨PMF.Diamond⟩

structure Frame where
  ℐ : Type --possible worlds
  ℛ : ℐ -> ℐ -> Prop -- accessibility relation
  --ℐ_nonempty : Nonempty ℐ --Textbook says this, not sure we will need it

structure Model where
  ℱ : Frame
  𝒜 : Type --atoms
  𝒯 : ℱ.ℐ -> 𝒜 -> Prop --Truth at a world

-- def sat (ℳ : Model) (Γ : ℳ.ℱ.ℐ) : @PMF ℳ.𝒜 -> Prop :=
-- | PMF.Atom a => ℳ.𝒯 Γ a
