/-
The file defines typeclasses and notations for
modal logical operators, it is based off a
discussion I've had on Zulip with
Eric Weiser.
-/

--For logical and ∧
class Land (α : Type) : Type where
  land : α → α → α

--For logical or ∨
class Lor (α : Type) : Type where
  lor : α → α → α

--For biconditional ↔
class Liff (α : Type) : Type where
  liff : α → α → α

--For material implication ⊃
class Lif (α : Type) : Type where
  lif : α → α → α

--For not ¬
class Lnot (α : Type) : Type where
  lnot : α → α

--For box □
class Box (α : Type) : Type where
  box : α → α

--For diamond ⋄
class Diamond (α : Type) : Type where
  diamond : α → α

class Forces (α : Type u) (β : Type v) : Type (max u v) where
  forces : α → β → Prop

infixr:65 "∧"  => Land.land
infixr:60 "∨" => Lor.lor
infixl:55 "⊃" => Lif.lif
infix:50 "↔" => Liff.liff
infix:50 "≡" => Liff.liff
infix:30 "⊩" => Forces.forces
notation:max "¬" a:70 => Lnot.lnot a
notation:max "□" a:70 => Box.box a
notation:max "⋄" a:70 => Diamond.diamond a
