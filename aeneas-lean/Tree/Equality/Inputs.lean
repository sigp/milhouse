import Tree.Funs

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- Full `ne` behavior for one input pair, without a law on other values. -/
def NeSpecAt {T : Type} (inst : core.cmp.PartialEq T T) (left right : T) : Prop :=
  ∃ different, inst.ne left right = ok different ∧ (different = false ↔ left = right)

/-- Only the positive-equality implication for one input pair. Neither
termination nor completeness is part of this successful-execution law. -/
def NeSoundAt {T : Type} (inst : core.cmp.PartialEq T T) (left right : T) : Prop :=
  inst.ne left right = ok false → left = right

theorem NeSpecAt.sound {T : Type} {inst : core.cmp.PartialEq T T} {left right : T}
    (hspec : NeSpecAt inst left right) : NeSoundAt inst left right := by
  obtain ⟨different, hcall, hsame⟩ := hspec
  intro hfalse
  have hdifferent : different = false := by simpa [hfalse] using hcall.symm
  exact hsame.mp hdifferent

/-- An element law on pairs reached by the external packed-vector `ne` loop.
Only a false answer requires the law on the remaining pairs. -/
def NeOn {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop) :
    _root_.List (T × T) → Prop
  | [] => True
  | pair :: rest => P pair.1 pair.2 ∧ (inst.ne pair.1 pair.2 = ok false → NeOn inst P rest)

/-- Laws on every supplied pair suffice for the weaker reached-pair scope. -/
theorem NeOn.of_pairs {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (pairs : _root_.List (T × T)) (hpairs : ∀ pair ∈ pairs, P pair.1 pair.2) :
    NeOn inst P pairs := by
  induction pairs with
  | nil => trivial
  | cons pair rest ih =>
    exact ⟨hpairs pair (by simp), fun _ => ih (fun item hitem => hpairs item (by simp [hitem]))⟩

theorem NeOn.of_all {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (hpairs : ∀ left right, P left right) (pairs : _root_.List (T × T)) : NeOn inst P pairs := by
  induction pairs with
  | nil => trivial
  | cons pair rest ih => exact ⟨hpairs pair.1 pair.2, fun _ => ih⟩

theorem NeOn.mono {T : Type} {inst : core.cmp.PartialEq T T} {P Q : T → T → Prop}
    (himp : ∀ left right, P left right → Q left right)
    {pairs : _root_.List (T × T)} (hscope : NeOn inst P pairs) : NeOn inst Q pairs := by
  induction pairs with
  | nil => trivial
  | cons pair rest ih => exact ⟨himp _ _ hscope.1, fun hfalse => ih (hscope.2 hfalse)⟩

end milhouse_models
