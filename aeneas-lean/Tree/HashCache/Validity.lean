import Tree.HashCache

open Aeneas Aeneas.Std Result

namespace milhouse

/-- A stored hash is either the invalidated zero sentinel or the mathematical
reference hash of its logical input. The reference function fixes the packing
layout and hash specification. This predicate does not replace the Rust hash
computation or assert that it has been extracted or proved. -/
def CacheValidFor {T : Type} (reference : CacheSubject T → CacheHash)
    (subject : CacheSubject T) (cached : CacheHash) : Prop :=
  cached = Array.repeat 32#usize 0#u8 ∨ cached = reference subject

theorem CacheValidFor.zero {T : Type} (reference : CacheSubject T → CacheHash)
    (subject : CacheSubject T) : CacheValidFor reference subject (Array.repeat 32#usize 0#u8) :=
  Or.inl rfl

end milhouse
