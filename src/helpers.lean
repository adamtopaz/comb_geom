import data.set

variables {T : Type*} {S : set T}

namespace helpers

lemma smaller {A B: set T} {x : T} (le : A ≤ B) (hx : x ∉ A): A ≤ B \ {x} :=
begin
  intros a ha,
  simp,
  split,
  exact le ha,
  intro contra,
  finish,
end

lemma missing_elem (A : set T) {x : T} (hx : x ∈ A): ¬ (A = A \ {x}) :=
begin
  intro,
  have : ∀ t : T, t ∈ A ↔ t ∈ A - {x}, by
  { change ∀ _, _ ↔ _ ∈ A \ {x},
    rw ←a,
    tauto, },
  replace this := (this x).mp hx,
  finish,
end

end helpers