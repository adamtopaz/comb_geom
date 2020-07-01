import set_theory.cardinal
import .basis
import data.finset

open_locale big_operators
open_locale classical

namespace pregeom
namespace dimension

open basis

variables {T : Type*} [pregeom T]


/-
  Independent set t1,...,tn, and a spanning set w1,...,wm, then n <= m, and ∃ W' ⊆ W, T ∪ W' spans
-/

private lemma has_elem_of_nonempty {S : set T} (hs : S ≠ ∅) : ∃ s : T, s ∈ S :=
begin
  by_contradiction contra,
  rw not_exists at contra,
  have Sempty : S = ∅, by
  { ext,
    split,
    intro hx,
    specialize contra x,
    contradiction,
    intro hx,
    exfalso,
    exact hx, },
  exact hs Sempty,
end

/-
  The dimension of a pregeometry T is the minimum cardinality over all the bases of T.
  This is well-defined, as every pregeometry has a basis.
-/
noncomputable def pregeom.dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (@pregeom.basis.exists_basis T _))
  (λ S, cardinal.mk S.val)

/-
  Precursor to the dimension theorem. The cardinality of any basis is less than or equal
  to the cardinality of any other spanning set.
-/
theorem basis_card_le_spanning_card {B1 B2 : set T} (hb1 : is_basis B1) (hb2 : is_spanning B2)
  : B1 ≠ ∅ → cardinal.mk B1 ≤ cardinal.mk B2 := λ h,
begin 
  by_contradiction contra,
  rw not_le at contra,
  have claim : ∀ (t : T), ∃ S : finset T, S ≠ (∅ : finset T) ∧ ↑S ≤ B1 ∧ t ∈ cl (↑S : set T),
  {
    intro t,
    rcases finchar (hb1.2 t) with ⟨S,h1,h2⟩,
    by_cases hS : S = ∅,
    {
      rw hS at *,
      rw finset.coe_empty at *,
      have : ∃ b : T, b ∈ B1, by exact has_elem_of_nonempty h,
      cases this with b hb,
      use insert b (∅ : finset T),
      exact ⟨by tidy ,by tidy,monotone (by tidy) h2⟩,
    },
    { exact ⟨S,hS,h1,h2⟩, }
  }
  --set family := λ t, classical.indefinite_description _ (claim t),
  --set family : B2 → set T := λ (t : B2), ↑(classical.some (claim t)),
  --set E := ⋃ j, (↑(family j).val : set T),
  --have E_le_B1 : E ≤ B1,
  --{ intros e he,
  --  rcases he with ⟨U,⟨b,rfl⟩,he⟩,
  --  exact (family b).2.1 he, },
  --cases le_or_lt cardinal.omega (cardinal.mk B2) with hO hO,
  sorry,
end

/-
  The dimension theorem, every basis of a pregeometry has the same cardinality.
-/
theorem basis_card_eq_basis_card {B1 B2 : set T} (hb1 : is_basis B1) (hb2 : is_basis B2)
  : cardinal.mk B1 = cardinal.mk B2 :=
  le_antisymm (basis_card_le_spanning_card hb1 hb2.right) (basis_card_le_spanning_card hb2 hb1.right)

end dimension
end pregeom