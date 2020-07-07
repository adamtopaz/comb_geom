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

--theorem strong_exchange {A B : finset T} {S : set T} : ↑A ≤ cl (↑B ∪ S) → ↑A ∩ cl S = ∅ → ↑B ≤ cl (↑A ∪ S) := sorry

/-
  The cardinality of a finite independent set is bounded above by the cardinality of a spanning set.
-/
theorem ind_card_le_spanning_card 
  (F : finset T) (S : set T) : is_indep (↑F : set T) → is_spanning S → (cardinal.mk ↥(↑F : set T) ≤ cardinal.mk S) := 
begin
  revert F,
  refine finset.induction _ _,
  {
    intros,
    change cardinal.mk (∅ : set T) ≤ _,
    rw cardinal.mk_emptyc,
    exact zero_le (cardinal.mk ↥S),
  },
  {
    intros a F ha ind hIndep hSpanning,
    have : is_indep (↑F : set T), by 
    {
      have claim : (↑F : set T) ≤ (↑(insert a F) : set T), by 
      {
        -- NOTE by not specifying the target of the coercion, this was made a lot harder.
        -- As soon as "set T" is specified, it's easy.
        rw finset.coe_insert,
        apply set.subset_insert,
      },
      exact indep_of_le_indep claim hIndep,
    },
    sorry,
  }
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
  have finite_generator : ∀ (t : T), ∃ S : finset T, S ≠ (∅ : finset T) ∧ ↑S ≤ B1 ∧ t ∈ cl (↑S : set T),
  { intro t,
    rcases finchar (hb1.2 t) with ⟨S,h1,h2⟩,
    by_cases hS : S = ∅,
    { rw hS at h1 h2,
      have : ∃ b : T, b ∈ B1, by exact has_elem_of_nonempty h,
      cases this with b hb,
      use insert b (∅ : finset T),
      exact ⟨by tidy ,by tidy,monotone (by tidy) h2⟩, },
    { exact ⟨S,hS,h1,h2⟩, } },
  set family := λ t, classical.indefinite_description _ (finite_generator t),
  set E := ⋃ t, (↑(family t).val : set T),
  have E_le_B1 : E ≤ B1, by 
  { intros e he,
    rcases he with ⟨U,⟨b,rfl⟩,he⟩,
    exact (family b).2.2.1 he, },
  cases le_or_lt cardinal.omega (cardinal.mk B2) with hO2 hO2,
  { -- Infinite case
    cases le_or_lt cardinal.omega (cardinal.mk B1) with hO1 hO1,
    {
      sorry,
    },
    { have problem := not_le.mpr (gt_of_ge_of_gt hO2 hO1),
      replace contra := le_of_lt contra,
      exact problem contra, }, },
  { -- Finite case
    -- We use that B2 is a spanning set smaller than B1, together with exhange, to get a proper subset C of B1 that spans.
    -- This is the hard part.
    have small_spanner : ∃ C : set T, is_spanning C ∧ C < B1, by sorry,
    cases small_spanner with C hc,
    -- The set C is a strict subset of B1, and thus not equal to it
    have CneS : C ≠ B1, by 
    { intro contra,
      exact ne_of_lt hc.right contra, },
    -- On the other hand, B1 is a basis, and therefore a minimal spanning set. Hence C = B1
    have CeqS : C = B1, by 
    { rw basis_iff_minimal_spanning at hb1,
      replace hb1 := hb1.right,
      specialize hb1 C,
      have claim : C ≤ B1, by 
      { intros x hx,
        exact hc.right.left hx, },
      symmetry,
      exact hb1 claim hc.left, },
    -- So C = B1 and C ≠ B1
    contradiction, },
end


theorem basis_empty_of_basis_empty {B1 B2 : set T} (hb1 : is_basis B1) (hb2 : is_basis B2)
  : B1 = ∅ → B2 = ∅ :=
begin
  intro b1e,
  have b2smaller : B1 ≤ B2, by finish,
  rw basis_iff_minimal_spanning at hb2,
  replace hb2 := hb2.2,
  specialize hb2 B1,
  rw ← b1e,
  exact hb2 b2smaller hb1.2,
end


/-
  The dimension theorem, every basis of a pregeometry has the same cardinality.
-/
theorem basis_card_eq_basis_card {B1 B2 : set T} (hb1 : is_basis B1) (hb2 : is_basis B2)
  : cardinal.mk B1 = cardinal.mk B2 :=
begin
  by_cases B1 = ∅,
  { have b2e : B2 = ∅ := basis_empty_of_basis_empty hb1 hb2 h,
    have he : B1 = B2, by finish,
    rwa he, },
  { have b2ne : B2 ≠ ∅, by
    { intro contra,
      exact h (basis_empty_of_basis_empty hb2 hb1 contra)},
    apply le_antisymm,
    exact basis_card_le_spanning_card hb1 hb2.2 h,
    exact basis_card_le_spanning_card hb2 hb1.2 b2ne, },
end
  

end dimension
end pregeom