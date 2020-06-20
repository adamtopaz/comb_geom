import data.set
import .basis
import .basic

/-!
# What is going on here?

Here we define the notion of spanning, independence, and basis for a family of terms in a pregeometry.
By a family, we just mean a function `ι : S → T` from some other type `S`.

The following lemmas help in going back and forth between the definitions here and those in `src/pregeom/basis.lean`:
1. `spanning_iff_range_spanning` says that `ι` spans if and only if its image does.
2. `indep_iff_injective_range_indep` says that `ι` is independent if and only if `ι` is injective and its image is independent.
3. `basis_iff_injective_range_basis` says that `ι` is a basis if and only if `ι` is injective and its image is a basis.

-/

open_locale classical

variables {T : Type*} 
variables {S : Type*} (ι : S → T)

namespace pregeom
namespace basis_family

open set
open function

/-- The restriction of ι to the complemenet of {x}. -/
def res (x : S) : {y : S // y ≠ x} → T := λ ⟨y,_⟩, ι y

/-- Independence for a family. -/
def is_indep [has_cl T] : Prop := ∀ x : S, ι x ∉ cl (range $ res ι x)

/-- Spanning condition for a family. -/
def is_spanning [has_cl T] : Prop := ∀ t : T, t ∈ cl (range ι)

/-- Definition of a basis for a family. -/
def is_basis [has_cl T] : Prop := is_indep ι ∧ is_spanning ι

variable {ι}

/-- If ι is injective, then the image of the restriction of ι to the complement of s is
the complement of ι s in the image of ι. -/
lemma range_res_eq_sub_range_of_injective {s : S} : injective ι → range (res ι s) = range ι \ {ι s} := 
begin
  intro h,
  ext, refine ⟨by tidy, _⟩,
  rintro ⟨⟨y,rfl⟩,h2⟩,
  use y,
  repeat {finish},
end

variable [pregeom T]

/-- If ι is independence, then ι is injective. -/
theorem injective_of_indep : is_indep ι → injective ι :=
begin
  intro indep,
  intros y x h,
  by_contradiction contra,
  replace indep := indep x,
  have : ι y ∈ range (res ι x), by exact ⟨⟨y,contra⟩, by finish⟩,
  rw h at this,
  replace this := inclusive this,
  contradiction,
end

/-- ι spans if and only if its image spans. -/
theorem spanning_iff_range_spanning : is_spanning ι ↔ basis.is_spanning (range ι) := by tauto

/-- ι is independent if and only if ι is injective and its image is independent. -/
theorem indep_iff_injective_range_indep : is_indep ι ↔ injective ι ∧ basis.is_indep (range ι) := 
begin
  split,
  {
    intro h,
    have c1 := injective_of_indep h,
    refine ⟨c1,_⟩,
    rintros _ ⟨y,rfl⟩,
    replace h := h y,
    change _ ∉ cl (range ι \ _),
    rwa ←range_res_eq_sub_range_of_injective c1,
  },
  {
    rintros ⟨h1,h2⟩,
    intro s,
    rw range_res_eq_sub_range_of_injective h1,
    apply h2,
    use s,
  }
end

/-- ι is a basis if and only if ι is injective and its image is a basis.
This can be used to go back and forth between the definition of bases for sets and for families.
 -/
theorem basis_iff_injective_range_basis : is_basis ι ↔ injective ι ∧ basis.is_basis (range ι) :=
begin
  split,
  {
    rintro ⟨h1,h2⟩,
    rw indep_iff_injective_range_indep at h1,
    exact ⟨h1.1,⟨h1.2,h2⟩⟩,
  },
  {
    rintro ⟨h1,h2,h3⟩,
    refine ⟨_,h3⟩,
    rw indep_iff_injective_range_indep,
    finish,
  }
end

end basis_family
end pregeom