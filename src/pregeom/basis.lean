import .basic

open_locale classical

variables {T : Type*} [pregeom T]

namespace pregeom
namespace basis

open has_cl

def is_indep (S : set T) := ∀ {x : T}, x ∈ S → x ∉ cl (S - {x})
def is_spanning (S : set T) := ∀ x : T, x ∈ cl S
def is_basis (S : set T) := is_indep S ∧ is_spanning S

theorem basis_iff_maximal_indep {S : set T} : 
  is_basis S ↔ 
  is_indep S ∧ (∀ S' : set T, S ≤ S' → is_indep S' → S = S') := sorry

theorem basis_iff_minimal_spanning {S : set T} :
  is_basis S ↔ 
  is_spanning S ∧ (∀ S' : set T, S' ≤ S → is_spanning S' → S = S') := sorry 

theorem exists_basis : ∃ S : set T, is_basis S := sorry 

end basis
end pregeom
