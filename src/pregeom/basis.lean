import tactic
import .basic

open_locale classical

variables {T : Type*} [pregeom T]

namespace pregeom
namespace basis

open has_cl

def is_indep (S : set T) := ∀ {x : T}, x ∈ S → x ∉ cl (S - {x})
def is_spanning (S : set T) := ∀ t : T, t ∈ cl S
def is_basis (S : set T) := is_indep S ∧ is_spanning S

lemma insert_indep {t : T} {S : set T} : is_indep S → t ∉ cl S → is_indep (insert t S) := 
begin
  intros h ht,
  by_contradiction,
  unfold is_indep at a,
  rw not_forall at a,
  cases a with z hz,
  simp only [set.mem_insert_iff, set.not_not_mem, set.sub_eq_diff, classical.not_imp] at hz,
  cases hz with h1 h2,
  cases h1,
  {
    rw h1 at *,
    suffices : insert t S - {t} ≤ S,
    {
      replace h2 := monotone this h2,
      contradiction,
    },
    tidy,
  },
  {
    have : insert t S \ {z} = insert t (S \ {z}), by tidy; finish,
    rw this at h2, clear this,
    have : z ∉ cl (S \ {z}), by {apply h, tidy, },
    have bad := exchange h2 this,
    have : insert z (S \ {z}) = S, by tidy; finish,
    rw this at bad,
    contradiction,
  }
end

theorem basis_iff_maximal_indep {S : set T} : 
  is_basis S ↔ 
  is_indep S ∧ (∀ S' : set T, S ≤ S' → is_indep S' → S = S') := 
begin
  split,
  {
    intro h,
    refine ⟨h.1,_⟩,
    intros S' hle hindep,
    suffices : S' ≤ S, by exact le_antisymm hle this,
    intros t ht,
    cases h with h1 h2,
    replace h2 := h2 t,
    by_contradiction contra,
    have claim1 : S ≤ S' - {t}, 
    {
      intros s hs,
      refine ⟨hle hs,_⟩,
      change s ≠ t,
      intro c,
      rw c at hs, 
      contradiction,
    },
    have claim2 : t ∈ cl (S' - {t}), by exact monotone claim1 h2,
    replace hindep := hindep ht, 
    contradiction,
  },
  {
    rintros ⟨h1,h2⟩,
    refine ⟨by assumption,_⟩,
    by_contradiction contra,
    have : ∃ t : T, t ∉ cl S, 
    {
      unfold is_spanning at contra,
      rw not_forall at contra,
      assumption,
    },
    cases this with t ht,
    replace h2 := h2 (insert t S),
    have : S ≤ insert t S, by finish,
    replace h2 := h2 this, clear this,
    have : is_indep (insert t S), by apply insert_indep; assumption,
    replace h2 := h2 @this,
    rw h2 at ht,
    have : t ∈ cl (insert t S),
    {
      apply inclusive,
      simp,
    },
    contradiction,
  }
end

lemma subtract_spanning {t : T} {S : set T} : is_spanning S → t ∈ cl (S - {t}) → is_spanning (S - {t}) := sorry

theorem basis_iff_minimal_spanning {S : set T} :
  is_basis S ↔ 
  is_spanning S ∧ (∀ S' : set T, S' ≤ S → is_spanning S' → S = S') := sorry 

theorem exists_basis : ∃ S : set T, is_basis S := sorry 

end basis
end pregeom
