import tactic
import .basic
import ..subtype.helpers

open_locale classical

variables {T : Type*} [pregeom T]

namespace pregeom
namespace basis

open has_cl

def is_indep (S : set T) := ∀ {x : T}, x ∈ S → x ∉ cl (S - {x})
def is_spanning (S : set T) := ∀ t : T, t ∈ cl S
def is_basis (S : set T) := is_indep S ∧ is_spanning S


@[simp]
lemma super_spans {A B : set T} {spans : is_spanning A} (le : A ≤ B): is_spanning B :=
begin
  unfold is_spanning at *,
  have mono: cl A ≤ cl B, by exact pregeom.monotone le,
  intro t,
  replace spans := spans t,
  exact mono spans,
end

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

lemma subtract_spanning {t : T} {S : set T} : is_spanning S → t ∈ cl (S - {t}) → is_spanning (S - {t}) :=
begin
  intros spanning ht,
  unfold is_spanning,
  intro u,
  have sets : {t} ⊆ cl (S - {t}), by simpa,
  have pull_in := cl_union_eq sets,
  rw ← pull_in,
  simp,
  have hu : u ∈ cl S, by exact spanning u,
  have le : S ≤ insert t S, by
  {
    intros s hs,
    exact set.mem_insert_of_mem t hs,
  },
  apply pregeom.monotone le,
  assumption,
end

theorem basis_iff_minimal_spanning {S : set T} :
  is_basis S ↔ 
  is_spanning S ∧ (∀ S' : set T, S' ≤ S → is_spanning S' → S = S') := 
begin
  split,
  {
    intro basis,
    refine ⟨ basis.2, _ ⟩,
    intros S' le spanning,
    tidy,
    by_contradiction contra,

    have remove : S' ≤ S - {x}, by exact smaller le contra,
    have smaller_spans: is_spanning (S - {x}),
    {
      apply super_spans remove,
      exact spanning,
    },
    have x_seperate: x ∉ cl (S - {x}), by
    {
      unfold is_indep at basis_left,
      replace basis_left := basis_left a,
      exact basis_left,
    },
    have x_included: x ∈ cl (S - {x}), by
    {
      unfold is_spanning at smaller_spans,
      replace smaller_spans := smaller_spans x,
      exact smaller_spans,
    },
    contradiction,
  },
  {
    intro h,
    cases h with spans inf,
    unfold is_basis,
    refine ⟨ _, spans⟩,
    unfold is_indep,
    intros x hx,
    intro contra,
    have lt : S - {x} ≤ S, by
    {
      intros t ht,
      finish,
    },
    replace inf := inf (S - {x}) lt,
    suffices : is_spanning (S - {x}), by 
    {
      replace inf := inf this,
      have problem: ¬ S = S - {x}, by exact missing_elem S hx,
      contradiction,
    },
    exact subtract_spanning spans contra,
  }
end

theorem exists_basis : ∃ S : set T, is_basis S := sorry 

end basis
end pregeom
