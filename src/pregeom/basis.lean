import order.zorn
import tactic
import .basic
import ..helpers
import data.set


open_locale classical

variables {T : Type*} [pregeom T]

namespace pregeom
namespace basis

open has_cl

/-- 
A set `S` is independent if for all `x ∈ S`, the element `x` is not contained in

`cl (S - {x})`
-/
def is_indep (S : set T) := ∀ {x : T}, x ∈ S → x ∉ cl (S - {x})

/--
A set `S` is spanning if `∀ t : T, t ∈ cl S`.
-/
def is_spanning (S : set T) := ∀ t : T, t ∈ cl S

/-- A basis is a spanning independent set. -/
def is_basis (S : set T) := is_indep S ∧ is_spanning S


/-- If `A` spans, and `A ≤ B`, then `B` spans. -/
@[simp]
lemma super_spans {A B : set T} {spans : is_spanning A} (le : A ≤ B): is_spanning B :=
begin
  have mono: cl A ≤ cl B, by exact pregeom.monotone le,
  intro t,
  replace spans := spans t,
  exact mono spans,
end

/-- If `S` is independent and `t ∉ cl S` then `insert t S` is independent. -/
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
  { rw h1 at *,
    suffices : insert t S - {t} ≤ S,
    { replace h2 := monotone this h2,
      contradiction, },
    tidy, },
  { have : insert t S \ {z} = insert t (S \ {z}), by tidy; finish,
    rw this at h2, clear this,
    have : z ∉ cl (S \ {z}), by {apply h, tidy, },
    have bad := exchange h2 this,
    have : insert z (S \ {z}) = S, by tidy; finish,
    rw this at bad,
    contradiction, }
end

/-- A basis is a maximal independent set. -/
theorem basis_iff_maximal_indep {S : set T} : 
  is_basis S ↔ 
  is_indep S ∧ (∀ S' : set T, S ≤ S' → is_indep S' → S = S') := 
begin
  split,
  { intro h,
    refine ⟨h.1,_⟩,
    intros S' hle hindep,
    suffices : S' ≤ S, by exact le_antisymm hle this,
    intros t ht,
    cases h with h1 h2,
    replace h2 := h2 t,
    by_contradiction contra,
    have claim1 : S ≤ S' - {t}, 
    { intros s hs,
      refine ⟨hle hs,_⟩,
      change s ≠ t,
      intro c,
      rw c at hs, 
      contradiction, },
    have claim2 : t ∈ cl (S' - {t}), by exact monotone claim1 h2,
    replace hindep := hindep ht, 
    contradiction, },
  { rintros ⟨h1,h2⟩,
    refine ⟨by assumption,_⟩,
    by_contradiction contra,
    have : ∃ t : T, t ∉ cl S, 
    { unfold is_spanning at contra,
      rw not_forall at contra,
      assumption, },
    cases this with t ht,
    replace h2 := h2 (insert t S),
    have : S ≤ insert t S, by finish,
    replace h2 := h2 this, clear this,
    have : is_indep (insert t S), by apply insert_indep; assumption,
    replace h2 := h2 @this,
    rw h2 at ht,
    have : t ∈ cl (insert t S),
    { apply inclusive,
      simp, },
    contradiction, }
end

/-- If `S` spans and `t ∈ cl (S - {t})` then `S - {t}` spans as well. -/
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
  { intros s hs,
    exact set.mem_insert_of_mem t hs, },
  apply pregeom.monotone le,
  assumption,
end

/-- A basis is a minimal spanning set. -/
theorem basis_iff_minimal_spanning {S : set T} :
  is_basis S ↔ 
  is_spanning S ∧ (∀ S' : set T, S' ≤ S → is_spanning S' → S = S') := 
begin
  split,
  { intro basis,
    refine ⟨ basis.2, _ ⟩,
    intros S' le spanning,
    tidy,
    by_contradiction contra,
    have remove : S' ≤ S - {x}, by exact helpers.smaller le contra,
    have smaller_spans: is_spanning (S - {x}),
    { apply super_spans remove,
      exact spanning, },
    have x_seperate: x ∉ cl (S - {x}), by
    { unfold is_indep at basis_left,
      replace basis_left := basis_left a,
      exact basis_left, },
    have x_included: x ∈ cl (S - {x}), by
    { unfold is_spanning at smaller_spans,
      replace smaller_spans := smaller_spans x,
      exact smaller_spans, },
    contradiction, },
  { intro h,
    cases h with spans inf,
    unfold is_basis,
    refine ⟨ _, spans⟩,
    unfold is_indep,
    intros x hx,
    intro contra,
    have lt : S - {x} ≤ S, by
    { intros t ht,
      finish, },
    replace inf := inf (S - {x}) lt,
    suffices : is_spanning (S - {x}), by 
    { replace inf := inf this,
      have problem: ¬ S = S - {x}, by exact helpers.missing_elem S hx,
      contradiction, },
    exact subtract_spanning spans contra, }
end

-- Ignore these definitions: they are only here to help in some of the proofs. 
variable (T)
private def indep_sets := { S : set T // is_indep S }
variable {T}
private def indep_sets_rel : indep_sets T → indep_sets T → Prop := λ A B, A.1 ≤ B.1
private def indep_sets_union (S : set (indep_sets T)) : set T := Sup (subtype.val '' S)

-- This proof takes a while to check! Can it be simplified? 
private lemma union_chain_indep {S : set (indep_sets T)} :
  zorn.chain indep_sets_rel S → is_indep (indep_sets_union S) :=
begin
  intros zorn t ht contra,
  rcases finchar contra with ⟨A,hA1,hA2⟩,
  suffices claim : ∀ A : finset T, ↑A ≤ indep_sets_union S - {t} →
    ∃ B : indep_sets T, B ∈ S ∧ t ∈ B.val ∧ ↑A ≤ B.val,
  { replace claim := claim A hA1,
    rcases claim with ⟨⟨B,hB⟩,hB1,hB2,hB3⟩,
    dsimp at hB2 hB3,
    have : ↑A ≤ B - {t},
    { intros a ha,
      refine ⟨hB3 ha,_⟩,
      dsimp,
      change a ≠ t,
      replace ha := hA1 ha,
      finish, },
    replace hA2 := monotone this hA2,
    unfold is_indep at hB,
    replace hB := hB hB2,
    contradiction, },
  refine finset.induction _ _,
  { intro,
    rcases ht with ⟨B,⟨C,hC1,hC2⟩,h1⟩,
    use C,
    tidy, },
  { rintros a B ha ind useful,
    have : ↑B ≤ indep_sets_union S - {t}, 
    { intros b hb,
      apply useful,
      finish, },
    replace ind := ind this,
    rcases ind with ⟨C,hC1,hC2,hC3⟩,
    have : a ∈ indep_sets_union S - {t}, 
    { apply useful,
      simp, },
    rcases this with ⟨⟨D,⟨⟨E,hE1,rfl⟩,hE3⟩⟩, h3⟩,
    by_cases eq : C = E,
    { rw eq at *,
      use E,
      refine ⟨hC1,hC2,_⟩,
      tidy, },
    { cases @zorn _ hC1 _ hE1 eq,
      { use E, tidy, },
      { use C, tidy, } } }
end

/-- Any pregeometry has a basis. -/
theorem exists_basis : ∃ S : set T, is_basis S :=  
begin
  have zorn := @zorn.exists_maximal_of_chains_bounded 
    (indep_sets T)
    (λ A B, A.1 ≤ B.1) _ _,
  { rcases zorn with ⟨⟨B,hB1⟩,hB2⟩,
    use B,
    rw basis_iff_maximal_indep,
    refine ⟨@hB1,_⟩,
    intros S' h1 h2,
    replace hB2 := hB2 ⟨S',@h2⟩ h1,
    rw le_antisymm_iff,
    exact ⟨h1,hB2⟩, },
  { intro C,
    intro hZ,
    refine ⟨⟨Sup (subtype.val '' C),_⟩,_⟩,
    { apply union_chain_indep,
      assumption, },
    { intros,
      dsimp,
      cases a with a ha,
      dsimp at *,
      change a ≤ _,
      refine le_Sup _,
      tidy, } },
  { tidy, }
end

lemma indep_of_le_indep {S1 S2 : set T} : S1 ≤ S2 → is_indep S2 → is_indep S1 :=
begin
  intros hle hindep x hx1,
  have hx2 : x ∈ S2, by exact hle hx1,
  have : x ∉ S2 - {x}, by finish,
  have inc : S1 - {x} ≤ S2 - {x}, by tidy,
  intro contra,
  have problem := monotone inc (contra),
  unfold is_indep at hindep,
  exact hindep hx2 problem, 
end

end basis
end pregeom