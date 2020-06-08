import data.finset

open_locale classical

variable (T : Type*)

class has_cl :=
(cl : set T → set T)

open has_cl
open has_insert

class inf_pregeom extends has_cl T :=
(inclusive {S} : S ⊆ cl S)
(monotone {S1 S2} : S1 ⊆ S2 → cl S1 ⊆ cl S2)
(idempotent {S} : cl (cl S) = cl S)
(exchange {x y} {S} : x ∈ cl (insert y S) → x ∉ cl S → y ∈ cl (insert x S))

class inf_reg_pregeom extends inf_pregeom T :=
(regular : cl ∅ = ∅)

class pregeom extends inf_pregeom T := 
(finchar {x} {S} : x ∈ cl S → ∃ U : finset T, ↑U ⊆ S ∧ x ∈ cl ↑U)

class reg_pregeom extends pregeom T :=
(regular : cl ∅ = ∅)

namespace has_cl

lemma reg_set_incl [has_cl T] {S : set T} : {t : T | t ∉ cl (∅ : set T)} ∩ S ⊆ S := by exact {t : T | t ∉ cl ∅}.inter_subset_right S

end has_cl

namespace inf_pregeom 
variable [inf_pregeom T]
variable {T}

lemma mem_cl_of_subset_mem {x : T} {A B : set T} : A ⊆ B → x ∈ cl A → x ∈ cl B := 
begin
  intros h hx,
  exact inf_pregeom.monotone h hx,
end

lemma cl_union_cl_subset_cl_union {A B : set T} : cl A ∪ cl B ⊆ cl (A ∪ B) :=
begin
  intros s hs,
  cases hs,
  {
    have : A ⊆ A ∪ B, by exact set.subset_union_left A B,
    exact monotone this hs,
  },
  {
    have : B ⊆ A ∪ B, by exact set.subset_union_right A B,
    exact monotone this hs,
  },
end

@[simp]
lemma cl_cl_union {A B : set T} : cl (cl A ∪ B) = cl (A ∪ B) := 
begin
  ext,
  split,
  {
    intro h,
    rw ←idempotent,
    have : cl A ∪ B ⊆ cl (A ∪ B),
    {
      intros t ht,
      cases ht,
      {
        have : A ⊆ A ∪ B, by exact set.subset_union_left A B,
        replace this := monotone this,
        apply this,
        assumption,
      },
      {
        have : B ⊆ A ∪ B, by exact set.subset_union_right A B,
        replace this := monotone this,
        apply this, apply inclusive, assumption,
      }
    },
    replace this := monotone this,
    apply this,
    assumption,
  },
  {
    have : A ∪ B ⊆ cl A ∪ B, by exact set.union_subset_union_left B inclusive,
    intro h,
    exact monotone this h,
  }
end

@[simp]
lemma cl_union_cl {A B : set T} : cl (A ∪ cl B) = cl (A ∪ B) := 
begin
  have : A ∪ cl B = cl B ∪ A, by exact sup_comm, rw this,
  have : A ∪ B = B ∪ A, by exact sup_comm, rw this,
  exact cl_cl_union
end

@[simp]
lemma cl_cl_union_cl {A B : set T} : cl (cl A ∪ cl B) = cl (A ∪ B) := 
calc cl (cl A ∪ cl B) = cl (cl A ∪ B) : cl_union_cl
... = cl (A ∪ B) : cl_cl_union

@[simp]
lemma cl_empty_union [inf_pregeom T] {S : set T} :
  cl (cl (∅ : set T) ∪ S) = cl S := 
calc cl (cl (∅ : set T) ∪ S) = cl (cl ∅ ∪ cl S) : by rw ←cl_union_cl
... = cl (∅ ∪ cl S) : by rw cl_cl_union
... = cl (cl S) : by rw set.empty_union
... = cl S : by rw inf_pregeom.idempotent

end inf_pregeom