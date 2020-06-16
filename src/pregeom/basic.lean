import data.set

class has_cl (T : Type*) := (cl : set T → set T)

class pregeom (T : Type*) extends has_cl T :=
(inclusive {S} : S ≤ cl S)
(monotone {A B} : A ≤ B → cl A ≤ cl B)
(idempotent {S} : cl (cl S) = cl S)
(exchange {x y S} : x ∈ cl (insert y S) → x ∉ cl S → y ∈ cl (insert x S))
(finchar {x S} : x ∈ cl S → ∃ A : finset T, ↑A ≤ S ∧ x ∈ cl ↑A)

class geometry (T : Type*) extends pregeom T :=
(cl_singleton {x} : cl {x} = {x})
(cl_empty : cl ∅ = ∅)

namespace pregeom
open has_cl

variables {T : Type*} 

def is_closed [has_cl T] (S : set T) := ∃ A, cl A = S 
def cls [has_cl T] (x : T) := cl ({x} : set T)

lemma mem_cls [pregeom T] {x : T} : x ∈ cls x := inclusive (set.mem_singleton x)

@[simp]
lemma cls_le_iff_mem_cl [pregeom T] {x : T} {S : set T} : cls x ≤ cl S ↔ x ∈ cl S := 
begin
  split,
  {
    intro hx,
    apply hx, 
    exact mem_cls,
  },
  {
    intro hx,
    suffices : cls x ≤ cl (cl S), by rwa idempotent at this,
    apply monotone, 
    rintros y ⟨rfl⟩, 
    assumption,
  }
end

@[simp]
lemma Sup_le_eq_cl [pregeom T] {S : set T} : Sup { A | ∃ x, A = cls x ∧ A ≤ cl S } = cl S :=
begin
  ext, split,
  {
    intro hx,
    rcases hx with ⟨A, ⟨t,rfl,h⟩, hA⟩,
    exact h hA,
  },
  {
    intro hx,
    refine ⟨cls x, ⟨x,rfl, _⟩,_⟩,
    { rw cls_le_iff_mem_cl, exact hx },
    { exact mem_cls },
  }
end

lemma exchange_cls [pregeom T] {u v : T} (u_in_cls : u ∈ cls v) (u_regular : u ∉ cl (∅ : set T))  : v ∈ cls u :=
begin
  unfold cls at *,
  rw set.singleton_def at *,
  exact exchange u_in_cls u_regular,
end

lemma mem_cl_iff_cls_le_cl [pregeom T] {x : T} {S : set T} : x ∈ cl S ↔ cls x ≤ cl S := 
begin
  split; intro hx,
  {
    have : ({x} : set T) ≤ cl S, 
    {
      rintros y ⟨hy⟩,
      assumption,
    },
    replace this := monotone this,
    rw idempotent at this,
    assumption,
  },
  {
    apply hx,
    exact mem_cls,
  }
end

lemma cl_cl_union_set_eq_cl_union [pregeom T] {A B : set T} : cl (cl A ∪ B) = cl (A ∪ B) := 
begin
  ext, split; intro h,
  {
    rw ←idempotent,
    refine monotone _ h,
    intros y hy,
    cases hy,
    {
      refine monotone _ hy,
      intros a ha,
      left, assumption,
    },
    {
      apply inclusive,
      right, assumption,
    }
  },
  {
    refine monotone _ h,
    intros z hz,
    cases hz,
    {
      left,
      apply inclusive, assumption,
    },
    {
      right, assumption,
    }
  }
end

lemma cl_set_union_cl_eq_cl_union [pregeom T] {A B : set T} : cl (A ∪ cl B) = cl (A ∪ B) := 
calc cl (A ∪ cl B) = cl (A ⊔ cl B) : rfl
... = cl (cl B ⊔ A) : by rw sup_comm
... = cl (B ∪ A) : cl_cl_union_set_eq_cl_union
... = cl (B ⊔ A) : rfl
... = cl (A ⊔ B) : by rw sup_comm

lemma cl_cl_union_cl_eq_cl_union [pregeom T] {A B : set T} : cl (cl A ∪ cl B) = cl (A ∪ B) := 
calc cl (cl A ∪ cl B) = cl (cl A ∪ B) : cl_set_union_cl_eq_cl_union
... = cl (A ∪ B) : cl_cl_union_set_eq_cl_union

@[simp]
lemma cl_union_cl_empty [pregeom T] {A : set T} : cl (cl (∅ : set T) ∪ A) = cl A := 
begin
  rw pregeom.cl_cl_union_set_eq_cl_union,
  rw set.empty_union,
end

end pregeom