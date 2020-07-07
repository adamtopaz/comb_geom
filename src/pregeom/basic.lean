import data.set
import tactic
import ..tactics

/-!
# Pregeometries

This file defines the typeclass `pregeom` of pregeometries.
These are types endowed with a "closure operator" `cl` acting on subsets, satisfying various axioms.
A pregeometry is a geometry provided that the closure of ∅ is ∅ and that the closure of a singleton is itself.

# Implementation Details

Typeclasses:
1. `has_cl` -- a typeclass for the cl operator
2. `pregeom` -- see above
3. `geom` -- see above

# Remarks

See the `geometrize.lean` file for the construction of a geometry from a pregeometry.

-/

set_option default_priority 100 

open_locale classical

/-- Typeclass for the `cl` operator -/
class has_cl (T : Type*) := (cl : set T → set T)

/-- Typeclass of `pregeometries` -/
class pregeom (T : Type*) extends has_cl T :=
(inclusive {S} : S ≤ cl S)
(monotone {A B} : A ≤ B → cl A ≤ cl B)
(idempotent {S} : cl (cl S) = cl S)
(exchange {x y S} : x ∈ cl (insert y S) → x ∉ cl S → y ∈ cl (insert x S))
(finchar {x S} : x ∈ cl S → ∃ A : finset T, ↑A ≤ S ∧ x ∈ cl ↑A)

/-- Typeclass for geometries -/
class geometry (T : Type*) extends pregeom T :=
(cl_singleton {x} : cl {x} = {x})
(cl_empty : cl ∅ = ∅)

notation `cl` := has_cl.cl

namespace pregeom

variables {T : Type*} 

/-- A set S is closed if there exists some other set A such that `cl A = S` -/
def is_closed [has_cl T] (S : set T) := ∃ A, cl A = S 

/-- `cls x` is the closure of the singleton `{x}` -/
def cls [has_cl T] (x : T) := cl ({x} : set T)

lemma mem_cls [pregeom T] {x : T} : x ∈ cls x := inclusive (set.mem_singleton x)

@[simp]
lemma cls_le_iff_mem_cl [pregeom T] {x : T} {S : set T} : cls x ⊆ cl S ↔ x ∈ cl S := 
begin
  split,
  { intro hx,
    apply hx, 
    exact mem_cls, },
  { intro hx,
    suffices : cls x ≤ cl (cl S), by rwa idempotent at this,
    apply monotone, 
    rintros y ⟨rfl⟩, 
    assumption, }
end

@[simp]
lemma Sup_le_eq_cl [pregeom T] {S : set T} : Sup { A | (∃ x, A = cls x) ∧ A ⊆ cl S } = cl S :=
begin
  ext, split,
  { intro hx,
    rcases hx with ⟨A,⟨⟨t,rfl⟩,h⟩,hA⟩,
    exact h hA, },
  { intro hx,
    refine ⟨cls x,⟨⟨x,rfl⟩,_⟩,_⟩,
    { change _ ⊆ _, rw cls_le_iff_mem_cl, exact hx },
    { exact mem_cls }, }
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
  { have : ({x} : set T) ≤ cl S, 
    { rintros y ⟨hy⟩,
      assumption, },
    replace this := monotone this,
    rw idempotent at this,
    assumption, },
  { apply hx,
    exact mem_cls, }
end

@[simp]
lemma cl_cl_union_eq_cl_union [pregeom T] {A B : set T} : cl (cl A ∪ B) = cl (A ∪ B) := 
begin
  ext, split; intro h,
  { rw ←idempotent,
    refine monotone _ h,
    intros y hy,
    cases hy,
    { refine monotone _ hy,
      intros a ha,
      left, assumption, },
    { apply inclusive,
      right, assumption, }},
  { refine monotone _ h,
    intros z hz,
    cases hz,
    { left,
      apply inclusive, assumption, },
    { right, assumption, }}
end

lemma cl_union_cl_eq_cl_union [pregeom T] {A B : set T} : cl (A ∪ cl B) = cl (A ∪ B) := 
calc cl (A ∪ cl B) = cl (A ⊔ cl B) : rfl
... = cl (cl B ⊔ A) : by rw sup_comm
... = cl (B ∪ A) : cl_cl_union_eq_cl_union
... = cl (B ⊔ A) : rfl
... = cl (A ⊔ B) : by rw sup_comm

lemma cl_cl_union_cl_eq_cl_union [pregeom T] {A B : set T} : cl (cl A ∪ cl B) = cl (A ∪ B) := 
calc cl (cl A ∪ cl B) = cl (cl A ∪ B) : cl_union_cl_eq_cl_union
... = cl (A ∪ B) : cl_cl_union_eq_cl_union

@[simp]
lemma cl_union_cl_empty [pregeom T] {A : set T} : cl (cl (∅ : set T) ∪ A) = cl A := 
begin
  rw pregeom.cl_cl_union_eq_cl_union,
  rw set.empty_union,
end

lemma cl_union_eq [pregeom T] {A S : set T}: A ≤ cl S → cl (A ∪ S) = cl S :=
begin
  intro hA,
  rw ←cl_union_cl_eq_cl_union,
  suffices : A ∪ cl S = cl S, by rw [this, idempotent],
  tidy, finish,
end

/-- If `As` is a set of sets, `map_cl As` is the set of sets obtained by
    applying `cl` to every memeber of `As`. -/
def map_cl [has_cl T] : set (set T) → set (set T) := set.image cl

lemma le_map_cl [pregeom T] (As : set (set T)) : Sup As ≤ Sup (map_cl As) := 
  λ a ⟨A,hA,ha⟩, ⟨cl A,⟨A,hA,rfl⟩,inclusive ha⟩

lemma cl_le_cl_Sup [pregeom T] {As : set (set T)} {A : set T} : A ∈ As → 
  cl A ≤ cl (Sup As) := λ h, monotone (λ x hx, ⟨A,h,hx⟩)

lemma map_cl_le_cl_Sup [pregeom T] (As : set (set T)) : Sup (map_cl As) ≤ cl (Sup As) :=
  λ x ⟨B,⟨C,hC,h⟩,hx⟩, by rw ←h at *; exact cl_le_cl_Sup hC hx

@[simp]
lemma cl_Sup_cl [pregeom T] {As : set (set T)} : cl (Sup (map_cl As)) = cl (Sup As) := 
begin
  ext,
  refine ⟨_,λ h, monotone (le_map_cl _) h⟩,
  intro hx,
  rw ←idempotent,
  refine monotone _ hx,
  apply map_cl_le_cl_Sup,
end

-- Library search didn't work on this one!
theorem le_sub_of_le {A B : set T} (hle : A ≤ B) (C : set T) : (A - C) ≤ (B - C) :=
begin
  rintros _ ⟨hA, hC⟩,
  exact ⟨hle hA, hC⟩,  -- Ask how to get this into a lambda
end

theorem le_sub_singleton_of_le {A B : set T} (hle : A ≤ B) : ∀ x : T, A - {x} ≤ B - {x} :=
  λ x, le_sub_of_le hle {x}

-- Library search didn't work here, either. Something wrong?
theorem le_insert_of_le {A B : set T} (hle : A ≤ B) (C : set T) : A ∪ C ≤ B ∪ C :=
begin
  intros x hx,
  cases hx with hA hC,
  left,
  exact hle hA,
  right,
  exact hC,
end

end pregeom