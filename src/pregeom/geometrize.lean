import .basic
import .pullback
import .pushforward
import data.finset

/-!
# Geometrization of a pregeometry

In this file we construct a geometry from a pregeometry in the "standard way".

We do this in four steps, as follows.
Given a pregeometry `T`, we define:
1. The subtype of "regular elements" of `T`, denoted `reg T`. 
  A "regular" element is an element which is not contained in the closure of `∅`. 
2. We construct a pregeometry instance on `reg T`. 
3. We construct the quotient of `reg T` by the equivalence relation `rel` defined as
  `rel x y ↔ cls x = cls y`. 
  This quotient type is denoted `geom T`.
4. We construct a geometry structure on `geom T`.

-/

set_option default_priority 100 

open_locale classical

namespace pregeom
open has_cl

variables (T : Type*) 

/-- The set of "regular elements" (see above). -/
def reg_set [has_cl T] := { t | t ∉ cl (∅ : set T) }

/-- The subtype of regular elements (see above). -/
def reg [has_cl T] := subtype (reg_set T)

namespace reg

/-- A typeclass for regular elements of T. Mainly used to inhabited instance. -/
-- This is only here so that the linted is happy. Is this actually necessary?
class has_reg_element extends has_cl T :=
(elem : T)
(is_regular : elem ∉ cl (∅ : set T))

open has_reg_element
instance [has_reg_element T] : inhabited (reg T) := ⟨⟨elem,is_regular⟩⟩

local notation `ι` := subtype.val

instance has_cl_instance [has_cl T] : has_cl (reg T) := pregeom.pullback.has_cl_instance subtype.val 

/-- The relation used to define a geometry from a pregeomery. -/
protected def rel [has_cl T] : reg T → reg T → Prop :=
λ s t, cls s = cls t 

variable {T}

protected theorem is_equiv [has_cl T] : equivalence (reg.rel T) := 
begin
  refine ⟨_,_,_⟩,
  { unfold reflexive reg.rel,
    intro x,
    refl, },
  { unfold symmetric reg.rel,
    rintros x y hx,
    rwa hx, },
  { unfold transitive reg.rel,
    intros x y z h1 h2,
    rwa [h1, h2], }
end

@[simp]
lemma cl_reg_set_inter [pregeom T] {S : set T} : cl (reg_set T ∩ S) = cl S := 
begin
  ext,
  split,
  { intro h,
    have : reg_set T ∩ S ≤ S, by {intros x hx, cases hx, assumption},
    exact monotone this h, },
  { intro h,
    have : S ≤ cl (∅ : set T) ∪ (reg_set T ∩ S), 
    { intros s hs,
      by_cases s ∈ cl (∅ : set T),
      { left, assumption },
      { right,
        exact ⟨h,hs⟩, } },
    replace h := monotone this h,
    rw cl_union_cl_empty at h,
    exact h,
  }
end

private lemma reg_lift_finset [has_cl T] {W : finset T} : ↑W ⊆ reg_set T → ∃ V : finset (reg T), finset.image ι V = W := 
begin
  refine finset.induction_on W _ _; intros,
  { use ∅,
    trivial, },
  { have : ↑s ⊆ reg_set T,
    { intros x hx,
      apply a_3,
      simp [hx], },
    rcases a_2 this with ⟨V,rfl⟩,
    have : a ∈ reg_set T,
    { apply a_3,
      simp, },
    use insert ⟨a,this⟩ V,
    rwa finset.image_insert, }
end

instance pregeom_instance [pregeom T] : pregeom (reg T) := pregeom.pullback.pregeom_instance subtype.val

@[simp]
theorem regularity [has_cl T] : cl (∅ : set (reg T)) = ∅ := 
begin
  change subtype.val ⁻¹' _ = _,
  rw set.image_empty,
  ext, split; intro hx,
  { change x.val ∈ _ at hx,
    have := x.2,
    contradiction, },
  { finish, }
end

end reg

/-- The setoid used to construct `geom T` from `reg T`. -/
protected def setoid [has_cl T] : setoid (reg T) := ⟨reg.rel T, reg.is_equiv⟩

/-- The geometry associated to `T`. See above. -/
def geom [has_cl T] := quotient (pregeom.setoid T)

namespace geom

variable {T}

/-- The canonical projection from `reg T` to `geom T`. -/
def to_geom [has_cl T] : reg T → geom T := quotient.mk'

local notation `π` := to_geom

instance [has_cl T] [inhabited (reg T)] : inhabited (geom T) := ⟨ π (default (reg T)) ⟩

/-- A variant of `to_geom`, but which takes a term of type `T` and a proof of "regularity" as inputs. -/
def to_geom_of_reg [has_cl T] {t : T} (h : t ∈ reg_set T) : geom T := π ⟨t,h⟩

theorem eq_iff [has_cl T] {u v : reg T} : π u = π v ↔ cls u = cls v := by simpa [to_geom]

theorem eq_iff' [pregeom T] {u v : reg T} : π u = π v ↔ u ∈ cls v :=
begin
  rw eq_iff,
  split,
  { intro h, rw ←h, exact mem_cls, },
  { intro h1, ext, split,
    { intro h2,
      unfold cls at h1,
      rw ←cls_le_iff_mem_cl at h1,
      exact h1 h2, },
    { intro h2,
      replace h1 := exchange_cls h1 _,
      { unfold cls at h1,
        rw ←cls_le_iff_mem_cl at h1,
        exact h1 h2, },
      { rw reg.regularity,
        tauto, } } }
end

theorem cls_le_pullback_of_mem [pregeom T] {t : reg T} {S : set (geom T) }: π t ∈ S ↔ cls t ≤ π ⁻¹' S :=
begin
  split; intro h,
  { intros u hu,
    change _ ∈ cls _ at hu,
    rw ←eq_iff' at hu,
    rwa ←hu at h, },
  { suffices : t ∈ π ⁻¹' S, by exact this,
    apply h,
    exact mem_cls, }
end

lemma mem_cl_of_mem_mk_eq_mk [pregeom T] {x y : reg T} {S : set (reg T)} : x ∈ cl S → π x = π y → y ∈ cl S := 
begin
  intros hx h,
  suffices : cls y ≤ cl S, by exact this mem_cls,
  rw eq_iff at h,
  rw ←h,
  change _ ⊆ _,
  rw cls_le_iff_mem_cl,
  assumption,
end

lemma mem_cl_of_mk_eq_mk [pregeom T] {a b : reg T} {S : set (reg T)} : a ∈ S → π b = π a → b ∈ cl S :=
begin
  intros ha h,
  rw eq_iff' at h,
  replace ha : ({a} : set (reg T)) ≤ S, 
  { rintros b ⟨rfl⟩,
    assumption, },
  apply monotone ha,
  assumption,
end

instance has_cl_instance [has_cl T] : has_cl (geom T) := 
⟨ λ S, π '' (cl (π ⁻¹' S)) ⟩

variable [pregeom T]

@[simp]
lemma pullback_insert {t : reg T} {S : set (geom T)} : π ⁻¹' insert (π t) S = cls t ∪ π ⁻¹' S := 
begin
  ext, split; intro hx,
  { change π x ∈ _ at hx,
    cases hx,
    { left, rwa eq_iff' at hx, },
    { right, exact hx, } },
  { change π x ∈ _,
    cases hx,
    { left, rwa eq_iff', },
    { right, exact hx, } }
end

instance pregeom_instance : pregeom (geom T) := 
begin
  refine @pregeom.pushforward.pregeom_instance _ _ π _ _ (quot.exists_rep),
  intros s t ht,
  change π t ∈ _ at ht,
  rcases ht with ⟨z,⟨rfl⟩,h2⟩,
  change quotient.mk' _ = quotient.mk' _ at h2,
  rw quotient.eq' at h2,
  change cls s = cls t at h2,
  rw h2,
  exact mem_cls
end

lemma mem_cls_geom {x y : geom T} : x ∈ cls y → x = y := 
begin
  intro hx,
  rcases hx with ⟨z,hz,rfl⟩,
  rcases quot.exists_rep y with ⟨w,hw,rfl⟩,
  rw set.singleton_def at hz,
  change _ ∈ cl ( π ⁻¹' (insert (π w) _) ) at hz,
  rw pullback_insert at hz,
  change π z = π _,
  unfold cls at hz,
  rw pregeom.cl_cl_union_eq_cl_union at hz,
  simp only [insert_emptyc_eq, set.singleton_union, set.preimage_empty] at hz,
  rwa eq_iff',
end

instance geom_instance : geometry (geom T) := 
begin
  split,
  { intro x,
    ext y, split; intro hy,
    { apply mem_cls_geom, assumption, },
    { change y = x at hy,
      rw hy,
      exact mem_cls, } },
  { change π '' cl (∅ : set (reg T)) = _,
    rw reg.regularity,
    finish, }
end

end geom

end pregeom