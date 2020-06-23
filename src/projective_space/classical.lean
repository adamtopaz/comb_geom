import tactic
import linear_algebra
import linear_algebra.dimension
import ..linear_algebra.lincomb
import ..pregeom.basic
import ..pregeom.geometrize
import ..helpers

/--!
# What is going on here?

In this file, we define the pregeometry instance on a vector space V.
Since the vectorspace structure on V depends on the field (a priori V is just an abelian group), this was made a definition and not an instance.
See `vector_space.pregeom_instance`.

We then define the projective geometry associated to the k-vectorspace V as the geometry associated to this pregeomety.
Explicitly, `projectivization k V` is the projectivization of V as a k-vectorspace.
It is a geometry in the sense of the definition in `pregeom.basic`.
-/

variables (k : Type*) [field k]
variables (V : Type*) [add_comm_group V] [module k V] 

set_option default_priority 100
open_locale classical

namespace vector_space

open submodule

include k
/--
A has_cl instance for a k-vectorspace V.
Used to define the associated projective geometry.
-/
def has_cl_instance : has_cl V := ⟨ λ S, span k S ⟩
local attribute [instance] has_cl_instance

/--
A pregeom instance for a k-vectorspace V.
Used to define the associated projective geometry. 
-/
def pregeom_instance : pregeom V := 
begin
  split; intros,
  { exact subset_span },
  { exact span_mono a },
  { unfold has_cl.cl, rwa span_span, },
  { replace a : x ∈ span k (insert y S), by exact a,
    rw mem_span_insert at a,
    rcases a with ⟨a,v,w,h⟩,
    have : a ≠ 0, 
    { intro contra, rw contra at h,
      replace h : x = v, by rwa [zero_smul,zero_add] at h,
      rw h at *,
      contradiction, },
    have : a⁻¹ • x + a⁻¹ • -v = y, by
    calc a⁻¹ • x + a⁻¹ • -v = a⁻¹ • a • y + a⁻¹ • v + a⁻¹ • -v : by rw [h, smul_add]
    ... = (1 : k) • y + a⁻¹ • v + a⁻¹ • -v : by rw [←mul_smul, inv_mul_cancel this]
    ... = y : by rw [add_assoc, ←smul_add, one_smul]; simp,
    rw ←this,
    set H := span k (insert x S),
    apply add_mem' H,
    { apply smul_mem' H, apply subset_span, simp, },
    { apply smul_mem' H, apply neg_mem H, 
      have : S ⊆ insert x S, by simp, 
      apply span_mono this, assumption, } },
  { unfold has_cl.cl at *,
    rw ←lcspan.lcspan_eq_span at a,
    rcases a with ⟨L,hL1,hL2⟩,
    refine ⟨(lincomb.vects L).to_finset, _ , _⟩,
    { intros x hx,
      replace hx : x ∈ (lincomb.vects L).to_finset, by exact hx,
      rw list.mem_to_finset at hx,
      exact hL2 hx, },
    { rw ←hL1,
      apply lincomb.mem_span, } }
end
local attribute [instance] pregeom_instance

@[simp]
lemma cl_empty : cl (∅ : set V) = {0} := by simp [has_cl.cl]

end vector_space

open vector_space

include k

/--
`projectivization k V` is the projectivization of the k-vectorspace V.
-/
abbreviation projectivization := @pregeom.geom V (has_cl_instance k V)

namespace projectivization

instance : geometry (projectivization k V) := @pregeom.geom.geom_instance V (pregeom_instance k V)

variable {V}
def homogenize {v : V} : v ≠ 0 → projectivization k V := λ hv, 
  @pregeom.geom.to_geom V (vector_space.has_cl_instance k V) ⟨v, by simpa [pregeom.reg_set]⟩

theorem homogenize_eq_iff {v w : V} {hv : v ≠ 0} {hw : w ≠ 0} : homogenize k hv = homogenize k hw ↔ 
  submodule.span k ({v} : set V) = submodule.span k {w} := 
begin
  set regs := @pregeom.reg V (vector_space.has_cl_instance k V),
  change pregeom.geom.to_geom _ = pregeom.geom.to_geom _ ↔ _,
  rw pregeom.geom.eq_iff,
  change pregeom.pullback.pcl _ _ = pregeom.pullback.pcl _ _ ↔ _,
  split; intro h, 
  { replace h := congr_arg (λ A, subtype.val '' A) h,
    change _ '' _ = _ '' _ at h,
    conv at h {
      congr,
      rw [pregeom.pullback.image_pcl, set.image_singleton],
      dsimp,
      skip,
      rw [pregeom.pullback.image_pcl, set.image_singleton],
      dsimp, },
    change _ ∩ ↑(submodule.span _ _) = _ ∩ ↑(submodule.span _ _) at h,
    have : v ∈ set.range (subtype.val : regs → V) ∩ ↑(submodule.span k ({v} : set V)),
    { split,
      { use v, change v ∉ cl _, rw cl_empty, assumption, },
      { apply submodule.subset_span, tauto, } },
    rw h at this,
    cases this with h1 h2,
    replace h2 : v ∈ submodule.span k ({w} : set V), by exact h2,
    rw submodule.mem_span_singleton at h2,
    symmetry,
    rw submodule.span_singleton_eq_iff,
    assumption' },
  { change _ ⁻¹' ↑(submodule.span _ _) = _ ⁻¹' ↑(submodule.span _ _), 
    repeat {rw set.image_singleton}, 
    rw h }
end

theorem homogenize_eq_iff' {v w : V} {hv : v ≠ 0} {hw : w ≠ 0} : 
  homogenize k hv = homogenize k hw ↔ ∃ x : k, x • v = w := 
begin
  rw homogenize_eq_iff,
  apply submodule.span_singleton_eq_iff,
  assumption'
end

end projectivization
