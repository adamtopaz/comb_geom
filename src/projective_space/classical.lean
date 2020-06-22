import tactic
import linear_algebra
import linear_algebra.dimension
import ..linear_algebra.lincomb
import ..pregeom.basic
import ..pregeom.geometrize

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

end vector_space

open vector_space

include k

/--
`projectivization k V` is the projectivization of the k-vectorspace V.
-/
abbreviation projectivization := @pregeom.geom V (has_cl_instance k V)

namespace projectivization

instance : geometry (projectivization k V) := @pregeom.geom.geom_instance V (pregeom_instance k V)

end projectivization
