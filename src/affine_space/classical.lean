import linear_algebra.affine_space
import ..pregeom.basic
import ..projective_space.classical
import data.set

variables (k : Type*) [field k]
variables (V : Type*) [add_comm_group V] [module k V]

open_locale classical

namespace affine_space

include k

def affine_shift_ne_zero (v : V) : ((1,v) : k × V) ≠ 0 := by simp

def affine_embedding : V → projectivization k (k × V) := 
  λ v, projectivization.homogenize k (affine_shift_ne_zero k V v)

open function 

lemma affine_embedding_injective : injective (affine_embedding k V) := 
begin
  intros x y h,
  unfold affine_embedding at h,
  rw projectivization.homogenize_eq_iff' at h,
  cases h with c hc,
  simp only [prod.smul_mk, mul_one, algebra.id.smul_eq_mul, prod.mk.inj_iff] at hc,
  cases hc with hc _,
  rw [hc, one_smul] at *,
  assumption,
end

def affine_geom : geometry V := @pregeom.geom.pullback.geom_instance _ _ 
  (affine_embedding k V) _ (affine_embedding_injective _ _)

end affine_space