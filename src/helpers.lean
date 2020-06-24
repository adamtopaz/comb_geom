import data.set
import tactic
import linear_algebra

namespace helpers

variables {T : Type*} {S : set T}

lemma smaller {A B: set T} {x : T} (le : A ≤ B) (hx : x ∉ A): A ≤ B \ {x} :=
begin
  intros a ha,
  simp,
  split,
  exact le ha,
  intro contra,
  finish,
end

lemma missing_elem (A : set T) {x : T} (hx : x ∈ A): ¬ (A = A \ {x}) :=
begin
  intro,
  have : ∀ t : T, t ∈ A ↔ t ∈ A - {x}, by
  { change ∀ _, _ ↔ _ ∈ A \ {x},
    rw ←a,
    tauto, },
  replace this := (this x).mp hx,
  finish,
end

end helpers

namespace set

variables {S : Type*} {T : Type*} (f : S → T)

lemma image_preimage_eq_range_inter {A : set T} : f '' (f ⁻¹' A) = range f ∩ A := by tidy

@[simp]
lemma Sup_singleton_eq (S : set T) : Sup ((singleton : T → set T) '' S) = S :=
  set.ext $ λ x, ⟨λ ⟨_, ⟨_,h,rfl⟩, rfl⟩, h, λ h, ⟨{x}, ⟨x, h, rfl⟩,rfl⟩⟩

/-
begin
  ext, split; intro hx,
  { tidy },
  { use {x}, finish }
end
-/

lemma Sup_preimage {X : Type*} (S : set (set T)) (f : X → T) : f ⁻¹' (Sup S) = Sup ((λ A, f ⁻¹' A) '' S) := 
  set.ext $ λ x, ⟨λ ⟨U,hU,hxU⟩, ⟨f ⁻¹' U, ⟨U,hU,rfl⟩, hxU⟩, λ ⟨U,⟨V,hUV,rfl⟩,hxU⟩, ⟨V,hUV,hxU⟩⟩

/-
begin
  ext, split; intro hx,
  { rcases hx with ⟨U,hU,hxU⟩,
    refine ⟨f ⁻¹' U,_,hxU⟩,
    refine ⟨U,hU,rfl⟩,
-- this will have some problems, but whatever.
     },
  { rcases hx with ⟨U, ⟨V,hUV,rfl⟩, hxU⟩,
    change f x ∈ _,
    exact ⟨V,hUV, hxU⟩, }
end
-/

end set

namespace submodule
variables {k : Type*} [field k]
variables {V : Type*} [add_comm_group V] [module k V]

theorem span_singleton_eq_iff_smul_nonzero {v : V} {a : k} : a ≠ 0 → submodule.span k ({a • v} : set V) = submodule.span k {v} := 
begin
  intro ha,
  ext, split; intro hx; rw submodule.mem_span_singleton at *;
  rcases hx with ⟨b,rfl⟩,
  {  use b * a, 
    rw mul_smul, },
  { use b * a⁻¹,
    rw [←mul_smul, mul_assoc, inv_mul_cancel ha, mul_one], }
end

theorem span_singleton_eq_iff {v w : V} {hv : v ≠ 0} {hw : w ≠ 0} : submodule.span k ({v} : set V) = submodule.span k {w} ↔ ∃ a : k, a • v = w := 
begin
split; intro h,
  { have : w ∈ submodule.span k ({v} : set V),
    { rw h,
      apply submodule.subset_span,
      tauto, },
    rw submodule.mem_span_singleton at this,
    assumption, },
  { rcases h with ⟨a,rfl⟩,
    have ha : a ≠ 0, 
    { intro contra, rw [contra, zero_smul] at *, contradiction },
    rw span_singleton_eq_iff_smul_nonzero ha, }
end

end submodule
