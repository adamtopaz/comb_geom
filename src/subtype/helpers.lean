import data.set

variables {T : Type*} {S : set T}

namespace subtype

local notation `ι` := val

@[simp]
lemma image_preimage (A : set T) : ι '' (ι ⁻¹' A : set (subtype S)) = S ∩ A :=
begin
  ext,
  split,
  {
    intro h,
    rcases h with ⟨y,h,rfl⟩,
    exact ⟨y.2,h⟩
  },
  {
    intro h,
    exact ⟨⟨x,h.1⟩,h.2,by refl⟩
  }
end

@[simp]
lemma preimage_image (A : set (subtype S)) : ι ⁻¹' (ι '' A) = A := 
begin
  ext, split,
  {
    intro h,
    cases x with x hx,
    change x ∈ _ at h,
    rcases h with ⟨y,h,rfl⟩,
    finish,
  },
  {
    intro h,
    change x.val ∈ ι '' A,
    exact set.mem_image_of_mem ι h,
  }
end

lemma image_le (A : set (subtype S)) : ι '' A ≤ S := 
begin
  rintros a ⟨b,hb,rfl⟩,
  exact b.2
end

end subtype