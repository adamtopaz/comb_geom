import .basic
import data.finset

open_locale classical

open has_cl

variable (T : Type*)

def reg_set [has_cl T] := {t : T | t ∉ cl (∅ : set T) }
def reg [has_cl T] := subtype (reg_set T)

namespace reg

open inf_pregeom
variable {T}

local notation `ι` := subtype.val

instance has_cl [has_cl T] : has_cl (reg T) :=
⟨ λ S, ι ⁻¹' cl (ι '' S) ⟩ 

@[simp]
lemma mem_cl_iff_val_mem_cl [has_cl T] {x : reg T} {S : set (reg T)} : x ∈ cl S ↔ x.val ∈ cl (ι '' S) := by trivial

@[simp]
lemma image_cl_eq_cl_reg_image [has_cl T] {S : set (reg T)} : 
  ι '' (cl S : set (reg T)) = reg_set T ∩ cl (ι '' S) :=
begin
  ext s, split,
  {
    rintro ⟨s', h1, h2⟩,
    rw ←h2, 
    exact ⟨s'.2, h1⟩
  },
  {
    rintro ⟨h1,h2⟩,
    use ⟨s, h1⟩,
    split,
    exact h2,
    simp only [],
  },
end

@[simp]
theorem cl_reg_inter [inf_pregeom T] {S : set T} :
  cl (reg_set T ∩ S) = cl S :=
begin
  ext, split,
  { 
    have : reg_set T ∩ S ⊆ S, by exact reg_set_incl T,
    apply monotone this,
  },
  {
    intro h,
    have : reg_set T ∩ S = ∅ ∪ (reg_set T ∩ S), by finish,
    rw [this, ←cl_cl_union],
    have : S ⊆ cl ∅ ∪ reg_set T ∩ S,
    {
      intros s hs,
      by_cases s ∈ cl (∅ : set T),
      left, assumption,
      right, split; assumption,
    }, 
    apply monotone this,
    assumption,
  }
end

instance inf_pregeom [inf_pregeom T] : inf_pregeom (reg T) := 
begin
  split; intros,
  {
    intros s hs,
    rw mem_cl_iff_val_mem_cl,
    have : s.val ∈ ι '' S, by exact set.mem_image_of_mem ι hs,
    exact inclusive this,
  },
  {
    intros s hs,
    rw mem_cl_iff_val_mem_cl at *,
    have : ι '' S1 ⊆ ι '' S2, by exact set.image_subset ι a,
    apply monotone this,
    assumption,
  },
  {
    ext, split,
    repeat {
      intro hx,
      rw [mem_cl_iff_val_mem_cl,image_cl_eq_cl_reg_image,cl_reg_inter,idempotent] at *,
      assumption,
    },
  },
  {
    rw mem_cl_iff_val_mem_cl,
    have : ι '' insert x S = insert x.val (ι '' S), by exact set.image_insert_eq, rw this,
    apply exchange,
    rw ←set.image_insert_eq, 
    assumption'
  }
end

instance pregeom [pregeom T] : pregeom (reg T) := 
begin
  split, intros x S hx,
  cases x with x h,
  have : x ∈ cl (ι '' S),
  {
    rw mem_cl_iff_val_mem_cl at hx,
    simpa only [],
  },
  cases pregeom.finchar this with W hW,
  -- we need the statement that the preimage of a finite set under an injective map is a finite set.
  sorry,
end

end reg