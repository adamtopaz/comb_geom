import .basic
import data.set

open_locale classical

namespace pregeom
namespace pullback

variables {T : Type*} {S : Type*} (f : S → T)

include f
def has_cl_instance [has_cl T] : has_cl S := ⟨λ A, f ⁻¹' (cl (f '' A))⟩

def pregeom_instance [pregeom T] : pregeom S :=
{ 
  inclusive := λ A a ha, 
  begin
    change f _ ∈ cl _,
    apply inclusive,
    use a,
    simpa,
  end,
  monotone := λ A B inc a ha, 
  begin
    change f _ ∈ _,
    have : f '' A ≤ f '' B, by tidy,
    apply monotone this,
    simpa,
  end,
  idempotent := λ A,
  begin
    change f ⁻¹' cl (f '' ( f ⁻¹' _) ) = f ⁻¹' _,
    tidy,
    { 
      replace a : f x ∈ cl (cl (f '' A)),
      {
        refine monotone _ a,
        tidy,
      },
      rwa idempotent at a,
    },
    { 
      apply inclusive,
      refine ⟨x,_,by refl⟩,
      simpa,
    }
  end,
  exchange := λ x y S h1 h2, 
  begin
    change f y ∈ _,
    change f x ∉ _ at h2,
    change f x ∈ _ at h1,
    rw set.image_insert_eq at *,
    exact exchange h1 h2,
  end,
  finchar := λ x U hx, 
  begin
    suffices : ∀ {C : finset T}, (↑C ≤ f '' U → ∃ D : finset S, finset.image f D = C ∧ ↑D ≤ U),
    {
      rcases finchar hx with ⟨A, h1, h2⟩,
      rcases this h1 with ⟨B, h3, h4⟩,
      refine ⟨B,h4,_⟩,
      change f x ∈ _,
      rwa [←finset.coe_image,h3],
    },
    refine finset.induction (by finish) _,
    {
      intros t E ht ind h,
      rw finset.coe_insert at h,
      have : ↑E ≤ f '' U, by {intros e he, apply h, finish},
      rcases ind this with ⟨D,h1,h2⟩,
      have : t ∈ f '' U, by {apply h, finish},
      rcases this with ⟨s,hs,rfl⟩,
      use insert s D,
      tidy, 
    }
  end,
  ..show has_cl S, by exact has_cl_instance f
}

end pullback
end pregeom