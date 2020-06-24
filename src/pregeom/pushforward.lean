import .basic
import data.set

open_locale classical

/-!
# The pushforward of a geometry.

First, start with two sets, S and T. Then, with a surjective map f : S → T, a closure operator on S,
and the requirement that ∀ t ∈ T, f ⁻¹({t}) is closed, we can define a closure operator on T, by
letting cl U := f (cl f ⁻¹ (U))
-/

namespace pregeom
namespace pushforward

open function

variables {T : Type*} {S : Type*} (f : S → T)
include f

def has_closed_fibers [has_cl S] := ∀ t, f⁻¹' ({t}) = cl (f⁻¹' {t})

def has_cl_instance [has_cl S] : has_cl T := ⟨λ (U : set T), f '' (cl (f ⁻¹' U))⟩

def pregeom_instance [pregeom S] (cf : has_closed_fibers f) (sf : surjective f) : pregeom T :=
{ inclusive := λ U u hu,
  begin
    change _ ∈ f '' _,
    rcases sf u with ⟨v,rfl⟩,
    exact ⟨v,inclusive hu,rfl⟩,
  end,
  monotone := λ A B h,
  begin
    replace h := @set.monotone_preimage _ _ f _ _ h,
    replace h := monotone h,
    exact @set.monotone_image _ _ f _ _ h,
  end,
  idempotent :=
  begin
    -- This one will be harder, uses the closed fibers
    intro U,
    ext,
    split,
    {
      sorry,
    },
    {
      -- Would be great if we could access previously defined instances here
      intro hx,
      change _ ∈ f '' _,
      sorry,
    },
  end,
  exchange :=
  begin
    intros x y U hx1 hx2,
    sorry,
  end,
  finchar :=
  begin
    intros x U hx,
    sorry,
  end,
  ..show has_cl T, by exact has_cl_instance f }

end pushforward
end pregeom