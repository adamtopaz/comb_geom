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

variables {T : Type*} {S : Type*} [has_cl S] (f : S → T)
include f

def has_closed_fibers := ∀ t, f⁻¹' ({t}) = cl (f⁻¹' {t})

def has_cl_instance (f : S → T) : has_cl T := ⟨λ (U : set T), f '' (cl (f ⁻¹' U))⟩

def pregeom_instance [pregeom S] (cf : has_closed_fibers f) (sf : surjective f): pregeom T :=
{
  inclusive := 
  begin
    intros U u hu,
    unfold cl,
  end,
  monotone := sorry,
  idempotent := sorry,
  exchange := sorry,
  finchar := sorry,
  ..show has_cl T, by exact has_cl_instance f,
}

end pushforward
end pregeom