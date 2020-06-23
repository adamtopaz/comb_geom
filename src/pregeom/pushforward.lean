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
namespace pullback

open function

variables {T : Type*} {S : Type*} [has_cl S] (f : S → T)

-- For f : S → T, if S has a closure operator, we say that f has closed fibers if the preimage of
-- every singleton is closed.
def has_closed_fibers := (∀ t, f⁻¹' {t} = cl (f⁻¹' {t}))

-- Define the closure on T in the most straightforward way.
def has_cl_instance  : has_cl T := ⟨ λ U, f '' (cl (f⁻¹' (U))) ⟩ 

def pregeom_instance [pregeom S] : pregeom T :=
{
  inclusive := sorry,
  idempotent := sorry,
  monotone := sorry,
  exchange := sorry,
  finchar := sorry,
}
end pullback
end pregeom