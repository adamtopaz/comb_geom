import .basic
import data.set
import ..helpers

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

def has_subclosed_fibers [has_cl S] := ∀ s, f ⁻¹' (f '' ({s} : set S)) ≤ cls s

def has_cl_instance [has_cl S] : has_cl T := ⟨λ (U : set T), f '' (cl (f ⁻¹' U))⟩

variable {f}
private lemma inclusive_helper [pregeom S] (sf : surjective f) {A : set T} :
  A ≤ f '' (cl (f ⁻¹' A)) := λ a ha, by rcases sf a with ⟨b,rfl⟩; exact ⟨b,inclusive ha,rfl⟩

def pregeom_instance [pregeom S] (cf : has_subclosed_fibers f) (sf : surjective f) : pregeom T :=
{ inclusive := λ U u hu, inclusive_helper sf hu,
  monotone := λ A B h,
  begin
    replace h := @set.monotone_preimage _ _ f _ _ h,
    replace h := monotone h,
    exact @set.monotone_image _ _ f _ _ h,
  end,
  idempotent := λ U,
  begin
    ext,
    refine ⟨λ hx, _,λ hx, inclusive_helper sf hx⟩,
    change _ ∈ f '' _,
    rcases hx with ⟨y,hy,rfl⟩,
    refine ⟨y,_,rfl⟩,
    change _ ∈ cl (_ ⁻¹' (f '' _)) at hy,
    suffices : y ∈ cl (cl (f ⁻¹' U)), by rwa idempotent at this,
    set X := cl (f ⁻¹' U),
    have : f ⁻¹' (f '' X) = Sup ((λ x, f ⁻¹' (f '' ({x} : set S))) '' X),
    { conv_lhs {rw ←set.Sup_singleton_eq (f '' X)},
      rw set.Sup_preimage,
      apply congr_arg Sup,
      tidy, },
    rw this at hy,
    have : Sup ((λ x, f ⁻¹' (f '' ({x} : set S))) '' X) ≤ Sup ((λ x, cls x) '' X),
    { sorry, }, 
    replace hy := monotone this hy,
    unfold cls at hy,
    have : ((λ (x : S), cl {x}) '' X) = map_cl ((singleton : S → set S) '' X),
    { sorry, },
    rw [this,cl_Sup_cl] at hy,
    have : Sup ((singleton : S → set S) '' X) = X,
    { sorry, },
    rw this at hy,
    assumption,
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