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

def has_subclosed_fibers [has_cl S] := ∀ {s}, f ⁻¹' (f '' ({s} : set S)) ≤ cls s

def has_cl_instance [has_cl S] : has_cl T := ⟨λ (U : set T), f '' (cl (f ⁻¹' U))⟩

variable {f}
private lemma inclusive_helper [pregeom S] (sf : surjective f) {A : set T} :
  A ≤ f '' (cl (f ⁻¹' A)) := λ a ha, by rcases sf a with ⟨b,rfl⟩; exact ⟨b,inclusive ha,rfl⟩

private lemma exchange_helper [pregeom S] (sf : surjective f) (cf : has_subclosed_fibers f) {s : S} {U : set S} :
  cl ((f ⁻¹' (f '' ({s} : set S)) ∪ U)) = cl (insert s U) :=
begin
  ext,
  split,
  { intro hx,
    change x ∈ cl ({s} ∪ U),
    rw ← cl_cl_union_eq_cl_union,
    change x ∈ cl (cls s ∪ U),
    refine monotone _ hx,
    intros y hy,
    cases hy with hl hr,
    { left,
      apply cf,
      assumption, },
    { right,
      assumption, } },
  { intro hx,
    refine monotone _ hx,
    tidy,
    finish, },
end

private lemma preimage_insert {s : S} {A : set T} :
  f ⁻¹' insert (f s) A = f ⁻¹' (f '' ({s}: set S)) ∪ f ⁻¹' A :=
begin
  ext,
  split,
  { intro hx,
    change f x ∈ _ at hx,
    cases hx,
    { left,
      simpa, },
    { right,
      assumption, }, },
  { intro hx,
    cases hx,
    { left,
      rw set.image_singleton at hx,
      assumption, },
    { right,
      assumption, }, },
end

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
    { intros s hs,
      rcases hs with ⟨U, ⟨x, hx, rfl⟩ , hs⟩,
      change s ∈ f ⁻¹' _ at hs,
      exact ⟨cls x, ⟨x,hx,rfl⟩, cf hs⟩ }, 
    replace hy := monotone this hy,
    unfold cls at hy,
    have : ((λ (x : S), cls x) '' X) = map_cl ((singleton : S → set S) '' X),
    { unfold map_cl,
      tidy, },
    unfold cls at this,
    rw [this,cl_Sup_cl] at hy,
    have : Sup ((singleton : S → set S) '' X) = X, by tidy,
    rw this at hy,
    assumption,
  end,
  exchange :=
  begin
    rintros x y U ⟨z,hz,rfl⟩ hx2,
    rcases sf y with ⟨w,rfl⟩,
    rw [preimage_insert, exchange_helper sf @cf] at hz,
    have : z ∉ cl (f ⁻¹' U),
    { intro contra,
      have : f z ∈ f '' (cl (f ⁻¹' U)), by exact set.mem_image_of_mem f contra,
      contradiction },
    refine ⟨w,_,rfl⟩,
    rw [preimage_insert,exchange_helper sf @cf],
    apply exchange,
    assumption',
  end,
  finchar :=
  begin
    intros x U hx,
    rcases hx with ⟨s, hs, rfl⟩,
    rcases finchar hs with ⟨A, h1, h2⟩,
    use finset.image f A,
    split,
    { intros y hy,
      rw finset.coe_image at hy,
      rcases hy with ⟨z, hz, rfl⟩,
      replace hz := h1 hz,
      assumption, },
    { rw finset.coe_image,
      refine ⟨s, monotone _ h2, rfl⟩,
      intros z hz,
      exact ⟨z, hz, rfl⟩, },
  end,
  ..show has_cl T, by exact has_cl_instance f }

end pushforward
end pregeom