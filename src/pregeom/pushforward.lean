import .basic
import data.set

/-!
# The pushforward of a geometry.

First, start with two sets, S and T. Then, with a surjective map f : S → T, a closure operator on S,
and the requirement that ∀ t ∈ T, f ⁻¹({t}) is closed, we can define a closure operator on T, by
letting cl U := f (cl f ⁻¹ (U))
-/

namespace pregeom
namespace pushforward

open function
open has_cl

variables {T : Type*} {S : Type*} (f : S → T)

[surjective f]


-- A function has closed fibers if the preimage of every singleton is closed.
def closed_fibers [has_cl S] (g : S → T) := ∀ t : T, f⁻¹' {t} = cl (f⁻¹' {t})


end pushforward
end pregeom