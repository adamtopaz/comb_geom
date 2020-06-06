import data.finset

variable (T : Type*)

class has_cl :=
(cl : set T → set T)

open has_insert

class inf_pregeom extends has_cl T :=
(inclusion {S} : S ⊆ cl S)
(monotone {S1 S2} : S1 ⊆ S2 → cl S1 ⊆ cl S2)
(idempotent {S} : cl (cl S) = cl S)
(exchange {x y} {S} : x ∈ cl (insert y S) → x ∉ cl S → y ∈ cl (insert x S))

class pregeom extends inf_pregeom T := 
(finchar {x} {S} : x ∈ cl S → ∃ U : finset T, ↑U ⊆ S ∧ x ∈ cl ↑U)