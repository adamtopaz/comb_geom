import ..pregeom.basic

variable (T : Type*)

class inf_geom extends inf_pregeom T :=
(cl_empty : cl ∅ = ∅)
(cl_singleton {x} : cl {x} = {x})

class geom extends pregeom T :=
(cl_empty : cl ∅ = ∅)
(cl_singleton {x} : cl {x} = {x})
