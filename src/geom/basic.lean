import ..pregeom.basic

variable (T : Type*)

class inf_geom extends inf_reg_pregeom T :=
(cl_singleton {x} : cl {x} = {x})

class geom extends reg_pregeom T :=
(cl_singleton {x} : cl {x} = {x})
