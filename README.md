# Combinatorial Geometries in Lean

This repository defines "pregeometries" in lean.
In mathematics, a pregeometry is a set `T` endowed with a "closure operator" `cl` acting on subsets of `T`.
This operator is assumed to satisfy certain axioms, the most important of which is the so-called "exchange" axiom.
This definition is formalized in `src/pregeom/basic.lean`.

One can associate a geometry to any pregeometry by first restricting to the complement of the closure of the empty set, then modding out by the relation which says that two elements `x` and `y` are equivalent if they (or more precisely, their associated singleton subsets) have the same closure.
We formalize this construction as well in the file `src/pregeom/geometrize.lean`.
