# Combinatorial Geometries in Lean

This repository defines "pregeometries" in lean.
In mathematics, a pregeometry is a set `T` endowed with a "closure operator" `cl` acting on subsets of `T`.
This operator is assumed to satisfy certain axioms, the most important of which is the so-called "exchange" axiom.
This definition is formalized in `src/pregeom/basic.lean`.

One can associate a geometry to any pregeometry by first restricting to the complement of the closure of the empty set, then modding out by the relation which says that two elements `x` and `y` are equivalent if they (or more precisely, their associated singleton subsets) have the same closure.
We formalize this construction as well in the file `src/pregeom/geometrize.lean`.

## Projective Geometry

Given a field `k` and a `k`-vectorspace `V`, one constructs the so-called *projectivization* of `V`.
As a set, this is the collection of lines in `V` (i.e. one-dimensional subspaces).
This inherits the structure of a geometry, arising from the pregeometry on `V` given by the span as the closure operator.

We construct these objects (the pregeometry structure on `V` and the projectivization of `V`) in the file `src/projective_space/classical.lean` (the word "classical" is meant to distinguish this from the scheme-theoretic versions of projective spaces).
