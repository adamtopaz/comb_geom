# Combinatorial Geometries in Lean

This repository defines "pregeometries" in lean.
In mathematics, a pregeometry is a set `T` endowed with a "closure operator" `cl` acting on subsets of `T`.
This operator is assumed to satisfy certain axioms, the most important of which is the so-called "exchange" axiom.
This definition is formalized in `src/pregeom/basic.lean`.

## Pullbacks

Given a pregeometry `T` and a function `f : S → T`, we construct a pregeometry structure on `S` by "pulling back" the structure from `T`.
This is done in `src/pregeom/pullback.lean`.
Restrictions to subsets are a special case of this (where `f` is an embedding).

If `f` is injective and `T` is a geometry, we also obtain the structure of a geometry on `S` via pullback.

## Pushforward

Given a pregeometry `S` and a surjective function `f : S → T` which has "subclosed fibers", i.e. for all `s` in `S`, the fibre of `f s` is contained in the closure of `{s}`, then one can "pushforward" the pregeometry structure from `S` to `T`.
This is done in `src/pregeom/pushforward.lean`.

## Geometrization

One can associate a geometry to any pregeometry by first restricting to the complement of the closure of the empty set, then modding out by the relation which says that two elements `x` and `y` are equivalent if they (or more precisely, their associated singleton subsets) have the same closure.
We formalize this construction as well in the file `src/pregeom/geometrize.lean`.
The geometrization is constructed in terms of a pushforward of a pullback.

# Examples

## Projective Spaces

Given a field `k` and a `k`-vectorspace `V`, one constructs the so-called *projectivization* of `V`.
As a set, this is the collection of lines in `V` (i.e. one-dimensional subspaces).
This inherits the structure of a geometry, arising from the pregeometry on `V` given by the span as the closure operator.

We construct these objects (the pregeometry structure on `V` and the projectivization of `V`) in the file `src/projective_space/classical.lean` (the word "classical" is meant to distinguish this from the scheme-theoretic versions of projective spaces).

## Affine Spaces

Given a field `k` and a `k`-vectorspace `V`, one can consider `V` as an *affine space*, which is an example of a combinatorial *geometry*.
This geometry embeds into the projectivization of `k × V` via the map sending a vector `v` to the span of `(1,v)`.
The geometric structure on `V` is obtained by restricting the structure from the projectivization of `k × V`.
We construct this geometry in `src/affine_space/classical.lean`.
