import linear_algebra

variables (R : Type*) (M : Type*) 

/-- 
An abbreviation for linear combinations.
By definition, a linear combination is a list of elements of type R × M
-/
abbreviation lincomb := list (R × M)

namespace lincomb

variables {R M}

/--
consts L is the list of constants appearing in the linear combination L.
-/
def consts : lincomb R M → list R := list.map prod.fst

/--
vects L is the list of vectors (or module elements) appearing in the linear combination L.
-/
def vects : lincomb R M → list M := list.map prod.snd

@[simp]
lemma vects_cons {t : R × M} {L : lincomb R M} : vects (t :: L)  = t.2 :: vects L := by refl

variable [semiring R]

/--
lmul c L is the linear combination obtained by multiplying all the constants of L by c (on the left).
-/
def lmul (c : R) : lincomb R M → lincomb R M
| [] := []
| ((a,m)::ls) := (c * a,m) :: (lmul ls)

@[simp]
lemma lmul_cons {c : R} {l : R × M} {L : lincomb R M} :
  lmul c (l :: L) = (c * l.1, l.2) :: (lmul c L) := by {cases l, refl}

@[simp]
lemma vects_lmul {c : R} {L : lincomb R M} : vects (lmul c L) = vects L :=
begin
  induction L with l ls hls,
  { simpa },
  { simpa [vects, lmul] }
end

variables [add_comm_monoid M] [semimodule R M]

/--
The evaluation of a linear combination in the module.
-/
def eval : lincomb R M → M
| [] := 0
| ((r,m) :: rest) := r • m + eval rest

@[simp]
lemma eval_nil : eval ([] : lincomb R M) = 0 := by refl

@[simp]
lemma eval_cons {l : R × M} {ls : lincomb R M} : eval (l :: ls) = l.1 • l.2 + eval ls :=
  by {cases l, refl}

@[simp]
lemma eval_add {L1 L2 : lincomb R M} : eval (L1 ++ L2) = eval L1 + eval L2 :=
begin
  induction L1 with l ls hls,
  { simp },
  { have : l :: ls ++ L2 = l :: (ls ++ L2), by refl,
    rw [this, eval_cons],
    finish, }
end

@[simp]
lemma eval_lmul {c : R} {L : lincomb R M} : eval (lmul c L) = c • (eval L) :=
begin
  induction L with l ls hls,
  { simpa only [eval_nil, smul_zero] },
  { rwa [lmul_cons,eval_cons,hls,eval_cons,mul_smul,smul_add] }
end

open submodule
open_locale classical

theorem mem_span {L : lincomb R M} : eval L ∈ (span R (↑(list.to_finset (vects L)) : set M)) :=
begin
  induction L with l ls hls,
  { simp, },
  { cases l with c v,
    set vs := vects ls,
    have : (vects ((c,v) :: ls)).to_finset = insert v vs.to_finset, by simp,
    rw [this, eval_cons],
    set H := span R (↑(insert v vs.to_finset) : set M),
    apply add_mem' H,
    { simp only [],
      apply smul_mem' H,
      apply subset_span,
      simp, },
    { suffices : eval ls ∈ span R (↑(vs.to_finset) : set M),
        by refine span_mono _ this; simp,
      assumption, }}
end

end lincomb

variable {M}

variables [semiring R] [add_comm_monoid M] [semimodule R M]

open lincomb

/--
The span of a set S defined in terms of linear combinations (using the above definition).
-/
def lcspan (S : set M) : submodule R M :=
begin
  refine_struct {
    carrier := { m | ∃ L : list (R × M), (eval L) = m ∧ (∀ {l}, l ∈ vects L → l ∈ S)}
  },
  { refine ⟨[],_,_⟩,
    { refl },
    { intros _ hl, exfalso, exact hl }},
  { rintros m n ⟨A,hA1,hA2⟩ ⟨B, hB1, hB2⟩,
    use A ++ B,
    split,
    { rwa [eval_add, hA1,hB1] },
    { intros l hl,
      unfold vects at hl,
      rw [list.map_append prod.snd, list.mem_append] at hl,
      cases hl, {apply hA2, assumption}, {apply hB2, assumption}}},
  { rintros c m ⟨L,hL1,hL2⟩,
    refine ⟨lmul c L,_,_⟩,
    { rwa [eval_lmul,hL1] },
    { rwa vects_lmul }, }
end

namespace lcspan

open submodule

/--
lcspan S agrees with span (which is defined as the infemum over all submodules containing S)
-/
theorem lcspan_eq_span {S : set M} : lcspan R S = span R S :=
begin
  ext m,
  split,
  { intro hm,
    rcases hm with ⟨L,rfl,hL2⟩,
    induction L with l ls hls,
    { apply zero_mem' (span R S) },
    { rw eval_cons,
      apply add_mem' (span R S),
      { apply smul_mem' (span R S), apply subset_span, apply hL2,
        rw vects_cons, simp, },
      { apply hls, intros u hu, apply hL2, rw vects_cons,
        exact list.mem_cons_of_mem l.snd hu, }}},
  { intro hm,
    have claim : lcspan R S ∈ { U : submodule R M | S ⊆ ↑U },
    { intros s hs,
      refine ⟨[(1,s)],_,_⟩,
      { simp, },
      { intros l hl,
        simp only [list.mem_cons_iff, vects_cons] at hl,
        rcases hl with ⟨ rfl,hl⟩,
        { assumption },
        { exfalso, exact hl, }}},
    { apply Inf_le claim,
      assumption, }
  }
end

end lcspan
