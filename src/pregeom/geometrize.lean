import .basic
import ..subtype.helpers
import data.finset

/-!
# What is going on here?!

Start with a pregeometry T.
Define 

reg T

to be the subtype of regular elements, where an element t ∈ T is regular
provided that t ∉ cl ∅

ι : (reg T) ↪ T

is the canonical inclusion.

Then we define an equiv. relation on reg T, by saying that x and y are equivalent
provided that x ∈ cl {y} (this is equivalent to cl {x} = cl {y}).

Define (geom T) to be the quotient of (reg T) relative to this relation.

And

π : (reg T) ↠ (geom T) 

is the canonical projection.

When referring to ι, we should use words like "image" and "preimage".

When referring to π, we should use words like "pushforward" and "pullback".

-/

open_locale classical

namespace pregeom
open has_cl

variables (T : Type*) 

def reg_set [has_cl T] := { t | t ∉ cl (∅ : set T) }
def reg [has_cl T] := subtype (reg_set T)

namespace reg

local notation `ι` := subtype.val

instance has_cl_instance [has_cl T] : has_cl (reg T) :=
⟨ λ S, ι ⁻¹' cl (ι '' S) ⟩

protected def rel [has_cl T] : reg T → reg T → Prop :=
λ s t, cls s = cls t 

variable {T}

-- Having equivalent closures is an equivalence relation on the regular elements.
protected theorem is_equiv [has_cl T] : equivalence (reg.rel T) := 
begin
  refine ⟨_,_,_⟩,
  {
    unfold reflexive reg.rel,
    intro x,
    refl,
  },
  {
    unfold symmetric reg.rel,
    rintros x y hx,
    rwa hx,
  },
  {
    unfold transitive reg.rel,
    intros x y z h1 h2,
    rwa [h1, h2],
  }
end

@[simp]
lemma cl_union_cl_empty [pregeom T] {A : set T} : cl (cl (∅ : set T) ∪ A) = cl A := 
begin
  rw pregeom.cl_cl_union_set_eq_cl_union,
  rw set.empty_union,
end

@[simp]
lemma cl_reg_set_inter [pregeom T] {S : set T} : cl (reg_set T ∩ S) = cl S := 
begin
  ext,
  split,
  {
    intro h,
    have : reg_set T ∩ S ≤ S, by {intros x hx, cases hx, assumption},
    exact monotone this h,
  },
  {
    intro h,
    have : S ≤ cl (∅ : set T) ∪ (reg_set T ∩ S), 
    {
      intros s hs,
      by_cases s ∈ cl (∅ : set T),
      { left, assumption },
      {
        right,
        exact ⟨h,hs⟩,
      }
    },
    replace h := monotone this h,
    rw cl_union_cl_empty at h,
    exact h,
  }
end


private lemma reg_lift_finset [has_cl T] {W : finset T} : ↑W ⊆ reg_set T → ∃ V : finset (reg T), finset.image ι V = W := 
begin
  refine finset.induction_on W _ _; intros,
  {
    use ∅,
    trivial,
  },
  {
    have : ↑s ⊆ reg_set T,
    {
      intros x hx,
      apply a_3,
      simp [hx],
    },
    rcases a_2 this with ⟨V,rfl⟩,
    have : a ∈ reg_set T,
    {
      apply a_3,
      simp,
    },
    use insert ⟨a,this⟩ V,
    rwa finset.image_insert,
  }
end

instance pregeom_instance [pregeom T] : pregeom (reg T) :=
begin
  split; intros,
  {
    intros s hs,
    change s.val ∈ _,
    apply inclusive,
    exact set.mem_image_of_mem ι hs,
  },
  {
    intros u hu,
    suffices : ι '' A ≤ ι '' B, by exact monotone this hu,
    apply set.monotone_image a,
  },
  {
    unfold cl,    
    rw [subtype.image_preimage, cl_reg_set_inter, idempotent],
  },
  {
    change y.val ∈ _,
    change x.val ∈ _ at a,
    change x.val ∉ _ at a_1,
    rw set.image_insert_eq at *,
    exact exchange a a_1,
  },
  {
    change x.val ∈ _ at a,
    rcases finchar a with ⟨W,h1,h2⟩,
    have : ↑W ≤ reg_set T,
    {
      refine le_trans h1 _,
      exact subtype.image_le S,
    },
    rcases reg_lift_finset this with ⟨V,rfl⟩,
    refine ⟨V,_,_⟩,
    {
      intros v hv,
      rw ←subtype.preimage_image S,
      apply h1,
      rw finset.coe_image,
      exact set.mem_image_of_mem ι hv,
    },
    {
      rw finset.coe_image at h2,
      exact h2,
    }
  },
end

@[simp]
theorem regularity [pregeom T] : cl (∅ : set (reg T)) = ∅ := 
begin
  unfold cl,
  rw set.image_empty,
  ext, split; intro hx,
  {
    change x.val ∈ _ at hx,
    have := x.2,
    contradiction,
  },
  {
    finish,
  }
end

end reg

protected def setoid [has_cl T] : setoid (reg T) := ⟨reg.rel T, reg.is_equiv⟩

def geom [has_cl T] := quotient (pregeom.setoid T)

namespace geom

variable {T}

def to_geom [has_cl T] : reg T → geom T := quotient.mk'

local notation `π` := to_geom

def to_geom_of_reg [has_cl T] {t : T} (h : t ∈ reg_set T) : geom T := π ⟨t,h⟩

theorem eq_iff [has_cl T] {u v : reg T} : π u = π v ↔ cls u = cls v := by simpa [to_geom]

theorem eq_iff' [pregeom T] {u v : reg T} : π u = π v ↔ u ∈ cls v :=
begin
  rw eq_iff,
  split,
  {
    intro h, rw ←h, exact mem_cls,
  },
  {
    intro h1, ext, split,
    {
      intro h2,
      unfold cls at h1,
      rw ←cls_le_iff_mem_cl at h1,
      exact h1 h2,
    },
    {
      intro h2,
      replace h1 := exchange_cls h1 _,
      {
        unfold cls at h1,
        rw ←cls_le_iff_mem_cl at h1,
        exact h1 h2,
      },
      {
        rw reg.regularity,
        tauto,
      }
    }
  }
end

theorem cls_le_pullback_of_mem [pregeom T] {t : reg T} {S : set (geom T) }: π t ∈ S ↔ cls t ≤ π ⁻¹' S :=
begin
  split; intro h,
  {
    intros u hu,
    change _ ∈ cls _ at hu,
    rw ←eq_iff' at hu,
    rwa ←hu at h,
  },
  {
    suffices : t ∈ π ⁻¹' S, by exact this,
    apply h,
    exact mem_cls,
  }
end

lemma mem_cl_of_mem_mk_eq_mk [pregeom T] {x y : reg T} {S : set (reg T)} : x ∈ cl S → π x = π y → y ∈ cl S := 
begin
  intros hx h,
  suffices : cls y ≤ cl S, by exact this mem_cls,
  rw eq_iff at h,
  rw ←h,
  rw cls_le_iff_mem_cl,
  assumption,
end

lemma mem_cl_of_mk_eq_mk [pregeom T] {a b : reg T} {S : set (reg T)} : a ∈ S → π b = π a → b ∈ cl S :=
begin
  intros ha h,
  rw eq_iff' at h,
  replace ha : ({a} : set (reg T)) ≤ S, 
  {
    rintros b ⟨rfl⟩,
    assumption,
  },
  apply monotone ha,
  assumption,
end

instance has_cl_instance [has_cl T] : has_cl (geom T) := 
⟨ λ S, π '' (cl (π ⁻¹' S)) ⟩

variable [pregeom T]

lemma pi_mem_cl_iff_mem_cl_preimage {t : reg T} {S : set (geom T)} : 
  t ∈ cl (π ⁻¹' S) ↔ π t ∈ cl S :=
begin
  split; intro h,
  {
    exact ⟨t,h,rfl⟩,
  },
  {
    rcases h with ⟨u,h,hu⟩,
    exact mem_cl_of_mem_mk_eq_mk h hu,
  }
end

lemma cl_pullback_cl_eq_cl_pullback {S : set (geom T)} : cl (π ⁻¹' cl S) = cl (π ⁻¹' S) := 
begin
  ext, split; intro hx,
  {
    rw ←idempotent,
    refine monotone _ hx,
    intros y hy,
    change π y ∈ _ at hy,
    rwa ←pi_mem_cl_iff_mem_cl_preimage at hy,
  },
  {
    -- This is the same as the inclusive proof in the pregeom instance.
    -- Should be made into a seaprate lemma to avoid repetition
    refine monotone _ hx,
    refine set.preimage_mono _,
    intros s hs,
    rcases quot.exists_rep s with ⟨t,ht⟩,
    change π _ = _ at ht,
    refine ⟨t,_,ht⟩,
    suffices : cls t ≤ π ⁻¹' S,
    {
      apply inclusive,
      apply this,
      apply mem_cls,
    },
    intros u hu,
    change π u ∈ S,
    rw ←eq_iff' at hu,
    rwa [hu,ht],
  }
end

@[simp]
lemma pullback_insert {t : reg T} {S : set (geom T)} : π ⁻¹' insert (π t) S = cls t ∪ π ⁻¹' S := 
begin
  ext, split; intro hx,
  {
    change π x ∈ _ at hx,
    cases hx,
    {
      left,
      rwa eq_iff' at hx,
    },
    {
      right,
      exact hx,
    }
  },
  {
    change π x ∈ _,
    cases hx,
    {
      left,
      rwa eq_iff',
    },
    {
      right,
      exact hx,
    }
  }
end

lemma cl_preimage_insert {t : reg T} {S : set (geom T)} : cl (π ⁻¹' insert (π t) S) = cl (insert t (π ⁻¹' S)) := 
begin
  rw pullback_insert,
  unfold cls,
  rw cl_cl_union_set_eq_cl_union,
  rw set.singleton_union,
end

instance pregeom_instance : pregeom (geom T) :=
begin
  split; intros,
  {
    intros s hs,
    rcases quot.exists_rep s with ⟨t,ht⟩,
    change π _ = _ at ht,
    refine ⟨t,_,ht⟩,
    suffices : cls t ≤ π ⁻¹' S, 
    {
      apply inclusive,
      apply this,
      apply mem_cls,
    },
    intros u hu,
    change π u ∈ S,
    rw ←eq_iff' at hu,
    rwa [hu, ht],
  },
  {
    intros a ha,
    rcases quot.exists_rep a with ⟨t,ht⟩,
    change π _ = _ at ht,
    refine ⟨t,_,ht⟩,
    have : π ⁻¹' A ≤ π ⁻¹' B, 
    {
      change _ ⊆ _,
      apply set.preimage_mono,
      assumption,
    },
    apply monotone this,
    rw ←ht at ha,
    rwa pi_mem_cl_iff_mem_cl_preimage,
  },
  {
    ext, split; intro hx,
    {
      rcases hx with ⟨y,hy,rfl⟩,
      rw cl_pullback_cl_eq_cl_pullback at hy,
      exact ⟨y,hy,rfl⟩,
    },
    {
      rcases hx with ⟨y,hy,rfl⟩,
      rw ←cl_pullback_cl_eq_cl_pullback at hy,
      exact ⟨y,hy,rfl⟩,
    }
  },
  {
    rcases a with ⟨a,ha,rfl⟩,
    rcases quot.exists_rep y with ⟨t,rfl⟩,
    change _ ∈ cl ( π ⁻¹' insert (π _) _) at ha,
    change π t ∈ _,
    rw cl_preimage_insert at ha,
    have : a ∉ cl (π ⁻¹' S), 
    {
      intro contra,
      rw pi_mem_cl_iff_mem_cl_preimage at contra,
      contradiction,
    },
    replace this := exchange ha this,
    rw [←pi_mem_cl_iff_mem_cl_preimage, cl_preimage_insert],
    assumption,
  },
  {
    rcases a with ⟨y,hy,rfl⟩,
    rcases finchar hy with ⟨W,hW1,hW2⟩,
    refine ⟨finset.image π W,_,_⟩,
    {
      intros w hw,
      rw finset.coe_image at hw,
      rcases hw with ⟨u,hu,rfl⟩,
      replace hu := hW1 hu,
      exact hu,
    },
    {
      rw finset.coe_image,
      rw ←pi_mem_cl_iff_mem_cl_preimage, 
      refine monotone _ hW2,
      intros w hw,
      change π w ∈ _,
      exact set.mem_image_of_mem π hw,
    }
  },
end

lemma mem_cls_geom [pregeom T] {x y : geom T} : x ∈ cls y → x = y := 
begin
  intro hx,
  rcases hx with ⟨z,hz,rfl⟩,
  rcases quot.exists_rep y with ⟨w,hw,rfl⟩,
  rw set.singleton_def at hz,
  change _ ∈ cl ( π ⁻¹' (insert (π w) _) ) at hz,
  rw pullback_insert at hz,
  change π z = π _,
  unfold cls at hz,
  rw pregeom.cl_cl_union_set_eq_cl_union at hz,
  simp only [insert_emptyc_eq, set.singleton_union, set.preimage_empty] at hz,
  change z ∈ cls w at hz,
  rwa eq_iff',
end

instance geom_instance : geometry (geom T) := 
begin
  split,
  {
    intro x,
    ext y, split; intro hy,
    {
      change y = x,
      apply mem_cls_geom,
      assumption,
    },
    {
      change y = x at hy,
      rw hy,
      exact mem_cls,
    }
  },
  {
    change π '' cl (∅ : set (reg T)) = _,
    rw reg.regularity,
    finish,
  }
end

end geom

end pregeom