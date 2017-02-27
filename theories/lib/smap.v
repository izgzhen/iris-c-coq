(* Simple, finite, computable map based on list *)

Require Import iris.prelude.base.
Require Import iris.prelude.fin_maps.

Section definitions.
  Definition smap K `{EqDecision K} A := list (K * A).

  Instance smap_fmap `{EqDecision K} : FMap (smap K) := λ A B f m, map (λ kv, ((kv.1), f (kv.2))) m.

  Instance smap_lookup `{EqDecision K} A: Lookup K A (smap K A) := λ k,
    fix go m :=
    match m with
      | (k', v')::m' => if decide (k' = k) then Some v' else go m'
      | _ => None
    end.
  
  Instance smap_empty `{EqDecision K} A: Empty (smap K A) := [].
  
  Instance smap_partial_alter `{EqDecision K} A: PartialAlter K A (smap K A) := λ f k,
    fix go m :=
    match m with
      | (k', v')::m' =>
        if decide (k = k') then
          (match f (Some v') with
             | Some v'' => (k', v'') :: m' (* alter *)
             | None => m' (* delete *)
           end)
        else (k', v') :: go m'
      | _ =>
        match f None with
          | Some v => [(k, v)]
          | None => []
        end
    end.
  
  Instance smap_omap `{EqDecision K} : OMap (smap K) := λ A B f,
    fix go m :=
    match m with
      | (k, v)::m' =>
        match f v with
          | Some v' => (k, v'):: go m'
          | None => go m'
        end
      | _ => []
    end.

  Fixpoint smap_merge_by_keys
           `{EqDecision K} {A B C} (f: option A → option B → option C)
           (ks: list K) (ma: smap K A) (mb: smap K B) : smap K C :=
    match ks with
      | k::ks' =>
        match f (ma !! k) (mb !! k) with
          | Some vc => (k, vc) :: smap_merge_by_keys f ks' ma mb
          | None => smap_merge_by_keys f ks' ma mb
        end
      | _ => []
    end.

  Instance smap_to_list `{EqDecision K} A: FinMapToList K A (smap K A) := id.

  Instance smap_merge `{eq: EqDecision K}: Merge (smap K) :=
    λ A B C f ma mb, smap_merge_by_keys f (nodup eq (ma.*1 ++ mb.*1)) ma mb.
    
  Instance smap_finmap `{eq: EqDecision K} :
    @FinMap K (smap K) smap_fmap
            smap_lookup
            smap_empty smap_partial_alter
            smap_omap smap_merge smap_to_list eq.
  Admitted. (* ALthough I don't know why I should do it at all *)
End definitions.
