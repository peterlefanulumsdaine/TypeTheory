(** This file defines further logical structure on split type-categories,
not yet integrated into the type theory of [Initiality.Syntax] and the statement/proof of initiality. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.

Require Import TypeTheory.Initiality.SplitTypeCat_Maps. (* TODO: check what this was needed for, and upstream it *)

Section Auxiliary.

  Context {C : split_typecat}.

  (* TODO: seek elsewhere in library!
   TODO: naming!  order of args isn’t traditional “bind” *)
  (** helpful for equality reasoning with terms,
   to avoid repeatedly using [etrans. { apply tm_transportf_compose. }] *)
  Definition tm_transportf_bind_l {Γ}
      {A A' A'': C Γ} {e : A = A'} {e' : A' = A''}
      {t} {t'} {t''}
      (ee : tm_transportf e t = t') (ee' : tm_transportf e' t' = t'')
    : tm_transportf (e @ e') t = t''.
  Proof.
    etrans. apply tm_transportf_compose.
    etrans. { apply maponpaths; eassumption. }
    assumption.
  Qed.

  Definition tm_transportf_bind {Γ}
      {A A' A'': C Γ} {e : A' = A} {e' : A'' = A'}
      {t} {t'} {t''}
      (ee : t = tm_transportf e t') (ee' : t' = tm_transportf e' t'')
    : t = tm_transportf (e' @ e) t''.
  Proof.
    etrans. 2: { apply pathsinv0, tm_transportf_compose. }
    etrans. { eassumption. }
    apply maponpaths; assumption.
  Qed.


  (* TODO: upstream? and see if can unify with anything? *)
  Definition cxt_map_ext
      {Γ} {A : C Γ}
      {Γ'} (f : Γ' --> Γ)
      (a : tm (A⦃f⦄))
    : Γ' --> Γ ◂ A.
  Proof.
    refine (a ;; _). apply q_typecat.
  Defined.

  (* TODO: upstream! *)
  Definition tm_transportf_unfold
      {Γ} {A A' : C Γ} (e : A = A') (a : tm A)
    : (tm_transportf e a : _ --> _)
    = a ;; comp_ext_compare e.
  Proof.
    apply idpath.
  Qed.

  (* TODO: upstream! *)
  Definition tm_transportb_unfold
      {Γ} {A A' : C Γ} (e : A = A') (a : tm A')
    : (tm_transportb e a : _ --> _)
    = a ;; comp_ext_compare (!e).
  Proof.
    apply idpath.
  Qed.

  (* TODO: upstream? and see if can unify with anything? *)
  Definition cxt_map_ext_postcompose_gen
      {Γ} {A : C Γ}
      {Γ'} (f : Γ' --> Γ)
      (a : tm (A⦃f⦄))
      {Γ''} (g : Γ'' --> Γ')
      (e : A ⦃g · f⦄ = (A ⦃f⦄) ⦃g⦄)
    : g ;; (cxt_map_ext f a)
    = cxt_map_ext (g ;; f) (tm_transportb e (reind_tm g a)).
  Proof.
    unfold cxt_map_ext.
    rewrite q_q_typecat.
    repeat rewrite assoc. apply maponpaths_2.
    rewrite <- reind_tm_q. apply maponpaths_2.
    rewrite tm_transportb_unfold.
    rewrite <- assoc.
    etrans. 2: { apply maponpaths, comp_ext_compare_comp. }
    rewrite comp_ext_compare_id_general.
    apply pathsinv0, id_right.
  Qed.
  (* TODO: remove duplicate access function [reind_comp_term_typecat]?
   TODO: fix naming conventions on [q_q_typecat], [q_q_typecat']
     (lemma name should describe LHS, and [tm_transportf] munging should go on RHS) *)

  (* TODO: upstream? and see if can unify with anything? *)
  Definition cxt_map_ext_postcompose
      {Γ} {A : C Γ}
      {Γ'} (f : Γ' --> Γ)
      (a : tm (A⦃f⦄))
      {Γ''} (g : Γ'' --> Γ')
    : g ;; (cxt_map_ext f a)
    = cxt_map_ext (g ;; f) 
        (tm_transportb (reind_comp_typecat _ _ _ _ _ _)
                       (reind_tm g a)).
  Proof.
    apply cxt_map_ext_postcompose_gen.
  Qed.

End Auxiliary.

Section Pi_eta_structure.

  Context {C : split_typecat} (Π : pi_struct C).

  Definition Pi_eta : UU.
  Proof.
    refine (forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)) (p : tm (Π _ A B)),
               p = _).
    (* now we have to construct the eta-expansion of [p],
     which in object-theory pseudocode is [lam x (app p x)] *)
    refine (pi_intro _ _ _ _ _). (* [pi_intro] is lambda-abstraction *)
    Fail refine (pi_app _ _ _ _ _ _).
    (* fails, but informatively:
       [pi_app] gives a term in a reindexing of B, not B itself.
    So we need to add a a [transportf].
    (In the object theory, the type-coercion rule). *)
    simple refine (transportf _ _ (pi_app Π _ _ _ _ _)).
    (* In the object theory, the application we want is [ app p x ].
    But note that this [p] is weakened from [Γ] to [Γ ◂ A],
    so we need to give that weakening explicitly,
    i.e. reindexing [p] along the rependent projection from [Γ ◂ A]. *)
    4: {
      Fail refine (reind_tm (dpr_typecat A) p).
    (* informative again: the reindexed pi-type is not definitionally a pi-type *)
      refine (transportf _ _ (reind_tm (dpr_typecat A) p)).
      apply pi_form_struct_natural.
    }
    (* now supply the argument: the “new variable” / generic term *)
    2: { apply var_typecat. }
    (* now some algebra to justify this type-reindexing equality *)
    eapply pathscomp0. { apply pathsinv0, reind_comp_type_typecat. }
    eapply pathscomp0. 2: { apply reind_id_type_typecat. }
    apply maponpaths. 
    (* look at the definition of the generic term, as a map into a pullback *)
    unfold var_typecat. apply Auxiliary.Pb_map_commutes_2.
  Defined.

End Pi_eta_structure.

Section Identity_types.
  (** The structure to model identity types in a split type-category. *)

  Context (C : split_typecat).

  Definition id_form_struct : UU
  := ∑ (Id : forall (Γ : C) (A : C Γ) (a b : tm A), C Γ),
       (forall (Γ Γ' : C) (f : Γ' --> Γ) (A : C Γ) (a b : tm A),
         (Id Γ A a b) ⦃ f ⦄ = Id Γ' (A⦃f⦄) (reind_tm f a) (reind_tm f b)).

  Definition id_form_struct_pr1 (Id : id_form_struct) := pr1 Id.
  Coercion id_form_struct_pr1 : id_form_struct >-> Funclass.

  Definition id_form_struct_natural {Id : id_form_struct}
      {Γ Γ'} (f : Γ' --> Γ) {A} a b
    : (Id _ _ a b) ⦃ f ⦄ = Id Γ' _ _ _
  := pr2 Id _ _ f A a b.
  (* TODO: try to get implicit args working better for these and other such structure? *)

  Definition maponpaths_id_form {Id : id_form_struct}
      {Γ} {A A'} (e_A : A = A')
      {a} {a'} (e_a : a = tm_transportb e_A a')
      {b} {b'} (e_b : b = tm_transportb e_A b')
    : Id Γ A a b = Id Γ A' a' b'.
  Proof.
    destruct e_A.
    rewrite tm_transportb_idpath in e_a, e_b.
    apply maponpaths_12; assumption.
  Qed.

  Definition id_intro_struct (Id : id_form_struct) : UU
  := ∑ (refl : forall (Γ : C) (A : C Γ) (a : tm A), tm (Id _ _ a a)),
       (forall (Γ Γ' : C) (f : Γ' --> Γ) A a,
         reind_tm f (refl Γ A a)
         = tm_transportb (id_form_struct_natural _ _ _)
             (refl _ _ (reind_tm f a))).

  Definition id_intro_struct_pr1 {Id} (refl : id_intro_struct Id) := pr1 refl.
  Coercion id_intro_struct_pr1 : id_intro_struct >-> Funclass.

  Definition id_intro_struct_natural {Id} (refl : id_intro_struct Id)
      {Γ Γ'} (f : Γ' --> Γ) A a
    : reind_tm f (refl Γ A a)
      = tm_transportb _ (refl Γ' _ _) 
  := pr2 refl _ _ f A a.

  Definition id_intro_q {Id} (refl : id_intro_struct Id)
      {Γ Γ'} (f : Γ' --> Γ) A a
    : f ;; refl Γ A a
      = refl Γ' _ (reind_tm f a)
        ;; comp_ext_compare (!id_form_struct_natural _ _ _)
        ;; q_typecat _ f.
  Proof.
    etrans. { apply pathsinv0, reind_tm_q. }
    apply maponpaths_2. 
    exact (maponpaths _ (id_intro_struct_natural _ _ _ _)).
  Qed.

  (** Auxiliary definitions towards the id-elim rule *) 

  Definition id_based_fam (Id : id_form_struct) {Γ:C} (A : C Γ) (a : tm A)
    : C (Γ ◂ A)
  := Id _ _ (reind_tm _ a) (var_typecat A).
  (* TODO: add defs to make this easier to read/write, e.g. for de Bruijn index variables?? *)

  Definition id_based_fam_natural (Id : id_form_struct)
    {Γ Γ':C} (f : Γ' --> Γ) (A : C Γ) (a : tm A)
    : (id_based_fam Id A a) ⦃ q_typecat A f ⦄
      = id_based_fam Id (A⦃f⦄) (reind_tm f a).
  Proof.
    unfold id_based_fam.
    etrans. { apply id_form_struct_natural. }
    use maponpaths_id_form.
    - etrans. { apply pathsinv0, reind_comp_typecat. }
      etrans. 2: { apply reind_comp_typecat. }
      apply maponpaths, dpr_q_typecat.
    - etrans. { apply pathsinv0, reind_compose_tm'. } 
      etrans. 2: { apply maponpaths, reind_compose_tm'. }
      etrans. 2: { apply tm_transportf_compose. }
      etrans.
      { eapply maponpaths.
        refine (maponpaths_2_reind_tm _ _). 
        apply dpr_q_typecat. }
      etrans. { apply pathsinv0, tm_transportf_compose. }
      apply tm_transportf_irrelevant.
    - apply reind_var_typecat_gen.
  Qed.
  (* TODO: consistentise direction of [tm_transportf_bind], and generally which side of equation [tm_transportf] goes on? (RHS) *)

  Definition id_refl_map {Id} (refl : id_intro_struct Id)
      {Γ} {A : C Γ} (a : tm A)
    : Γ --> Γ ◂ A ◂ id_based_fam Id A a.
  Proof.
    apply (cxt_map_ext a). unfold id_based_fam.
    refine (tm_transportb _ (refl _ _ a)).
    abstract 
    ( refine (id_form_struct_natural _ _ _ @ _);
      use maponpaths_id_form;
      [ refine (!reind_comp_typecat _ _ _ _ _ _ @ _);
        refine (maponpaths _ (section_property _) @ _);
        apply reind_id_type_typecat
      | refine (_ @ tm_transportf_irrelevant _ _ _);
        refine (tm_transportf_bind (! reind_compose_tm' _ _ _) _);
        refine (maponpaths_2_reind_tm (section_property _) _ @ _);
        refine (_ @ ! tm_transportf_compose _ _ _);
        apply maponpaths, reind_id_tm
      | refine (reind_tm_var_typecat _ @ _); apply tm_transportf_irrelevant]
    ).
  Defined.

  (* TODO: move [tm_transport] to RHS in [maponpaths_2_reind_tm], [reind_id_tm] to fit general convention? 
   Also switch direvtions of [reind_compose_tm], etc? *)

  Definition id_refl_map_natural {Id} (refl : id_intro_struct Id)
      {Γ Γ'} (f : Γ' --> Γ) {A : C Γ} (a : tm A)
    : id_refl_map refl (reind_tm f a)
        · (comp_ext_compare (! id_based_fam_natural Id f A a)
        · q_typecat (id_based_fam Id A a) (q_typecat A f))
    = f · id_refl_map refl a.
  Proof.
    unfold id_refl_map, cxt_map_ext.
    repeat rewrite tm_transportb_unfold.
    etrans. 2: { apply maponpaths, assoc. }
    etrans. 2: { apply pathsinv0, assoc. }
    etrans. 2: { eapply maponpaths_2, pathsinv0, id_intro_q. }
    etrans. { apply pathsinv0, assoc. }
    etrans. { apply pathsinv0, assoc. }
    etrans. 2: { apply assoc. }
    etrans. 2: { apply assoc. }
    apply maponpaths.
    etrans.
    { apply maponpaths.
      etrans. { apply assoc. }
      etrans. { apply maponpaths_2, pathsinv0, q_typecat_typeeq. }
      etrans. { apply assoc'. }
      apply maponpaths, q_q_typecat'.
    }
    etrans.
    2: { apply pathsinv0, maponpaths.
      etrans. { apply assoc. }
      etrans. { apply maponpaths_2, pathsinv0, q_typecat_typeeq. }
      etrans. { apply assoc'. }
      apply maponpaths, q_q_typecat'. 
    }
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2, pathsinv0, comp_ext_compare_comp. }
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2, pathsinv0, comp_ext_compare_comp. }
    etrans. 2: { apply assoc'. }
    etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
    etrans. 2: { apply assoc'. }
    etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
    etrans.
    2: { apply maponpaths.
         refine (comp_ext_compare_q_typecat _ _).
         apply pathsinv0, reind_tm_q.
    }
    etrans. 2: { apply assoc'. }
    etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
    apply maponpaths_2, comp_ext_compare_irrelevant.
  Qed.

  (* We use the based definition of the Id-elim rule *)
  Definition id_elim_struct Id (refl : id_intro_struct Id) : UU.
  Proof.
    refine (∑ (J : forall {Γ} (A : C Γ) (a : tm A)
                     (P : C (_ ◂ id_based_fam Id A a))
                     (d : @tm _ Γ (P ⦃ id_refl_map refl a ⦄)), 
             tm P),
      forall {Γ Γ'} (f : Γ' --> Γ)
             (A : C Γ) (a : tm A)
             (P : C (_ ◂ id_based_fam Id A a))
             (d : @tm _ Γ (P ⦃ id_refl_map refl a ⦄)),
        _).
    simple refine (reind_tm _ (J Γ A a P d)
                   = J Γ' (A⦃f⦄) (reind_tm f a) (P⦃_⦄) _).
    - simple refine (comp_ext_compare (!_) ;; q_typecat _ (q_typecat _ f)).
      apply id_based_fam_natural.
    - refine (tm_transportb _ (reind_tm f d)).
      etrans. { apply pathsinv0, reind_comp_typecat. }
      etrans. 2: { apply reind_comp_typecat. }
    (* TODO: remove/unify duplicate access functions [reind_comp_typecat], [reind_comp_type_typecat] upstream. *)
      apply maponpaths.
      apply id_refl_map_natural.
  Defined.
  (* TODO: this is currently the “universal” form of Id-elim, where the
  output is a term in the same context as the family P.
  For consistency with other rules, would be better to give the “hypothetical” form, with output in the ambient context [Γ], and two more term inputs and naturality in those. *)

  Definition id_elim_struct_pr1 {Id} {refl : id_intro_struct Id}
       (J : id_elim_struct Id refl)
       {Γ} (A : C Γ) (a : tm A)
       (P : C (_ ◂ id_based_fam Id A a))
       (d : @tm _ Γ (P ⦃ id_refl_map refl a ⦄)) 
    : tm P
  := pr1 J Γ A a P d.

  Coercion id_elim_struct_pr1 : id_elim_struct >-> Funclass.

  Definition id_elim_natural {Id} {refl : id_intro_struct Id}
             (J : id_elim_struct Id refl)
             {Γ Γ'} (f : Γ' --> Γ)
             (A : C Γ) (a : tm A)
             (P : C (_ ◂ id_based_fam Id A a))
             (d : @tm _ Γ (P ⦃ id_refl_map refl a ⦄))
    : reind_tm _ (J _ _ _ _ _) = J _ _ _ _ _
  := pr2 J _ _ f _ _ _ d.

  Definition id_comp_struct {Id} {refl} (J : id_elim_struct Id refl) : UU
  := forall {Γ} (A : C Γ) (a : tm A)
            (P : C (_ ◂ id_based_fam Id A a))
            (d : @tm _ Γ (P ⦃ id_refl_map refl a ⦄)),
    reind_tm (id_refl_map refl a) (J _ _ _ _ d) = d.

  (* TODO: package up Id-types, as for Pi-types *)
End Identity_types.
