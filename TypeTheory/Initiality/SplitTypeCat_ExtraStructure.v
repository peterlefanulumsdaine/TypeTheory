(** This file defines further logical structure on split type-categories,
not yet integrated into the type theory of [Initiality.Syntax] and the statement/proof of initiality. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.

Section Pi_eta_structure.

  Context (C : split_typecat) (Π : pi_struct C).

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

End Identity_types.
