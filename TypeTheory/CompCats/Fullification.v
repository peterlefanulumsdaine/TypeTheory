(*
  [TypeTheory.CompCats.Fullification]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** Any comp category can be “fullified”, replacing the maps in its fibration of types with maps from the slice, to make it a full comprehension category. 

Moreover, this should form a right adjoint to the inclusion of full comp-cats into all comp-cats over a given base. 

Both of these extend constructions at the level of displayed functors and fibrations.

TODO: unify all this a bit better with the material in [FullyFaithfulDispFunctor]. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

Require Import TypeTheory.CompCats.FullyFaithfulDispFunctor.

Section Auxiliary.

  (** ** Some missing access functions for fibrations and comprehension cats. *)
  (** TODO: split out into their own file(s), and unify with the more specialised access functions for _discrete_ comp cats given elsewhere. *)

  Coercion disp_cat_from_fibration {C} : fibration C -> disp_cat C := pr1.

  Definition fib_cleaving {C} (T : fibration C) : cleaving T := pr2 T.

  Coercion types_fib {C} (T : comprehension_cat_structure C)
    : fibration C
  := (pr1 T,, pr12 T).

  Definition comprehension {C} (T : comprehension_cat_structure C)
    : cartesian_disp_functor (functor_identity C) (types_fib T) (disp_codomain C)
  := (pr122 T,, pr222 T).

  Definition make_comprehension_cat_structure {C}
      (T : fibration C)
      (comp : cartesian_disp_functor (functor_identity C) T (disp_codomain C))
    : comprehension_cat_structure C.
  Proof.
    exists T. exists (fib_cleaving T).
    exists comp. apply cartesian_disp_functor_is_cartesian.
  Defined.

  (** ** Misc lemmas *)

  Lemma weq_from_fully_faithful_disp
      {C C' : category} {F : functor C C'}
      {D} {D'} (FF : disp_functor F D D')
      (FF_ff : disp_functor_ff FF)
      {x x' : C} (f : x --> x') {xx : D x} {xx': D x'}
    : (xx -->[f] xx') ≃ (FF x xx -->[#F f] FF x' xx'). 
  Proof.
    exists (# FF)%mor_disp. apply FF_ff.
  Defined.

  (* TODO: too many different things called FF here!!  Probably rename “ff_disp_functor” to something less abbreviated upstream. *)
  Lemma fully_faithul_disp_inv_hom
      {C C' : category} {F : functor C C'}
      {D} {D'} (FF : disp_functor F D D')
      (FF_ff : disp_functor_ff FF)
      {x x' : C} (f : x --> x') {xx : D x} {xx': D x'}
    : (FF x xx -->[#F f] FF x' xx') -> (xx -->[f] xx'). 
  Proof.
    apply invweq, weq_from_fully_faithful_disp, FF_ff.
  Defined.

  Lemma ff_reflects_cartesian
      {C C' : category} {F : functor C C'}
      {D} {D'} (FF : disp_functor F D D')
      (FF_ff : disp_functor_ff FF)
      {x x' : C} (f : x' --> x) {xx : D x} {xx'} (ff : xx' -->[f] xx)
      (FF_ff_cart : is_cartesian (#FF ff)%mor_disp)
    : is_cartesian ff.
  Proof.
    intros x'' g xx'' hh.
    eapply iscontrweqb.
    2: { 
      use (FF_ff_cart (F x'') (#F g) (FF _ xx'')).
      refine (transportf _ _ (# FF hh)%mor_disp).
      apply functor_comp.
    }
    use weqtotal2.
    apply weq_from_fully_faithful_disp. { apply FF_ff. }
    simpl. intros gg.
    apply weqimplimpl; try apply homsets_disp.
    - intros e_gf_h.
      etrans. 2: { apply maponpaths, maponpaths, e_gf_h. }
      apply transportf_transpose_right, pathsinv0.
      apply disp_functor_comp.
    - intros e_Fgf_Fh.
      eapply invmaponpathsincl. { apply isinclweq, FF_ff. }
      simpl. etrans. { apply disp_functor_comp. }
      apply transportb_transpose_left.
      assumption.
  Defined.
      
End Auxiliary.

Section Fullification_Disp_Cat.

  Context {C : category} {D D' : disp_cat C} (F : disp_functor (functor_identity _) D' D).
  
  Definition fullification_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists D'.
    intros x y xx yy f. exact ((F x xx) -->[f] (F y yy)).
  Defined.

  Definition fullification_disp_cat_data : disp_cat_data C.
  Proof.
    exists fullification_disp_cat_ob_mor; split.
    - intros x xx; apply id_disp.
    - intros x y z f g xx yy zz; apply comp_disp.
  Defined.

  Definition fullification_disp_cat_axioms
    : disp_cat_axioms _ fullification_disp_cat_data.
  Proof.
    repeat split.
    - intros; apply id_left_disp.
    - intros; apply id_right_disp.
    - intros; apply assoc_disp.
    - intros; apply homsets_disp.
  Defined.

  Definition fullification_disp_cat : disp_cat C.
  Proof.
    exists fullification_disp_cat_data.
    apply fullification_disp_cat_axioms.
  Defined.

  Definition from_fullification_ob_mor
    : disp_functor_data (functor_identity _) fullification_disp_cat D.
  Proof.
    exists (fun x xx => F x xx).
    intros x y xx yy f ff; exact ff.
  Defined.

  Definition from_fullification_axioms
    : disp_functor_axioms from_fullification_ob_mor.
  Proof.
    repeat split. (* Startling that this completes the proof! 
    The reason is that under the expected “split”, all goals just need “refl”,
    which is a 1-constructor inductive, so “split” finds that too. *)
  Defined.

  Definition from_fullification
    : disp_functor (functor_identity _) fullification_disp_cat D.
  Proof.
    exists from_fullification_ob_mor; exact from_fullification_axioms.
  Defined.

  Definition from_fullification_ff
    : disp_functor_ff from_fullification.
  Proof.
    intros ? ? ? ? ?; apply idisweq.
  Defined.

  (* TODO: some form of the universal property — this is a right bi-adjoint from “disp-cats-with-functor-to-D” to “disp-cats-with-ff-functor-to-D”. *)

  (* TODO specifically: at least the unit map [D —> fullification F] *)
  
End Fullification_Disp_Cat.

Section Fullification_Fibration.

  Context {C : category} {D : disp_cat C}.

  Definition fullification_cleaving
      {D' : disp_cat C} (D'_fib : cleaving D')
      (F : cartesian_disp_functor (functor_identity _) D' D)
    : cleaving (fullification_disp_cat F).
  Proof.
    intros x x' f xx.
    set (d'_ff_ffcart := D'_fib _ _ f xx).
    exists (pr1 d'_ff_ffcart).
    exists (# F (pr12 d'_ff_ffcart))%mor_disp.
    eapply ff_reflects_cartesian. { apply from_fullification_ff. }
    apply cartesian_disp_functor_is_cartesian.
    exact (pr22 _).
  Defined.

  Definition fullification_fibration
      {D' : fibration C}
      (F : cartesian_disp_functor (functor_identity _) D' D)
    : fibration C.
  Proof.
    exists (fullification_disp_cat F). apply fullification_cleaving, D'.
  Defined.

  Definition from_fullification_is_cartesian
      {D' : fibration C}
      (F : cartesian_disp_functor (functor_identity _) D' D)
    : is_cartesian_disp_functor (from_fullification F).
  Proof.
    (* probably use: to show a map from a fibration cartesian,
     enough to show it preserves cartesianness of given lifts *)
  Admitted.

  Definition from_fullification_fibration
      {D' : fibration C}
      (F : cartesian_disp_functor (functor_identity _) D' D)
    : cartesian_disp_functor (functor_identity _) (fullification_fibration F) D.
  Proof.
    exists (from_fullification F). apply from_fullification_is_cartesian. 
  Defined.

  (* TODO: specialise universal property of fullification from disp-cats to fibrations *)
End Fullification_Fibration.

Section Fullification.
  Context {C : category} (T : comprehension_cat_structure C).

  Definition fullification_compcat : comprehension_cat_structure C.
  Proof.
    use make_comprehension_cat_structure.
    - exact (fullification_fibration (comprehension T)).
    - apply from_fullification_fibration.
  Defined.

  (* TODO: universal property *)

End Fullification.
