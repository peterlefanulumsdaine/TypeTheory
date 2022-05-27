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
(* Some missing access functions for fibrations and comprehension cats.
  TODO: split out into their own file(s), and unify with the more specialised access functions for _discrete_ comp cats given elsewhere. *)

  Coercion disp_cat_from_fibration {C} : fibration C -> disp_cat C := pr1.
  
  Coercion types_fib {C} (T : comprehension_cat_structure C)
    : fibration C
  := (pr1 T,, pr1 (pr2 T)).

  Definition comprehension {C} (T : comprehension_cat_structure C)
    : disp_functor (functor_identity C) T (disp_codomain C)
  := pr1 (pr2 (pr2 T)).

End Auxiliary.

Section Fullification_Disp_Cat.

  Context {C : category} (D D' : disp_cat C) (F : disp_functor (functor_identity _) D' D).
  
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

  (* TODO: factorisation of F *)

End Fullification_Disp_Cat.

Section Fullification_Fibration.

  Context {C : category} (D D' : fibration C)
          (F : cartesian_disp_functor (functor_identity _) D D').
  
  Definition fullification_fibration : fibration C.
  Admitted.

End Fullification_Fibration.

Section Fullification.
  Context {C : category} (T : comprehension_cat_structure C).
  
  Definition fullification_compcat : comprehension_cat_structure C.
  Admitted.

End Fullification.
