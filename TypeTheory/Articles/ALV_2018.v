(**
  [Articles.ALV_2018]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

This file is intended to accompany a sequel article to ALV-2017, currently in (delayed) preparation.  Eventually, it should provide an index to the results of the paper, similar to that of [Articles.ALV_2017].  For now, this file contains placeholder results and statements, with [Admitted.], giving a roadmap of the planned paper.

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Cats.

(** * Categories of the structures under consideration *)

Definition split_typecat_structure_cat (C : category) : category.
Admitted.

Definition split_typecat'_structure_cat (C : category) : category
  := sty'_structure_precat C.

Definition cwf_structure_cat (C : category) : category.
Admitted.

Definition cwf'_structure_cat (C : category) : category
  := cwf'_structure_precat C.

Definition rep_map_cat (C : category) : category.
Admitted.

Definition rel_univ_structure_cat (C : category) : category.
Admitted.

Definition wk_rel_univ_structure_cat (C : category) : category.
Admitted.

(** ** Univalence of these categories. *)

Definition is_univalent_split_typecat_structure (C : category)
  : is_univalent (split_typecat_structure_cat C).
Admitted.

Definition is_univalent_split_typecat'_structure_cat (C : category)
  : is_univalent (split_typecat'_structure_cat C).
Admitted.

Definition is_univalent_cwf_structure_cat (C : category)
  : is_univalent (cwf_structure_cat C).
Admitted.

Definition is_univalent_cwf'_structure_cat (C : category)
  : is_univalent (cwf'_structure_precat C).
Admitted.

Definition is_univalent_rep_map_cat (C : category)
  : is_univalent (rep_map_cat C).
Admitted.

Definition is_univalent_rel_univ_structure_cat (C : category)
  : is_univalent (rel_univ_structure_cat C).
Admitted.

Definition is_univalent_wk_rel_univ_structure_cat (C : category)
  : is_univalent (wk_rel_univ_structure_cat C).
Admitted.

(** * Equivalence of categories between split type structures and families structures *)

(** ** Equivalence between two versions of cwf structures *)

Definition equiv_cat_cwf_cwf'_structure (C : category)
  : equivalence_of_cats (cwf_structure_cat C) (cwf'_structure_cat C).
Admitted.

(** ** Equivalence between two versions of split typecat structures *)

Definition equiv_cat_standalone_to_regrouped (C : category)
  : equivalence_of_cats
      (split_typecat_structure_cat C) (split_typecat'_structure_cat C).
Admitted.

(** ** Auxiliary equivalence between the reordered structures *)

Definition weq_cwf'_sty' (C : category)
  : equivalence_of_cats
      (cwf'_structure_cat C) (split_typecat'_structure_cat C).
Admitted.

(** ** Main construction: equivalence between split typecat structures and cwf structures *)

Definition weq_sty_cwf (C : category)
  : equivalence_of_cats
      (split_typecat_structure_cat C) (cwf_structure_cat C).
Admitted.


(** * Map from [cwf_structure C] to [rep_map C] *)
(** and proof that the map is an equivalence when [C] is univalent *)  

Definition functor_cwf_to_rep (C : category)
  : cwf_structure_cat C ⟶ rep_map_cat C. 
Admitted.

Proposition fully_faithful_cwf_to_rep (C : category)
  : fully_faithful (functor_cwf_to_rep C).
Admitted.

Definition isweq_from_cwf_to_rep {C : category} (C_univ : is_univalent C)
  : adj_equivalence_of_cats (functor_cwf_to_rep C).
Admitted.

(** * Functorial transfer results for various structures *)

Definition transfer_cwf_weak_equivalence {C D : category} (F : C ⟶ D)
  : fully_faithful F → essentially_surjective F
    → is_univalent D → 
    cwf_structure_cat C ⟶ cwf_structure_cat D.
Admitted.
(* TODO: perhaps show functorial in F also. *)

Definition transfer_rep_map_weak_equivalence
  {C D : category} (F : C ⟶ D) 
  : fully_faithful F → essentially_surjective F
  → equivalence_of_cats (rep_map_cat C) (rep_map_cat D).
Admitted.

Definition equiv_cat_rep_map_cwf_Rezk (C : category)
  : equivalence_of_cats
      (rep_map_cat C)
      (cwf_structure_cat (Rezk_completion C)).
Admitted.

(** * Comparison with comprehension categories *)

(** (Bi)categories of comprehension categories, and the fullification adjunction *)

(** Equivalece between (non-split) type-cat structures and full comprehension cat structures on a category *)

(** Equivalence between split type-cat structures and discrete comprehension cat structures on a category *)

(** Commutativity of the (split) type-cat inclusions modulo fullification *)


