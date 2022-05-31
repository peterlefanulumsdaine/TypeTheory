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
Require Import TypeTheory.Auxiliary.DisplayedCategories.

Require Import TypeTheory.CompCats.FullyFaithfulDispFunctor.

Local Open Scope hide_transport_scope. (* for calculations in displayed cats *)

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

  (** ** Displayed natural isomorphisms *)
  Arguments disp_functor_cat {_ _} _ _.

  Definition disp_nat_iso
      {C C' : category} {F G : functor C C'} (α : nat_iso F G)
      {D : disp_cat C} {D' : disp_cat C'}
      (FF : disp_functor F D D') (GG : disp_functor G D D')
    : UU
  := @iso_disp _ (disp_functor_cat D D') _ _ α FF GG.

  Definition disp_nat_iso_of_id
      {C C' : category} {F G : functor C C'} (e : F = G)
      {D : disp_cat C} {D' : disp_cat C'}
      (FF : disp_functor F D D') (GG : disp_functor G D D')
      (ee : transportf (fun H => disp_functor H _ _) e FF = GG)
    : disp_nat_iso (@idtoiso [_,_] _ _ e) FF GG.
  Proof.
    apply idtoiso_disp, ee.
  Defined.

  (** ** Missing access functions for displayed isomorphisms *)
  
  Definition iso_inv_disp
      {C : category} {D : disp_cat C} {x y : C} {i : iso x y}
      {xx : D x} {yy : D y} (ii : iso_disp i xx yy)
    : yy -->[inv_from_iso i] xx
  := pr12 ii.

  Definition iso_after_iso_inv_disp
      {C : category} {D : disp_cat C} {x y : C} {i : iso x y}
      {xx : D x} {yy : D y} (ii : iso_disp i xx yy)
    : (iso_inv_disp ii ;; ii)%mor_disp
      = transportb _ (iso_after_iso_inv i) (id_disp yy)
  := pr122 ii.

  Definition iso_inv_after_iso_disp
      {C : category} {D : disp_cat C} {x y : C} {i : iso x y}
      {xx : D x} {yy : D y} (ii : iso_disp i xx yy)
    : (ii ;; iso_inv_disp ii)%mor_disp
      = transportb _ (iso_inv_after_iso i) (id_disp xx)
  := pr222 ii.

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
  Lemma fully_faithful_disp_inv_hom
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

  Context {C : category} {E D : disp_cat C}
          (FF : disp_functor (functor_identity _) D E).
(* This construction can be generalised to work over a functor [ F : C' -> C ], but in the general case, the structure on the fullification gets complicated by transports along [functor_id], [functor_comp].  Since this simpler special case is what we expect to use, we give just this for now, to keep it tractable. *)
  
  Definition fullification_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists D.
    intros x y xx yy f. exact ((FF x xx) -->[f] (FF y yy)).
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
    : disp_functor_data (functor_identity _) fullification_disp_cat E.
  Proof.
    exists (fun x xx => FF x xx).
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
    : disp_functor (functor_identity _) fullification_disp_cat E.
  Proof.
    exists from_fullification_ob_mor; exact from_fullification_axioms.
  Defined.

  Definition from_fullification_ff
    : disp_functor_ff from_fullification.
  Proof.
    intros ? ? ? ? ?; apply idisweq.
  Defined.

  (* There are several possible ways to state and prove the universal property —that this is a right bi-adjoint from “disp-cats-with-functor-to-D” to “disp-cats-with-ff-functor-to-D”.

  Option 1: “there’s an equivalence [ (D' —> D'') ~ (fullif D' -> D'') ] for any D'' fully-faithful over D”; then defined the unit [ D' —> fullif D' ] as corresponding to the identity under this

  Option 2: define the unit [D' —> fullif D'] explicitly, then show that composition with it induces an equivalence. 

  Either way: How to show equivalence of these complex objects?  Oe way: exhibit them as a univalent displayed category, and show this is an equivalence of cats.  But will it be univaleny in general?  Probably not — where as this u.m.p. really should be!  Perhaps: just show it explicitly? 

  In fact: all this should be a little more general, and needs to be, to give the eventually desired universal property of the fullification of a comp cat.  It should be generalised to over a functor not the identity. *)

  Definition fullification_unit_data
    : disp_functor_data (functor_identity _) D fullification_disp_cat.
  Proof.
    exists (fun c d => d).
    intros ? ? ? ? ?; apply (# FF)%mor_disp.    
  Defined.

  Definition fullification_unit_axioms
    : disp_functor_axioms fullification_unit_data.
  Proof.
    split.
    - apply @disp_functor_id.
    - apply @disp_functor_comp.
  Defined.

  Definition fullification_unit
    : disp_functor (functor_identity _) D fullification_disp_cat.
  Proof.
    exists fullification_unit_data.
    apply fullification_unit_axioms.
  Defined.

  (** The universal property we give here is neither the simplest form of the universal property of fullification, nor the most general.

  The simplest form would take C'=C, G=id, D'=D: in other words, it just compares [fullification FF] with other factorisations of [FF] through a fully-faithful functor into [D].

  A very general form could have [FF'] living over a further functor [C' -> C''] (and could also have started with [FF] living over a non-identity functor).  However, it complicates the statements and constructions a lot. The most general form is probably best formulated as a “displayed factorisation system”: showing that “injective on objects” functors have unique lifts against “full and faithful”.

  The intermediate form we give here is just what’s needed to show that the fullification of _comprehension categories_ is a reflection into the sub-2-category of full comp-cats.

  We preview it here, before building it up gradually below. 
 *)
  (* TODO: consider naming! *)
  (* TODO: in fact this probably isn’t the right version to give (though this should be true too): we will want a version with a natural isomorphism instead of an equality; and as such, its uniqueness will probably hold only up to isomorphism. *)
  Definition fullification_universal_property_general
    {C' : category} {D' E' : disp_cat C'}
    (FF' : disp_functor (functor_identity _) D' E')
    {G : functor C C'} (GE : disp_functor G E E') (GE_ff : disp_functor_ff GE)
  : (∑ (GD : disp_functor G D D'),
      transportf (fun G' => disp_functor G' _ _) (functor_identity_right _ _ _) 
                 (disp_functor_composite GD FF')
      = disp_functor_composite FF GE)
   ≃ 
    (∑ (GD : disp_functor G fullification_disp_cat D'),
      transportf (fun G' => disp_functor G' _ _) (functor_identity_right _ _ _) 
                 (disp_functor_composite GD FF')
      = disp_functor_composite from_fullification GE).
  Proof.
  Abort.

  Section Strict_Universal_Property.
    (* The version we start with is _strict_ insofar as it assumes an equality of composites, not just a natural iso. *)
    
    Context 
        {C' : category} {D' E' : disp_cat C'}
        (FF' : disp_functor (functor_identity _) D' E')
          (FF_ff : disp_functor_ff FF')
        {G : functor C C'} (GE : disp_functor G E E')
        (GD : disp_functor G D D')
        (e : transportf (fun G' => disp_functor G' _ _) (functor_identity_right _ _ _) 
                        (disp_functor_composite GD FF')
             = disp_functor_composite FF GE).
(*
          D —————FF———> E _______    GE
           \    \_____ /         \________
            \         X______GD           \________>
             \       /       \—————> D' ————FF'—————> E'
              \     /                 \            /
               \   /                   \          /
                V V                     \        /
                 C ____                  \      /
                       \_____ G           \    /
                             \______       V  V
                                    \—————> C'
*)
    Local Definition FF'_GD_iso_GE_FF
      : disp_nat_iso _
          (disp_functor_composite GD FF') (disp_functor_composite FF GE)
    := disp_nat_iso_of_id _ _ _ e.

    Local Definition FF'_GD_iso_GE_FF_ptwise {x:C} (xx:D x)
      : iso_disp (identity_iso _) (FF' _ (GD _ xx)) (GE _ (FF _ xx)).
    Proof.
      (* some wrestling with the above [disp_nat_iso]; perhaps unnecessary if we should have assumed a displayed nat iso from the start? *)
    Admitted.

    Definition from_fullification_general_data
      : disp_functor_data G fullification_disp_cat D'.
    Proof.
      exists GD.
      intros x y xx yy f ff.
      apply (fully_faithful_disp_inv_hom FF'). { assumption. }
      simpl.
      (* TODO: are there better idioms for composition with (nat-)isos-over-identity? could we set up a better interface? *)
      refine (transportf _ (id_left _) _).
      eapply comp_disp. { use FF'_GD_iso_GE_FF_ptwise. }
      refine (transportf _ (id_right _) _).
      eapply comp_disp. 2: { apply (iso_inv_disp (FF'_GD_iso_GE_FF_ptwise _)). }
      simpl. exact (#GE ff)%mor_disp.
    Defined.

    Definition from_fullification_general_axioms
      : disp_functor_axioms from_fullification_general_data.
    Proof.
      split.
      - intros x xx. simpl.
        apply invmap_eq. simpl.
        (* rewrite RHS to (transport of) identity *)
        unfold transportb. rewrite (disp_functor_transportf _ FF').
        rewrite (disp_functor_id FF'). unfold transportb; rewrite transport_f_f.
        (* rewrite LHS to (transport of) identity *)
        rewrite mor_disp_transportf_prewhisker, transport_f_f.
        cbn. rewrite (disp_functor_id GE).
        unfold transportb; rewrite mor_disp_transportf_postwhisker,
          mor_disp_transportf_prewhisker, transport_f_f.
        rewrite id_left_disp. unfold transportb;
          rewrite mor_disp_transportf_prewhisker, transport_f_f.
        etrans. { apply maponpaths, 
                    (iso_inv_after_iso_disp (FF'_GD_iso_GE_FF_ptwise xx)). }
        rewrite transport_f_b.
        apply transportf_paths, homset_property.
      - intros x y z xx yy zz f g ff gg; simpl.
        apply invmap_eq; simpl.
        (* rewrite LHS to transport of composite, right-associated *)
        etrans. { 
          rewrite mor_disp_transportf_prewhisker, transport_f_f.
          cbn; rewrite (disp_functor_comp GE).
          unfold transportb. rewrite mor_disp_transportf_postwhisker,
                               mor_disp_transportf_prewhisker, transport_f_f.
          rewrite assoc_disp_var,  mor_disp_transportf_prewhisker, transport_f_f.
          apply idpath.
        }
        (* rewrite RHS to transport of composite, right-associated to match LHS *)
        etrans. 2: { apply pathsinv0.
          unfold transportb. rewrite (disp_functor_transportf _ FF').
          rewrite (disp_functor_comp FF').
          unfold transportb; rewrite transport_f_f.
          etrans. { apply maponpaths, maponpaths. use homotweqinvweq. }
          etrans. { apply maponpaths, maponpaths_2. use homotweqinvweq. }
          rewrite mor_disp_transportf_postwhisker,
            4 mor_disp_transportf_prewhisker,
            mor_disp_transportf_postwhisker,
            4 transport_f_f.
          etrans. { apply maponpaths, maponpaths_2, assoc_disp. }
          unfold transportb; 
            rewrite mor_disp_transportf_postwhisker, transport_f_f.
          rewrite assoc_disp_var, transport_f_f.
          etrans. { apply maponpaths, maponpaths.
            rewrite assoc_disp.
            apply maponpaths, maponpaths_2. 
            apply (iso_after_iso_inv_disp (FF'_GD_iso_GE_FF_ptwise _)).
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker, id_left_disp.
          unfold transportb. rewrite 2 transport_f_f,
            mor_disp_transportf_prewhisker, transport_f_f.
          rewrite assoc_disp_var.
          apply transport_f_f.
       }
       apply transportf_paths, homset_property.
    Qed.
    (* TODO: Quite slow here!  Would it be quicker using explicit algebra instead of rewrite? *)

    Definition from_fullification_general
      : disp_functor G fullification_disp_cat D'.
    Proof.
      exists from_fullification_general_data.
      apply from_fullification_general_axioms.
    Defined.

  End Strict_Universal_Property.

  Definition fullification_universal_property_general
    {C' : category} {D' E' : disp_cat C'}
    (FF' : disp_functor (functor_identity _) D' E')
          (FF'_ff : disp_functor_ff FF')
    {G : functor C C'} (GE : disp_functor G E E')
  : (∑ (GD : disp_functor G D D'),
      transportf (fun G' => disp_functor G' _ _) (functor_identity_right _ _ _) 
                 (disp_functor_composite GD FF')
      = disp_functor_composite FF GE)
   ≃ 
    (∑ (GD : disp_functor G fullification_disp_cat D'),
      transportf (fun G' => disp_functor G' _ _) (functor_identity_right _ _ _) 
                 (disp_functor_composite GD FF')
      = disp_functor_composite from_fullification GE).
  Proof.
  Admitted.

End Fullification_Disp_Cat.


Section Fullification_Fibration.

  Context {C : category} {E : disp_cat C}.

  Definition fullification_cleaving
      {D : disp_cat C} (D_fib : cleaving D)
      (FF : cartesian_disp_functor (functor_identity _) D E)
    : cleaving (fullification_disp_cat FF).
  Proof.
    intros x x' f xx.
    set (d'_ff_ffcart := D_fib _ _ f xx).
    exists (pr1 d'_ff_ffcart).
    exists (# FF (pr12 d'_ff_ffcart))%mor_disp.
    eapply ff_reflects_cartesian. { apply from_fullification_ff. }
    apply cartesian_disp_functor_is_cartesian.
    exact (pr22 _).
  Defined.

  Definition fullification_fibration
      {D : fibration C}
      (FF : cartesian_disp_functor (functor_identity _) D E)
    : fibration C.
  Proof.
    exists (fullification_disp_cat FF). apply fullification_cleaving, D.
  Defined.

  Definition from_fullification_is_cartesian
      {D : fibration C}
      (FF : cartesian_disp_functor (functor_identity _) D E)
    : is_cartesian_disp_functor (from_fullification FF).
  Proof.
    (* probably use: to show a map from a fibration cartesian,
     enough to show it preserves cartesianness of given lifts *)
  Admitted.

  Definition from_fullification_fibration
      {D : fibration C}
      (FF : cartesian_disp_functor (functor_identity _) D E)
    : cartesian_disp_functor (functor_identity _) (fullification_fibration FF) E.
  Proof.
    exists (from_fullification FF). apply from_fullification_is_cartesian. 
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
