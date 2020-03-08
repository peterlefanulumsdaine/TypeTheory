
Require Import TypeTheory.ECategories.Auxiliary
        TypeTheory.ECategories.SwedishSetoids.

Delimit Scope ecats_scope with ecats.
Open Scope ecats_scope.

(** * E-categories *)

Record ECat : Type
:= {
    Obj_ECat :> Type;
    Hom (a b : Obj_ECat)      : setoid;
    id {a}                    : Hom a a;
    comp {a b c}              : Hom b c ⇒ Hom a b ⇒ Hom a c;
    idL {a b} (f : Hom a b)   : comp id f ≈ f;
    idR {a b} (f : Hom a b)   : comp f id ≈ f;
    assoc {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d)
                              : comp h (comp g f) ≈ comp (comp h g) f
  }.

Arguments Hom [X] a b : rename.
Arguments id [X a] : rename.
Arguments comp [X a b c] : rename.
Arguments idL [X a b f] : rename.
Arguments idR [X a b f] : rename.
Arguments assoc [X a b c d f g h] : rename.

Notation "F ° G" := (comp F G) (at level 10).

(** * Isomorphisms *)

Definition is_iso {X : ECat} {a b : X} (f : Hom a b)
  := ∃ g : Hom b a, g ° f ≈ id ∧ f ° g ≈  id.

Lemma id_is_iso {X : ECat} (a : X) : is_iso (id : Hom a a).
Proof.
  exists id.
  split; apply idL.
Defined.

Definition inv_iso {X : ECat} {a b : X} {f : Hom a b} (fI : is_iso f)
  : Hom b a
:= pr1 fI.

(* Naming conventions for these lemmas follow the conventions used for paths in the HoTT library, documented there. *)
Lemma iso_fV {X : ECat} {a b : X} {f : Hom a b} (fI : is_iso f)
  : f ° (inv_iso fI) ≈ id.
Proof.
  exact (snd (pr2 fI)).
Qed.

Lemma iso_Vf {X : ECat} {a b : X} {f : Hom a b} (fI : is_iso f)
  : (inv_iso fI) ° f ≈ id.
Proof.
  exact (fst (pr2 fI)).
Qed.

(** * Terminal objects *)

Definition is_terminal {C : ECat} (t : C)
  := ∀ a:C, ∃ e : Hom a t,
       ∀ f : Hom a t, f ≈ e.

Definition terminal_existence {C : ECat} {t : C} (p : is_terminal t) (a : C)
  : Hom a t
  := pr1 (p a).

Lemma terminal_uniqueness {C : ECat} {t : C} (Ht : is_terminal t) {x} (f g : Hom x t)
  : f ≈ g.
Proof.
  eapply tra_setoid. apply (pr2 (Ht x)).
  apply sym_setoid, (pr2 (Ht x)).
Qed.

(** * Pullbacks *)

Definition ispullback {X : ECat} {a b c d : X}
  (q : Hom a b) (p : Hom a c) (g : Hom b d) (f : Hom c d)
:=
    f ° p ≈ g ° q   
  ∧
    (∀ a':X, ∀ q' : Hom a' b, ∀ p' : Hom a' c, 
      f ° p' ≈ g ° q'  
      -> ∃ r : Hom a' a, p' ≈ p ° r ∧ q'≈ q ° r)
  ∧
    (∀ a':X, ∀ r r' : Hom a' a, 
      p ° r ≈ p ° r' -> q ° r ≈ q ° r' -> r ≈ r').
 
Definition pb_comm {C : ECat} {a b c d : C}
    {q : Hom a b} {p : Hom a c} {g : Hom b d} {f : Hom c d}
    (pb : ispullback q p g f)
  : f ° p ≈ g ° q.
Proof.
  exact (fst pb).
Defined.

Definition pbpair {X : ECat} {a b c d : X}
    {q : Hom a b} {p : Hom a c} {g : Hom b d} {f : Hom c d}
    (pbpf : ispullback q p g f)
  : ∀ a':X, ∀ q' : Hom a' b, ∀ p' : Hom a' c, 
      f ° p' ≈ g ° q' -> Hom a' a 
  := fun a' q' p' P
        => (pr1 ((fst (snd pbpf)) a' q' p' P)).

Theorem pbpair_comm {X : ECat} {a b c d : X}
    {q : Hom a b} {p : Hom a c} {g : Hom b d} {f : Hom c d}
    (pbpf : ispullback q p g f)
  : ∀ a':X,  ∀ q' : Hom a' b, ∀ p' : Hom a' c, 
      ∀ w : f ° p' ≈ g ° q',  
        p' ≈ p ° (pbpair pbpf a' q' p' w)  
        ∧ q' ≈ q ° (pbpair pbpf a' q' p' w).
Proof.
  intros. apply (pr2 ((fst (snd pbpf)) _ _ _ _)).
Defined.

(* TODO : perhaps rename to [pb_uniq], since this isn’t about [pbpair] specifically? *) 
Theorem pbpair_uniq {X : ECat} {a b c d : X}
    {q : Hom a b} {p : Hom a c} {g : Hom b d} {f : Hom c d}
    (pbpf : ispullback q p g f)
  : ∀ a':X, ∀ r r' : Hom a' a, 
      (p ° r ≈  p ° r') -> (q ° r ≈  q ° r') -> r ≈ r'.
Proof.
  apply (snd (snd pbpf)).
Defined.


(** * E-functors between E-categories *)
     
Record efunctor_type (X Y : ECat) : Type
:= {
    ftorobj :> X -> Y;
    ftorarr : ∀ a b : X, 
                Hom a b ⇒ 
                 Hom (ftorobj a) (ftorobj b);
    ftorid   : ∀ a : X, 
                ftorarr a a id ≈ 
                  id;
    ftorcmp  : ∀ a b c : X, 
                ∀ f : Hom a b, ∀ g : Hom b c,
                ftorarr a c (g ° f) ≈
                  (ftorarr b c g) ° (ftorarr a b f)  
  }.

Definition Build_efunctor X Y Fobj Farr Fid Fcmp
  := Build_efunctor_type X Y Fobj Farr Fid Fcmp.

Notation "F [ f ]" := (ftorarr _ _ F _ _ f)
  (at level 9).

(** * Natural transformations *)

Record nattransf_type {X Y} (F G : efunctor_type X Y) : Type
:= {
    nt_transf :> forall x:X, Hom (F x) (G x) ;
    nt_nat : forall x y f, (G [ f ]) ° (nt_transf x) ≈ (nt_transf y) ° (F [ f ])
  }.

Arguments nt_transf [X Y F G] α x : rename.
Arguments nt_nat [X Y F G] α [x y] f : rename.

Definition nattransf {X Y} (F G : efunctor_type X Y) : setoid.
Proof.
  refine (Build_setoid (nattransf_type F G) (fun α β => forall x, α x ≈ β x) _);
    split.
  intros α x. apply refl_setoid.
  intros α β e x. apply sym_setoid, e.
  intros α β γ e e' x. eapply tra_setoid. apply e. apply e'.
Defined.

Definition id_nattransf {X Y} (F : efunctor_type X Y) : nattransf F F.
Proof.
  exists (fun x => id).
  intros. eapply tra_setoid. apply idR. apply sym_setoid, idL.
Defined.

Definition comp_nattransf {X Y} {F G H : efunctor_type X Y} 
  : nattransf G H ⇒ nattransf F G ⇒ nattransf F H.
Proof.
  transparent assert
    (cmp_nt_0 : (nattransf G H -> nattransf F G -> nattransf F H)).
    intros β α. 
    exists (fun x => (β x) ° (α x)); intros.
    eapply tra_setoid. apply assoc.
    eapply tra_setoid. apply ap_setoid_2, nt_nat.
    eapply tra_setoid. apply sym_setoid, assoc.
    eapply tra_setoid. apply ap_setoid, nt_nat.
    eapply assoc.
  transparent assert
    (cmp_nt_1 : (nattransf G H -> nattransf F G ⇒ nattransf F H)).
    intros β. exists (cmp_nt_0 β).
    intros α α' e x; simpl. apply ap_setoid, e.
  exists (fun β => cmp_nt_1 β).
  intros β β' e α x; simpl. apply ap_setoid_2, e.
Defined.

(** * E-categories of E-functors *)

Definition efunctor (X Y : ECat) : ECat.
Proof.
  refine (Build_ECat
    (efunctor_type X Y) nattransf id_nattransf (@comp_nattransf _ _) _ _ _).
  intros; intro; apply idL.
  intros; intro; apply idR.
  intros; intro; apply assoc.
Defined.

Lemma ftorarr_extensionality (X Y : ECat) (F : efunctor X Y)
    (a b : X) (f g : Hom a b)
  : f ≈ g -> F [ f ] ≈ F [ g ].
Proof.
  intro P. apply ap_setoid.
  apply P.
Defined.

Definition comp_efunctor {X Y Z} (G : efunctor Y Z) (F : efunctor X Y)
  : efunctor X Z.
Proof.
  refine (Build_efunctor _ _ (fun x => G (F x))
           (fun x y => (ftorarr _ _ G _ _) ∘ (ftorarr _ _ F _ _)) _ _).
  intros; simpl; eapply tra_setoid. 
    apply ap_setoid, ftorid. apply ftorid.
  intros; simpl; eapply tra_setoid.
    apply ap_setoid, ftorcmp. apply ftorcmp.
Defined.

Definition id_efunctor (X : ECat) : efunctor X X.
Proof.
  refine (Build_efunctor _ _ (fun x => x) (fun x y => idmap_setoid) _ _);
  intros; apply refl_setoid.
Defined.

Definition nattransf_pw_iso {X Y} {F G : efunctor X Y} (α : Hom F G)
  : (forall x, is_iso (α x)) -> is_iso α.
Proof.
  intros α_pw_iso. unfold is_iso.
  transparent assert (α_inv : (Hom G F)).
    exists (fun x => inv_iso (α_pw_iso x)).
    intros; simpl.
    eapply tra_setoid. apply sym_setoid, idL.
    eapply tra_setoid. apply ap_setoid_2.
      apply sym_setoid. exact (iso_Vf (α_pw_iso _)).
    eapply tra_setoid. apply sym_setoid, assoc. apply ap_setoid.
    eapply tra_setoid. apply assoc.
    eapply tra_setoid. apply ap_setoid_2.
      apply sym_setoid, nt_nat.
    eapply tra_setoid. apply sym_setoid, assoc.
    eapply tra_setoid. apply ap_setoid, iso_fV.
    apply idR.
  exists α_inv; split; intro x.
  apply iso_Vf. apply iso_fV.
Defined.
    
Definition efunctor_assoc {X Y Z W} 
    (F : efunctor X Y) (G : efunctor Y Z) (H : efunctor Z W)
  : Hom
      (comp_efunctor H (comp_efunctor G F))
      (comp_efunctor (comp_efunctor H G) F).
Proof.
  exists (fun x => @id _ (H (G (F x)))).
  intros; simpl. eapply tra_setoid. apply idR. apply sym_setoid, idL.
Defined.

Lemma efunctor_assoc_is_iso {X Y Z W} 
    (F : efunctor X Y) (G : efunctor Y Z) (H : efunctor Z W)
  : is_iso (efunctor_assoc F G H).
Proof.
  apply nattransf_pw_iso. intro; apply id_is_iso.
Qed.

Definition efunctor_idL {X Y} (F : efunctor X Y)
  : Hom (comp_efunctor (id_efunctor _) F) F.
Proof.
  simple refine (Build_nattransf_type _ _ _ _ _ _); simpl.
  intros; apply id.
  intros; simpl. eapply tra_setoid. apply idR. apply sym_setoid, idL.
Defined.

Lemma efunctor_idL_is_iso {X Y} (F : efunctor X Y)
  : is_iso (efunctor_idL F).
Proof.
  apply nattransf_pw_iso. intro; apply id_is_iso.
Qed.

Definition efunctor_idR {X Y} (F : efunctor X Y)
  : Hom F (comp_efunctor (id_efunctor _) F).
Proof.
  simple refine (Build_nattransf_type _ _ _ _ _ _); simpl.
  intros; apply id.
  intros; simpl. eapply tra_setoid. apply idR. apply sym_setoid, idL.
Defined.

Lemma efunctor_idR_is_iso {X Y} (F : efunctor X Y)
  : is_iso (efunctor_idR F).
Proof.
  apply nattransf_pw_iso. intro; apply id_is_iso.
Qed.

(* TODO : whiskering, interchange, pentagon? *)

(** * Properties of functors *)

Definition preserves_pullbacks {C D : ECat} (F : efunctor C D)
  := forall (a b c d : C)
       (q : Hom a b) (p : Hom a c) (g : Hom b d) (f : Hom c d),
  (ispullback q p g f) -> (ispullback (F [q]) (F [p]) (F [g]) (F [f])). 

Definition reflects_pullbacks {C D : ECat} (F : efunctor C D)
  := forall (a b c d : C)
       (q : Hom a b) (p : Hom a c) (g : Hom b d) (f : Hom c d),
  (ispullback (F [q]) (F [p]) (F [g]) (F [f])) -> (ispullback q p g f). 

Definition preserves_terminal {C D : ECat} (F : efunctor C D)
  := forall a : C, is_terminal a -> is_terminal (F a).

Definition reflects_terminal {C D : ECat} (F : efunctor C D)
  := forall a : C, is_terminal (F a) -> is_terminal a.

(** * Slice E-categories *)

Record slice_obj (X : ECat) (x : X) : Type
:= {
    overobj :> X;
    downarr : Hom overobj x
  }.

Arguments downarr [X] x f : rename.

Definition map_as_slice_obj {C : ECat} {x y : C} (f : Hom x y)
  : slice_obj C y
:= {| overobj := x; downarr := f |}.

Record slice_hom_set {X : ECat} {x : X} (a b : slice_obj X x) : Type
:= {
    upper :> Hom (overobj X x a) (overobj X x b);
    triangle : downarr x b ° upper ≈ downarr x a
  }.

Definition slice_hom {X : ECat} {x : X} (a b : slice_obj X x)
  : setoid.
Proof.
  apply (Build_setoid_flat (slice_hom_set a b)
         (fun f g => upper a b f ≈ upper a b g)).
  intro h. swesetoid.
  intros h k P. swesetoid.
  intros h k l P Q. swesetoid.
Defined.

Definition slice_id {X : ECat} (x : X) (a : slice_obj X x)
  : slice_hom a a.
Proof.
  apply (Build_slice_hom_set X x a a id).
  apply idR.
Defined.

Definition slice_cmp_helper1 {X : ECat} (x : X) (a b c : slice_obj X x)
    (f : slice_hom b c) (g : slice_hom a b)
  : slice_hom a c.
Proof.
  apply (Build_slice_hom_set X x a c ((upper b c f) ° (upper a b g))).
  destruct f as  [f fp]. 
  destruct g as  [g gp]. 
  simpl. 
  assert ( (downarr x c) ° (f ° g) ≈ 
            ((downarr x c) ° f) ° g) as H.
  assert (((downarr x c) ° f) ° g  ≈
            (downarr x b) ° g) as H2.
  apply ap_setoid_12.
  apply fp.
  apply refl_setoid.    
  apply assoc.
  assert (((downarr x c) ° f) ° g  ≈  (downarr x b) ° g) as H3.
  apply ap_setoid_12. 
  apply fp. 
  apply refl_setoid.
  swesetoid.
Defined.

Definition slice_cmp_helper2 {X : ECat} (x : X) (a b c : slice_obj X x)
    (f : slice_hom b c)
  : (slice_hom a b) ⇒ (slice_hom a c).
Proof.
  apply (Build_setoid_map _ _ (slice_cmp_helper1 x a b c f)).
  intros g h P.
  destruct f as  [f fp]. 
  destruct g as  [g gp]. 
  destruct h as  [h hp]. 
  simpl in P. 
  simpl.
  apply ap_setoid_12.
  apply refl_setoid.
  apply P.
Defined.


Definition slice_cmp {X : ECat} (x : X) (a b c : slice_obj X x)
  : (slice_hom b c) ⇒ (slice_hom a b) ⇒ (slice_hom a c).
Proof.
  apply (Build_setoid_map _ _ (slice_cmp_helper2 x a b c)).
  intros f g P.
  intro h.
  destruct f as  [f fp]. 
  destruct g as  [g gp]. 
  destruct h as  [h hp]. 
  simpl in P. 
  simpl.
  apply ap_setoid_12.
  apply P. 
  apply refl_setoid.
Defined.

Definition slice (X : ECat) (x : X) : ECat.
Proof.
  apply (Build_ECat (slice_obj X x)
           (fun a b => slice_hom a b)
           (fun a => slice_id x a)
           (fun a b c => slice_cmp x a b c)).
  intros. simpl. apply idL. 
  intros. simpl. apply idR.
  intros. simpl. apply assoc.         
Defined.

Definition forgetful_functor_from_slice (C : ECat) (c : C)
  : efunctor (slice C c) C.
Proof.
  simple refine (Build_efunctor (slice _ _) C (fun c => c) _ _ _).
  (* ftorarr *) simpl; intros x' x.
  refine (Build_setoid_map (slice_hom _ _) (Hom _ _) (fun f => f) _). auto.
  (* ftorid *) intros; apply refl_setoid.
  (* ftorcmp *) intros; apply refl_setoid.
Defined.

(** A universal property of the slice : functors into [slice D d0] correspond to functors into the [D] equipped with a co-cone to [d0]. *)
(* TODO : factor out definition of co-cone? *)
Definition functor_to_slice {C D} (F : efunctor C D)
    {d0 : D} (cone_map : forall c:C, Hom (F c) d0)
    (cone_comm : forall c' c (f : Hom c' c),
                   (cone_map c) ° (F[f]) ≈ (cone_map c'))
  : efunctor C (slice D d0).
Proof.
  simple refine (Build_efunctor _ (slice _ _)
    (fun c => map_as_slice_obj (cone_map c)) _ _ _).
  (* ftorarr *) simpl; intros c' c. simple refine (Build_setoid_map _ _ _ _).
    intros f. exists (F [f]). apply cone_comm.
  simpl. apply ap_setoid_1; assumption.
  (* ftorid *) intros; apply ftorid.
  (* ftorcmp *) intros; apply ftorcmp.
Defined.

(* TODO : perhaps try re-typing this as “the forgetful functor from the slice preserves pullbacks”; see if that’s more or less convenient to use. *)
Lemma pullback_in_slice {C : ECat} {x : C}
    {a b c d : slice C x}
    (q : Hom a b) (p : Hom a c) (g : Hom b d) (f : Hom c d)
  : @ispullback C _ _ _ _ q p g f
    -> @ispullback (slice C x) _ _ _ _ q p g f.
Proof.
  intros [e [pbpair pbuniq]].
  split. exact e.
  split; intros.
    transparent assert (pair_q'_p' : (Hom a' a)). 
      exists (pr1 (pbpair a' q' p' X)).
      eapply tra_setoid.
        apply ap_setoid_2, sym_setoid. exact (triangle _ _ q).
      eapply tra_setoid. apply sym_setoid, assoc.
      eapply tra_setoid.
        apply ap_setoid_1, sym_setoid.
        refine (snd (pr2 (pbpair _ _ _ _))).
      apply triangle.
    exists pair_q'_p'.
    refine (pr2 (pbpair _ _ _ _)).
  apply pbuniq; assumption.
Qed.

Lemma id_terminal_in_slice {C : ECat} (x : C)
  : @is_terminal (slice C x) (map_as_slice_obj id).
Proof.
  intros x'_f. 
  exists (Build_slice_hom_set _ _ _ (map_as_slice_obj _)
    (downarr _ x'_f) idL).
  intros; simpl.
  eapply tra_setoid. apply sym_setoid, idL.
  apply (triangle _ _ f).
Qed.

Definition slice_to_double_slice (C : ECat) (X : C) (Yf : slice C X)
  : efunctor (slice C Yf) (slice (slice C X) Yf).
Proof.
  transparent assert (ftorobj : (slice C Yf → slice (slice C X) Yf)).
  intros Zg.
    exists ( {| overobj := Zg : C ; downarr := comp (downarr _ Yf) (downarr _ Zg) |}
           : slice C X ).
    exists (downarr _ Zg). apply refl_setoid.
  transparent assert (ftorarr : (∀ a b : slice C Yf, Hom a b ⇒ Hom (ftorobj a) (ftorobj b))).
    intros Zg Wh. simple refine (Build_setoid_map _ _ _ _); simpl.
      intros k. simple refine (Build_slice_hom_set _ _ _ _ _ _); simpl.
        simple refine (Build_slice_hom_set _ _ _ _ _ _); simpl. 
          exact ((upper _ _ k) : @Hom C Zg Wh).
        eapply tra_setoid. apply sym_setoid, assoc.
        apply ap_setoid. apply triangle.
      simpl. apply triangle.
    auto.
  refine (Build_efunctor _ _ ftorobj ftorarr _ _).
  (* ftorid *) simpl. auto using refl_setoid.
  (* ftorcmp *) simpl. auto using refl_setoid.
Defined.

(** * Hash : the discrete E-category on a setoid. *)

(* TODO : consider renaming to [discrete_ecat], or similar? *)
Definition hash (A : setoid) : ECat.
Proof.
  transparent assert (hash_cmp : (∀ a b c : A,
    indiscrete_setoid (b ≈ c)
    ⇒ indiscrete_setoid (a ≈ b)
    ⇒ indiscrete_setoid (a ≈ c))).
  intros. apply (@binsetoid_map_helper
    (indiscrete_setoid _) (indiscrete_setoid _) (indiscrete_setoid _)
    (fun bc ab => bc ⊙ ab)); auto.
  apply (Build_ECat A (fun a b => indiscrete_setoid (a ≈ b))
           refl_setoid hash_cmp); intros; constructor.
Defined.

(** * Full subcategories *)

(** The full subcategory of an e-category on a subclass of its objects *)
Definition full_subcat_on_obs (C : ECat) (X : Type) (F : X -> C) : ECat.
Proof.
  refine (Build_ECat X (fun x y => Hom (F x) (F y))
    (fun x => id) (fun x y z => @comp C (F x) (F y) (F z))
      _ _ _); intros.
  apply idL.
  apply idR.
  apply assoc.
Defined.

Definition forgetful_functor_from_full_subcat {C : ECat} {X : Type} {F : X -> C}
  : efunctor (full_subcat_on_obs C X F) C. 
Proof.
  simple refine (Build_efunctor _ _ _ _ _ _).
  (* on obs *) exact F. 
  (* on maps *) intros a b. exact idmap_setoid.
  (* ftorid *) intros; apply refl_setoid. 
  (* ftorcmp *) intros; apply refl_setoid. 
Defined.

Lemma terminal_in_full_subcat {C : ECat} {X : Type} {F : X -> C}
  : reflects_terminal (@forgetful_functor_from_full_subcat C X F).
Proof.
  intros t term_Ft x.
  exists (terminal_existence term_Ft (F x)).
  intros. apply (terminal_uniqueness term_Ft).
Defined.

Lemma pullback_in_full_subcat {C : ECat} {X : Type} {F : X -> C}
  : reflects_pullbacks (@forgetful_functor_from_full_subcat C X F).
Proof.
  intros a b c d q p f g pb_C. split.
  (* pb_comm *) apply (pb_comm pb_C).
  split; simpl. 
  (* pbpair, pbpair_comm *) intros a' q' p' comm'.
  exists (pbpair pb_C _ q' p' comm'). 
  apply pbpair_comm.
  (* pbpair_uniq *) intros a' r r' comm_r comm_r'.
  apply (pbpair_uniq pb_C _ _ _ comm_r comm_r').
Defined.

(** A universal property of the full subcategory *)
Definition functor_to_full_subcat {C D} (F : efunctor C D)
    {X : Type} (i : X -> D)
    (F_lift : forall c : C, { x:X & { f : Hom (i x) (F c) & is_iso f }})
  : efunctor C (full_subcat_on_obs D X i).
Proof.
  simple refine (Build_efunctor _ (full_subcat_on_obs _ _ _)
    (fun c => pr1 (F_lift c)) _ _ _).
  (* ftorar *) intros a b. simpl.
  eapply comp_setoid. Focus 2. apply (ftorarr _ _ F). 
  eapply comp_setoid. exact (comp (inv_iso (pr2 (pr2 (F_lift b))))).
  eapply comp_setoid. Focus 2. eapply comp. 
  apply ev_setoid_map. exact (pr1 (pr2 (F_lift a))).
  (* ftorid *) intros a; simpl.
  eapply tra_setoid. apply ap_setoid_1, ap_setoid_2, ftorid.
  eapply tra_setoid. apply ap_setoid_1, idL.
  apply iso_Vf.
  (* ftorcmp *) intros a b c f g; simpl.
  eapply tra_setoid. Focus 2. apply assoc.
  apply ap_setoid_1.
  eapply tra_setoid. Focus 2. apply sym_setoid, assoc.
  eapply tra_setoid. Focus 2. apply sym_setoid, assoc.
  apply ap_setoid_2.
  eapply tra_setoid. apply ftorcmp.
  apply ap_setoid_2.
  eapply tra_setoid. Focus 2. apply assoc.
  eapply tra_setoid. apply sym_setoid, idR.
  apply ap_setoid_1, sym_setoid, iso_fV.
Defined.

(** * The ecategory of setoids *)

Definition Setoid : ECat
:= {|
    Obj_ECat := setoid;
    Hom := @setoid_map;
    id := @idmap_setoid;
    comp := @comp_setoid;
    idL := @idL_setoid;
    idR := @idR_setoid;
    assoc a b c d f g h
      := @assoc_setoid a b c d h g f
|}.

(** * Sections *)
(** General infrastructure of sections of objects of slices *)

Record Sections_type {C : ECat} {X : C} (Y : slice C X) : Type
:= {
    section   : Hom X Y;
    sectionpf : (downarr _ Y) ° section ≈ id
  }.

Arguments section [C X Y] s : rename.
Arguments sectionpf [C X Y] s : rename.
Arguments Build_Sections_type [C X Y] sec secpf : rename.

(* A more readable alias *)
Definition Build_Sections := @Build_Sections_type.
Arguments Build_Sections [C X Y] sec secpf : rename.

Definition Sections_ob {C : ECat} {X : C} (Y : slice C X) : Setoid.
Proof.
  apply (Build_setoid_flat (Sections_type Y)
          (fun u v => section u ≈ section v));
  swesetoid.
Defined.

Definition Sections_map {C : ECat} {X : C} {Y1 Y2 : slice C X}
  : Hom Y1 Y2 ⇒ Hom (Sections_ob Y1) (Sections_ob Y2).
Proof.
  simple refine (@binsetoid_map_helper (Hom Y1 Y2) (Sections_ob Y1) (Sections_ob Y2)
    (fun f s => Build_Sections ((f : @Hom C Y1 Y2) ° (section s)) _) _ _).
  (* sectionpf *)
    eapply tra_setoid. apply assoc.
    eapply tra_setoid. apply ap_setoid_2, triangle.
    apply sectionpf.
  (* extensionality in f *) intros; simpl. apply ap_setoid_2; assumption.
  (* extensionality in s *) swesetoid.
Defined.

Definition Sections {C : ECat} {X : C} : efunctor (slice C X) Setoid.
Proof.
  refine (Build_efunctor (slice C X) Setoid
    (@Sections_ob C X) (@Sections_map C X) _ _).
  (* ftorid *) intros Y s; simpl. apply idL.
  (* ftorcmp *) intros Y1 Y2 Y3 f g s; simpl. apply sym_setoid, assoc.
Defined.

(* Like [ap10_setoid], this is a no-op, but convenient. *)
Lemma ap_section {C : ECat} {X : C} {Y : slice C X} (e1 e2 : Sections Y)
  : e1 ≈ e2 -> (section e1) ≈ (section e2).
Proof.
  auto.
Qed.



(* Fin *)
(* Local Variables : *)
(* coq-prog-name : "hoqtop" *)
(* End : *)

