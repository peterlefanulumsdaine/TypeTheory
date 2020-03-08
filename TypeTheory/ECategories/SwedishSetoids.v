(** * Swedish setoids

  A library for setoids, under propositions-as-types:
  equality is (universe-polymorphically) Type-valued,
  not Prop-valued as in “French setoids”.

  NOTE: Adapted from earlier work 2010–16 by Gylterud, Lumsdaine, Wilander, Palmgren.
  Should not be relicensed (e.g. incorporated into [UniMath/UniMath]) until Wilander has been consulted.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.ECategories.Auxiliary.

Declare Scope setoid_scope.
Declare Scope setoid_eq_scope.
Delimit Scope setoid_scope with setoid.
Delimit Scope setoid_eq_scope with setoid_eq.
Open Scope setoid_scope.
Open Scope setoid_eq_scope.

Set Universe Polymorphism.

(** * Setoids: definition *)

Record Is_Equiv_Relation {A : Type} (R : A -> A -> Type) : Type
:= {
    refl_eqrel  : ∏x, R x x;
    sym_eqrel   : ∏x y, R x y → R y x;
    trans_eqrel : ∏x y z, R x y → R y z → R x z
  }.

Record setoid : Type
:= {
    setoid_base :> Type;
    setoid_eq   : setoid_base → setoid_base → Type;
    setoid_eq_is_eqrel  : Is_Equiv_Relation setoid_eq
  }.

Bind Scope setoid_scope with setoid.
Bind Scope setoid_eq_scope with setoid_eq.

(* TODO: try avoiding the following duplicate definitions,
   by making [Is_Equiv_Relation] a type class? *)
Definition refl_setoid (A:setoid) 
  := refl_eqrel _ (setoid_eq_is_eqrel A).

Definition sym_setoid (A:setoid) 
  := sym_eqrel _ (setoid_eq_is_eqrel A).

Definition tra_setoid (A:setoid)
  := trans_eqrel _ (setoid_eq_is_eqrel A).

Arguments refl_setoid {_} _.
Arguments sym_setoid [_ _ _] _.
Arguments tra_setoid [_ _ _ _] _ _.

Hint Resolve refl_setoid : swesetoid.
Hint Immediate sym_setoid : swesetoid.
Hint Resolve tra_setoid : swesetoid. (* The warning here is expected *)

Ltac swesetoid := simpl; auto with swesetoid; eauto with swesetoid.

Definition Build_setoid_flat (X : Type) (E : X -> X -> Type)
  : (∏x, E x x)
  -> (∏x y, E x y → E y x)
  -> (∏x y z, E x y → E y z → E x z)
  -> setoid
:= fun E_refl E_sym E_trans
     => Build_setoid X E (Build_Is_Equiv_Relation X E E_refl E_sym E_trans).

Notation "x ≈ y" := (setoid_eq _ x y)
    (at level 70, no associativity, only parsing) : type_scope.
Notation "x ≈{ A } y" := (setoid_eq A x y)
    (at level 70, no associativity) : type_scope.
Notation "p ⁻¹" := (sym_setoid p)
    (at level 3, no associativity) : setoid_eq_scope.
Notation "p ⊙ q" := (tra_setoid q p)
    (at level 20, right associativity) : setoid_eq_scope.

(** * Setoid maps *)
 
Record setoid_map_type (A B : setoid)
:= {
    setoid_map_function :> A → B;
    ap_setoid
      : ∏x y : A, x ≈ y → setoid_map_function x ≈ setoid_map_function y
  }.

(* [ap_setoid] is named as the setoid analogue of the HoTT library’s [ap] *)

Notation "F ↱ p" := (ap_setoid _ _ F _ _ p) (at level 65) : setoid_eq_scope.
Hint Resolve ap_setoid : swesetoid.

Definition setoid_map (A B : setoid) : setoid.
Proof.
  apply (Build_setoid_flat (setoid_map_type A B)
    (λ f g, ∏x:A, f x ≈ g x));
  swesetoid.
Defined.

Notation Build_setoid_map := Build_setoid_map_type.

Notation "A ⇒ B" := (setoid_map A B)
    (at level 95, right associativity) : type_scope.

(** This helper lemma is vacuous as a definition,
  but is often useful in tactic proofs:
  given a goal of the form [ f1 x ≈ f2 x ], invoking 
  [apply ap10_setoid] reduces it to [ f1 ≈ f2 ].

  The name is modeled after the HoTT library’s [ap10].

  TODO: find name that makes more sense in our context. *)
Definition ap10_setoid {A B} (f g : A ⇒ B)
  : f ≈ g -> ∏x:A, f x ≈ g x
:= idfun _.

(** Extensionality lemmas for multi-ary setoid maps.

Naming convention: “ap_setoid_245” would be a lemma stating simultaneous
extensionality of a (non-dependently) ≥5-ary setoid map in its 2nd, 4th, and
5th arguments, counting arguments *backwards* from the last.  That is, its goal
would look like [f x5 x4 x3 x2 x1 = f x5' x4' x3 x2' x1].

Not to be confused with the HoTT library’s [apXY] dimension convention! *)

Lemma ap_setoid_1 {X Y} (f : X ⇒ Y)
  {x x'} (ex : x ≈ x')
: f x ≈ f x'.
Proof.
  apply ap_setoid, ex.
Qed.

Lemma ap_setoid_2 {X Y Z} (f : X ⇒ Y ⇒ Z)
  {x x'} (ex : x ≈ x') y
: f x y ≈ f x' y.
Proof.
  apply ap10_setoid, ap_setoid, ex.
Qed.

Lemma ap_setoid_12 {X Y Z} {f : X ⇒ Y ⇒ Z}
  {x x'} (ex : x ≈ x') {y y'} (ey : y ≈ y')
: f x y ≈ f x' y'.
Proof.
  eapply tra_setoid.
    apply ap10_setoid, ap_setoid, ex.
  apply ap_setoid, ey.
Qed.

(* Construction lemmas for multi-ary setoid maps. *)

Lemma binsetoid_map_helper {A B C : setoid} (f : A → B → C)
  (p : ∏a a', a ≈ a' → ∏b, f a b ≈ f a' b)
  (q : ∏a b b', b ≈ b' → f a b ≈ f a b')
: A ⇒ B ⇒ C.
Proof.
  apply (Build_setoid_map _ (B ⇒ C)
    (λ a, (Build_setoid_map _ _ (f a) (q a))) p).
Defined.

Lemma trinsetoid_map_helper {A B C D : setoid} (f : A → B → C → D)
  (p : ∏a a', a ≈ a' → ∏b c, f a b c ≈ f a' b c)
  (q : ∏a b b', b ≈ b' → ∏c, f a b c ≈ f a b' c)
  (r : ∏a b c c', c ≈ c' → f a b c ≈ f a b c')
: A ⇒ B ⇒ C ⇒ D.
Proof.
  apply (Build_setoid_map _ (B ⇒ C ⇒ D))
  with (λ a, binsetoid_map_helper (f a) (q a) (r a));
    assumption.
Defined.

Definition ev_setoid_map {A B} : A ⇒ ((A ⇒ B) ⇒ B).
Proof.
  simple refine (Build_setoid_map _ _ _ _).
    intros a; simple refine (Build_setoid_map _ _ _ _).
      intros f; exact (f a).
    simpl; intros f g e_fg. apply ap10_setoid; assumption.
  simpl; intros x y e_xy f. apply ap_setoid; assumption.
Defined.


(* “rewrite” lemmas (acting on the LHS of an equality goal) *)
Theorem extensionality_depth3 {A1 A2 A3 A4} 
  (f1:A1 ⇒ A2) (f2:A2 ⇒ A3) (f3:A3 ⇒ A4) (x y:A1) (z:A4)
: x ≈ y
  -> f3 (f2 (f1 x)) ≈ z 
  -> f3 (f2 (f1 y)) ≈ z.
Proof.
  intros H1 H2.
  assert (f3 (f2 (f1 x)) ≈ f3 (f2 (f1 y))) as E.
  apply ap_setoid,
        ap_setoid,
        ap_setoid.
  apply H1.
  apply (tra_setoid (sym_setoid E) H2).
Qed.

Theorem extensionality_depth4 {A1 A2 A3 A4 A5} 
  (f1:A1 ⇒ A2) (f2:A2 ⇒ A3) (f3:A3 ⇒ A4) (f4:A4 ⇒ A5)
  (x y:A1) (z:A5)
: x ≈ y
  -> f4 (f3 (f2 (f1 x))) ≈ z 
  -> f4 (f3 (f2 (f1 y))) ≈ z.
Proof.
  intros H1 H2.
  assert (f4 (f3 (f2 (f1 x))) ≈ f4 (f3 (f2 (f1 y)))) as E.
  apply ap_setoid,
        ap_setoid,
        ap_setoid,
        ap_setoid.
  apply H1.
  apply (tra_setoid (sym_setoid E) H2).
Qed.


(** * Category structure on setoid maps. *)

(** For now we can only define the components of the e-category
  of setoids; in [ECat], we will put them together. *)

Definition idmap_setoid {A} : A ⇒ A.
Proof.
  apply (Build_setoid_map _ _ (idfun _)); swesetoid.
Defined.

Definition comp_setoid {A B} (C : setoid) : (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C).
Proof.
  apply trinsetoid_map_helper with (λ f : B ⇒ C, λ g : A ⇒ B, λ a, f (g a));
  swesetoid.
Defined.

Notation "F ∘ G" := (comp_setoid _ F G) (at level 40, left associativity).

Theorem assoc_setoid {A B C D} (F : C ⇒ D) (G : B ⇒ C) (H : A ⇒ B)
  : F ∘ G ∘ H ≈ F ∘ (G ∘ H).
Proof.
  swesetoid.
Qed.

Theorem idL_setoid {A B} (F : A ⇒ B) : idmap_setoid ∘ F ≈ F.
Proof.
  swesetoid.
Qed.

Theorem idR_setoid {A B} (F : A ⇒ B) : F ∘ idmap_setoid ≈ F.
Proof.
  swesetoid.
Qed.

(** * Examples *)

Local Open Scope path_scope.

Definition discrete_setoid (X : Type) : setoid.
Proof.
  apply (Build_setoid_flat X (λ x y, x = y));
    eauto using pathsinv0, pathscomp0.
Defined.

Definition nat_setoid := discrete_setoid nat.

Definition indiscrete_setoid (X : Type) : setoid.
Proof.
  apply (Build_setoid_flat X (λ x y, unit)); intros; exact tt.
Defined.

(* Needed since indiscrete setoid equality types often get unfolded quickly,
  so they don’t look like equality types when Coq tries to apply the other
  basic setoid constructs. *)  
Hint Immediate tt : swesetoid.

Definition empty_setoid := indiscrete_setoid empty.

Definition unit_setoid := indiscrete_setoid unit.

Definition sum_setoid (A B : setoid) : setoid.
Proof.
  apply (Build_setoid_flat (A + B)%type
    (λ a b, match a with
              | inl α => match b with
                           | inl α' => α ≈ α'
                           | inr _  => empty
                         end
              | inr β => match b with
                           | inl _  => empty
                           | inr β' => β ≈ β'
                         end
            end)).
  intros []; swesetoid.
  intros [] []; swesetoid.
  intros [] [] []; swesetoid; try contradiction.
Defined.

Notation "x ⊕ y" := (sum_setoid x y)
    (at level 50, left associativity) : setoid_scope.

Definition inl_setoid {A B} : A ⇒ A ⊕ B.
Proof.
  apply (Build_setoid_map _ (A ⊕ B) (λ a : A, inl B a)).
  auto.
Defined.

Definition inr_setoid {A B} : B ⇒ A ⊕ B.
Proof.
  apply (Build_setoid_map _ (A ⊕ B) (λ b : B, inr A b)).
  auto.
Defined.

Definition sum_mediating {A B} (X : setoid) (f : A ⇒ X) (g : B ⇒ X)
  : A ⊕ B ⇒ X.
Proof.
  apply (Build_setoid_map (A ⊕ B) _
    (λ x, match x with
            | inl a => f a
            | inr b => g b
          end)).
intros [a | b] [a' | b'] p; try contradiction p;
  apply ap_setoid; assumption.
Defined.

Lemma sum_universality {A B} (X : setoid) (f : A ⇒ X) (g : B ⇒ X)
  : f ≈ sum_mediating X f g ∘ inl_setoid
  ∧ g ≈ sum_mediating X f g ∘ inr_setoid
  ∧ ∏h, f ≈ h ∘ inl_setoid → g ≈ h ∘ inr_setoid → sum_mediating X f g ≈ h.
Proof.
  repeat split; try (intro; apply refl_setoid).
  intros h feq geq [a | b]; simpl. apply (feq a). apply (geq b).
Qed.

Definition sum_map {A B C D} (f : A ⇒ C) (g : B ⇒ D) : A ⊕ B ⇒ C ⊕ D
  := sum_mediating (C ⊕ D) (inl_setoid ∘ f) (inr_setoid ∘ g).

Definition prod_setoid (A B : setoid) : setoid.
Proof.
  apply (Build_setoid_flat (A ∧ B)
    (λ p q, (fst p ≈ fst q) ∧ (snd p ≈ snd q))).
  intros []; swesetoid.
  intros [] [] []; swesetoid.
  intros [] [] [] [] []; swesetoid.
Defined.

Notation "x ⊗ y" := (prod_setoid x y)
    (at level 40, left associativity) : setoid_scope.

Definition fst_setoid {A B} : A ⊗ B ⇒ A.
Proof.
  apply (Build_setoid_map (A ⊗ B) _ fst).
  intros [x x'] [y y'] [p p']; auto.
Defined.

Definition snd_setoid {A B} : A ⊗ B ⇒ B.
Proof.
  apply (Build_setoid_map (A ⊗ B) _ snd).
  intros [x x'] [y y'] [p p']; auto.
Defined.

Definition prod_mediating {A B} (X : setoid) (f : X ⇒ A) (g : X ⇒ B)
  : X ⇒ A ⊗ B.
Proof.
  apply (Build_setoid_map _ (A ⊗ B) (λ x, (f x, g x))).
  intros; split; apply ap_setoid; assumption.
Defined.

Lemma prod_universality {A B} (X : setoid) (f : X ⇒ A) (g : X ⇒ B)
  : f ≈ fst_setoid ∘ (prod_mediating X f g)
  ∧ g ≈ snd_setoid ∘ (prod_mediating X f g)
  ∧ ∏h, f ≈ fst_setoid ∘ h → g ≈ snd_setoid ∘ h → prod_mediating X f g ≈ h.
Proof.
  split. intro; apply refl_setoid.
  split. intro; apply refl_setoid.
  intros h feq geq x. simpl.
  split. apply (feq x). apply (geq x).
Qed.

Definition prod_map {A B C D} (f : A ⇒ C) (g : B ⇒ D) : A ⊗ B ⇒ C ⊗ D
  := prod_mediating (A ⊗ B) (f ∘ fst_setoid) (g ∘ snd_setoid).

(** * Coequalisers

  Coequalisers in the E-category of setoids are a little more involved. *)

(* First the transitive closure of a reflexive relation on a setoid. *)
Definition Transitive_Closure {A : setoid} (R : A → A → Type) (x y : A)
  := ∑f : nat → A, ∑n : nat, (x ≈ f 0 ∧ f n ≈ y ∧ ∏m:nat, R (f m) (f (S m))).

Lemma trans_transclosure {A : setoid} (R : A → A → Type)
  (Rextl : ∏x y z : A, x ≈ y → R x z → R y z)
  : ∏x y z : A, Transitive_Closure R x y → Transitive_Closure R y z
  → Transitive_Closure R x z.
Proof.
  intros x y z [f [m [ef0 [em fp]]]] [g [n [eg0 [en gp]]]].
  exists (λ a : nat, if (le a m) then (f a) else (g (a - m))).
  exists (n + m).
  split. simpl; assumption.
  split.
    destruct n. simpl. destruct (le_refl m). swesetoid.
    destruct (gt_suc_sum n m), (add_subtract_cancellation (S n) m)^.
    assumption.
  intro k.
  assert (Bool_dec : ((S k) ≤ m) + ((S k) > m)).
  case (le (S k) m); [left | right]; exact 1.
  destruct Bool_dec as [i | i].
    destruct (le_pred k m i). destruct i. apply fp.
  assert (Bool_dec : (k ≤ m) + (k > m)).
    case (le k m); [left | right]; exact 1.
  destruct Bool_dec as [j | j].
      assert (eq : m = k).
      apply le_antisym. apply (gt_suc_le (S k) m i). assumption.
    destruct i. destruct j. destruct eq.
    apply Rextl with (g 0). swesetoid.
    assert (eq : 1%nat = (S m - m)). change (1%nat = 1 + m - m).
      apply inverse, add_subtract_cancellation.
    destruct eq. apply gp.
  assert (eq : S (k - m) = S k - m). apply suc_subtract.
    apply (gt_suc_le (S k) m i).
  destruct i. destruct j. destruct eq. apply gp.
Qed.

Lemma transclosure_preserves_sym {A : setoid} (R : A → A → Type)
  (Rsym : ∏x y : A, R x y → R y x)
  (Rrefl : ∏x : A, R x x)
  : ∏x y : A, Transitive_Closure R x y → Transitive_Closure R y x.
Proof.
  intros x y [f [m [ef0 [em fp]]]].
  exists (λ n : nat, f (m - n)).
  exists m.
  split.
    assert (eq : m = m - 0).
      case m; intros; exact 1.
    destruct eq; swesetoid.
  split.
    assert (eq : 0 = m - m). clear em.
      induction m. exact 1. simpl. assumption.
    destruct eq. swesetoid.
  intro k.
  assert (Bool_dec : (m > k) + (m ≤ k)).
    case (le m k); [right | left]; exact 1.
  destruct Bool_dec as [ g | l ].
    change (m - k) with (S m - S k).
    destruct (suc_subtract m (S k) (gt_suc_le m k g)).
    apply Rsym.   apply fp.
  destruct (sub_cutoff m k l).
  destruct (sub_cutoff m (S k) (le_suc m k l)).
  apply Rrefl.
Qed.

Lemma transclosure_preserves_refl {A : setoid} (R : A → A → Type)
  (Rrefl : ∏x : A, R x x)
  : ∏x : A, Transitive_Closure R x x.
Proof.
  intro x.
  exists (λ n, x).
  exists 0.
  repeat split; try swesetoid.
Qed.

Definition coequalizer_setoid {A B} (f g : A ⇒ B) : setoid.
Proof.
  apply
    (Build_setoid_flat B
      (Transitive_Closure
        (λ x y, x ≈ y
                ∨ (∑a : A, f a ≈ x ∧ g a ≈ y)
                ∨ (∑a : A, f a ≈ y ∧ g a ≈ x)))).
  apply transclosure_preserves_refl. swesetoid.
  apply transclosure_preserves_sym.
    intros x y [e | [[a [e1 e2]] | [a [e1 e2]]]]; swesetoid. swesetoid.
  apply trans_transclosure.
  intros x y z e [e' | [[a [e1 e2]] | [a [e1 e2]]]]; swesetoid.
    right; left; swesetoid.
  right; right; swesetoid.
Defined.

Definition coequalizer_map {A B} (f g : A ⇒ B) : B ⇒ coequalizer_setoid f g.
Proof.
  apply (Build_setoid_map B (coequalizer_setoid f g) (λ b, b)).
  intros. exists (λ n, x). exists 0. repeat split; swesetoid.
Defined.

Lemma coequalizer_eq {A B} (f g : A ⇒ B)
  : (coequalizer_map f g) ∘ f ≈ (coequalizer_map f g) ∘ g.
Proof.
  intro a. simpl.
  exists (nat_rect (λ _, B) (f a) (λ _ _, g a)). exists 1%nat.
  repeat split; swesetoid.
  intro k; case k; simpl.
  right; left; swesetoid.
  intro; left; swesetoid.
Qed.

Definition coequalizer_mediating {A B} (f g : A ⇒ B) 
  {C} (h : B ⇒ C) (e_hf_hg : h ∘ f ≈ h ∘ g)
: (coequalizer_setoid f g) ⇒ C.
Proof.
  refine (Build_setoid_map (coequalizer_setoid f g) _ (λ x, h x) _).
  intros x y [φ [n [e0 [en p]]]].
  assert (claim : ∏m : nat, h x ≈ h (φ m)).
    induction m as [ | m IHm].
      swesetoid.
    apply tra_setoid with (h (φ m)). apply IHm.
    destruct p with m as [e | [[a [e1 e2]] | [a [e1 e2]]]].
        swesetoid.
      apply tra_setoid with (h (f a)). swesetoid.
      apply tra_setoid with (h (g a)). apply (e_hf_hg a). swesetoid.
    apply tra_setoid with (h (g a)). swesetoid.
    apply tra_setoid with (h (f a)). apply sym_setoid, (e_hf_hg a). swesetoid.
  apply tra_setoid with (h (φ n)); swesetoid.
Defined.

Lemma coequalizer_universal {A B} (f g : A ⇒ B) 
  {C} (h : B ⇒ C) (e_hf_hg : h ∘ f ≈ h ∘ g)
: (coequalizer_mediating f g h e_hf_hg) ∘ (coequalizer_map f g) ≈ h
  ∧ ∏ m : coequalizer_setoid f g ⇒ C,
      m ∘ (coequalizer_map f g) ≈ h
      → m ≈ (coequalizer_mediating f g h e_hf_hg).
Proof.
  split.
    swesetoid.
  intros m e_mc_h c; simpl in *.
    swesetoid.
Qed.
