(* 
  Auxiliary utility lemmas used in the [ECats] library, but not specifically
  related to E-categories.


  NOTE: Adapted from earlier work 2010–16 by Gylterud, Lumsdaine, Wilander, Palmgren.
  Should not be relicensed (e.g. incorporated into [UniMath/UniMath]) until Wilander has been consulted.
*)

Require Import UniMath.Foundations.All.

Declare Scope path_scope.
Bind Scope path_scope with paths.
Delimit Scope path_scope with path.

Notation "1" := (paths_refl _) : path_scope.

Lemma sigrejig (B: Type) (P: B → Type) (Q: (∑y, P y) → Type)
  : (∑y: B, ∑p: P y, Q (y,,p)) → ∑x: (∑y, P y), Q x.
Proof.
  intros [y [p Qyp]]. exists (y,, p); assumption.
Defined.

(* The “type-theoretic axiom of choice”.  Again, a trivial re-association,
  but useful in tactic scripts. *)
Lemma TTAC (A B: Type) (R: A → B → Type)
  : (∏x: A, ∑y: B, R x y) → ∑f: A → B, ∏x: A, R x (f x).
Proof.
  intro H. exists (λ a, pr1 (H a)). intro x; apply (pr2 (H x)).
Defined.

(** * Arithemetic lemmas 

  Some arithmetic lemmas, used in construction of setoid coequalisers. 

  Naming scheme for many lemmas is similar to that used and documented 
  in [HoTT.PathGroupoids]. *)

Definition is_true (b:bool) : Type
  := match b with 
    | false => empty
    | true  => unit
  end.

Lemma ne_t_f : true != false.
Proof.
  assert (H : forall b, true = b -> is_true b).
    intros b p; destruct p; constructor.
  exact (H false).
Qed.

Fixpoint plus (x y : nat) : nat
  := match x with
    | 0 => y
    | (S x') => S (plus x' y)
  end.

Arguments plus _ _ : simpl nomatch.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Fixpoint minus (x y : nat) {struct y} : nat
  := match y with
    | 0 => x
    | S y' => match x with 
      | 0 => 0
      | S x' => minus x' y'
    end
  end.

Arguments minus _ _ : simpl nomatch.

Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Lemma plus_x_0: ∏x: nat, x + 0 = x.
Proof.
  induction x.
  - exact 1%path.
  - simpl; apply maponpaths. assumption.
Qed.

Lemma plus_x_S: ∏ x y: nat, x + S y = S x + y.
Proof.
  intros. induction x.
  - exact 1%path. 
  - simpl; apply maponpaths. assumption.
Qed.

Lemma add_subtract_cancellation: ∏x y: nat, ((x + y) - y) = x.
Proof.
  intros x y. induction y as [ | y IH].
    simpl; apply plus_x_0.
  destruct (!plus_x_S x y). simpl. assumption.
Qed.

Fixpoint le (x y: nat): bool
  := match x, y with
      | 0, _ => true
      | (S _), (0) => false
      | (S m), (S n) => le m n
    end.

Arguments le _ _ : simpl nomatch.

Notation "x ≤ y" := (true = (le x y)) (at level 70) : nat_scope.
Notation "x > y" := (false = (le x y)) (at level 70) : nat_scope.

Lemma le_refl (x: nat): x ≤ x.
Proof.
  induction x. exact 1%path. assumption.
Qed.

Lemma le_trans
  : ∏ x y z, x ≤ y → y ≤ z → x ≤ z.
Proof.
  induction x as [ | x IH].
    intros; exact 1%path.
  intros [ | y].
    intros z Hpaths_refl; simpl in Hpaths_refl.
    destruct (ne_t_f Hpaths_refl).
  intros [ | z].
    intros _ H2; simpl in H2.
    destruct (ne_t_f H2).
  simpl.
  apply IH.
Qed.

Lemma gt_trans
  : ∏x y z: nat, x > y → y > z → x > z.
Proof.
  induction x as [ | x IH].
    simpl; intros y z H1 _.
    destruct (ne_t_f (!H1)).
  intros [ | y ].
    intros z _ H2; simpl in H2.
    destruct (ne_t_f (!H2)).
  intros [ | z]; simpl in *.
    intros; exact 1%path.
  apply IH.
Qed.

Lemma le_antisym
  : ∏x y: nat, x ≤ y → y ≤ x → x = y.
Proof.
  induction x as [ | x IH]; intros [ | y]; simpl.
  (* 0, 0 *) intros; exact 1%path.
  (* 0, S *) intros _ H2. destruct (ne_t_f H2).
  (* S, 0 *) intros H1 _. destruct (ne_t_f H1).
  (* S, S *) intros H1 H2. apply maponpaths. auto.
Qed.

Lemma le_suc: ∏x y: nat, x ≤ y → x ≤ S y.
Proof.
  induction x.
    intros; exact 1%path.
  intros [ | y]; simpl; intro H1.
    destruct (ne_t_f H1).
  auto.
Qed.

Lemma le_pred: ∏x y, S x ≤ y → x ≤ y.
Proof.
  destruct y as [ | y]; intros H1; simpl in H1.
    destruct (ne_t_f H1).
  apply le_suc; assumption.
Qed.

Lemma gt_suc (x: nat): S x > x.
Proof.
  induction x. exact 1%path. assumption.
Qed.

Lemma gt_suc_le: ∏x y: nat, x > y → S y ≤ x.
Proof.
  induction x as [ | x IH].
    simpl; intros _ H.
    destruct (ne_t_f (!H)).
  intros [ | y].
    intro; exact 1%path.
  apply IH.
Qed.

Lemma gt_suc_sum (x y: nat): S x + y > y.
Proof.
  induction x. simpl plus. apply gt_suc.
  apply gt_trans with (S x + y). apply gt_suc. assumption.
Qed.

Lemma suc_subtract: ∏x y: nat, y ≤ x → S (x - y) = S x - y.
Proof.
  induction x as [ | x IH]; intros [ | y].
  (* 0, 0 *) intro; exact 1%path.
  (* 0, S *) intros H1. destruct (ne_t_f H1).
  (* S, 0 *) intro; exact 1%path.
  (* S, S *) apply IH.
Qed.

Lemma sub_cutoff: ∏x y: nat, x ≤ y → 0 = x - y.
Proof.
  induction x as [ | x IH].
    intros; destruct y; exact 1%path.
  intros [ | y]; simpl.
    intros H; destruct (ne_t_f H). 
  apply IH.
Qed.
