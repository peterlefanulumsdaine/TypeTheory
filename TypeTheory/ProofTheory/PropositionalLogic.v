(** The goal of this package is to formalise some classical proof-theoretic material, in particular normalisation/cut-elimination proofs, consciously staying on the propositions/proofs side of the Curry–Howard correspondence in approach.

  This file aims to start with a very simple case: cut-eliination for natural deduction in propositional logic, following Carlström 2007/2013 “Logic”.  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Initiality.Syntax.
(* TODO: factor out the de Bruijn machinery from Initiality.Syntax so that this can import that specifically *)

Local Open Scope logic.

Local Open Scope logic.
Local Open Scope decidable_logic.

Section Auxiliary.
(* TODO: upstream material from this section *)

  Definition isdecprop_unit : isdecprop unit.
  Proof.
    apply isdecpropfromiscontr, iscontrunit.
  Defined.

  Definition decidableTrue : DecidableProposition.
  Proof.
    esplit; apply isdecprop_unit.
  Defined.

  Definition decidableFalse : DecidableProposition.
  Proof.
    esplit; apply isdecpropempty.
  Defined.

  (* TODO: we really seem to need at least a better library interplay between Bool and DecidableProposition.  Search harder for this upstream! *)

End Auxiliary.

(* the file from here on is heavily WIP, so for now uses placeholders and “Admitted” where convenient. *)
Section WIP.

Context { placeholder : forall (X : Type), X }.
 
Section Expressions.
 (* TODO: add atmoic propositions! *)

  Inductive proposition : UU
  :=
    | true_prop : proposition
    | and_prop : proposition -> proposition -> proposition
    | false_prop : proposition
    | or_prop : proposition -> proposition -> proposition
    | implies_prop : proposition -> proposition -> proposition.

  Definition not_prop φ : proposition
  := implies_prop φ false_prop.

  Definition context : UU
  := ∑ (n : nat), dB_vars n -> proposition.

  Definition context_length : context -> nat := pr1.
  Coercion context_length : context >-> nat.

  Definition context_props : forall Γ : context, _ := pr2.
  Coercion context_props : context >-> Funclass.

  Definition make_context {n} : (_ -> _) -> context
    := fun Γ => (n,,Γ).

  Definition context_extend (Γ : context) (φ : proposition) : context
  := make_context ( dB_Sn_rect _ φ Γ ).

  Inductive proof : context -> proposition -> UU
  :=
    | assumption (Γ : context) (i : Γ) : proof Γ (Γ i) 
    | true_intro Γ : proof Γ true_prop
    | and_intro {Γ} {φ1 φ2} (p : proof Γ φ1) (q : proof Γ φ2)
                     : proof Γ (and_prop φ1 φ2)
    | and_elim_l {Γ} {φ1 φ2} (p : proof Γ (and_prop φ1 φ2))
                     : proof Γ φ1
    | and_elim_r {Γ} {φ1 φ2} (p : proof Γ (and_prop φ1 φ2))
                     : proof Γ φ2
    | false_elim {Γ} {σ} (p : proof Γ false_prop) : proof Γ σ
    | or_intro_l {Γ} {φ1 φ2} (p : proof Γ φ1)
                     : proof Γ (or_prop φ1 φ2)
    | or_intro_r {Γ} {φ1 φ2} (q : proof Γ φ2)
                     : proof Γ (or_prop φ1 φ2)
    | or_elim {Γ} {φ1 φ2 σ} (p : proof Γ (or_prop φ1 φ2))
                            (q1 : proof (context_extend Γ φ1) σ) 
                            (q2 : proof (context_extend Γ φ2) σ) 
                     : proof Γ σ
    | implies_intro {Γ} {φ ψ} (p : proof (context_extend Γ φ) ψ)
                     : proof Γ (implies_prop φ ψ)
    | implies_elim {Γ} {φ ψ} (p : proof Γ (implies_prop φ ψ)) (q : proof Γ φ)
                     : proof Γ ψ
    | raa {Γ} {φ} (p : proof (context_extend Γ (not_prop φ)) false_prop)
                     : proof Γ φ
  .
(*
  1 args: true_intro
  2 args: assumption 
  3 args: false_elim, raa
  4 args: and_elim_l, and_elim_r, or_intro_l, or_intro_r, implies_intro
  5 args: and_intro, implies_elim
  6 args: or_elim
 *)

(* generic induction template:
  induction p as
    [ Γ i
    | Γ
    | Γ φ1 φ2 p1 IH_p1 p2 IH_p2
    | Γ φ1 φ2 p IP_p
    | Γ φ1 φ2 p IP_p
    | Γ φ p IP_p
    | Γ φ1 φ2 p IP_p
    | Γ φ1 φ2 p IP_p
    | Γ φ1 φ2 σ q IH_q p1 IH_p1 p2 IH_p2
    | Γ φ ψ p IH_p
    | Γ φ ψ p IH_p q IH_q
    | Γ φ p IH_p ].
  - (* assumption *) admit.
  - (* true_intro *) admit.
  - (* and_intro *) admit.
  - (* and_elim_l *) admit.
  - (* and_elim_r *) admit.
  - (* false_elim *) admit.
  - (* or_intro_l *) admit.
  - (* or_intro_r *) admit.
  - (* or_elim *) admit.
  - (* implies_intro *) admit.
  - (* implies_elim *) admit.
  - (* raa *) admit.
*)

  (* TODO: find a good general machinery for simplifying defs of matches/fixpoints in which most cases are “parallel”/“obvious”, etc; for instance, [is_raa_free_below] should just need specifying the base case for [raa _] and then saying “in all other cases, take [decidableAnd] of all other subderivations” *)

  Definition assumption' (Γ : context) {φ} (i : Γ) (e : Γ i = φ) : proof Γ φ.
  Proof.
    destruct e; apply assumption.
  Defined.

  Definition assumption_top (Γ : context) {φ} : proof (context_extend Γ φ) φ.
  Proof.
    exact (assumption (context_extend _ _) dB_top).
  Defined.

End Expressions.

(* Generalised weakening of derivations, i.e. reindexing of assumption-contexts *)
Section Weakening.

  Definition weakening (Γ Δ : context)
    := ∑ (f : Δ -> Γ), ∏ (i:Δ), Δ i = Γ (f i).


End Weakening.

(* Substitution of derivations under change of assumptions *)
Section Substitution.


  Definition substitute_proof {Γ} {φ} (p : proof Γ φ) {Δ} (qs : forall i:Γ, proof Δ (Γ i)) : proof Δ φ.  
  Proof.
  revert Δ qs.
  induction p as
    [ Γ i
    | Γ
    | Γ φ1 φ2 p1 IH_p1 p2 IH_p2
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 σ q IH_q p1 IH_p1 p2 IH_p2
    | Γ φ ψ p IH_p
    | Γ φ ψ p IH_p q IH_q
    | Γ φ p IH_p ]; intros Δ qs.
  - (* assumption *) apply qs.
  - (* true_intro *) apply true_intro.
  - (* and_intro *) apply and_intro; [ apply IH_p1 | apply IH_p2 ]; apply qs.
  - (* and_elim_l *) eapply and_elim_l, IH_p, qs.
  - (* and_elim_r *) eapply and_elim_r, IH_p, qs.
  - (* false_elim *) apply false_elim, IH_p, qs.
  - (* or_intro_l *) apply or_intro_l, IH_p, qs.
  - (* or_intro_r *) apply or_intro_r, IH_p, qs.
  - (* or_elim *) eapply or_elim.
    + apply IH_q, qs.
    + apply IH_p1. admit. (* TODO: define extension of substitutions (requires renaming/generalised weakening) *)
    + apply IH_p2. admit.
  - (* implies_intro *) eapply implies_intro, IH_p. admit.
  - (* implies_elim *) eapply implies_elim;
                         [ apply IH_p | apply IH_q ]; apply qs.
  - (* raa *) eapply raa, IH_p. admit.
  Admitted.

  Definition substitute_proof_top {Γ} {φ ψ} (p : proof (context_extend Γ ψ) φ) (q : proof Γ ψ) : proof Γ φ.
  Proof.
    apply (substitute_proof p).
    apply dB_Sn_rect.
    - apply q.
    - apply assumption.
  Defined.

  (* TODO: should just use renaming, not substitution, once that’s defined. *)
  Definition weaken_proof {Γ φ ψ} (p : proof Γ φ) : proof (context_extend Γ ψ) φ.
  Proof.
  Admitted.

End Substitution.

(* TODO: better to define as [is_raa_free], or as [uses_raa] and then negate? *)
(* TODO: better to define as a bool, rather than as a DecidableProposition? *)
Fixpoint is_raa_free {Γ : context} {φ1 : proposition} (p : proof Γ φ1)
    : DecidableProposition
  := match p with
    | raa _ => decidableFalse (* the only exceptional case *)
    | assumption _ _ => decidableTrue
    | true_intro _ => decidableTrue
    | and_intro p1 p2 => decidableAnd (is_raa_free p1) (is_raa_free p2)
    | and_elim_l p => is_raa_free p
    | and_elim_r p => is_raa_free p
    | false_elim p => is_raa_free p
    | or_intro_l p => is_raa_free p
    | or_intro_r p => is_raa_free p
    | or_elim q p1 p2 => decidableAnd (is_raa_free q) (decidableAnd (is_raa_free p1) (is_raa_free p2))
    | implies_intro p => is_raa_free p
    | implies_elim p q => decidableAnd (is_raa_free p) (is_raa_free q)
  end.

(* TODO: better to separate the transformation from the proof of RAA-freeness?
  Almost certainly! *)
Theorem glivenko {Γ} {φ} (p : proof Γ φ)
    : ∑ (p' : proof (context_extend Γ (not_prop φ)) false_prop), is_raa_free p'.
Proof.
  induction p as
    [ Γ i
    | Γ p
    | Γ φ1 φ2 p1 IH_p1 p2 IH_p2
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 p IH_p
    | Γ φ1 φ2 q IH_q p1 IH_p1 p2 IH_p2
    | Γ φ ψ p IH_p
    | Γ φ ψ p IH_p q IH_q
    | Γ φ p IH_p ]; use tpair.
  - (* assumption *)
    eapply implies_elim.
    + apply assumption_top.
    + apply weaken_proof, assumption.
  - repeat constructor. admit.
     (* should be automatic once weaken_proof defined, if that computes well;
     if not, give it by hand instead using assumption', dB_next. *)
  - (* true_intro *)
    eapply implies_elim.
    + use assumption'. { apply dB_top. } apply idpath.
    + apply true_intro.
  - repeat constructor.
  - (* and_intro *)
    apply (@substitute_proof_top _ _ (not_prop φ2)) .
    { admit. } (* exchange + weakening of IH_p2 *)
    apply implies_intro.
    apply (substitute_proof (pr1 IH_p1)).
    apply dB_Sn_rect.
    2: { intros i. 
       use assumption'. { apply dB_next, dB_next, i. } apply idpath. }
    apply implies_intro.
    eapply implies_elim.
    { use assumption'. { apply dB_next, dB_next, dB_top. } apply idpath. }
    apply and_intro.
    + apply assumption_top.
    + apply weaken_proof, assumption_top.
  - admit.
  - (* and_elim_l *) admit.
  - admit.
  - (* and_elim_r *) admit.
  - admit.
  - (* false_elim *) admit.
  - admit.
  - (* or_intro_l *) admit.
  - admit.
  - (* or_intro_r *) admit.
  - admit.
  - (* or_elim *) admit.
  - admit.
  - (* implies_intro *) admit.
  - admit.
  - (* implies_elim *) admit.
  - admit.
  - (* raa *) admit.
  - admit.
Admitted.

Definition is_cut_free {Γ : context} {φ1 : proposition} (p : proof Γ φ1) : hProp.
Admitted.

Theorem cut_elimination {Γ} {φ} : proof Γ φ -> ∑ (p : proof Γ φ), is_cut_free p.
Admitted.

End WIP.
