Require Import UniMath.Foundations.All.
Require Import TypeTheory.Initiality.Syntax.

(** The goal of this package is to formalise some classical proof-theoretic material, in particular normalisation/cut-elimination proofs, consciously staying on the propositions/proofs side of the Curry–Howard correspondence in approach.

  This file aims to start with a very simple case: cut-eliination for natural deduction in propositional logic, following Carlström 2007/2013 “Logic”.  *)

(* TODO: factor out the de Bruijn machinery from Initiality.Syntax so that this can import that specifically *)

(* the file from here on is heavily WIP, so for now uses placeholders and “Admitted” where convenient. *)
Section WIP.

Context { placeholder : forall (X : Type), X }.
 
Section Expressions.

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
    | assumption {Γ : context} (i : Γ) : proof Γ (Γ i)
    | true_intro {Γ} : proof Γ true_prop
    | and_intro {Γ} {φ1 φ2} (p : proof Γ φ1) (q : proof Γ φ2)
                     : proof Γ (and_prop φ1 φ2)
    | and_elim_l {Γ} {φ1 φ2} (p : proof Γ (and_prop φ1 φ2))
                     : proof Γ φ1
    | and_elim_r {Γ} {φ1 φ2} (p : proof Γ (and_prop φ1 φ2))
                     : proof Γ φ2
    | false_elim {Γ} : proof Γ true_prop
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

End Expressions.

Definition is_raa_free {Γ : context} {φ1 : proposition} (p : proof Γ φ1) : hProp.
Admitted.

Theorem glivenko {Γ} {φ} : proof Γ φ
    -> ∑ (p : proof (context_extend Γ (not_prop φ)) false_prop), is_raa_free p.
Admitted.

Definition is_cut_free {Γ : context} {φ1 : proposition} (p : proof Γ φ1) : hProp.
Admitted.

Theorem cut_elimination {Γ} {φ} : proof Γ φ -> ∑ (p : proof Γ φ), is_cut_free p.
Admitted.

End WIP.
