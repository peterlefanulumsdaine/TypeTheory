Require Import UniMath.Foundations.All.
Require Import TypeTheory.Initiality.Syntax.

(* TODO: factor out the de Bruijn machinery from Initiality.Syntax so that this can import that specifically *)

Section Expressions.

  Inductive prop_expr : nat -> UU
  :=
    | true_expr {n} : prop_expr n
    | and_expr {n} : prop_expr n -> prop_expr n -> prop_expr n
    | false_expr {n} : prop_expr n
    | or_expr {n} : prop_expr n -> prop_expr n -> prop_expr n
    | implies_expr {n} : prop_expr n -> prop_expr n -> prop_expr n.

End Expressions.
