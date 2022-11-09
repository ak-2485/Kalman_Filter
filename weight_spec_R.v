From Coq Require Import Reals.
From Coq Require Import List.
Import ListNotations.
Open Scope R_scope.
Coercion INR : nat >-> R.

Definition filter_step (i : nat) (g : R) (m : R) : R :=
  g + (1 / i * (m - g)).

Fixpoint alpha_filter (guess : R) (i : nat) (ns : list R) : R :=
  match ns with
  | [] => guess
  | n::ns' =>
    let i' := (i + 1)%nat in
    let guess' := filter_step i' guess n in
    alpha_filter guess' i' ns'
  end.

Definition sum : list R -> R :=
  fold_right Rplus 0.

Definition mean (ns : list R) : R :=
  sum ns / length ns.
