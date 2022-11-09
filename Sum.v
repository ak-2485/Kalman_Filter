From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.

Open Scope R_scope.

Section WITHNANS.
Context {NANS: Nans}.

Definition sum_step (acc x : ftype Tsingle) : ftype Tsingle := (acc + x)%F32.

Definition _acc : ident := 1%positive.
Definition _x : ident := 2%positive.

Definition sum_step_expr : expr := ltac:(let e :=
  HO_reify_float_expr constr:([_acc; _x]) sum_step in exact e).

Definition vmap (acc x : ftype Tsingle) : valmap :=
  valmap_of_list [(_acc, existT ftype _ acc); (_x, existT ftype _ x)].

Lemma reflect_reify_eq : forall acc x,
  fval (env_ (vmap acc x)) sum_step_expr = sum_step acc x.
Proof.
  intros.
  unfold sum_step_expr, sum_step.
  reflexivity.
Qed.

Definition bmap : boundsmap :=
  boundsmap_of_list [
    Build_varinfo Tsingle _acc (-10000) 10000;
    Build_varinfo Tsingle _x (-10000) 10000
  ].

Lemma roundoff_bound:
  forall x y : ftype Tsingle,
    prove_roundoff_bound bmap (vmap x y) sum_step_expr
    (/ 838).
Proof.
  intros.
  prove_roundoff_bound.
  - abstract (prove_rndval; interval).
  - prove_roundoff_bound2.
    match goal with |- Rabs ?a <= _ => field_simplify a end.

    (* Duplicate the goal, so we can see two ways of solving it *)
    destruct true.

    (* "Guess" the bound *)
    + match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
      eapply Rle_trans; [apply H | clear].
      eapply roundoff_bound_hack; try lia.
      compute; reflexivity.
      lia.

    (* Or just solve with interval *)
    + interval.
Qed.

End WITHNANS.
