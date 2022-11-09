From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary Reals List ListNotations micromega.Lra.
Open Scope R_scope.

Definition sum : list R -> R :=
  fold_right Rplus 0.

Definition mean (ms : list R) : R :=
  sum ms / INR (length ms).

Definition mean_R_step' (mu m : R) (n : nat) : R :=
  mu + (m - mu) / (1 + INR n).

Definition mean_R_step (mu m n: R) : R :=
  mu + (m - mu) / (1 +  n).

Lemma mean_cons :
  forall m ms,
    mean (m::ms) =
    mean_R_step (mean ms) m (INR (length ms)).
Proof.
  intros m ms.
  unfold mean, mean_R_step.
  generalize dependent m.
  destruct ms; intros m.
  - simpl; lra.
  - replace (sum (m::r::ms))
      with (m + sum (r::ms))
      by reflexivity.
    replace (INR (length (m::r::ms)))
      with (1 + INR (length (r::ms)))
      by (simpl; lra).
    assert (0 < INR (length (r::ms)))
      by (apply lt_0_INR; simpl; intuition).
    field; split; lra.
Qed.

Inductive mean_rel_R (g : R) : list R -> R -> Prop :=
| mean_rel_R_nil : mean_rel_R g [] g
| mean_rel_R_cons : forall mu m ms,
    mean_rel_R g ms mu ->
    mean_rel_R g (m::ms) (mean_R_step mu m (INR (length ms))).

Theorem mean_rel_correct_1 :
  forall g m ms, mean_rel_R g (m::ms) (mean (m::ms)).
Proof.
  intros g m ms.
  generalize dependent m.
  induction ms; intros m.
  - unfold mean, sum; simpl.
    replace ((m + 0) / 1) with (mean_R_step g m 0).
    repeat constructor.
    unfold mean_R_step.
    simpl; lra.
  - rewrite mean_cons.
    constructor.
    apply IHms.
Qed.

Theorem mean_rel_correct_2 :
  forall g m ms mu,
    mean_rel_R g (m::ms) mu -> mean (m::ms) = mu.
Proof.
  intros g m ms mu H.
  generalize dependent m.
  generalize dependent mu.
  induction ms; intros mu m H.
  - inversion H; subst; clear H.
    unfold mean, mean_R_step; simpl.
    field.
  - rewrite mean_cons.
    inversion H; subst; clear H.
    unfold mean_R_step.
    repeat f_equal; apply IHms; assumption.
Qed.

Theorem mean_rel_correct :
  forall g m ms mu,
    mean_rel_R g (m::ms) mu <-> mean (m::ms) = mu.
Proof.
  split; intros.
  apply mean_rel_correct_2 with g; assumption.
  subst; apply mean_rel_correct_1; assumption.
Qed.

Section WithNANS.
Context {NANS: Nans}.

Definition mean_F_step' (mu m : ftype Tsingle) (n : nat) : ftype Tsingle :=
  let l := Zconst Tsingle (Z.of_nat n) in
  (mu + (m - mu) / (1 + l))%F32.

Definition mean_F_step (mu m n: ftype Tsingle)  : ftype Tsingle :=
  (mu + (m - mu) / (1 + n))%F32.

Inductive mean_rel_F (g : ftype Tsingle) : list (ftype Tsingle) -> ftype Tsingle -> Prop :=
| mean_rel_F_nil : mean_rel_F g [] g
| mean_rel_F_cons : forall mu m ms,
    mean_rel_F g ms mu ->
    mean_rel_F g (m::ms) (mean_F_step mu m (Zconst Tsingle (Z.of_nat (length ms)))).


Section ErrorAnalysis.

Variable eps : R. (* The error added at each step - replace with actual bound *)

Lemma mean_step_bound :
  forall mu mu_f m n,
    let n'' := INR n in
    let n':= (Zconst Tsingle (Z.of_nat n)) in
    Rabs (mean_R_step mu (FT2R m) n'' - FT2R (mean_F_step mu_f m n')) <= Rabs (mu - FT2R mu_f) + eps.
Proof.
  intros mu mu_f m n n'.
  unfold mean_R_step, mean_F_step.
Admitted.

Theorem mean_rel_bound :
  forall g ms mu mu_f,
    mean_rel_R (FT2R g) (map FT2R ms) mu ->
    mean_rel_F g ms mu_f ->
    Rabs (mu - FT2R mu_f) <= INR (length ms) * eps.
Proof.
  intro g.
  induction ms; intros mu mu_f HR HF;
    inversion HF; subst; clear HF;
    inversion HR; subst; clear HR.
  - simpl; rewrite Rminus_eq_0, Rabs_R0.
    lra.
  - rename mu1 into mu.
    rename mu0 into mu_f.
    replace (length (map FT2R ms)) with (length ms) by (symmetry; apply map_length).
    replace (length (a::ms)) with (length ms + 1)%nat by (simpl; intuition).
    rewrite plus_INR; simpl.
    apply Rle_trans with (Rabs (mu - FT2R mu_f) + eps).

    apply mean_step_bound.
    field_simplify.
    apply Rplus_le_compat_r.
    replace (eps * INR (length ms)) with (INR (length ms) * eps) by field.
    apply IHms; assumption.
Qed.

End ErrorAnalysis.

End WithNANS.
