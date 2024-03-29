Require Import List vcfloat.VCFloat.
From vcfloat Require Import IEEE754_extra.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import Mean.

Import Interval.Tactic.

Open Scope R_scope.

Section WITHNANS.
Context {NANS: Nans}.

Definition _mu : ident := 1%positive.
Definition _m : ident := 2%positive.
Definition _i : ident := 3%positive.


Definition reify_mean_step := ltac:(let e' :=
    HO_reify_float_expr constr:([_mu;_m;_i]) mean_F_step in exact e').

Definition state ty : Type := ftype ty * (ftype ty * ftype ty).

Definition vmap_raw (s:  state Tsingle)  :=
 valmap_of_list [(_mu, existT ftype _   (fst s) ) ;(_m, existT ftype _ (fst (snd s))); (_i, existT ftype _ (snd (snd s)))].

Definition vmap s : valmap :=
 ltac:(let z := compute_PTree (vmap_raw s) in exact z).


Lemma reflect_reify_s : forall s, 
    let e := env_ (vmap s) in 
     fval e reify_mean_step = mean_F_step (fst s) (fst (snd s)) (snd (snd s)).
Proof. reflexivity. Qed.

Definition bmap_list len lb ub : list varinfo := 
(* len: list length; lb: lower bound of elements in the list; ub : upper bound
  of elements in the list *)
  [ Build_varinfo Tsingle _mu (lb + INR len * -1.2e-4) (ub + INR len * 1.2e-4) ;  
      Build_varinfo Tsingle _m lb ub ;
        Build_varinfo Tsingle _i 0 (INR len)].

Definition bmap len lb ub: boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (bmap_list len lb ub)) in exact z).


Lemma prove_roundoff_bound:
  forall s : state Tsingle,
  prove_roundoff_bound (bmap 10 0 10) (vmap s) reify_mean_step 
    1.2e-4.
Proof.
intros [mu [m i]].
prove_roundoff_bound.
-
(prove_rndval; interval).
- 
prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro a end.
all: try interval; try split; try interval.
Qed.


Lemma prove_roundoff_bound_implies':
  forall s : state Tsingle,
  boundsmap_denote (bmap 10 0 10) (vmap s)-> 
  Rabs (FT2R (fval (env_ (vmap s)) reify_mean_step) 
           - rval (env_ (vmap s)) reify_mean_step)
    <= 1.2e-4.
Proof.
intros.
apply (prove_roundoff_bound s H).
Qed.
 


Lemma reflect_reify_sF : forall s, 
    let e := env_ (vmap s) in 
    let '(mu, (m,i) ) := s in 
    fval e reify_mean_step = mean_F_step mu m i.
Proof. intros. destruct s. destruct p. reflexivity. Qed.


Lemma reflect_reify_sR : forall s, 
    let e := env_ (vmap s) in 
    let '(mu, (m,i) ) := s in 
    rval e reify_mean_step = mean_R_step (FT2R mu) (FT2R m) (FT2R i).
Proof. intros. destruct s. destruct p. unfold_rval. unfold mean_R_step. f_equal. Qed.

Lemma Rabs_eq x y : x = y -> Rabs x = Rabs y. Proof. intros. subst. nra. Qed. 

Lemma prove_roundoff_bound_implies:
  forall s : state Tsingle, 
    let e := env_ (vmap s) in 
    let '(mu, (m,i) ) := s in 
    boundsmap_denote (bmap 10 0 10) (vmap s)-> 
    Rabs (mean_R_step (FT2R mu) (FT2R m) (FT2R i) - FT2R (mean_F_step mu m i ))
          <= 1.2e-4.
Proof.
intros.
pose proof reflect_reify_sF s.
pose proof reflect_reify_sR s.
destruct s as [mu [m i]].
intros.
rewrite <- H.
rewrite <- H0.
eapply Rle_trans.
2: apply prove_roundoff_bound_implies'; try apply H1.
apply Req_le; rewrite Rabs_minus_sym; auto.
Qed.


Lemma mean_R_step_bound :
  forall mu1 mu2 m n, 
   0 <= n -> Rabs (mean_R_step mu1 m n - mean_R_step mu2 m n) <= Rabs (mu1 - mu2).
Proof.
intros;
unfold mean_R_step.
match goal with |-context [Rabs ?a <= _] => field_simplify a end; try nra.
match goal with |-context [Rabs ?a <= _] => assert (Rabs a = Rabs (mu1 - mu2) * Rabs (n / (n + 1))) end.
rewrite <- Rabs_mult.
apply Rabs_eq. nra.
rewrite H0.
eapply Rle_trans.
eapply Rmult_le_compat_l.
apply Rabs_pos.
assert (Hl1 : Rabs (n / (n + 1)) <= 1).
rewrite Rabs_pos_eq.
rewrite <- Rcomplements.Rdiv_le_1; try nra.
apply Rcomplements.Rdiv_le_0_compat; try nra.
apply Hl1.
nra.
Qed.

Fixpoint list_sum_p ty (l : list ty) (b : ty) (op : ty -> ty -> ty) :=
  match l with 
  | a :: tl => op a (list_sum_p ty tl b op)
  | _ => b
  end.

Definition list_sum_F (l : list (ftype Tsingle)) : ftype Tsingle := 
  list_sum_p (ftype Tsingle) l (B754_zero _ _ false) (BPLUS Tsingle).
Definition list_sum_R (l : list R): R := 
  list_sum_p R l (0%R) Rplus.

Definition FT2R_list (l: list (ftype Tsingle)) := map FT2R l.



Lemma Rabs_add_sub_eq a b c:
   Rabs (a - b) = Rabs ((a - c) + (c - b)).
Proof.
match goal with |-context[ _ =  Rabs(?A) ] =>
field_simplify A
end; auto.
Qed.


Lemma mean_step_bound' :
  forall mu mu_f m n,
    boundsmap_denote (bmap 10 0 10) (vmap (mu_f, (m, n))) -> 
    Rabs (mean_R_step mu (FT2R m) (FT2R n) - FT2R (mean_F_step mu_f m n)) <= Rabs (mu - FT2R mu_f) + 1.2e-4.
Proof.
  intros ? ? ? ? BMD.
  simpl.
  eapply Rle_trans.
  match goal with |- context[Rabs(?a -?b) <= _] =>
    let c:= constr:(mean_R_step (FT2R mu_f) (FT2R m) (FT2R n)) in
    assert (Hle : Rabs (a - b) = Rabs ((a - c) + (c - b))) by (apply Rabs_add_sub_eq);
    rewrite Hle; clear Hle
  end.
  apply Rabs_triang.
  pose proof prove_roundoff_bound_implies (mu_f,(m,n)).
  apply Rplus_le_compat.
  apply mean_R_step_bound. 
clear H.
destruct (BMD _i) as [_ [_ [_ Bi]]].
simpl in Bi; interval.
simpl in H.
apply H; auto.
Qed.

Lemma mean_step_bound_1' :
  forall mu_f m n,
    boundsmap_denote (bmap 10 0 10) (vmap (mu_f, (m, n))) -> 
    Rabs (mean_R_step (FT2R mu_f) (FT2R m) (FT2R n) - FT2R (mean_F_step mu_f m n)) <=  1.2e-4.
Proof.
intros.
pose proof mean_step_bound' (FT2R mu_f) mu_f m n H.
replace (Rabs (FT2R mu_f - FT2R mu_f) + 1.2e-4) with (1.2e-4) in H0; auto.
match goal with  |- context [Rabs (?a)] => field_simplify a end.
rewrite Rabs_R0.
nra.
Qed.


Definition zero := (B754_zero (fprec Tsingle) 128 false).
Definition hd_single := hd zero. 

Ltac unfold_all_fval :=  (* move this to vcfloat *)
 repeat
  match goal with
  | |- context [fval (env_ ?e) ?x] =>
     pattern (fval (env_ e) x);
     let M := fresh in match goal with |- ?MM _ => set (M := MM) end;
     unfold fval; try unfold x; unfold type_of_expr; unfold_fval;
    repeat match goal with |- context [env_ ?a ?b ?c] => 
       let u := constr:(env_ a b c) in 
       let u1 := eval hnf in u in
      change u with u1
     end;
    subst M; cbv beta
end.


Lemma sum_lem: 
    forall (ms : list R) (n: R) ,
    (forall a, In a ms -> 0 <= a <= n ) ->
    sum  (ms)  <= INR (length ms) *  n. 
Proof.
induction ms; intros.
+ 
simpl. nra.
+ 
assert (forall a : R, In a ms -> 0 <= a <= n).
intros. specialize (H a0 (in_cons a a0 ms H0)); auto.
specialize (IHms n H0).
change (sum (a::ms) ) with (a + sum ms).
eapply Rle_trans.
eapply Rplus_le_compat_l; try apply IHms.
replace (INR (length (a :: ms))) with (INR (length ms) + 1).
eapply Rle_trans.
Search (In _ (_::_)).
assert (Ha: a <= n) by (specialize (H a (in_eq a ms)); nra).
eapply Rplus_le_compat_r; try apply Ha.
apply Req_le; try nra.
    replace (length (a::ms)) with (length ms + 1)%nat by (simpl; intuition).
    replace (INR (length ms) + 1) with (INR (length ms + 1)); auto.
rewrite Rplus_comm.
change 1 with (INR 1).
rewrite <- S_O_plus_INR.
f_equal; lia.
Qed.

Lemma sum_lem': 
    forall (ms : list (ftype Tsingle)) (n: R) ,
    (forall a, In a ms -> 0 <= FT2R a <= n ) ->
    sum (map FT2R ms)  <= INR (length ms) *  n. 
Proof.
induction ms; intros.
+ 
simpl. nra.
+ 
assert (forall a : ftype Tsingle, In a ms -> 0 <= FT2R  a <= n).
intros. specialize (H a0 (in_cons a a0 ms H0)); auto.
specialize (IHms n H0).
change (sum (map FT2R (a::ms)) ) with (FT2R a + sum (map FT2R ms)).
eapply Rle_trans.
eapply Rplus_le_compat_l; try apply IHms.
replace (INR (length (a :: ms))) with (INR (length ms) + 1).
eapply Rle_trans.
assert (Ha: FT2R a <= n) by (specialize (H a (in_eq a ms)); nra).
eapply Rplus_le_compat_r; try apply Ha.
apply Req_le; try nra.
    replace (length (a::ms)) with (length ms + 1)%nat by (simpl; intuition).
    replace (INR (length ms) + 1) with (INR (length ms + 1)); auto.
rewrite Rplus_comm.
change 1 with (INR 1).
rewrite <- S_O_plus_INR.
f_equal; lia.
Qed.

Lemma sum_pos:
forall ms, (forall a, In a ms -> 0 <= a) -> 0 <= sum ms.
Proof.
intros.
induction ms; simpl; try nra.
apply Rplus_le_le_0_compat.
apply H; try apply in_eq.
apply IHms.
intros.
apply (H a0).
apply in_cons; auto.
Qed.

Lemma sum_pos':
forall (ms: list (ftype Tsingle)), (forall a, In a ms -> 0 <= FT2R a) -> 0 <= sum (map FT2R ms).
Proof.
intros.
induction ms; simpl; try nra.
apply Rplus_le_le_0_compat.
apply H; try apply in_eq.
apply IHms.
intros.
apply (H a0).
apply in_cons; auto.
Qed.

Lemma real_mean_lem:  
    forall (ms : list R) 
    (mu : R) (m : R) (n: nat),
    ( (length ms) <= n)%nat -> 
    (forall a, In a (m::ms) -> 0 <= a <= INR n ) ->
    mean_rel_R 0%R  (m::ms) mu -> 0 <= mu <= INR n. 
Proof.
intros.
pose proof mean_rel_correct_2 0 m ms mu H1. rewrite <- H2.
unfold mean.
assert (INR (length (m :: ms)) <> 0).
replace (length (m::ms)) with (length ms + 1)%nat by (simpl; intuition).
apply not_eq_sym.
apply Rlt_not_eq.
replace (INR (length ms + 1)) with (INR (length ms) + 1).
apply Rcomplements.INRp1_pos.
change 1 with (INR 1).
rewrite Rplus_comm.
rewrite <- S_O_plus_INR; f_equal; lia.
assert (0 < INR (length (m :: ms))) by
(apply INR_not_0 in H3;
apply lt_0_INR;
lia).
split.
apply Rcomplements.Rdiv_le_0_compat; auto.
apply sum_pos; try apply H0.
apply Rdiv_le_left; auto.
eapply Rle_trans.
apply sum_lem; auto.
apply Req_le; nra. 
Qed.

Lemma real_mean_lem':  
    forall (ms : list (ftype Tsingle)) 
    (mu : R) (m : ftype Tsingle) (n: nat),
    ( (length ms) <= n)%nat -> 
    (forall a, In a (m::ms) -> 0 <= FT2R a <= INR n ) ->
    mean_rel_R (FT2R zero) (FT2R m:: map FT2R ms) mu -> 0 <= mu <= INR n. 
Proof.
intros.
pose proof mean_rel_correct_2 0 (FT2R m) (map FT2R ms) mu H1. rewrite <- H2.
unfold mean.
assert (INR (length (FT2R m :: map FT2R ms)) <> 0).
replace (length (FT2R m :: map FT2R ms)) with (length (map FT2R ms) + 1)%nat by (simpl; intuition).
apply not_eq_sym.
apply Rlt_not_eq.
replace (INR (length (map FT2R ms) + 1)) with (INR (length ms) + 1).
apply Rcomplements.INRp1_pos.
change 1 with (INR 1).
rewrite Rplus_comm.
rewrite map_length.
rewrite <- S_O_plus_INR; f_equal; lia.
assert (0 < INR (length (FT2R m :: map FT2R ms))) by
(apply INR_not_0 in H3;
apply lt_0_INR;
lia).
split.
apply Rcomplements.Rdiv_le_0_compat; auto.
rewrite <- map_cons.
apply sum_pos'; try apply H0.
apply Rdiv_le_left; auto.
eapply Rle_trans.
rewrite <- map_cons.
apply sum_lem'; auto.
rewrite Rmult_comm.
apply Rmult_le_compat; try nra; try apply pos_INR.
apply le_INR.
rewrite <- map_cons.
rewrite map_length.
lia.
Qed.


Theorem FT2R_INR:
  forall (n :Z) (ty : type), 
  (-2 ^ (fprec ty) <= n <= 2 ^ (fprec ty))%Z -> 
  FT2R (Zconst ty n) = IZR n.
Proof.
intros. 
apply BofZ_exact.
auto.
Qed.

Lemma FT2R_nat_ge_0 a:
(Z.of_nat a <= 2 ^ fprec Tsingle)%Z -> 
0 <= FT2R (Zconst Tsingle (Z.of_nat a)).
Proof.
intros.
assert (0 <= Z.of_nat a)%Z by lia. 
rewrite FT2R_INR; try split; try lia; auto.
apply IZR_le; auto.
Qed.

Lemma INR_eq_le a b c1 c2:
INR c1 = c2 ->
a <= b <= c2 <-> a <= b <= INR c1.
Proof.
repeat split; destruct H0; intros; subst; auto.
Qed.


Lemma Zconst_finite:
  forall (n :Z) (ty : type), 
  (-2 ^ (fprec ty) <= n <= 2 ^ (fprec ty))%Z -> 
  is_finite _ _ (Zconst ty n) = true.
Proof.
intros. 
apply BofZ_exact.
auto.
Qed.

Lemma tl_len_le {A} (ms : list A) : 
(length (tl ms) <= length ms)%nat.
Proof.
destruct ms;
simpl; auto.
Qed.

Lemma tl_len_eq {A} (a : A) (ms : list A) : 
(length ms + 1 = length (a:: ms))%nat.
Proof.
destruct ms; simpl; 
try rewrite Nat.add_1_r; auto.
Qed.


Lemma mean_R_step_pos : 
forall mu m (i : nat),
0 <= mu -> 0 <= m ->
0 <= mean_R_step mu m (INR i).
Proof.
intros.
unfold mean_R_step.
replace (mu + (m - mu) / (1 + INR i))
with (mu - mu / (1 + INR i) + m / (1 + INR i)) by nra.
pose proof Rcomplements.INRp1_pos i.
rewrite Rplus_comm in H1.
apply Rplus_le_le_0_compat.
apply Rle_0_minus.
apply Rdiv_le_left; auto.
rewrite Rmult_plus_distr_l; rewrite Rmult_1_r.
rewrite Rplus_comm.
apply Rcomplements.Rle_minus_l.
rewrite Rminus_eq_0.
apply Stdlib.Rmult_le_pos_pos; try nra.
apply pos_INR.
apply Rcomplements.Rdiv_le_0_compat; auto.
Qed.

Lemma mean_rel_bound_bmd_aux :
  forall (ms : list (ftype Tsingle)) 
  (mu : R) (mu_f a: ftype Tsingle),
  ((length (a :: ms)) <= 10)%nat ->
  boundsmap_denote (bmap 10 0 10) (vmap 
    (mu_f, (a, Zconst Tsingle (Z.of_nat (length ms))))) ->
  mean_rel_R (FT2R zero) (map FT2R ms) mu ->
  (forall a0 : ftype Tsingle, In a0 (a :: ms) -> 0 <= FT2R a0 <= 10 /\
    is_finite (fprec Tsingle) (femax Tsingle) a0 = true) ->
  Rabs (mean_R_step mu (FT2R a) (INR (length (map FT2R ms))) -
    FT2R (mean_F_step mu_f a (Zconst Tsingle (Z.of_nat (length ms))))) 
    <= INR (length (a :: ms)) * 1.2e-4 ->
  boundsmap_denote (bmap 10 0 10) (vmap
    (mean_F_step mu_f a (Zconst Tsingle (Z.of_nat (length ms))),
    (a, Zconst Tsingle (Z.of_nat (length (tl (a :: ms))))))).
Proof.
intros ? ? ? ? Hlen BMD Hmrel Hin Habs.
pose proof (Hin a (in_eq a ms)) as Ht; destruct Ht as (Ha1 & Ha2).
assert 
( BMD3:      boundsmap_denote (bmap 10 0 10)
         (vmap
            (mu_f,
            (a, Zconst Tsingle (Z.of_nat (length (tl (a::ms)))))))).
  { 
  replace (Z.of_nat (length (tl (a::ms)))) with ( (Z.of_nat (length ms))); auto.
  }
set (mur:=mean_R_step mu (FT2R a) (INR (length (map FT2R ms)))).
assert (Hlist2:
(forall a0 : ftype Tsingle, In a0 (a :: ms) -> 0 <= FT2R a0 <= INR 10)).
  {intros. specialize (Hin a0).
  apply in_inv in H; destruct H. subst.
    -
      rewrite <- INR_eq_le; try apply Ha1; simpl; try nra.
    -
      rewrite <- INR_eq_le; try apply Ha1; simpl; try nra.
      pose proof (in_cons a a0 (ms) H) as H3.
      specialize (Hin H3). try apply Hin. field_simplify; nra.
  }
assert (Hlen2: (length  ms <= 10)%nat).
  { eapply Nat.le_trans.
  apply Nat.le_le_succ_r.
  apply le_refl.
  rewrite <- tl_len_eq in Hlen.
  eapply le_trans.
  2 : apply Hlen.
  apply Nat.eq_le_incl; lia. 
  }
pose proof (real_mean_lem'  ms mur a 10 Hlen2 Hlist2) as Hrel.
rewrite <- map_cons in Hrel.
pose proof mean_rel_correct_1 (FT2R zero) (FT2R a) (map FT2R ms). 
destruct (prove_roundoff_bound _ BMD3) as [? ?].
apply boundsmap_denote_e in BMD3.
apply boundsmap_denote_i;
repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
eexists; repeat (try split; try reflexivity); simpl; auto; try field_simplify;
try apply Ha1.
eexists; repeat (try split; try reflexivity); simpl; auto; try field_simplify.
-
assert 
(Hbnd: 10 * -1.2 / 10000 <= - (INR (length (a :: ms)) * 1.2e-4)).
  {
  field_simplify.
  apply Ropp_le_cancel.
  field_simplify.
  replace (-10 * -1.2 / 10000) with (10 * (1.2 / 10000)) by nra.
  replace (INR (length (a :: ms)) * 1.2 / 10000) with 
    (INR (length (a :: ms)) * (1.2 / 10000)) by nra.
  apply Rmult_le_compat; try nra; auto.
  try apply pos_INR.
  apply le_INR in Hlen.
  eapply Rle_trans. apply Hlen. simpl; field_simplify; interval.
  }
eapply Rle_trans.
apply Hbnd.
eapply Rle_trans.
rewrite Rabs_minus_sym in Habs.
apply Rabs_le_inv in Habs.
destruct Habs as (Habs & _).
apply Habs.
apply Rcomplements.Rle_minus_l.
rewrite Rplus_comm.
rewrite <- Rcomplements.Rle_minus_l.
field_simplify.
{ destruct ms.
-
simpl in Hrel, mur. subst mur. simpl.
unfold mean_R_step . field_simplify; auto. try apply Ha1.
-
rewrite mean_cons in H.
rewrite map_cons in Hmrel.
rewrite  mean_rel_correct in Hmrel.
rewrite map_cons in H.
change (INR (length (FT2R f :: map FT2R ms))) with
(INR (length ( map FT2R (f:: ms)))) in H.
subst. fold mur in H.
specialize (Hrel H); try apply Hrel; auto.
}
-
rewrite Rabs_minus_sym in Habs.
apply Rabs_le_inv in Habs.
destruct Habs as (_ & Habs).
rewrite Rcomplements.Rle_minus_l in Habs.
eapply Rle_trans. apply Habs.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; try nra.
apply le_INR. apply Hlen.
{ destruct ms.
-
simpl in Hrel, mur. subst mur. simpl.
unfold mean_R_step . field_simplify; auto. 
apply Rdiv_le_left; nra.
-
rewrite mean_cons in H.
rewrite map_cons in Hmrel.
rewrite  mean_rel_correct in Hmrel.
rewrite map_cons in H.
change (INR (length (FT2R f :: map FT2R ms))) with
(INR (length ( map FT2R (f:: ms)))) in H.
subst. fold mur in H. fold mur.
field_simplify. apply Rdiv_le_left; try nra.
field_simplify. 
apply Rplus_le_compat.
apply Rmult_le_compat; try apply pos_INR; try nra.
simpl; field_simplify; nra.
eapply Rle_trans. apply Rmult_le_compat_l; try nra.
specialize (Hrel H); try apply Hrel. 
simpl; field_simplify; nra.
}
-
assert (Hint: (- 2 ^ fprec Tsingle <= Z.of_nat (length ms) <= 2 ^ fprec Tsingle)%Z) by
  (split; simpl; try lia; try interval).
eexists; repeat (try split; try reflexivity); simpl; auto; try field_simplify.
apply Zconst_finite; auto.
apply FT2R_nat_ge_0. destruct Hint; auto.
rewrite FT2R_INR; auto.
rewrite <- INR_IZR_INZ.
field_simplify.
eapply Rle_trans.
apply le_INR. apply Hlen2.
simpl; field_simplify; nra.
Qed.

Theorem mean_rel_bound :
    forall (ms : list (ftype Tsingle)) 
    (mu : R) (mu_f : ftype Tsingle),
    mean_rel_R (FT2R zero) (map FT2R ms) mu ->
    mean_rel_F zero ms mu_f ->
    (forall a, In a ms -> 0 <= FT2R a <= 10 /\ is_finite _ _ a = true) ->
    (length  ms <= 10)%nat -> 
    boundsmap_denote (bmap 10 0 10) (vmap (mu_f, (hd_single ms , Zconst Tsingle (Z.of_nat (length (tl ms)))))) /\
    Rabs (mu - FT2R mu_f) <= INR (length  ms) * 1.2e-4.
Proof.
induction ms; intros mu mu_f HR HF ? Hfin;
inversion HF; subst; clear HF;
inversion HR; subst; clear HR;
intros; subst.
- 
split. 
+
apply boundsmap_denote_i.
all: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto;
repeat apply list_forall_cons; try apply list_forall_nil;
(eexists; split; [|split;[|split]]; try reflexivity; auto;
 simpl; try nra; auto).
+ 
simpl; rewrite Rminus_eq_0, Rabs_R0; lra.
- 
assert
(Hlist: (forall a : ftype Tsingle,
         In a ms ->
         0 <= FT2R a <= 10 /\ is_finite (fprec Tsingle) (femax Tsingle) a = true)).
  {
  intros. 
  specialize (H a0 (in_cons a a0 ms H0)); auto.
  }
rename mu1 into mu.
rename mu0 into mu_f.
simpl in Hfin.
assert 
(BMD2: boundsmap_denote (bmap 10 0 10) (vmap (mu_f, (a, Zconst Tsingle (Z.of_nat (length ( ms))))))).
  {
  assert (Htl: ((length  ms) <= S(length ms))%nat) by apply Nat.le_succ_diag_r.
    {
    specialize (IHms mu mu_f H4 H3 Hlist) as (IHms & _).
    eapply Nat.le_trans; try apply Htl; auto. 

    specialize (H a (in_eq a ms)); destruct H as (Ha1 & Ha2).

    apply boundsmap_denote_e in IHms.
    simpl in IHms; destruct IHms as (_ & B & C).
    apply boundsmap_denote_i;
    repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
    eexists; repeat (try split; try reflexivity); simpl; auto; try interval. 
    assert (Hint: (- 2 ^ fprec Tsingle <= Z.of_nat (length ms) <= 2 ^ fprec Tsingle)%Z) by
      (split; simpl; try lia; try interval).
    eexists; repeat (try split; try reflexivity); simpl; auto; try interval.
    assert (Z.of_nat (length ms) + 1  <= 10 + 1)%Z by lia.
    assert ((Z.of_nat (length ms) + 1 <= femax Tsingle)%Z).
    eapply Z.le_trans.
    apply H. simpl; lia.
    apply Zconst_finite; auto.
    apply FT2R_nat_ge_0; destruct Hint; auto.
    rewrite FT2R_INR; auto.
    rewrite <- INR_IZR_INZ.
    field_simplify.
    replace 10 with (INR 10).
    apply le_INR; auto.
    eapply Nat.le_trans; try apply Htl; auto. 
     simpl; try nra.
    }
  }
assert (Hyp: (- 2 ^ fprec Tsingle <= Z.of_nat (length (ms)) <= 2 ^ fprec Tsingle)%Z) by 
  (simpl; lia). 
assert (0 <= Z.of_nat (length (ms)) <= 10)%Z by lia.
match goal with |- context [ ?A /\ ?B] =>
  assert B
end.
+
assert (Hlen: (length ms <= 10)%nat).
  {
  eapply Nat.le_trans.
  apply Nat.le_le_succ_r.
  apply le_refl. 
  apply Hfin.
  }
replace (length (map FT2R ms)) with (length ms) by (symmetry; apply map_length).
replace (length (tl (a::ms))) with (length ms )%nat by (simpl; intuition).
apply Rle_trans with (Rabs (mu - FT2R mu_f) + 1.2e-4).
pose proof (FT2R_INR (Z.of_nat (length ms)) Tsingle Hyp) as Hyp1; clear Hyp.
    rewrite INR_IZR_INZ.
rewrite <- Hyp1.
apply mean_step_bound'; auto.
specialize (IHms mu mu_f H4 H3 Hlist) as ( _ & IHms); auto.
eapply Rle_trans.
eapply Rplus_le_compat_r.
apply IHms.
replace (INR (length (a :: ms))) with (INR (length ( ms)) +1).
apply Req_le. nra.
rewrite <- S_INR. f_equal. 
+
split;auto.
unfold hd_single, hd.
assert ((length (a :: ms) <= 10)%nat).
  { 
  eapply Nat.le_trans.
  2: apply Hfin. 
  rewrite <- tl_len_eq. lia. 
  }
apply (mean_rel_bound_bmd_aux ms mu mu_f a H2 BMD2 H4 H H1). 
Qed.



End WITHNANS.
