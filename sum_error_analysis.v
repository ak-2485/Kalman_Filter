From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import weight_spec weight_spec_R.


Section WITHNANS.
Context {NANS: Nans}.

Fixpoint pos_list (n : nat) : list (positive) :=
  match n with
  | 0%nat => []
  | S n' =>  pos_list n' ++ [Pos.of_nat n]
  end.

Definition fsum_list : list (ftype Tdouble) := [1%F64;11%F64;11%F64;110%F64].

Local Open Scope float64_scope.

Definition default_val := 0. 

Definition sum_F a b:= a + b.

Fixpoint fix_fsum_list_F (l : list (ftype Tdouble)) :  ftype Tdouble := 
  match l with
  | nil     => default_val
  | h :: tl => h + fix_fsum_list_F tl 
  end. 

Close Scope float64_scope. 


Fixpoint fix_fsum_list_R (l : list R) :  R := 
  match l with
  | nil     => 0
  | h :: tl => h + fix_fsum_list_R tl 
  end. 


Ltac reify_float_expr' l_var l_sum :=
  match l_var with
  | ?hv :: ?tlv => 
    match l_sum with
    | ?hs :: ?tls => let a' := reify_float_expr' hv hs in let b' := reify_float_expr' tlv tls in 
                                      constr:(@Binop ident (Rounded2 PLUS None) a' b')
    | [] => constr:(@Const ident Tdouble (B754_zero 53 1024 false))
    | _ => constr:(@Var ident Tdouble hv)
    end
  | [] => constr:(@Const ident Tdouble (B754_zero 53 1024 false))
  | _  => constr:(@Var ident Tdouble l_var) 
end.

Definition pos_list' := ltac:(let e' :=
   eval compute in (pos_list (length fsum_list))  in exact e').

Definition reify_sum := ltac:(let e' :=
    reify_float_expr' constr:(ltac:(let e' := eval compute in pos_list' in exact e')) 
                      constr:(ltac:(let e' := eval compute in fsum_list in exact e')) in exact e').

Definition state : Type := list (ftype Tdouble).

Definition list_nth (n:nat) (x : list (ftype Tdouble)) : (ftype Tdouble) :=
  @List.nth (ftype Tdouble) n x default_val.


Fixpoint assoc_list (l1 : list positive) (l2: list (ftype Tdouble))  := 
  match l1, l2 with
 |  h1 :: tl1 , h2 :: tl2 => assoc_list tl1 tl2 ++ [(h1, existT ftype Tdouble h2)] 
 | _, _ => []
end.


Definition assoc_list'  := ltac: (let e' :=  eval hnf in  (assoc_list pos_list' fsum_list) in exact e').


Definition varmap : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list assoc_list') in exact z).


Fixpoint bmap_list  (l1 : list positive) (l2: list (ftype Tdouble)) := 
  match l1, l2 with
 |  h1 :: tl1 , h2 :: tl2 => [Build_varinfo Tdouble h1 0 (FT2R h2)] ++ bmap_list tl1 tl2
 | _, _ => []
end.

Definition bmap_list' := ltac: (let e' :=  eval hnf in  (bmap_list pos_list' fsum_list) in exact e').

Definition bmap : boundsmap :=
 ltac:(let z := eval compute in (boundsmap_of_list bmap_list') in exact z).



Lemma absolute_roundoff_bound:
  prove_roundoff_bound bmap varmap reify_sum 
  (length fsum_list  * 1/2^52 * 100).
Proof.
intros.
prove_roundoff_bound.
- 
time (prove_rndval; interval).
-
time (
prove_roundoff_bound2;
clear BOUND BOUND0 BOUND1 BOUND2;
match goal with |- context[ Rabs ?a <= _] => 
field_simplify a 
end;
match goal with |- context[ Rabs ?a <= _] => 
interval_intro a upper 
end;
simpl;
interval).
Qed.


Definition _acc := 1%positive.
Definition _x   := 2%positive. 

Definition reify_sum' := 
Binop (Rounded2 PLUS None)
  (Var Tdouble _acc)
     (Var Tdouble _x).

Definition a_list (s : state) :=  assoc_list [_acc; _x] [list_nth 0 s; list_nth 1 s].


Definition vmap (s : state) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (a_list s)) in exact z).

Definition b_list : list varinfo := 
  [ Build_varinfo Tdouble _acc 0 91 ;  
      Build_varinfo Tdouble _x 0 10].

Definition bmap' : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list b_list) in exact z).

Lemma absolute_roundoff_bound': forall s,
  prove_roundoff_bound bmap' (vmap s) reify_sum'
    (101.01 * 1/2^53).
Proof.
intros. 
prove_roundoff_bound.
- prove_rndval; unfold list_nth in *; interval. 
- prove_roundoff_bound2; unfold list_nth in *.
match goal with |- context[ Rabs ?a <= _] => 
field_simplify a 
end;
match goal with |- context[ Rabs ?a <= _] => 
interval_intro a upper
end.
simpl;
interval.
Qed.

Lemma round_off_bound_implies : 
  forall s, 
  boundsmap_denote bmap' (vmap s)-> 
Rabs (FT2R (fval (env_ (vmap s)) reify_sum') 
      - rval (env_ (vmap s)) reify_sum')  <= 
          (101.01 * 1/2^53).
Proof.
Admitted.

Definition FT2R_list (ty : type) (l : list (ftype ty)) : list R :=  map FT2R l.

Lemma reflect_f : 
forall s : state, 
fval (env_ (vmap s)) reify_sum' = sum_F (list_nth 0 s) (list_nth 1 s).
Proof.
Admitted.

Lemma reflect_r : 
forall s : state, 
rval (env_ (vmap s)) reify_sum' = FT2R (list_nth 0 s) + FT2R (list_nth 1 s).
Proof.
Admitted.


Theorem prove_roundoff_bound_total:
  forall l,
  (* Geoff was right, we have to bound the length of the list in this proof; our boundsmap
  was constructed under the assumption that our list has length 9. This is one reason why 
  we might want the boundsmap to be a function of the length of the list *)
  length l <= 9 ->
  (forall x, In x l -> Rabs (FT2R x) <= 10) -> 
  (boundsmap_denote bmap' (vmap [(fix_fsum_list_F (tl l)); hd default_val l]) /\
  Rabs (FT2R (fix_fsum_list_F l) - fix_fsum_list_R (FT2R_list Tdouble l)) <= 
    length l * 101.01 *  1/2^53).
Proof.
intros.
induction l.
- 
split.
+
simpl. admit.
+
eapply Rle_trans.  simpl. admit. admit.
-  
assert (IHH: (forall x : ftype Tdouble,
       In x l -> Rabs (FT2R x) <= 10)) by admit.
+ 
assert (Hlen: length l <= 9) by admit.
specialize (IHl Hlen IHH).
clear IHH Hlen.
split.
*
(* I think this is provable from IHl, IHH, and H. In particular,
  if we know 
  (1) from H that the length of (a::l) is less than or equal to 9, and 
  (2) from H0 that each element of (a::l) is less than or equal to 10, 
  then we can prove that fix_fsum_list_F (tl (a :: l)) is less than or equal to 90
  and that a <= 10 *)
admit.
* destruct IHl as (IHa & IHb).
set (accF := (fix_fsum_list_F l)) in *.
set (accR := fix_fsum_list_R (FT2R_list Tdouble l)) in *.
assert (Hf: FT2R (fix_fsum_list_F (a :: l)) = FT2R (sum_F a accF)) by f_equal.
assert (Hr: fix_fsum_list_R
     (FT2R_list Tdouble (a :: l)) = (FT2R a) + accR ) by (simpl; f_equal).
rewrite Hf; rewrite Hr.
set (C:= (FT2R a + FT2R accF)).
eapply Rle_trans.
match goal with |- context[(Rabs (?A - ?B))] =>
  replace (A - B) with ((A - C) + (C - B)) by nra ;
  subst C
end.
eapply Rabs_triang.
eapply Rle_trans.
rewrite Rplus_comm.
eapply Rplus_le_compat.
match goal with |- context[(Rabs ?A)] =>
field_simplify A
end.
apply IHb.
pose proof round_off_bound_implies [fix_fsum_list_F l;a].
rewrite reflect_r in H1.
rewrite reflect_f in H1.
cbv [list_nth nth] in H1.
unfold accF, accR.
assert (Hcomm: sum_F a (fix_fsum_list_F l) = (sum_F (fix_fsum_list_F l)) a).
unfold sum_F.
(* see theorem from compcert float module 
 add_commut *) admit.
rewrite Hcomm.
rewrite Rplus_comm.
apply H1.
(* we already proved this so should assert it earlier on *) admit.
assert (Hlen : length (a :: l) * 101.01 * 1 / 2 ^ 53 =
  INR (length l + 1)%nat * 101.01 * 1 / 2 ^ 53) by
  (try repeat f_equal; simpl; try lia).
rewrite Hlen. clear Hlen.
apply Req_le.
apply symmetry.
rewrite !Rmult_1_r.
field_simplify.
f_equal.
rewrite Rmult_comm.
replace  (101.01 * length l + 101.01) with (101.01 * length l + 101.01 * 1) by nra.
rewrite <- Rmult_plus_distr_l.
f_equal.
(* well, ...*)
Admitted.

 




End WITHNANS.