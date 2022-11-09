From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import weight_spec weight_spec_R.

Open Scope R_scope.

Section WITHNANS.
Context {NANS: Nans}.

Definition _i : ident := 1%positive.
Definition _g : ident := 2%positive.
Definition _m : ident := 3%positive.

Definition reify_filter_step := ltac:(let e' :=
    HO_reify_float_expr constr:([_i; _g; _m]) weight_spec.filter_step in exact e').

Definition state : Type := ftype Tdouble * (ftype Tdouble * ftype Tdouble).

Definition vmap_raw (s:  state)  :=
 valmap_of_list [(_i, existT ftype _   (fst s) ) ;(_g, existT ftype _ (fst (snd s))); (_m, existT ftype _ (snd (snd s)))].

Definition vmap s : valmap :=
 ltac:(let z := compute_PTree (vmap_raw s) in exact z).


Lemma reflect_reify_s : forall s, 
    let e := env_ (vmap s) in 
     fval e reify_filter_step = weight_spec.filter_step (fst s) (fst (snd s)) (snd (snd s)).
Proof. reflexivity. Qed.

Definition bmap_list : list varinfo := 
  [ Build_varinfo Tdouble _i 1 10 ;  
      Build_varinfo Tdouble _g 0  10 ;
        Build_varinfo Tdouble _m 0 10].

Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).


Lemma prove_roundoff_bound:
  forall s : state,
  prove_roundoff_bound bmap (vmap s) reify_filter_step 
    1.9985e-14.
Proof.
intros [i [g m]].
prove_roundoff_bound.
-
(prove_rndval; interval).
- 
prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
all: try interval.
Qed.

Lemma prove_roundoff_bound_implies':
  forall s : state,
  boundsmap_denote bmap (vmap s)-> 
  Rabs (FT2R (fval (env_ (vmap s)) reify_filter_step) 
           - rval (env_ (vmap s)) reify_filter_step)
        <=     1.9985e-14.
Proof.
intros.
apply (prove_roundoff_bound s H).
Qed.
 

Lemma prove_roundoff_bound_implies_1:
  forall s1 s2 : state,
  boundsmap_denote bmap (vmap s1)-> 
  boundsmap_denote bmap (vmap s2)-> 
  Rabs (FT2R (fval (env_ (vmap s1)) reify_filter_step) 
           - FT2R (fval (env_ (vmap s2)) reify_filter_step))
        <=     1.9985e-14.
Proof.
intros.
pose proof (prove_roundoff_bound s1 H).
pose proof (prove_roundoff_bound s2 H0).
destruct H1 as (_ & B1).
destruct H2 as (_ & B2).
eapply Rle_trans.
  set (c1:= (rval (env_ (vmap s1)) reify_filter_step)).
  set (c2:= (rval (env_ (vmap s2)) reify_filter_step)).
match goal with |- context[Rabs(?a - ?b)] =>
  assert (Rabs (a - b ) <= Rabs (a - c1) + Rabs (b - c2) + Rabs (c1 -c2))
end.
Admitted.

Lemma reflect_reify_sF : forall s, 
    let e := env_ (vmap s) in 
    let '(i, (g,m) ) := s in 
    fval e reify_filter_step = weight_spec.filter_step i g m.
Proof. intros. destruct s. destruct p. reflexivity. Qed.


Lemma reflect_reify_sR : forall s, 
    let e := env_ (vmap s) in 
    let '(i, (g,m) ) := s in 
    rval e reify_filter_step = filter_step (FT2R i) (FT2R g)  (FT2R m).
Proof. intros. destruct s. destruct p. unfold_rval. unfold filter_step. f_equal. Qed.

Lemma prove_roundoff_bound_implies:
  forall s : state,
    let e := env_ (vmap s) in 
    let '(i, (g,m) ) := s in 
  boundsmap_denote bmap (vmap s)-> 
  Rabs (filter_step (FT2R i) (FT2R g)  (FT2R m) - FT2R (weight_spec.filter_step i g m ))
        <=     1.9985e-14.
Proof.
intros.
Admitted.



Definition FT2R_list (ty : type) (l : list (ftype ty)) : list R :=  map FT2R l.

(*
Lemma aux :
forall g ns a,
alpha_filter g (ns ++  [a]) (length ns + 1) = 
  filter_step (length ns + 1) (alpha_filter g ns (length ns)) a. 
Proof.
intros.
Admitted.*)

Ltac simplify_Rabs :=
  match goal with |- context [Rabs ?a] =>
    field_simplify a; try nra
  end.

(* measure and iteration are the same, guess from previous step
  is rounded *)
Lemma alpha_filterR_diff :
forall i g g' m ,
  Rabs (filter_step i g m  -  filter_step i g' m) <=  (1 + (1/i)) * Rabs (g - g') .
Proof.
intros.
unfold filter_step.
rewrite <- Rabs_pos_eq.
Admitted.



Theorem prove_roundoff_bound_total:
  forall g ns f r,
  let i_init := Zconst Tdouble (Z.of_nat (length ns)) in
  let s := (1%F64, (g, @hd (ftype Tdouble) (B754_zero _ _ false ) ns)) in
  boundsmap_denote bmap (vmap s) ->
  (weight_spec.alpha_filter g ns (Z.of_nat (length ns)), alpha_filter (FT2R g) (FT2R_list Tdouble ns) (length ns))
      = (Some f, Some r) -> 
    let a:= List.nth (length ns + 1) ns (B754_zero _ _ false ) in 
    let '(i,g',m') := (Zconst Tdouble (Z.of_nat (length ns + 1)), f, a)  in
    boundsmap_denote bmap (vmap (i ,(g',m')) ) /\  
    Rabs (r - FT2R f) <= length ns * 1.9985e-14.
Proof.
intros.
simpl.
induction ns.
-
simpl. 
split.
+
simpl.
simpl in a.
admit.
+
simpl in *.
assert False by admit.
contradiction.
-
split.
+ simpl; admit.
+
simpl in IHns.




eapply Rle_trans. 
pose proof aux (FT2R g) (rev (FT2R_list Tdouble ns)) (FT2R a0).
assert ((length (rev (FT2R_list Tdouble ns)) + 1) = (S (length ns))).
admit.
rewrite H1 in H0. clear H1.
change (length (a0 :: ns)) with (S (length ns)).
change (rev (FT2R_list Tdouble (a0 :: ns))) with (rev (FT2R_list Tdouble ns) ++ [FT2R a0]).
rewrite H0. clear H0.
assert
  (boundsmap_denote bmap
         (vmap (B754_zero (fprec Tdouble) 1024 false, (g, hd (B754_zero (fprec Tdouble) 1024 false) ns)))).
pose proof prove_roundoff_bound_implies s H.



Admitted.

    let '(i',g',m') := ((length ns + 1), ((weight_spec.alpha_filter g (rev ns) (Z.of_nat (length ns)))), a)  in
    boundsmap_denote bmap (vmap (Zconst Tdouble (Z.of_nat (length ns)),(g',m')) ) /\
    Rabs (alpha_filter (FT2R g) (rev (FT2R_list Tdouble ns)) (length ns) -
    FT2R (weight_spec.alpha_filter g (rev ns) (Z.of_nat (length ns)))) <= length ns * 1.9985e-14.

End WITHNANS.