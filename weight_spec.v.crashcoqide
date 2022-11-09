From Coq Require Import Floats.
From Coq Require Import Numbers.Cyclic.Int63.Uint63.
From Coq Require Import List.
Import ListNotations.

Section Util.
  Variables A B : Type.

  Fixpoint fold_map (f : A -> B -> A) (a : A) (bs : list B) : list A :=
    match bs with
    | [] => []
    | b::bs =>
      let a' := f a b in
      a' :: fold_map f a' bs
    end.
End Util.

Arguments fold_map {A B} f a bs.

Open Scope float_scope.

Definition filter_step (i : int) (g : float) (m : float) : float :=
  g + (1 / (of_uint63 i) * (m - g)).

Definition alpha_filter (guess : float) : list float -> list (int * float) :=
  fold_map (fun '(i,g) m =>
    let i' := (i + 1)%uint63 in
    (i', filter_step i' g m))
  (0%uint63, guess).

Compute
  (* noisy measurements normally distributed around true value of 1010 *)
  let measurements :=
    [1030.0;  989.0; 1017.0; 1009.0; 1013.0;
      979.0; 1008.0; 1042.0; 1012.0; 1011.0]
  in
  let initial_guess := 1000.0 in
  alpha_filter initial_guess measurements.
