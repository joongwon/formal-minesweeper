Require Import Grid.
Require Import List.
Require Import Relations.Relation_Operators.
Import ListNotations.

Definition bool_grid (n m : nat) : Type := grid bool n m.

Definition B2N (b : option bool) : nat := match b with
  | Some true => 1
  | _ => 0
end.

Definition get_NW {n m} (M : bool_grid n m) (i j : nat) : option bool :=
  match i, j with
  | O, O => None
  | O, S j' => None
  | S i', O => None
  | S i', S j' => M[i',j']
  end.

Definition count_mines {n m} (M : bool_grid n m) (i j : nat) : nat :=
  let i' := S i in
  let j' := S j in
  let ds := [
    (i'-1, j'-1); (i', j'-1); (i'+1, j'-1);
    (i'-1, j);             (i'+1, j);
    (i'-1, j'+1); (i', j'+1); (i'+1, j'+1)
  ] in
  fold_left (fun acc '(i, j) => acc + B2N (get_NW M i j)) ds 0.

Definition neighbor n n' : Prop := S n = n' \/ n = S n' \/ n = n'.
Infix "~" := neighbor (at level 70).

Definition is_numbered {n m} (M C : bool_grid n m) x y cnt : Prop :=
  C[x,y] = Some false /\
  count_mines M x y = cnt.
Definition is_covered {n m} (C : bool_grid n m) x y : Prop :=
  C[x,y] = Some true.
Definition is_mine {n m} (M : bool_grid n m) x y : Prop :=
  M[x,y] = Some true.
Definition is_safe {n m} (M : bool_grid n m) x y : Prop :=
  M[x,y] = Some false.

Inductive uncover_zero_step {n m} : forall (M C C' : bool_grid n m), Prop :=
  | UZ_step : forall M C x y x' y',
      is_numbered M C x y 0 ->
      x ~ x' /\ y ~ y' ->
      is_covered C x' y' ->
      uncover_zero_step M C (C[x',y' <- false]).

Definition uncover_zeros {n m} (M : bool_grid n m) (C C' : bool_grid n m) : Prop :=
  clos_refl _ (uncover_zero_step M) C C' /\ ~exists C'', uncover_zero_step M C' C''.

Inductive game : Type :=
  | START (w h : nat)
  | PLAY {n m} (M : bool_grid n m) (C : bool_grid n m)
  | WIN  {n m} (M : bool_grid n m)
  | LOSE {n m} (M : bool_grid n m) (C : bool_grid n m) (x y : nat).

Inductive step : game -> nat -> nat -> game -> Prop :=
  | step_start_play : forall w h (M : bool_grid w h) x y C',
      is_safe M x y ->
      uncover_zeros M (grid_make true w h)[x,y <- false] C' ->
      M <> C' ->
      step (START w h) x y (PLAY M C')
  | step_start_win : forall w h (M : bool_grid w h) x y,
      is_safe M x y ->
      uncover_zeros M (grid_make true w h)[x,y <- false] M ->
      step (START w h) x y (WIN M)
  | step_play_play : forall n m (M : bool_grid n m) C C' x y,
      is_covered C x y ->
      is_safe M x y ->
      uncover_zeros M C[x,y <- false] C' ->
      M <> C' ->
      step (PLAY M C) x y (PLAY M C')
  | step_play_win : forall n m (M : bool_grid n m) C x y,
      is_covered C x y ->
      is_safe M x y ->
      uncover_zeros M C[x,y <- false] M ->
      step (PLAY M C) x y (WIN M)
  | step_play_lose : forall n m (M : bool_grid n m) C x y x' y',
      is_covered C x y ->
      is_mine M x y ->
      step (PLAY M C) x' y' (LOSE M C x y).

Notation "g1 =( x , y )=> g2" := (step g1 x y g2) (at level 70).
