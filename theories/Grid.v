Require Import Tactics.
Require Import Nat.
Require Import PeanoNat.

Inductive listn (A : Type) : nat -> Type :=
  | niln : listn A 0
  | consn (n : nat) (x : A) (xs : listn A n) : listn A (S n).

Fixpoint listn_make {A : Type} (default : A) (n : nat) : listn A n :=
  match n with
  | 0 => niln _
  | S n' => consn _ n' default (listn_make default n')
  end.

Fixpoint listn_get {A : Type} {n : nat} (i : nat) (r : listn A n) : option A :=
  match i, r with
  | 0, consn _ _ x _ => Some x
  | S i', consn _ _ _ r' => listn_get i' r'
  | _, _ => None
  end.

Fixpoint listn_map {A B : Type} {n : nat} (f : A -> B) (r : listn A n) : listn B n :=
  match r with
  | niln _ => niln _
  | consn _ _ x r' => consn _ _ (f x) (listn_map f r')
  end.

Fixpoint listn_update {A : Type} {n : nat} (i : nat) (x : A) (r : listn A n) : listn A n :=
  match i, r with
  | _, niln _ => niln _
  | 0, consn _ _ _ r' => consn _ _ x r'
  | S i', consn _ _ y r' => consn _ _ y (listn_update i' x r')
  end.

Notation "x [ i ]" := (listn_get i x) (at level 9).
Notation "x [ i <- v ]" := (listn_update i v x) (at level 9).

Require Import Lia.

Lemma listn_get_some {A : Type} :
  forall n i (r : listn A n) (H : i < n), exists x, r[i] = Some x.
Proof.
  induction n; intros; [lia|].
  dependent inversion_clear r.
  destruct i; simpl; [exists x; reflexivity|].
  apply IHn; lia.
Qed.

Lemma listn_get_none {A : Type} :
  forall n i (r : listn A n) (H : i >= n), r[i] = None.
Proof.
  induction n; intros; dependent inversion_clear r; destruct i; auto; simpl.
  - lia.
  - apply IHn. lia.
Qed.

Lemma listn_get_cases {A : Type} :
  forall n i (r : listn A n),
  (i < n /\ exists x, r[i] = Some x) \/ (i >= n /\ r[i] = None).
Proof.
  intros. destruct (Nat.lt_ge_cases i n).
  - left. split; auto. apply listn_get_some; auto.
  - right. split; auto. apply listn_get_none; auto.
Qed.

Lemma listn_make_get {A : Type} (default : A) :
  forall n i (H : i < n), (listn_make default n)[i] = Some default.
Proof.
  induction n; intros; inversion_clear H; [destruct n|destruct i];
      auto; apply IHn; lia.
Qed.

Lemma listn_update_get {A : Type} :
  forall n i (r : listn A n) x (H : i < n), r[i<-x][i] = Some x.
Proof.
  induction n; [lia|].
  intros. dependent inversion_clear r.
  destruct i; simpl; [reflexivity|].
  apply IHn. lia.
Qed.

Lemma listn_update_eq {A : Type} :
  forall n i (H : i >= n) (r : listn A n) x, r[i<-x] = r.
Proof.
  induction n.
  - intros. dependent inversion_clear r. destruct i; auto.
  - intros. dependent inversion_clear r. destruct i; try lia.
    simpl. f_equal. apply IHn. lia.
Qed.

Lemma listn_update_get_neq {A : Type} :
  forall n i i' (r : listn A n) x (H : i <> i'),
  r[i<-x][i'] = r[i'].
Proof.
  induction n; dependent inversion_clear r; destruct i, i'; simpl; auto. lia.
Qed.

Definition grid A n m := listn (listn A n) m.

Definition grid_make {A : Type} (default : A) n m : grid A n m :=
  listn_make (listn_make default n) m.

Definition grid_get {A : Type} {n m : nat} (i j : nat) (g : grid A n m) : option A :=
  match g[j] with
  | Some row => row[i]
  | None => None
  end.

Definition grid_map {A B : Type} {n m : nat} (f : A -> B) (g : grid A n m) : grid B n m :=
  listn_map (listn_map f) g.

Definition grid_update {A : Type} {n m : nat} (i j : nat) (x : A) (g : grid A n m) : grid A n m :=
  match g[j] with
  | Some row => g[j <- row[i <- x]]
  | None => g
  end.

Notation "x [ i , j ]" := (grid_get i j x) (at level 9).
Notation "x [ i , j <- v ]" := (grid_update i j v x) (at level 9).

Lemma grid_make_get {A : Type} (default : A) :
  forall n m i j (H : i < n) (H' : j < m), (grid_make default n m)[i, j] = Some default.
Proof.
  intros. unfold grid_make, grid_get. repeat rewrite listn_make_get; auto.
Qed.

Lemma grid_update_get {A : Type} :
  forall n m i j (g : grid A n m) x (Hi : i < n) (Hj : j < m), g[i, j <- x][i, j] = Some x.
Proof.
  intros. unfold grid_update, grid_get.
  destruct (g[j]) eqn:?.
  - repeat rewrite listn_update_get; auto.
  - destruct (listn_get_some m j g Hj).
    rewrite Heqo in *. discriminate.
Qed.

Lemma grid_update_get_neq {A : Type} :
  forall n m i j i' j' (g : grid A n m) x (H : i <> i' \/ j <> j'),
  g[i, j <- x][i', j'] = g[i', j'].
Proof.
  intros. unfold grid_update, grid_get.
  destruct (Nat.eq_dec j j'); destruct H; try lia; auto;
  destruct (listn_get_cases m j g) as [[Hj [r Hr]] | [Hj Hr]]; repeat rewrite Hr; auto;
  try (rewrite listn_update_get_neq by assumption; reflexivity).
  subst. rewrite listn_update_get by assumption.
  rewrite listn_update_get_neq by assumption.
  rewrite Hr. reflexivity.
Qed.

Declare Custom Entry grid.
Notation "G{ x ; .. ; y }" := (consn _ _ x .. (consn _ _ y (niln _)) ..)
    (at level 9, x custom grid at level 2, y custom grid at level 2,
      format "G{  '[' x ']' ; '//'    .. ; '//'    '[' y ']' '//' }").
Notation "G{ x ; .. ; y ; }" := (consn _ _ x .. (consn _ _ y (niln _)) ..)
    (at level 9, x custom grid at level 2, y custom grid at level 2,
      format "G{ '//'   '[' x ']' ; '//'   .. ; '//'   '[' y ']' ; '//' }").
Notation "x .. y" := (consn _ _ x .. (consn _ _ y (niln _)) ..)
    (in custom grid at level 1, x custom grid at level 0, y custom grid at level 0,
      format "'[' x ']'  ..  '[' y ']'").
Notation "(#)" := true (in custom grid at level 0).
Notation "(_)" := false (in custom grid at level 0).
Notation "( x )" := x (in custom grid, x constr at level 0).
Notation "[ x ]" := (Some x) (in custom grid, x constr at level 0).
Notation "[ ]" := None (in custom grid at level 0).

Example grid_example : grid nat 3 2 :=
  G{ (1) (2) (3) ; (4) (5) (6) }.

Example grid_example' : grid bool 3 2 :=
  G{ (#) (#) (#) ; (#) (_) (#) }.

Example grid_example'' : grid (option nat) 3 2 :=
  G{ [1] [2] [ ] ; [4] [ ] [6] }.

Print grid_example.
Print grid_example'.
Print grid_example''.
