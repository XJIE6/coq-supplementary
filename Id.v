(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof. intros id1. induction id1. induction n.
  - intros id2. induction id2. induction n.
    + left. right. auto.
    + left. left. constructor. omega.
  - intros id2. induction id2. induction n0.
    + right. constructor. omega.
    + destruct (IHn (Id n0)).
      -- destruct s.
        ++ left. left. constructor. inversion l. omega.
        ++ left. right. inversion e.  constructor.
      -- right. constructor. inversion l. omega. Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. intros id1. induction id1. induction n.
  - intros id2. induction id2. induction n.
    + left. right. auto.
    + right. constructor. omega.
  - intros id2. induction id2. induction n0.
    + left. left. constructor. omega.
    + destruct (IHn (Id n0)).
      -- destruct s.
        ++ left. left. constructor. inversion g. omega.
        ++ left. right. inversion e.  constructor.
      -- right. constructor. inversion g. omega. Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. intros id1. induction id1. induction n.
  - intros id2. induction id2. induction n.
    + left. constructor. omega.
    + left. constructor. omega.
  - intros id2. induction id2. induction n0.
    + right. constructor. omega.
    + destruct (IHn (Id n0)).
      -- left. constructor. inversion l. omega.
      -- right. constructor. inversion g. omega. Qed.


Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof. intros n. induction n.
  - intros m. induction m.
    + left. auto.
    + right. omega.
  - intros m. induction m.
    + right. omega.
    + destruct (IHn m).
      -- left. omega.
      -- right. omega. Qed. 

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. intros. destruct id1. destruct id2. remember (eq_dec n n0). inversion s.
  - left. rewrite H. constructor.
  - right. intros eq. inversion eq. omega. Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof. intros. destruct (eq_id_dec x x). auto. contradiction. Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof. intros. destruct (eq_id_dec x y). contradiction. auto. Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof. intros. inversion H. rewrite <- H2 in H0. rewrite <- H3 in H0. inversion H0. omega. Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof. intros. inversion H. rewrite <- H2 in H0. rewrite <- H3 in H0. inversion H0. omega. Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof. intros. remember (gt_eq_gt_id_dec id2 id1). inversion s.
  - inversion H0.
    + right. auto.
    + left. auto. 
  - remember (le_gt_id_false id2 id1 H H0). inversion f. Qed.


Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof. intros. remember (gt_eq_gt_id_dec id1 id2). inversion s.
  - inversion H0.
    + left. auto.
    + rewrite H1 in H. contradiction.
  - right. auto. Qed.

Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof. intros. rewrite H in H0. inversion H0. omega. Qed.


