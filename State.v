(** Based on Benjamin Pierce's "Software Foundations" *)
Add LoadPath "/Users/YuryKravchenko/Documents/coq-supplementary/".
Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof. intros s id n m. induction s.
  - intros e1. inversion e1.
  - intros e2. inversion e2.
    + intros e3. inversion e3.
      -- reflexivity.
      -- contradiction.
    + intros e3. inversion e3.
      -- symmetry in H5. contradiction.
      -- auto. Qed.

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof. intros. unfold update. apply st_binds_hd. Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof. intros. unfold update. assert(x1 <> x2). auto. apply (st_binds_tl st x1 m x2 n H1 H0). Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof. intros. inversion H.
    - apply update_eq.
    - apply update_neq. 
      + auto.
      + inversion H6.
        -- rewrite H7 in H5. contradiction. 
        -- auto. Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof. intros. destruct (eq_id_dec x1 x2).
    - rewrite e. rewrite e in H. remember (state_deterministic st x2 n1 m H H0). rewrite e0. apply update_eq.
    - apply update_neq. auto. auto. Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. intros. destruct (eq_id_dec x1 x3).
    - destruct (eq_id_dec x2 x3).
      + rewrite <- e0 in e. rewrite e in H. contradiction.
      + rewrite e in H0. remember (update_eq ((st) [x2 <- n1]) x3 n2). remember (state_deterministic ((st) [x2 <- n1][x3 <- n2]) x3 m n2 H0 s). rewrite e0. apply update_neq. 
        -- auto.
        -- rewrite e. apply update_eq.
    - destruct (eq_id_dec x2 x3).
      + rewrite e in H0. remember (update_eq st x3 n1).  apply (update_neq ((st)[x3 <- n1]) x1 x3 n2 n1) in n.
        -- remember (state_deterministic (((st) [x3 <- n1]) [x1 <- n2]) x3 n1 m n H0). rewrite e. rewrite e0. apply update_eq.
        -- auto.
      + apply update_neq. auto. apply update_neq. auto. inversion H0. contradiction. inversion H7. contradiction. auto. Qed.
End S.