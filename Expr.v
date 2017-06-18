Add LoadPath "/Users/YuryKravchenko/Documents/coq-supplementary/".
Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt'  : bop
| Ge  : bop
| Gt'  : bop
| Eq'  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : Z -> expr
| Var : id  -> expr
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt'  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt'  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq'  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.

Lemma zbool0 : zbool Z0.
Proof. apply Logic.or_intror. auto. Qed.

Lemma zbool1 : zbool 1%Z.
Proof. constructor. auto. Qed.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : Z), [| Nat n |] s => n
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always : 
    forall (n : Z) (s : state Z), [| Nat n |] s => n.
  Proof. intros. apply bs_Nat. Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof. intros. inversion H. inversion H5. simpl. assert (Z.mul za 2 = Z.add za za). omega. rewrite H9. apply bs_Add. auto. auto. Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt'  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt'  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq'  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof. intros. induction H. inversion H0. 
  - inversion H0. exists z. rewrite <- H1. apply H.
  - inversion H0. destruct H5. auto. auto.
  - inversion H0. destruct H5. auto. auto.
  - inversion H0. destruct H5. auto. auto.
  - inversion H0. destruct H5. auto. auto.
  - inversion H0. destruct H5. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H6. auto. auto.
  - inversion H0. destruct H7. auto. auto.
  - inversion H0. destruct H7. auto. auto. Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof. unfold not. intros. remember (defined_expression e s z id). apply e0 in H1. destruct H1. apply H0 in H1.
  - auto.
  - auto. Qed.
(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof. induction e.
  - intros. inversion H. inversion H0. congruence.
  - intros. inversion H. inversion H0. apply state_deterministic with s i. auto. auto.
  - intros. destruct b. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H3). reflexivity. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H3). reflexivity. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H3). reflexivity. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H3). reflexivity. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H3). reflexivity. 
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. auto. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. inversion_clear H0. rewrite (IHe1 s za za0 H1 H) in H3. rewrite (IHe2 s zb zb0 H2 H4) in H3. contradiction. auto.
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H5). auto. 
    + inversion_clear H. inversion_clear H0. rewrite (IHe1 s za za0 H1 H). rewrite (IHe2 s zb zb0 H2 H5). auto. Qed. 

(* Eq'uivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id) (z : Z), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof. induction e.
  - intros. inversion H0. apply bs_Nat.
  - intros. inversion H0. apply bs_Var. apply H.
    + auto.
    + apply v_Var.
    + auto.
  - intros. inversion_clear H0.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto. 
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
    + apply bs_Le_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Le_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Lt_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Lt_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Ge_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Ge_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Gt_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Gt_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Eq_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Eq_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Ne_T with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + apply bs_Ne_F with (za := za) (zb := zb).
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
      -- auto.
    + constructor.
      -- apply IHe1 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- apply IHe2 with (s1 := s1).
        ++ intros. apply H. auto. destruct b.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
          --- constructor. auto.
        ++ intros. auto.
      -- auto.
      -- auto. Qed.

(* Semantic equivalence *)
Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof. intros. remember (eq_intro e e). apply e0. intros. split. auto. auto. Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof. intros. destruct H. apply eq_intro. split. apply H. apply H. Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof. intros. destruct H. destruct H0. apply eq_intro. split.
  - intros. apply H0. apply H. auto.
  - intros. apply H. apply H0. auto. Qed.

(* Contexts *)
Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b e1 (plug C e)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof. intros. split.
  - intros. apply ceq_intro. intros. apply eq_intro. induction C.
    + simpl. destruct H. auto.
    + split.
      -- intros. inversion H0.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Le_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Le_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Lt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Lt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ge_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ge_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Gt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Gt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Eq_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Eq_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ne_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ne_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_And with (za := za) (zb := zb). auto. auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Or with (za := za) (zb := zb). auto. auto. auto. auto.
      -- intros. inversion H0.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H6. constructor. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Le_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Le_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Lt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Lt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ge_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ge_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Gt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Gt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Eq_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Eq_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ne_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Ne_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_And with (za := za) (zb := zb). auto. auto. auto. auto.
        ++ simpl. apply IHC in H4. apply bs_Or with (za := za) (zb := zb). auto. auto. auto. auto.
    + split.
      -- intros. inversion H0.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Le_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Le_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Lt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Lt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ge_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ge_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Gt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Gt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Eq_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Eq_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ne_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ne_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H5. apply bs_And with (za := za) (zb := zb). auto. auto. auto. auto.
        ++ simpl. apply IHC in H5. apply bs_Or with (za := za) (zb := zb). auto. auto. auto. auto.
      -- intros. inversion H0.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. constructor. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Le_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Le_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Lt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Lt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ge_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ge_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Gt_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Gt_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Eq_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Eq_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ne_T with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H7. apply bs_Ne_F with (za := za) (zb := zb). auto. auto. auto.
        ++ simpl. apply IHC in H5. apply bs_And with (za := za) (zb := zb). auto. auto. auto. auto.
        ++ simpl. apply IHC in H5. apply bs_Or with (za := za) (zb := zb). auto. auto. auto. auto.
  - intros. inversion H. apply (H0 Hole). Qed.

Fixpoint constant_simpl (e : expr) : expr := 
  match e with
  | Nat n => Nat n
  | Var i => Var i
  | Bop b e1 e2 => match constant_simpl e1, constant_simpl e2 with
                   | Nat n1, Nat n2 => match b with
                                        | Add => Nat (n1 + n2)
                                        | Sub => Nat (n1 - n2)
                                        | Mul => Nat (n1 * n2)
                                        | Div => Nat (Z.div n1 n2)
                                        | Mod => Nat (Z.modulo n1 n2)
                                        | Le  => match Z.compare n1 n2 with
                                                 |Lt => Nat 1
                                                 |Gt => Nat 0
                                                 |Eq => Nat 1
                                                  end
                                        | Lt'  => match Z.compare n1 n2 with
                                                 |Lt => Nat 1
                                                 |Gt => Nat 0
                                                 |Eq => Nat 0
                                                  end
                                        | Ge  => match Z.compare n1 n2 with
                                                 |Lt => Nat 0
                                                 |Gt => Nat 1
                                                 |Eq => Nat 1
                                                  end
                                        | Gt'  => match Z.compare n1 n2 with
                                                 |Lt => Nat 0
                                                 |Gt => Nat 1
                                                 |Eq => Nat 0
                                                  end
                                        | Eq'  => match Z.compare n1 n2 with
                                                 |Lt => Nat 0
                                                 |Gt => Nat 0
                                                 |Eq => Nat 1
                                                  end
                                        | Ne  => match Z.compare n1 n2 with
                                                 |Lt => Nat 1
                                                 |Gt => Nat 1
                                                 |Eq => Nat 0
                                                  end
                                        | And => match Z.compare n1 Z0 with
                                                 |Eq => match Z.compare n2 Z0 with
                                                        |Eq => Nat 0
                                                        |Lt => match Z.compare n2 1%Z with
                                                                |Eq => Nat 0
                                                                |Lt => Bop b (Nat n1) (Nat n2)
                                                                |Gt => Bop b (Nat n1) (Nat n2)
                                                                 end
                                                        |Gt => match Z.compare n2 1%Z with
                                                                |Eq => Nat 0
                                                                |Lt => Bop b (Nat n1) (Nat n2)
                                                                |Gt => Bop b (Nat n1) (Nat n2)
                                                                 end
                                                         end
                                                 |Lt => match Z.compare n1 1%Z with
                                                        |Eq => match Z.compare n2 Z0 with
                                                                |Eq => Nat 0
                                                                |Lt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                |Gt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                 end
                                                         |Lt => Bop b (Nat n1) (Nat n2) 
                                                         |Gt => Bop b (Nat n1) (Nat n2)
                                                          end
                                                 |Gt => match Z.compare n1 1%Z with
                                                        |Eq => match Z.compare n2 Z0 with
                                                                |Eq => Nat 0
                                                                |Lt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                |Gt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                 end
                                                         |Lt => Bop b (Nat n1) (Nat n2) 
                                                         |Gt => Bop b (Nat n1) (Nat n2)
                                                         end
                                                  end
                                        | Or  => match Z.compare n1 Z0 with
                                                 |Eq => match Z.compare n2 Z0 with
                                                        |Eq => Nat 0
                                                        |Lt => match Z.compare n2 1%Z with
                                                                |Eq => Nat 1
                                                                |Lt => Bop b (Nat n1) (Nat n2)
                                                                |Gt => Bop b (Nat n1) (Nat n2)
                                                                 end
                                                        |Gt => match Z.compare n2 1%Z with
                                                                |Eq => Nat 1
                                                                |Lt => Bop b (Nat n1) (Nat n2)
                                                                |Gt => Bop b (Nat n1) (Nat n2)
                                                                 end
                                                         end
                                                 |Lt => match Z.compare n1 1%Z with
                                                        |Eq => match Z.compare n2 Z0 with
                                                                |Eq => Nat 1
                                                                |Lt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                |Gt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                 end
                                                         |Lt => Bop b (Nat n1) (Nat n2) 
                                                         |Gt => Bop b (Nat n1) (Nat n2)
                                                          end
                                                 |Gt => match Z.compare n1 1%Z with
                                                        |Eq => match Z.compare n2 Z0 with
                                                                |Eq => Nat 1
                                                                |Lt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                |Gt => match Z.compare n2 1%Z with
                                                                        |Eq => Nat 1
                                                                        |Lt => Bop b (Nat n1) (Nat n2)
                                                                        |Gt => Bop b (Nat n1) (Nat n2)
                                                                         end
                                                                 end
                                                         |Lt => Bop b (Nat n1) (Nat n2) 
                                                         |Gt => Bop b (Nat n1) (Nat n2)
                                                         end
                                                  end
                                        end
                   | e1'   , e2'    => Bop b e1' e2' 
                   end
  end.

Lemma constant_simpl_eq: forall (e : expr), e ~~ constant_simpl e.
Proof. induction e.
  - simpl. constructor. intros. split. intros. auto. intros. auto.
  - simpl. constructor. intros. split. intros. auto. intros. auto.
  - constructor. split.
    + intros. inversion_clear IHe1. inversion_clear IHe2. inversion H.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. inversion H7. inversion H8. rewrite <- H15. rewrite <- H18. auto.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. inversion H7. inversion H8. rewrite <- H15. rewrite <- H18. auto.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. inversion H7. inversion H8. rewrite <- H15. rewrite <- H18. auto.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. inversion H7. inversion H8. rewrite <- H15. rewrite <- H18. auto.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. inversion H7. inversion H8. rewrite <- H15. rewrite <- H18. auto.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto.
        ++ remember (H0 za s). inversion i. apply H9 in H7. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i1. apply H11 in H8. constructor. auto. auto. 
          --- remember (H1 zb s). inversion i0. apply H11 in H8. constructor. auto. auto.
      -- simpl. remember (bs_Le_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. auto. remember (Z.compare_le_iff za zb). inversion i1. apply H8 in H9. rewrite cmp in H9. contradiction.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Le_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. inversion H9. rewrite cmp in H8. inversion H8. inversion H9. rewrite cmp in H8. inversion H8. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Lt_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. inversion H9. rewrite cmp in H8. inversion H8. auto. inversion H9. rewrite cmp in H8. inversion H8. 
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Lt_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. remember (Z.compare_lt_iff za zb). inversion i1. apply H5 in cmp. omega. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Ge_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. remember (Z.compare_lt_iff za zb). inversion i1. apply H5 in cmp. omega. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Ge_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. remember (Z.compare_eq_iff za zb). inversion i1. apply H5 in cmp. omega. auto. remember (Z.compare_lt_iff za zb). inversion i1. apply H8 in H9. rewrite cmp in H9. inversion H9.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Gt_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. remember (Z.compare_eq_iff za zb). inversion i1. apply H5 in cmp. omega. remember (Z.compare_lt_iff za zb). inversion i1. apply H5 in cmp. omega. auto. 
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Gt_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. auto. remember (Z.compare_le_iff za zb). inversion i1. apply H8 in H9. rewrite cmp in H9. contradiction.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Eq_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. remember (Z.compare_eq_iff za zb). inversion i1. apply H8 in H9. rewrite H9 in cmp. inversion cmp.  remember (Z.compare_eq_iff za zb). inversion i1. apply H8 in H9. rewrite H9 in cmp. inversion cmp.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Eq_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. remember (Z.compare_eq_iff za zb). inversion i1. apply H5 in cmp. rewrite cmp in H9. remember (neg_false (Z.eq zb zb)). apply i2 in H9. inversion H9. assert (Z.eq zb zb). constructor. apply H14 in H16. contradiction. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Ne_T) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. remember (Z.compare_eq_iff za zb). inversion i1. apply H5 in cmp. rewrite cmp in H9. remember (neg_false (Z.eq zb zb)). apply i2 in H9. inversion H9. assert (Z.eq zb zb). constructor. apply H14 in H16. contradiction. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. remember (bs_Ne_F) as x. destruct (constant_simpl e1) eqn:eq. 
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. inversion_clear H8. destruct (Z.compare za zb) eqn:cmp. auto. remember (Z.compare_eq_iff za zb). inversion i1. apply H8 in H9. rewrite H9 in cmp. inversion cmp.  remember (Z.compare_eq_iff za zb). inversion i1. apply H8 in H9. rewrite H9 in cmp. inversion cmp.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. inversion_clear H5. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. inversion_clear H8. apply x with (za := za) (zb := zb). auto. auto. auto. 
          --- remember (H1 zb s). inversion i2. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H10 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H12 in H8. apply x with (za := za) (zb := zb). auto. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion_clear i. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion_clear i0. apply H13 in H6. inversion_clear H5. inversion_clear H6. destruct (Z.compare za 0) eqn:r1.
              +++ destruct (Z.compare zb 0) eqn:r2.
                  ---- remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. simpl. auto.
                  ---- destruct (Z.compare zb 1) eqn:r3.
                      ++++ remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. simpl. auto.
                      ++++ constructor. auto. auto. auto. auto.
                      ++++ constructor. auto. auto. auto. auto.
                  ---- destruct (Z.compare zb 1) eqn:r3.
                      ++++ remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. simpl. auto.
                      ++++ constructor. auto. auto. auto. auto.
                      ++++ constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare za 1) eqn:r2.
                  ---- destruct (Z.compare zb 0) eqn:r3.
                      ++++ remember (Z.compare_eq_iff zb Z0). inversion i1. apply H5 in r3. rewrite r3. remember (Z.compare_eq_iff za 1%Z). inversion i2. apply H15 in r2. rewrite r2. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare za 1) eqn:r2.
                  ---- destruct (Z.compare zb 0) eqn:r3.
                      ++++ remember (Z.compare_eq_iff zb Z0). inversion i1. apply H5 in r3. rewrite r3. remember (Z.compare_eq_iff za 1%Z). inversion i2. apply H15 in r2. rewrite r2. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i2. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
      -- simpl. destruct (constant_simpl e1) eqn:eq.
        ++ remember (H0 za s). inversion_clear i. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion_clear i0. apply H13 in H6. inversion_clear H5. inversion_clear H6. destruct (Z.compare za 0) eqn:r1.
              +++ destruct (Z.compare zb 0) eqn:r2.
                  ---- remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. remember (Z.compare_eq_iff zb Z0). inversion i2. apply H15 in r2. rewrite r2. assert (Z.eq Z0 (zor Z0 Z0)). constructor. rewrite <- H17. auto.
                  ---- destruct (Z.compare zb 1) eqn:r3.
                      ++++ remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r3. rewrite r3. assert (Z.eq 1%Z (zor Z0 1%Z)). constructor. rewrite <- H17. auto.
                      ++++ constructor. auto. auto. auto. auto.
                      ++++ constructor. auto. auto. auto. auto.
                  ---- destruct (Z.compare zb 1) eqn:r3.
                      ++++ remember (Z.compare_eq_iff za Z0). inversion i1. apply H5 in r1. rewrite r1. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r3. rewrite r3. assert (Z.eq 1%Z (zor Z0 1%Z)). constructor. rewrite <- H17. auto.
                      ++++ constructor. auto. auto. auto. auto.
                      ++++ constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare za 1) eqn:r2.
                  ---- destruct (Z.compare zb 0) eqn:r3.
                      ++++ remember (Z.compare_eq_iff zb Z0). inversion i1. apply H5 in r3. rewrite r3. remember (Z.compare_eq_iff za 1%Z). inversion i2. apply H15 in r2. rewrite r2. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare za 1) eqn:r2.
                  ---- destruct (Z.compare zb 0) eqn:r3.
                      ++++ remember (Z.compare_eq_iff zb Z0). inversion i1. apply H5 in r3. rewrite r3. remember (Z.compare_eq_iff za 1%Z). inversion i2. apply H15 in r2. rewrite r2. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare zb 1) eqn:r4.
                          ----- remember (Z.compare_eq_iff za 1%Z). inversion i1. apply H5 in r2. rewrite r2. remember (Z.compare_eq_iff zb 1%Z). inversion i2. apply H15 in r4. rewrite r4. simpl. auto.
                          ----- constructor. auto. auto. auto. auto.
                          ----- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
                  ---- constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
        ++ remember (H0 za s). inversion i0. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i2. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
        ++ remember (H0 za s). inversion i. apply H11 in H5. destruct (constant_simpl e2) eqn:eq1.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i1. apply H13 in H6. constructor. auto. auto. auto. auto.
          --- remember (H1 zb s). inversion i0. apply H13 in H6. constructor. auto. auto. auto. auto.
    + simpl. intros. destruct b.
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 z s). auto. apply (H1 z0 s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 z s). auto. apply (H1 z0 s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 z s). auto. apply (H1 z0 s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 z s). auto. apply (H1 z0 s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 z s). auto. apply (H1 z0 s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. 
      -- remember bs_Le_T as x. remember bs_Le_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. remember (Z.compare_lt_iff z z0). inversion i. apply H5 in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- remember bs_Lt_T as x. remember bs_Lt_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. auto.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply neg_false. rewrite eq2. split. intros. inversion H5. intros. contradiction.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- remember bs_Ge_T as x. remember bs_Ge_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. auto.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply neg_false. rewrite eq2. split. intros. inversion H5. intros. contradiction.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- remember bs_Gt_T as x. remember bs_Gt_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. remember (Z.compare_lt_iff z z0). inversion i. apply H5 in eq2. omega.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- remember bs_Eq_T as x. remember bs_Eq_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. rewrite eq2. apply (Logic.eq_refl z0).
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (neg_false). split. intros. remember (Z.compare_lt_iff z z0). inversion i. apply H6 in eq2. rewrite H5 in eq2. omega. intros. contradiction.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (neg_false). split. intros. remember (Z.compare_eq_iff z z0). inversion i. apply H7 in H5. rewrite H5 in eq2. inversion eq2. intros. contradiction.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- remember bs_Ne_T as x. remember bs_Ne_F as y. destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- destruct (Z.compare z z0) eqn:eq2.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply y with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (Z.compare_eq_iff z z0) in eq2. auto.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (neg_false). split. intros. remember (Z.compare_lt_iff z z0). inversion i. apply H6 in eq2. rewrite H5 in eq2. omega. intros. contradiction.
              +++ inversion_clear IHe1. inversion_clear IHe2. inversion H. apply x with (za := z) (zb := z0). auto. apply (H0 z s). auto. apply (H1 z0 s). auto. apply (neg_false). split. intros. remember (Z.compare_eq_iff z z0). inversion i. apply H7 in H5. rewrite H5 in eq2. inversion eq2. intros. contradiction.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
              +++ apply y with (za := za) (zb := zb). auto. apply (H0 za s). auto. apply (H1 zb s). auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H.
              +++ apply x with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
              +++ apply y with (za := za) (zb := zb). apply (H0 za s). auto. apply (H1 zb s). auto. auto.
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1. 
          --- inversion_clear IHe1. inversion_clear IHe2. destruct (Z.compare z Z0) eqn:r1.
              +++ remember (Z.compare_eq_iff z Z0). inversion i. apply H2 in r1. destruct (Z.compare z0 Z0) eqn:r2.
                  ---- inversion H. assert (Z.eq Z0 (Z0 * Z0)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r2. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r2. auto. apply zbool0. apply zbool0.
                  ---- destruct (Z.compare z0 1%Z) eqn:r3.
                      ++++ inversion H. assert (Z.eq Z0 (Z0 * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r3. auto. apply zbool0. apply zbool1.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- destruct (Z.compare z0 1%Z) eqn:r3.
                      ++++ inversion H. assert (Z.eq Z0 (Z0 * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r3. auto. apply zbool0. apply zbool1.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare z 1%Z) eqn:r2.
                  ---- remember (Z.compare_eq_iff z 1%Z). inversion i. apply H2 in r2. destruct (Z.compare z0 Z0) eqn:r3.
                      ++++ inversion H. assert (Z.eq Z0 (1%Z * Z0)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r3. auto. apply zbool1. apply zbool0.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (1%Z * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (1%Z * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare z 1%Z) eqn:r2.
                  ---- remember (Z.compare_eq_iff z 1%Z). inversion i. apply H2 in r2. destruct (Z.compare z0 Z0) eqn:r3.
                      ++++ inversion H. assert (Z.eq Z0 (1%Z * Z0)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r3. auto. apply zbool1. apply zbool0.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (1%Z * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (1%Z * 1%Z)). simpl. apply Logic.eq_refl. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
      -- destruct (constant_simpl e1) eqn:eq.
        ++ destruct (constant_simpl e2) eqn:eq1. 
          --- inversion_clear IHe1. inversion_clear IHe2. destruct (Z.compare z Z0) eqn:r1.
              +++ remember (Z.compare_eq_iff z Z0). inversion i. apply H2 in r1. destruct (Z.compare z0 Z0) eqn:r2.
                  ---- inversion H. assert (Z.eq Z0 (zor Z0 Z0)). constructor. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r2. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r2. auto. apply zbool0. apply zbool0.
                  ---- destruct (Z.compare z0 1%Z) eqn:r3.
                      ++++ inversion H. assert (Z.eq 1%Z (zor Z0 1%Z)). constructor. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r3. auto. apply zbool0. apply zbool1.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- destruct (Z.compare z0 1%Z) eqn:r3.
                      ++++ inversion H. assert (Z.eq 1%Z (zor Z0 1%Z)). constructor. rewrite H7. remember (H0 Z0 s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r1. auto. apply H11. rewrite r3. auto. apply zbool0. apply zbool1.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
               +++ destruct (Z.compare z 1%Z) eqn:r2.
                  ---- remember (Z.compare_eq_iff z 1%Z). inversion i. apply H2 in r2. destruct (Z.compare z0 Z0) eqn:r3.
                      ++++ inversion H. assert (Z.eq 1%Z (zor 1%Z Z0)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r3. auto. apply zbool1. apply zbool0.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (zor 1%Z 1%Z)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1. 
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (zor 1%Z 1%Z)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
              +++ destruct (Z.compare z 1%Z) eqn:r2.
                  ---- remember (Z.compare_eq_iff z 1%Z). inversion i. apply H2 in r2. destruct (Z.compare z0 Z0) eqn:r3.
                      ++++ inversion H. assert (Z.eq 1%Z (zor 1%Z Z0)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 Z0 s). inversion i1. remember (Z.compare_eq_iff z0 Z0). inversion i2. apply H12 in r3. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r3. auto. apply zbool1. apply zbool0.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (zor 1%Z 1%Z)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                      ++++ destruct (Z.compare z0 1%Z) eqn:r4.
                          ----- inversion H. assert (Z.eq 1%Z (zor 1%Z 1%Z)). constructor. rewrite H7. remember (H0 1%Z s). inversion i0. remember (H1 1%Z s). inversion i1. remember (Z.compare_eq_iff z0 1%Z). inversion i2. apply H12 in r4. constructor. apply H9. rewrite r2. auto. apply H11. rewrite r4. auto. apply zbool1. apply zbool1.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                          ----- inversion H. remember (H0 za s). inversion i0. apply H13 in H6. remember (H1 zb s). inversion i1. apply H15 in H7. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
                  ---- inversion H. remember (H0 za s). inversion i. apply H11 in H4. remember (H1 zb s). inversion i0. apply H13 in H5. constructor. auto. auto. auto. auto.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
        ++ destruct (constant_simpl e2) eqn:eq1.
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. 
          --- inversion_clear IHe1. inversion_clear IHe2. inversion H. constructor. apply (H0 za s). auto. apply (H1 zb s). auto. auto. auto. Qed.