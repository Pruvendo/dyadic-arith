From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.
Require Import Basic.

Local Open Scope nat_scope.

Inductive binary_lt: bilist -> bilist -> Prop :=
  | binary_lt_cons: forall x y b, length x <= length y -> binary_lt x (b::y)
  | binary_lt_E: forall x y, (length x = length y) -> binary_lt (E1::x) (E2::y)
  | binary_lt_cons2: forall x y b, binary_lt x y -> binary_lt (b::x) (b::y).

Example test_lt1: binary_lt [E1; E2; E1] [E2; E1; E1].
Proof.
  apply binary_lt_E. auto.
Qed.

Example test_lt2: binary_lt [E1; E2; E1] [E1; E2; E2; E2].
Proof.
  apply binary_lt_cons. auto.
Qed.

Example test_lt3: binary_lt [E1; E1] [E1; E2].
Proof.
  apply binary_lt_cons2. apply binary_lt_E. auto.
Qed.


Lemma lt_incr1: forall b, binary_lt b (incr1 b).
Proof.
  induction b using list_ind_length.
  simpl.
  constructor 1.
  auto.
  destruct b.
  simpl. constructor. auto.
  destruct b; simpl; remember (length (incr1 b0) =? length b0) as q; 
  destruct q. 
  apply binary_lt_cons2.
  apply H. auto.
  apply binary_lt_E.
  apply eq_add_S.
  rewrite tl_S.
  apply length_le_S.
  symmetry in Heqq.
  apply  length_neq_incr.
  assumption.
  constructor 3.
  apply H.
  auto.
  constructor 1.
  simpl.
  symmetry in Heqq.
  apply length_eq_incr_S in Heqq.
  rewrite Heqq.
  auto.
Qed.

Lemma lt_less_length: forall a b,
  length a < length b -> binary_lt a b.
Proof.
  intros.
  destruct b.
  inversion H.
  destruct b.
  constructor.
  simpl in H.
  lia.
  constructor.
  simpl in H.
  lia.
Qed.

Lemma binary_lt_leq: forall a b,
  binary_lt a b -> length a <= length b.
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length.
  intros.
  inversion H.
  destruct b.
  simpl.
  intros.
  inversion H0.
  intros.
  simpl.
  inversion H0.
  lia.
  simpl. lia.
  simpl.
  assert (length x <= length a).
  rewrite <- H2.
  simpl.
  auto.
  rewrite <- PeanoNat.Nat.succ_le_mono.
  eapply H.
  auto.
  assumption.
Qed.


Lemma binary_lt_trans: forall a b c, 
binary_lt a b -> 
binary_lt b c -> 
binary_lt a c.
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction c using list_ind_length;
  intros.
  inversion H0.
  destruct c.
  inversion H0.
  destruct a.
  constructor .
  simpl.
   lia.
  destruct b.
  inversion H1.
  destruct b; destruct b1; destruct b0.
  -
  inversion H0.
  inversion H1.
  apply binary_lt_cons.
  simpl in *.
  lia.
  constructor.
  apply binary_lt_leq in H0.
  apply binary_lt_leq in H7.
  simpl in *.
  lia.
  constructor 3.
  apply H with (b := b2).
  
  apply binary_lt_leq in H0.
  apply binary_lt_leq in H1.
  simpl in *.
  lia.
  assumption.
  inversion H1.
  simpl in H8.
  apply lt_less_length.
  lia.
  assumption.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  apply binary_lt_leq in H7.
  constructor.
  simpl in *. lia.
  inversion H1.
  apply binary_lt_cons.
  simpl in *. lia.
  apply binary_lt_leq in H6.
  assert (length a = length b2 \/ length a < length b2).
  lia.
  inversion H9.
  constructor 2.
  lia.
  constructor.
  simpl; lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *. lia.
  inversion H1.
  apply binary_lt_leq in H3.
  constructor.
  simpl in *.
  lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  constructor.
  simpl in *.
  lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *. lia.
  inversion H1.
  constructor.
  simpl in *. lia.
  constructor.
  simpl in *.
  lia.
  inversion H1.
  constructor.
  simpl in *.
  apply binary_lt_leq in H3. lia.
  assert (length c = length b2 \/ length b2 < length c).
  apply binary_lt_leq in H3. lia.
  inversion H9.
  constructor 2.
  lia.
  constructor.
  simpl.
  lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  apply binary_lt_leq in H7.
  assert (length a = length b2 \/ length a < length b2).
  lia.
  inversion H10.
  constructor.
  simpl in *.
  lia.
  constructor.
  simpl in *.
  lia.
  -
  inversion H0.
  inversion H1.
  constructor.
  simpl in *.
  lia.
  apply binary_lt_leq in H7.
  constructor.
  simpl in *.
  lia.
  inversion H1.
  apply binary_lt_leq in H3.
  constructor.
  simpl in *. lia.
  constructor 3.
  apply H with (b := b2).
  simpl; auto.
  assumption.
  assumption.
Qed.


Lemma lt_decr1: forall b, 
  0 < length b ->
  binary_lt (decr1 b) b.
Proof.
  intros.
  rewrite <- incr1_decr1.
  apply lt_incr1.
  assumption.
Qed.


Lemma bilist_lt_length: forall x y, binary_lt x y -> length x <= length y.
Proof.
  intros.
  generalize dependent x.
  induction y; intros.
  inversion H.
  inversion H.
  simpl. lia.
  simpl. lia.
  simpl. apply IHy in H2. lia.
Qed.


Example iter_relation1: iter_relation binary_lt 3 [] [E1; E2].
Proof.
  apply iter_relationS with (y':=[E1;E1]).
  constructor 3. constructor 2. auto. 
  apply iter_relationS with (y':=[E2]).
  constructor 1. auto.
  apply iter_relationS with (y':=[E1]).
  constructor 2. auto.
  apply iter_relation0.
  constructor. auto.
Qed.  

Lemma binary_lt_length: forall a b, 
binary_lt a b -> length a <= length b.
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length; intros.
  inversion H.
  destruct b.
  inversion H0.
  inversion H0.
  -
  simpl. lia.
  - 
  simpl. lia.
  -
  simpl.
  assert (length x <= length b0).
  apply H. simpl. lia.
  auto.
  lia.
Qed.


Lemma allE2_noless: forall a b, length a = length b -> 
                  Forall (eq E2) b ->
                  Forall (eq E2) a \/ binary_lt a b.
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length; intros.
  left.
  destruct a.
  auto.
  simpl in H. lia.
  destruct b.
  left.
  destruct a. auto.
  simpl in H1. lia.
  destruct a.
  left. auto.
  assert (Forall (eq E2) a \/ binary_lt a b0).
  apply H.
  simpl. lia.
  inversion H0. auto.
  simpl in H1. auto.
  inversion_clear H2.
  destruct b1.
  right.
  inversion_clear H0.
  rewrite <- H2.
  apply binary_lt_E. simpl in H1. auto.
  left. constructor. auto. auto.
  inversion_clear H0.
  rewrite <- H2.
  right.
  destruct b1.
  apply binary_lt_trans with (b:=E2::a).
  apply binary_lt_E. auto.
  apply binary_lt_cons2. auto.
  apply binary_lt_cons2. auto.
Qed.

Lemma binary_lt_decr1: forall a b, 
binary_lt a b -> a = decr1 b \/ binary_lt a (decr1 b).
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length; intros.
  inversion H.
  destruct b.
  inversion H0.
  destruct b. 
  - (* E1 *)
  destruct a.
  destruct b0.
  left. auto.
  right. simpl.
  destruct b. destruct b0.
  simpl. constructor. simpl. auto.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0)).
  destruct (length (E1 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct (length (E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct b0.
  simpl. constructor. simpl. lia.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0)).
  destruct (length (E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct (length (E1 :: E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct b.
  + (*E1*)
  inversion H0.
  *
  simpl.
  destruct b0.
  simpl in H3. lia.
  remember ((b0 :: b1)) as b'.
  remember (length (decr1 b') =? length b' ).
  destruct b2.
  **
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H. simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3.
  apply binary_lt_cons. simpl. lia.
  inversion_clear H5.
  left. congruence.
  right.
  apply binary_lt_cons2. auto.
  **
  right.
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H. simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3.
  apply binary_lt_cons. simpl. lia.
  inversion_clear H5.
  rewrite <- H6.
  apply binary_lt_E. auto.
  apply binary_lt_trans with (b:=E2::a).
  apply binary_lt_E. auto.
  apply binary_lt_cons2. auto.
  *
  assert (a = decr1 b0 \/ binary_lt a (decr1 b0)).
  apply H. simpl. lia.
  auto.
  simpl.
  destruct b0.
  inversion H2.
  remember (b0::b1) as b'.
  remember (length (decr1 b') =? length b').
  destruct b2.
  **
  inversion_clear H5.
  left. congruence.
  right.
  apply binary_lt_cons2. auto.
  **
  inversion_clear H5.
  right. rewrite <- H6.
  apply binary_lt_E. auto.
  right.
  apply binary_lt_trans with (b:=E2::a).
  apply binary_lt_E. auto.
  apply binary_lt_cons2. auto.
  + (*E2*)
  inversion H0.
  simpl.
  destruct b0. simpl in H3. lia.
  remember (b0 :: b1) as b'.
  remember (length (decr1 b') =? length b').
  destruct b2.
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H.
  simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3.
  apply binary_lt_cons. lia.
  **
  right.
  inversion_clear H5.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  simpl in H3.
  rewrite <- Heqb2 in H3.
  rewrite <- H6 in H3. lia.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  simpl in H3.
  rewrite <- Heqb2 in H3.
  apply binary_lt_length in H6.
  apply binary_lt_cons. simpl. lia.
  **
  simpl in H3.
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H.
  simpl. lia.
  destruct b'. simpl in H3.
  lia.
  apply binary_lt_cons. simpl in H3. lia.
  inversion_clear H5.
  left. congruence.
  right.
  apply binary_lt_cons2. auto.
  - (* E2 *)
  destruct a.
  destruct b0.
  right. simpl. constructor. simpl. lia.
  right. simpl.
  destruct b. destruct b0.
  simpl. constructor. simpl. auto.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0)).
  destruct (length (E1 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct (length (E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct b0.
  simpl. constructor. simpl. lia.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0)).
  destruct (length (E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct (length (E1 :: E2 :: decr1 (b :: b0)) =? S (length (b :: b0))).
  constructor. simpl. lia.
  constructor. simpl. lia.
  destruct b.
  + (*E1*)
  inversion H0.
  *
  simpl.
  destruct b0.
  simpl in H3. lia.
  remember ((b0 :: b1)) as b'.
  remember (length (decr1 b') =? length b' ).
  destruct b2.
  **
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H. simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3.
  apply binary_lt_cons. simpl. lia.
  inversion_clear H5.
  right.
  rewrite <- H6.
  apply binary_lt_E. auto.
  right.
  apply binary_lt_trans with (b:=E2::a).
  apply binary_lt_E. auto.
  apply binary_lt_cons2. auto.
  **
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H. simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3.
  apply binary_lt_cons. simpl. lia.
  inversion_clear H5.
  right.
  rewrite <- H6.
  apply binary_lt_cons. simpl. lia.
  right.
  apply binary_lt_length in H6.
  apply binary_lt_cons. simpl. lia.
  *
  simpl.
  destruct b0.
  destruct a. left. auto.
  simpl in H3. lia.
  remember ((b :: b0)) as b'.
  remember (length (decr1 b') =? length b' ).
  destruct b1.
  right.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  apply binary_lt_E. congruence.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  remember (H (E2::decr1 b')).
  clear Heqo.
  assert (forall a,binary_lt a (E2 :: decr1 b') -> a = decr1 (E2 :: decr1 b') \/ binary_lt a (decr1 (E2 :: decr1 b'))).
  apply o.
  simpl.
  enough (length (decr1 b') < length b').
  lia.
  rewrite <- incr1_decr1 with (b:=b') at 2.
  enough (length (decr1 b') <= length (incr1 (decr1 b'))).
  enough (length (decr1 b') <> length (incr1 (decr1 b'))).
  lia.
  rewrite incr1_decr1. auto.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_length.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  clear o.
  enough (Forall (eq E2) (decr1 b')).
  remember H3. clear Heqe.
  replace (length b') with (length (E2::decr1 b')) in e.  
  apply allE2_noless in e.
  inversion_clear e.
  left.
  apply Forall_eq_length  with (l':=E2 :: decr1 b') in H6.
  congruence.
  rewrite H3.
  simpl.
  rewrite <- incr1_decr1 with (b:=b') at 1.
  symmetry.
  apply incr1_length_plus.
  enough (length (decr1 b') <= length (incr1 (decr1 b'))).
  enough (length (decr1 b') <> length (incr1 (decr1 b'))).
  lia.
  rewrite incr1_decr1. auto.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_length.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  constructor. auto. auto.
  right.
  apply binary_lt_cons2. auto.
  constructor.
  auto.
  apply incr1_cons2.
  enough (length (decr1 b') <= length (incr1 (decr1 b'))).
  enough (length (decr1 b') <> length (incr1 (decr1 b'))).
  lia.
  rewrite incr1_decr1. auto.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_length.
  simpl. 
  rewrite <- incr1_decr1 with (b:=b') at 2.
  apply incr1_length_plus.
  enough (length (decr1 b') <= length (incr1 (decr1 b'))).
  enough (length (decr1 b') <> length (incr1 (decr1 b'))).
  lia.
  rewrite incr1_decr1. auto.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_length.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_cons2.
  enough (length (decr1 b') <= length (incr1 (decr1 b'))).
  enough (length (decr1 b') <> length (incr1 (decr1 b'))).
  lia.
  rewrite incr1_decr1. auto.
  destruct b'. simpl in Heqb1. lia.
  simpl. lia.
  apply incr1_length.
  +
  inversion H0.
  *
  simpl.
  destruct b0.
  destruct a. left. auto.
  simpl in H3. lia.
  simpl in H3. lia.
  remember ((b0 :: b1)) as b'.
  remember (length (decr1 b') =? length b' ).
  destruct b2.
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H.
  simpl. lia.
  destruct b'.
  simpl in H3. lia.
  apply binary_lt_cons. simpl in H3. lia.
  inversion_clear H5.
  left.
  rewrite <- H6.
  auto. right.
  apply binary_lt_cons2. auto.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H.
  simpl. lia.
  destruct b'.
  simpl in H3. lia.
  simpl in H3. apply binary_lt_cons. lia.
  inversion_clear H5.
  right. rewrite <- H6.
  apply binary_lt_cons. lia.
  right.
  apply binary_lt_length in H6.
  apply binary_lt_cons. simpl. lia.
  *
  simpl.
  destruct b0.
  inversion H2.
  remember (b0::b1) as b'.
  remember (length (decr1 b') =? length b').
  assert (a = decr1 b' \/ binary_lt a (decr1 b')).
  apply H.
  simpl. lia.
  auto.
  destruct b2.
  **
  inversion_clear H5.
  left. congruence.
  right. apply binary_lt_cons2. auto.
  **
  inversion_clear H5.
  right.
  rewrite <- H6.
  apply binary_lt_cons. simpl. lia. 
  right.
  apply binary_lt_cons. 
  apply binary_lt_length in H6.
  simpl. lia. 
Qed.


Lemma decr1_lt: forall b, 0 < length b -> binary_lt (decr1 b) b.
Proof.
  intros.
  rewrite <- incr1_decr1.
  apply lt_incr1.
  auto.
Qed.

Lemma binary_lt_decr1_iter: forall a b n, 
iter_relation binary_lt n a b -> 
a = iter (S n) decr1 b \/ binary_lt a (iter (S n) decr1 b).
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction n; intros.
  inversion H.
  simpl.
  apply binary_lt_decr1. auto.
  apply iter_relation_S2 in H.
  inversion_clear  H.
  inversion_clear H0.
  apply IHn in H.
  inversion_clear H.
  rewrite iterS.
  rewrite <- H0.
  apply binary_lt_decr1. auto.
  rewrite iterS.
  remember ((iter (S n) decr1 b)) as b'.
  apply binary_lt_decr1 in H1.
  apply binary_lt_decr1 in H0.
  inversion_clear H1; inversion_clear H0.
  -
  destruct x.
  left.
  simpl in H. congruence.
  right. rewrite <- H1.
  rewrite H. 
  apply decr1_lt. simpl. lia.
  -
  rewrite H.
  destruct x.
  destruct b'.
  inversion H1.
  right. apply H1.
  right.
  apply binary_lt_trans with (b:=b0::x).
  apply decr1_lt. simpl. lia.
  auto.
  -
  rewrite H1 in H.
  destruct (decr1 b').
  inversion H.
  right. apply binary_lt_trans with (b:=decr1(b0::l)).
  auto.
  apply decr1_lt. simpl. lia.
  -
  right.
  destruct x.
  inversion H.
  apply binary_lt_trans with (b:=decr1 (b0 :: x)).
  auto.
  apply binary_lt_trans with (b:=b0 :: x).
  apply decr1_lt. simpl. lia.
  auto.
Qed.


Lemma binary_lt_with_decr1: forall a b,
binary_lt [E1] b ->
binary_lt a b -> 
binary_lt (decr1 a) (decr1 b) .
Proof.
  intros.
  remember H0. clear Heqb0.
  apply binary_lt_decr1 in b0.
  inversion_clear b0.
  rewrite H1.
  apply decr1_lt.
  destruct b. inversion H0.
  simpl. 
  destruct b; destruct b0.
  inversion H. simpl in H4. lia.
  inversion H3.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0));simpl; lia.
  simpl. lia.
  destruct (length (decr1 (b :: b0)) =? length (b :: b0));simpl; lia.
  destruct a.
  simpl. auto.
  apply binary_lt_trans with (b:=b0::a).
  apply decr1_lt. simpl. lia.
  auto.
Qed.

Lemma iter_relation_binary_lt_lt: forall n (x y: bilist),
iter_relation binary_lt n x y -> binary_lt x y.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction n; intros.
  inversion H.
  auto.
  apply iter_relation_S2 in H.
  inversion_clear H.
  inversion H0.
  apply IHn in H.
  apply binary_lt_trans  with (b:=x0) .
  auto. auto. 
Qed.


Lemma bilist_lt_reducible_prop: bilist_reducible_prop binary_lt.
Proof.
  unfold bilist_reducible_prop.
  intros.
  induction y using list_ind_length.
  exists 0. intros.
  inversion H.
  inversion H0.
  destruct y.
  exists 0. intros.
  inversion H0.
  inversion H1.
  destruct y.
  all: cycle 1.
  remember (b0::y) as y'.
  enough (exists n, forall x, iter_relation binary_lt n x (b :: y') -> length x <= length y' /\ binary_lt x y').
  destruct H0.
  assert (exists n : nat, forall x : bilist, iter_relation binary_lt n x y' -> False).
  apply H. simpl. auto.
  inversion_clear H1.
  exists (x0+x).
  intros.
  (*   y < .. x .. < (b::y)  *)
  (*   x1 < .. x + x0 .. < (b::y)  *)

  apply iter_relation_trans with (y0:=y') in H1.
  apply H2 with (x:=x1).
  auto.
  intros. apply H0. auto.

  remember (H y').
  clear Heqe.
  assert (exists n : nat, forall x : bilist, iter_relation binary_lt n x y' -> False).
  apply e. simpl. lia.
  clear e. destruct H0.
  
  remember (remove_head1 b y'). clear Heqe.
  inversion_clear e.

  exists (x + x0).
  intros.
  remember H2. clear Heqi.
  apply iter_relation_trans with (y0:=y') in i.
  enough (binary_lt x1 y').
  split.
  apply binary_lt_length in H3. auto.
  auto.
  apply iter_relation_binary_lt_lt with (n:=x).
  auto.

  intros.
  apply binary_lt_decr1_iter in H3.
  inversion_clear H3.
  rewrite iterS in H4.
  rewrite H1 in H4.
  rewrite H4.
  apply decr1_lt.
  rewrite Heqy'. simpl. lia.
  rewrite iterS in H4.
  rewrite H1 in H4.
  apply binary_lt_trans with (b:=decr1 y').
  auto.
  apply decr1_lt.
  rewrite Heqy'. simpl. lia.
  destruct b.
  exists 1.
  intros.
  inversion H0.
  inversion H3.
  inversion H2.
  destruct y'. inversion H6.
  simpl in H11. lia. inversion H11.
  exists 2.
  intros.
  inversion_clear  H0.
  inversion_clear H2.
  inversion_clear H3.
  inversion H1.
  destruct y'. inversion H0.
  simpl in H5. lia. 
  destruct x0. subst y'.
  inversion H0.
  destruct y'0.
  inversion H2.
  simpl in H7. lia.
  inversion H7.
  simpl in H5. lia.
  inversion H5.
Qed.


Lemma bilist_lt_ind: forall (P: bilist -> Prop), 
P [] -> (forall b, (forall b', binary_lt b' b -> P b') -> P b) -> forall b, P b .
Proof.
  intros.
  induction b using list_ind_length.
  auto.
  apply H0.
  intros.
  remember bilist_lt_reducible_prop as e. clear Heqe.
  unfold bilist_reducible_prop in e.
  remember (e b). clear Heqe0.
  inversion_clear e0.
  generalize dependent b'.
  generalize dependent b.
  induction x; intros.
  exfalso.
  apply H3 with (x:=b').
  constructor. auto.
  apply H0. intros.
  apply IHx with (b:=b'). intros.
  -
  apply H1.
  enough (length b' <= length b).
  lia.
  apply bilist_lt_length. auto.
  -
  intros.
  apply H3 with (x0:=x0).
  apply iter_relationS with (y':=b'). auto. auto.
  -
  auto.
Qed.


Lemma bilist_incr_ind: forall (P: bilist -> Prop), 
P [] -> (forall b, P b -> P (incr1 b)) -> forall b, P b .
Proof.
  intros.
  induction b using bilist_lt_ind.
  auto.
  destruct b.
  auto.
  enough (exists b', incr1 b' = b :: b0).
  inversion_clear H2. rewrite <- H3.
  apply H0. apply H1.
  rewrite <- H3.
  apply lt_incr1.
  exists (decr1 (b :: b0)).
  apply incr1_decr1.
  simpl. lia.
Qed.


Lemma incr1_lt_hom: forall b b',
binary_lt b b' ->
binary_lt (incr1 b) (incr1 b').
Proof.
  intros.
  generalize dependent b.
  induction b' using bilist_lt_ind; intros.
  inversion H.
  enough (iter_relation binary_lt 0 b b').
  apply binary_lt_decr1_iter in H1.
  simpl in H1. inversion H1.
  -
  rewrite H2.
  rewrite incr1_decr1.
  apply lt_incr1.
  destruct b'. inversion H0.
  simpl. lia.
  -
  assert (binary_lt (incr1 b) (incr1 (decr1 b'))).
  apply H; auto.

  apply decr1_lt.
  destruct b'.
  inversion H0.
  simpl. lia.
  replace (incr1 (decr1 b')) with b' in H3.
  apply binary_lt_trans with (b:=b'); auto.
  apply lt_incr1.
  rewrite incr1_decr1.
  auto.
  destruct b'.
  inversion H0.
  simpl. lia.
  -
  constructor. auto.  
Qed.


Lemma incr1_length_hom: forall b b',
binary_lt b b' ->
length (incr1 b) <= length (incr1 b').
Proof.
  intros.
  apply binary_lt_length.
  apply incr1_lt_hom.
  auto.
Qed.


Lemma binary_lt_incr1_iter_hom: forall n b b',
binary_lt b b' ->  
binary_lt (iter n incr1 b) (iter n incr1 b').
Proof.
  intros.
  generalize dependent b.
  generalize dependent b'.
  induction n; intros.
  simpl. auto.
  simpl.
  apply IHn.
  apply incr1_lt_hom.
  auto.
Qed.

Lemma binary_lt_not: forall x y,
length x = length y ->
binary_lt (E2::x) (E1::y) -> False.
Proof.
  intros.
  inversion H0.
  simpl in H3.
  lia.
Qed.
