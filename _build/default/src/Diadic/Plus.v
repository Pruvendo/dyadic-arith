From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.
Require Import Basic.
Require Import Lt.

Import Common.

Local Open Scope nat_scope.


Fixpoint plus (b b' : bilist) : bilist :=
  match b with
  | [] => b' 
  | h :: t => let l := plus t b' in
              let (p, r) := split (length l - (length t)) l in
              match h with
              | E1 => (incr1 p) ++ r
              | E2 => (incr2 p) ++ r
              end
  end.     


Example test_plus_1 :  plus [E1] [E1] = [E2].
Proof.
auto. Qed.

Example test_plus_2 :  plus [E1] [E2] = [E1;E1].
Proof.
    auto. Qed.
    
Example test_plus_3 :  plus [E2] [E2] = [E1;E2].
Proof.
auto. Qed.

Example test_plus_4 :  plus [E1] [E1;E1] = [E1;E2].
Proof.
auto. Qed.

Example test_plus_5 :  plus [E1] [E2;E2] = [E1;E1;E1].
Proof.
auto. Qed.

Example test_plus_6 :  plus [E2;E2] [E2;E2] = [E2;E1;E2].
Proof.
    auto. Qed.
  
  
Example test_plus_7:  plus [E1;E1] [E1] = [E1;E2].
Proof.
auto. Qed.

Example test_plus_8 :  plus [E2;E2] [E1] = [E1;E1;E1].
Proof.
auto. Qed.

Example test_plus_9 :  plus [E1;E2] [E2;E2] = [E1;E2;E2].
Proof.
    auto. Qed.
  
Example test_plus_10 :  plus [E1; E1] [E1; E1; E1] = [E1;E2;E2].
Proof.
    auto. 
Qed.

Example test_plus_11 :  plus [E1; E2] [E1; E2; E1] = [E2;E2;E1].
Proof.
    auto. 
Qed.

Example test_plus_12 :  plus [E2;E2] [E1;E2] = [E1;E2;E2].
Proof.
    auto. Qed.

Example test_plus_13 :  plus [E1; E1;E1] [ E1; E1] = [E1;E2;E2].
Proof.
    auto. 
Qed.

Example test_plus_14 :  plus [E1; E2;E1] [E1; E2] = [E2;E2;E1].
Proof.
    auto. 
Qed.


Lemma incr_plus_r: forall b : bilist,
  incr1 b = plus [E1] b.
Proof.
  induction b.
  auto.
  simpl.
  simpl in IHb.
  rewrite skipn_n in IHb.
  rewrite PeanoNat.Nat.sub_0_r  with (length b) in IHb.
  simpl in IHb.
  rewrite firstn_n. rewrite <- PeanoNat.Nat.sub_0_r with (length b).
  rewrite skipn_n.
  rewrite app_nil_r. auto.
Qed.

Lemma incr_plus_l: forall b : bilist, incr1 b = plus b [E1].
Proof.
  induction b using list_ind_length.
  auto.
  destruct b. auto.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b1; destruct b.
  -
  rewrite <- H.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  rewrite Heqb1.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite firstn_O.
  rewrite skipn_O.
  simpl. auto.
  auto.
  -
  rewrite <- H.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  rewrite Heqb1.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite firstn_O.
  rewrite skipn_O.
  simpl. auto.
  auto.
  - rewrite <- H.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (S (length b0) = length (incr1 b0)).
  rewrite <- H0.
  replace (S (length b0) - length b0) with 1.
  replace ((firstn 1 (incr1 b0))) with [E1].
  replace (skipn 1 (incr1 b0)) with (tl ((incr1 b0))).
  simpl. auto.
  rewrite skipn_1. auto.
  destruct b0.
  simpl. auto.
  simpl. destruct b; destruct (length (incr1 b0) =? length b0); simpl; try lia; auto.
  apply forall_head.
  destruct b0.
  simpl. auto.
  simpl. destruct b; destruct (length (incr1 b0) =? length b0); simpl; try lia; auto.
  apply incr1_cons1.
  lia. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)). lia.
  apply incr1_length.
  auto.
  - rewrite <- H.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (S (length b0) = length (incr1 b0)).
  rewrite <- H0.
  replace (S (length b0) - length b0) with 1.
  replace ((firstn 1 (incr1 b0))) with [E1].
  replace (skipn 1 (incr1 b0)) with (tl ((incr1 b0))).
  simpl.
  rewrite head_tail with (l:=incr1 b0) at 1.
  replace (firstn 1 (incr1 b0)) with [E1]. auto.
  apply forall_head.
  lia.  apply incr1_cons1.
  lia. lia.
  apply skipn_1. lia.
  apply forall_head.
  lia. apply incr1_cons1. lia. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)). lia.
  apply incr1_length.
  auto.
  
Qed.


Lemma plus_nil: forall b, plus b [] = b.
Proof.
  induction b.
  auto.
  simpl.
  destruct a.
  rewrite ?IHb.
  rewrite ?PeanoNat.Nat.sub_diag. 
  simpl. auto.
  rewrite ?IHb.
  rewrite ?PeanoNat.Nat.sub_diag.
  simpl.
  auto.
Qed.

Lemma plus_len: forall b b', 
  length b <= length (plus b b').
Proof.
  intros.
  generalize dependent b'.
  induction b using list_ind_length; intros.
  simpl. lia.
  destruct b.
  simpl. lia.
  simpl.
  destruct b.
  -
  rewrite app_length.
  rewrite skipn_length.
  replace (length (plus b0 b') - (length (plus b0 b') - length b0)) with (length b0).
  remember (firstn (length (plus b0 b') - length b0) (plus b0 b')).
  destruct l.
  simpl.  lia.
  simpl.
  destruct b; destruct (length (incr1 l) =? length l); simpl; lia.
  enough (length b0 <= length (plus b0 b')).
  lia.
  apply H.
  simpl. lia.
  -
  rewrite app_length.
  rewrite skipn_length.
  replace (length (plus b0 b') - (length (plus b0 b') - length b0)) with (length b0).
  remember (firstn (length (plus b0 b') - length b0) (plus b0 b')).
  destruct l.
  simpl.  lia.
  simpl.
  destruct b; destruct (length (incr2 l) =? length l); simpl; destruct l; simpl length; lia.
  enough (length b0 <= length (plus b0 b')).
  lia.
  apply H.
  simpl. lia.
Qed.


Lemma lt_plus: forall b b',
0 < length b' -> 
binary_lt b (plus b b').
Proof.
  intros.
  generalize dependent b'.
  induction b using list_ind_length; intros.
  simpl. 
  destruct b'. inversion H.

  constructor. simpl. lia.
  destruct b.
  simpl.
  destruct b'. inversion H0.
  constructor. simpl. lia.
  simpl.
  destruct b.
  -
  remember (length (plus b0 b') - length b0) as n.
  remember (plus b0 b') as x.
  remember (iter_incr1_tail x (length b0)).
  assert (iter (2 ^ length b0) incr1 x = incr1 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply binary_lt_length.
  apply H.
  simpl. lia.
  destruct b'. inversion H0.
  simpl. lia.
  rewrite <- Heqn in H1.
  rewrite <- H1.
  clear a Heqa.
  assert (E1 :: b0  = iter (2 ^ length b0) incr1 b0).
  rewrite iter_incr1_tail1.
  auto.
  rewrite H2.
  apply binary_lt_incr1_iter_hom.
  rewrite Heqx.
  apply H.
  simpl. lia.
  destruct b'. inversion H0.
  simpl. lia.
  -
  remember (length (plus b0 b') - length b0) as n.
  remember (plus b0 b') as x.
  remember (iter_incr1_tail x (length b0)).
  assert (iter (2 ^ length b0 + 2 ^ length b0) incr1 x =
  incr2 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply binary_lt_length.
  apply H.
  simpl. lia.
  destruct b'. inversion H0.
  simpl. lia.
  rewrite <- Heqn in H1.
  rewrite <- H1.
  clear a Heqa.
  assert (E2 :: b0  = iter (2 ^ length b0 + 2 ^ length b0) incr1 b0).
  rewrite iter_incr1_tail2.
  auto.
  rewrite H2.
  apply binary_lt_incr1_iter_hom.
  rewrite Heqx.
  apply H.
  simpl. lia.
  destruct b'. inversion H0.
  simpl. lia.
Qed.



Lemma plus_incr1_left: forall b b', plus (incr1 b) b' = incr1 (plus b  b') .
Proof.
  intros.
  generalize dependent b'.
  induction b using bilist_lt_ind.
  intros.
  simpl.
  replace (length b' - 0) with (length b').
  rewrite firstn_all.
  rewrite skipn_all.
  rewrite ?app_nil_r.
  auto.
  lia.
  intros.

  destruct b.
  simpl.
  replace (length b' - 0) with (length b').
  rewrite firstn_all.
  rewrite skipn_all.
  rewrite ?app_nil_r.
  auto.
  lia.
  simpl.
  remember (length (incr1 b0) =? length b0).
  remember (length (plus b0 b') - length b0).
  remember (plus b0 b') as x.
  destruct b; destruct b1.
  -
  simpl.
  rewrite H.
  rewrite <- Heqx.
  remember ((length (incr1 x) - length (incr1 b0))) as m.
  remember (iter_incr1_tail x (length b0)).
  clear Heqa.
  rewrite <- Heqn in a.
  assert (iter (2 ^ length b0) incr1 x = incr1 (firstn n x) ++ skipn n x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- H0.
  remember (iter_incr1_tail (incr1 x) (length (incr1 b0))).
  clear Heqa0.
  rewrite <- Heqm in a0.
  assert (iter (2 ^ length (incr1 b0)) incr1 (incr1 x) =
  incr1 (firstn m (incr1 x)) ++ skipn m (incr1 x)).
  apply a0.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil. lia.
  apply incr1_length_hom.
  apply lt_plus.
  simpl. lia.
  clear a H0 a0 H1.
  remember (iter_incr1_tail (incr1 x) (length (incr1 b0))).
  assert (iter (2 ^ length (incr1 b0)) incr1 (incr1 x) =
  incr1 (firstn (length (incr1 x) - length (incr1 b0)) (incr1 x)) ++
  skipn (length (incr1 x) - length (incr1 b0)) (incr1 x)).
  apply a.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil. lia.
  apply incr1_length_hom.
  apply lt_plus. simpl. lia.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  replace (length (incr1 b0)) with (length b0).
  rewrite <- iterS.
  simpl. auto.
  apply PeanoNat.Nat.eqb_eq.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  constructor. lia.
  - simpl.
  remember (length (plus (tl (incr1 b0)) b') - length (tl (incr1 b0))) as m.
  remember ((plus (tl (incr1 b0)) b')).
  destruct b0.
  +
  simpl in Heqb.
  simpl in Heqm.
  simpl in Heqx.
  simpl in Heqn.
  rewrite Heqx.
  rewrite Heqb.
  replace m with n.
  subst.
  replace (length b' - 0) with (length b') by lia.
  rewrite firstn_all2.
  rewrite skipn_all2.
  rewrite ?app_nil_r.
  rewrite incr2_incr1.
  auto.
  lia. lia.
  subst.
  auto.
  +
  rewrite <- incr1_tl_comm_E2 in Heqb.
  rewrite H in Heqb.
  rewrite <- incr1_tl_comm_E2 in Heqm.
  simpl in Heqm.
  simpl in Heqb.
  remember  (iter_incr1_tail b (length (incr1 b1))).
  assert (iter (2 ^ length (incr1 b1) + 2 ^ length (incr1 b1)) incr1 b =
  incr2 (firstn (length b - length (incr1 b1)) b) ++ skipn (length b - length (incr1 b1)) b).
  apply a.
  rewrite Heqb.
  destruct b'.
  rewrite plus_nil. lia.
  apply incr1_length_hom.
  apply lt_plus. simpl. lia.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  clear a Heqa H0.
  remember  (iter_incr1_tail x (length (b0 :: b1))).
  assert (iter (2 ^ length (b0 :: b1)) incr1 x =
  incr1 (firstn (length x - length (b0 :: b1)) x) ++ skipn (length x - length (b0 :: b1)) x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- Heqn in H0.
  rewrite <- H0.
  simpl.
  simpl in Heqx.
  replace b0 with E2 in Heqx.
  clear a Heqa H0.
  remember (plus b1 b') as y.
  remember  (iter_incr1_tail y (length b1)).
  assert (iter (2 ^ length b1 + 2 ^ length b1) incr1 y =
  incr2 (firstn (length y - length b1) y) ++ skipn (length y - length b1) y).
  apply a.
  rewrite Heqy.
  apply plus_len.
  rewrite <- H0 in Heqx.
  clear a Heqa H0.
  rewrite Heqx.
  rewrite Heqb.
  replace (2 ^ length b1 + (2 ^ length b1 + 0)) with (2 ^ length b1 + 2 ^ length b1 ).
  replace (length (incr1 b1)) with (S (length b1)).
  simpl.
  replace  (2 ^ length b1 + 0) with (2 ^ length b1 ).
  rewrite iter_plus.
  rewrite <- iterS.
  simpl.
  rewrite <- iterS.
  simpl. auto.
  lia.
  apply incr1_length_plus.
  apply incr1_cons2_inv.
  enough (length (b0 :: b1) < length (incr1 (b0 :: b1))).
  apply incr1_cons2 in H0.
  inversion H0. auto.
  enough (length (b0 :: b1) <= length (incr1 (b0 :: b1))).
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  lia.
  apply incr1_length.
  lia.
  enough (Forall (eq E2) (b0 :: b1)).
  inversion H1. auto.
  apply incr1_cons2.
  enough (length (b0 :: b1) <= length (incr1 (b0 :: b1))).
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  lia. apply incr1_length.
  simpl. lia.
  apply incr1_cons2.
  enough (length (b0 :: b1) <= length (incr1 (b0 :: b1))).
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  lia. apply incr1_length.
  simpl.
  constructor 1. simpl. lia.
  simpl. lia.
  apply incr1_cons2.
  enough (length (b0 :: b1) <= length (incr1 (b0 :: b1))).
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  lia. apply incr1_length.
  -
  simpl.
  remember (length (plus (incr1 b0) b') - length (incr1 b0)) as m.
  rewrite H.
  rewrite <- Heqx.
  remember  (iter_incr1_tail x (length b0)).
  assert (iter (2 ^ length b0 + 2 ^ length b0) incr1 x =
  incr2 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- Heqn in H0.
  rewrite <- H0.
  clear a Heqa H0.
  rewrite H in Heqm.
  rewrite <- Heqx in Heqm.
  remember  (iter_incr1_tail (incr1 x) (length (incr1 b0))).
  assert (iter (2 ^ length (incr1 b0) + 2 ^ length (incr1 b0)) incr1 (incr1 x) =
  incr2 (firstn (length (incr1 x) - length (incr1 b0)) (incr1 x)) ++
  skipn (length (incr1 x) - length (incr1 b0)) (incr1 x)).
  apply a.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil.
  lia.
  apply incr1_length_hom.
  apply lt_plus. simpl. lia.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  rewrite <- iterS.
  simpl.
  replace (length (incr1 b0)) with (length b0).
  auto.
  apply PeanoNat.Nat.eqb_eq.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  constructor. lia.
  constructor. lia.
  -
  simpl.
  rewrite H.
  rewrite <- Heqx.
  remember (length (incr1 x) - length (incr1 b0)) as m.
  remember  (iter_incr1_tail x (length b0)).
  assert (iter (2 ^ length b0 + 2 ^ length b0) incr1 x =
  incr2 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- Heqn in H0.
  rewrite <- H0.
  clear a Heqa H0.
  remember  (iter_incr1_tail (incr1 x) (length (incr1 b0))).
  assert (iter (2 ^ length (incr1 b0)) incr1 (incr1 x) =
  incr1 (firstn (length (incr1 x) - length (incr1 b0)) (incr1 x)) ++
  skipn (length (incr1 x) - length (incr1 b0)) (incr1 x)).
  apply a.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil.
  lia.
  apply incr1_length_hom.
  apply lt_plus. simpl. lia.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  replace (length (incr1 b0)) with (S (length b0)).
  simpl.
  replace (2 ^ length b0 + (2 ^ length b0 + 0)) with (2 ^ length b0 + 2 ^ length b0 ).
  rewrite <- iterS.
  simpl. auto.
  lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)).
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  lia.
  apply incr1_length.
  constructor. lia.
Qed.


Lemma plus_incr1_right: forall b b', plus b (incr1 b') = incr1 (plus b b') .
Proof.
  intros.
  generalize dependent b'.
  induction b using bilist_lt_ind.
  intros.
  simpl. auto.

  intros.
  destruct b.
  simpl. auto.
  simpl.
  rewrite H.
  remember  (plus b0 b') as x.
  destruct b.
  -
  remember ((length (incr1 x) - length b0)) as m.
  remember (length x - length b0) as n.
  remember (iter_incr1_tail x (length b0)).
  clear Heqa.
  assert (iter (2 ^ length b0) incr1 x =
  incr1 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- Heqn in H0.
  rewrite <- H0.
  clear a H0.
  remember (iter_incr1_tail (incr1 x) (length  b0)).
  assert (iter (2 ^ length b0) incr1 (incr1 x) =
  incr1 (firstn (length (incr1 x) - length b0) (incr1 x)) ++
  skipn (length (incr1 x) - length b0) (incr1 x)).
  apply a.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil. 
  apply incr1_length.
  apply binary_lt_length.
  apply binary_lt_trans with (b:=(plus b0 (b :: b'))).
  apply lt_plus.
  simpl. lia.
  apply lt_incr1.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  clear a Heqa H0.
  rewrite <- iterS. simpl. auto.
- 
  remember ((length (incr1 x) - length b0)) as m.
  remember (length x - length b0) as n.
  remember (iter_incr1_tail x (length b0)).
  clear Heqa.
  assert (iter (2 ^ length b0 + 2 ^ length b0) incr1 x =
  incr2 (firstn (length x - length b0) x) ++ skipn (length x - length b0) x).
  apply a.
  rewrite Heqx.
  apply plus_len.
  rewrite <- Heqn in H0.
  rewrite <- H0.
  clear a H0.
  remember (iter_incr1_tail (incr1 x) (length  b0)).
  assert (iter (2 ^ length b0 + 2 ^ length b0) incr1 (incr1 x) =
  incr2 (firstn (length (incr1 x) - length b0) (incr1 x)) ++
  skipn (length (incr1 x) - length b0) (incr1 x)).
  apply a.
  rewrite Heqx.
  destruct b'.
  rewrite plus_nil. 
  apply incr1_length.
  apply binary_lt_length.
  apply binary_lt_trans with (b:=(plus b0 (b :: b'))).
  apply lt_plus.
  simpl. lia.
  apply lt_incr1.
  rewrite <- Heqm in H0.
  rewrite <- H0.
  clear a Heqa H0.
  rewrite <- iterS. simpl. auto.
-
  constructor.
  lia.
Qed.    

Theorem plus_comm: forall b b' : bilist,
  plus b b' = plus b' b.
Proof.
  intros.
  generalize dependent b'.
  induction b using bilist_incr_ind.
  intros.
  rewrite plus_nil. simpl. auto.
  intros.
  enough (forall b b', plus (incr1 b) b' = incr1 (plus b b')).
  enough (forall b b', plus b (incr1 b') = incr1 (plus b b')).
  rewrite H.
  rewrite IHb.
  rewrite H0.
  auto.
  intros. apply plus_incr1_right.
  intros. apply plus_incr1_left.
Qed.  


Fixpoint plus' (b b' : bilist) :  bilist := 
match b with
| [] => b'
| E1 :: t => iter (pow 2 (length t)) incr1 (plus' t b')
| E2 :: t => iter (pow 2 (length t) + pow 2 (length t)) incr1 (plus' t b')
end.

Lemma plus'_0_l: forall b, plus' [] b = b .
Proof.
  simpl.
  auto.
Qed.

Lemma iter_incr1_next_digit: forall b,
iter (2 ^ length b) incr1 b = E1 :: b /\
iter (2 ^ length b + 2 ^ length b) incr1 b = E2 :: b.
Proof.
  intros.
  remember (iter_incr1_tail b (length b)).
  assert (iter (2 ^ length b) incr1 b =
  incr1 (firstn (length b - length b) b) ++ skipn (length b - length b) b /\
  iter (2 ^ length b + 2 ^ length b) incr1 b =
  incr2 (firstn (length b - length b) b) ++ skipn (length b - length b) b).
  apply a.
  lia.
  clear Heqa a.
  inversion_clear H.
  rewrite H0. rewrite H1.
  replace (length b - length b) with 0 by lia.
  simpl.
  auto.
Qed.


Lemma plus'_0_r: forall b, plus' b [] = b .
Proof.
  induction b using list_ind_length.
  auto.
  destruct b; auto.
  simpl.

  destruct b.
  -
  rewrite H; [| simpl; lia].
  apply iter_incr1_next_digit.
  -
  rewrite H; [| simpl; lia].
  apply iter_incr1_next_digit.
Qed.


Lemma plus_plus': forall b b', plus b b' = plus' b b'.
Proof.
  intros.
  generalize dependent b'.
  induction b using list_ind_length; intros.
  simpl. auto.
  destruct b; auto.
  simpl.
  rewrite <- H.
  remember (plus b0 b').
  remember (iter_incr1_tail b1 (length b0)).
  enough (length b0 <= length b1).
  apply a in H0.
  inversion_clear H0.
  rewrite H1, H2.
  auto.
  rewrite Heqb1.
  apply plus_len.
  simpl. lia.
Qed.
