From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.
Require Import Basic.
Require Import Lt.
Require Import Plus.
Require Import Minus.


Import Common.

Local Open Scope nat_scope.

Lemma minus_plus: forall a b : bilist,
  minus (plus a b) b = a.
Proof.
  induction b using bilist_incr_ind.
  simpl.
  rewrite plus_comm.
  auto.
  rewrite minus_incr_decr.
  rewrite minus_decr.
  rewrite plus_incr1_right.
  rewrite decr1_incr1.
  assumption.
Qed.

Lemma minus_plus2: forall a b : bilist,
  minus (plus a b) a = b.
Proof.
  intros.
  generalize dependent b.
  induction a using bilist_incr_ind; intros.
  simpl. auto.
  rewrite plus_incr1_left.
  rewrite minus_incr_hom.
  auto.
Qed.  

