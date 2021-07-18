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


Definition siglist := {x : bilist | ltb (length x) 6 = true}.

Program Definition foo (a: {x: nat | ltb x 6 = true}) :  {x: nat | ltb x 7 = true} := S a.


Lemma lt_sum : forall (a b c d : bilist), 
    binary_lt a b -> binary_lt c d -> binary_lt (plus a c) (plus a d).
Proof.
    intros.
    induction a.
    simpl.
    assumption.
    simpl.
    destruct a.
    remember (length (plus a0 c) - length a0).
    remember (plus a0 c).
    remember (length (plus a0 d) - length a0).
    remember (plus a0 d).
    destruct n.
    simpl.
    destruct n0.
    simpl.
    constructor 3.
    apply IHa.
    apply binary_lt_trans with (b := E1 :: a0).
    constructor.
    auto.
    assumption.
    simpl.
    destruct b1.
    simpl.
    simpl in Heqn0.
    lia.
    simpl.
    destruct b1.
    remember (length (incr1 (firstn n0 b2)) =? length (firstn n0 b2)).
    destruct b1.
    simpl.
    constructor.
    simpl.
    symmetry in Heqb2.
    

Lemma plus_help : forall (b b1 : bilist),
    Forall (eq E2) (plus b b1) -> length b1 < length b -> length (plus b b1) = length b.
Proof.
    induction b using list_ind_length.
    intros.
    simpl.
    inversion H0.
    intros.
    destruct b.
    inversion H1.
    rewrite plus_plus'.
    destruct b.
    simpl.
    unfold plus'.
    remember (plus b b1).
    destruct b0.
    simpl.
    destruct b.
    simpl.
    auto.
    simpl in Heqb0.
    destruct b.
    assert (incr1 (firstn (length (plus b0 b1) - length b0) (plus b0 b1)) <> []).
    apply neq_in.
    remember (incr1 (firstn (length (plus b0 b1) - length b0) (plus b0 b1))).
    destruct b.
    contradiction.
    inversion Heqb0.
    rewrite <- incr2_incr1 in Heqb0.
    remember (incr1 (incr1 (firstn (length (plus b0 b1) - length b0) (plus b0 b1)))).
    destruct b.
    assert (incr1 (incr1 (firstn (length (plus b0 b1) - length b0) (plus b0 b1))) <> []).
    apply neq_in.
    rewrite Heqb in H1.
    contradiction.
    inversion Heqb0.
    destruct b0.


    


Program Definition sigmaplus (n : nat) (b b1: {x: bilist | ltb (length x) n = true}) :  {x: bilist | ltb (length x) (1 + n) = true} := plus b b1.

Next Obligation.
    rewrite plus_plus'.
    induction b using bilist_incr_ind.
    simpl.
    rewrite Nat.ltb_lt.
    rewrite Nat.ltb_lt in H.
    lia.
    rewrite <- plus_plus'.
    rewrite plus_incr1_left.
    rewrite plus_plus'.
    remember (plus' b b1).
    destruct b0.
    simpl.
    rewrite Nat.ltb_lt.
    rewrite Nat.ltb_lt in H0.
    assert (0 < length (incr1 b)).
    induction b.
    simpl.
    auto.
    destruct a; simpl; destruct (length (incr1 b) =? length b); simpl; lia.
    lia.
    destruct b0;
    simpl; remember (length (incr1 b2) =? length b2); destruct b0; simpl.
    enough ((length b <? n) = true ).
    apply IHb in H1.
    simpl in *.
    rewrite Nat.ltb_lt in *.
    destruct b2.
    simpl in *.
    inversion Heqb1.
    Search (_ =? _ = true).
    symmetry in Heqb1.
    rewrite Nat.eqb_eq in Heqb1.
    rewrite Heqb1.
    apply H1.
    rewrite Nat.ltb_lt in *.
    assert (length b <= length (incr1 b)).
    apply incr1_length.
    lia.
    rewrite tl_S.
    symmetry in Heqb1.
    apply length_eq_incr_S in Heqb1.
    rewrite Heqb1.
    assert (length b <= length (incr1 b)).
    apply incr1_length.
    rewrite Nat.ltb_lt in *.
    enough (length b < n).
    apply IHb in H2.
    rewrite Nat.ltb_lt in *.
    simpl in *.
    lia.
    lia.
    symmetry in Heqb1.
    rewrite Nat.eqb_eq in Heqb1.
    rewrite Heqb1.
    rewrite Nat.ltb_lt in *.
    enough (length b < n).
    apply IHb in H1.
    rewrite Nat.ltb_lt in *.
    simpl in *.
    lia.
    assert (length b <= length (incr1 b)).
    apply incr1_length.
    lia.
    symmetry in Heqb1.
    apply length_eq_incr_S in Heqb1.
    rewrite Heqb1.
    assert (length b <= length (incr1 b)).
    apply incr1_length.
    rewrite Nat.ltb_lt in *.
    assert (length b < n).
    lia.
    apply IHb in H2.
    rewrite Nat.ltb_lt in *.
    simpl in *.







assert (length b <= length (incr1 b)).
apply incr1_length.
lia.
assert (length b <= length (incr1 b)).
apply incr1_length.
lia.
rewrite tl_S.
symmetry in Heqb1.
apply length_eq_incr_S in Heqb1.
rewrite Heqb1.
assert (length b <= length (incr1 b)).
apply incr1_length.
rewrite Nat.ltb_lt in *.
enough (length b < n).
apply IHb in H2.
rewrite Nat.ltb_lt in *.
simpl in *.
lia.
lia.


rewrite app_length.
rewrite skipn_length.
replace (length (plus b b1) - (length (plus b b1) - length b)) with (length b).
remember (firstn (length (plus b b1) - length b) (plus b b1)).
destruct l.
simpl.
rewrite Nat.ltb_lt.
rewrite Nat.ltb_lt in H0.
simpl in H0.
lia.
simpl in H0.
destruct b0.
simpl.
remember (length (incr1 l) =? length l).
destruct b0.
simpl.
destruct l.
simpl.
rewrite Nat.ltb_lt.
rewrite Nat.ltb_lt in H0.
lia.
simpl.
destruct b0.

apply IHb.

Admitted.
Fail Next Obligation.