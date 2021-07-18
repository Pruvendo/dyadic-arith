From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.
Require Import Basic.
Require Import Plus.

Local Open Scope nat_scope.


Fixpoint bin_to_nat (b : bilist) : nat :=
  match b with
  | [] => 0
  | E1 :: t => pow 2 (length t) + bin_to_nat t
  | E2 :: t => pow 2 (1 + length t) + bin_to_nat t
  end.

Lemma bin_to_nat_incr: forall b,
  S (bin_to_nat b) = bin_to_nat (incr1 b).
Proof.
  intros.
  induction b using list_ind_length.
  simpl.
  reflexivity.
  destruct b.
  simpl. auto.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  destruct b1.
  simpl.
  rewrite <- H.
  symmetry in Heqb1.
  apply EqNat.beq_nat_true in Heqb1.
  rewrite Heqb1.
  lia.
  auto.
  simpl.
  destruct b0.
  simpl.
  reflexivity.
  rewrite <- incr1_tl_comm_E2.
  simpl tl.
  rewrite <- H.
  simpl length.
  rewrite <- length_le_S.
  destruct b.
  simpl.
  rewrite E1_head_incr in Heqb1.
  inversion Heqb1.
  simpl.
  lia.
  destruct b.
  rewrite E1_head_incr in Heqb1.
  inversion Heqb1.
  assert (false = (length (incr1 (E2 :: b0)) =? length (E2 :: b0)) -> false = (length (incr1 (b0)) =? length (b0))).
  induction b0.
  simpl. auto.
  simpl. remember (length (incr1 b0) =? length b0).
  destruct a; simpl.
  destruct b; simpl; try (rewrite <- Heqb).
  simpl.
  rewrite <- Heqb.
  auto.
  rewrite length_incr_tl.
  remember (length b0 =? length b0).
  destruct b.
  simpl. rewrite length_incr_tl. rewrite <- Heqb0.
  auto.
  apply length_neq_incr. symmetry.
  auto.
  simpl.
  auto.
  apply length_neq_incr. symmetry.
  auto.
  destruct b.
  simpl.
  rewrite <- Heqb.
  simpl.
  rewrite <- Heqb; auto.
  simpl.
  rewrite <- Heqb.
  simpl.
  rewrite <- Heqb.
  auto.
  apply H0 in Heqb1.
  apply length_neq_incr.
  symmetry; auto.
  simpl.
  auto.
  simpl. lia.
  apply incr1_cons2.
  apply length_neq_incr.
  symmetry; auto.
  destruct b1.
  simpl.
  symmetry in Heqb1.
  apply EqNat.beq_nat_true in Heqb1.
  rewrite Heqb1.
  rewrite <- H.
  lia.
  auto.
  simpl. rewrite <- H.
  rewrite <- length_le_S.
  simpl. lia.
  apply length_neq_incr.
  symmetry. auto.
  auto.
Qed.

Fixpoint nat_to_bin (n : nat) : bilist :=
  match n with
  | 0 => []
  | S n => incr1 (nat_to_bin n)
  end.

Theorem bin_to_nat_corr: forall b,
 bin_to_nat (nat_to_bin b) = b.
Proof.
  intros.
  induction b.
  auto.
  simpl.
  rewrite <- bin_to_nat_incr.
  rewrite IHb.
  auto.
Qed.


Fixpoint bilist2nat (b: bilist) : nat :=
  match b with
  | [] => 0
  | h::t => let n := bilist2nat t in
            match h with 
            | E1 => pow 2 (length t) + n
            | E2 => pow 2 (1 + length t) + n
            end
  end.

Compute bilist2nat [E2;E1;E1].
Compute bilist2nat [E2;E2;E2].


Inductive diadic : Type := Diadic:  bilist -> diadic . 

Definition diadic2Z (d: diadic) : Z := 
  let (b) := d in
  Z.of_nat (bilist2nat b).


Fixpoint nat2bilist (n: nat) : bilist :=
  match n with 
  | 0 => []
  | S n => incr1 (nat2bilist n)
  end.

Definition Z2diadic (z: Z) : diadic := Diadic (nat2bilist (Z.to_nat z)).

Lemma nat2bilist_plus: forall a b, nat2bilist (a + b) = plus (nat2bilist a) (nat2bilist b) .
Proof.
  intros.
  generalize dependent b.
  induction a; intros.
  simpl. auto.
  simpl.
  rewrite IHa.
  rewrite plus_incr1_left. auto.
Qed.


Lemma bilist2nat_correct: forall b, nat2bilist (bilist2nat b) = b.
Proof.
  intros.
  induction b using list_ind_length.
  simpl. auto.

  destruct b.
  simpl. auto.

  simpl.
  destruct b.

  rewrite nat2bilist_plus.
  rewrite H.
  rewrite <- iter_incr1_tail1.
  remember ((2 ^ length b0)).
  clear H. clear Heqn.
  generalize dependent b0.
  induction n; intros.
  simpl. auto.
  simpl.
  rewrite plus_incr1_left.
  rewrite IHn.
  rewrite <- iterS.
  simpl. auto.
  simpl. lia.

  replace ((2 ^ length b0 + (2 ^ length b0 + 0) + bilist2nat b0)) with ((2 ^ length b0 + 2 ^ length b0 ) + bilist2nat b0).
  rewrite nat2bilist_plus.
  rewrite H.
  rewrite <- iter_incr1_tail2.
  remember ((2 ^ length b0 + 2 ^ length b0)).
  clear H. clear Heqn.
  generalize dependent b0.
  induction n; intros.
  simpl. auto.
  simpl.
  rewrite plus_incr1_left.
  rewrite IHn.
  rewrite <- iterS.
  simpl. auto.
  simpl. lia.
  lia. 
Qed.

Lemma nat2bilist_correct: forall n, bilist2nat (nat2bilist n) = n.
Proof.
  intros.
  induction n.
  simpl. auto.
  simpl.
  enough (forall b, bilist2nat (incr1 b) = S (bilist2nat b)).
  rewrite H.
  rewrite IHn. auto.
  clear IHn.
  induction b using list_ind_length.
  simpl.
  auto.
  simpl.
  destruct b.
  simpl. auto.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b; destruct b1; simpl.
  -
  rewrite H.
  replace (length (incr1 b0)) with (length b0).
  lia.
  apply PeanoNat.Nat.eqb_eq.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  simpl. lia.
  -
  destruct b0.
  simpl. auto.
  rewrite <- incr1_tl_comm_E2.
  simpl tl.
  rewrite H.
  replace (length (incr1 b0)) with (S (length b0)).
  replace b with E2.
  simpl. lia.
  enough (Forall (eq E2) (b :: b0)).
  inversion H0. auto.
  apply incr1_cons2.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia.
  apply incr1_length.
  apply incr1_length_plus.
  symmetry in Heqb1.
  assert (Forall (eq E2) b0).
  enough (Forall (eq E2) (b::b0)).
  inversion H0.
  auto.
  apply incr1_cons2.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia.
  apply incr1_length.
  apply incr1_cons2_inv. auto.
  simpl. lia.
  simpl. lia.
  apply incr1_cons2.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia.
  apply incr1_length.
-
  rewrite H.
  replace  (length (incr1 b0)) with (length b0).
  lia.
  apply PeanoNat.Nat.eqb_eq.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  simpl. lia.
-
  rewrite H.
  replace (length (incr1 b0)) with (S (length b0)).
  simpl.
  lia.
  apply incr1_length_plus.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length b0 <= length (incr1 b0))  .
  lia.
  apply incr1_length.
  simpl. lia.
Qed.  


Declare Scope diadic_scope.
Delimit Scope diadic_scope with diadic.
