From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.

Local Open Scope nat_scope.

Inductive binary : Type :=
  | E1
  | E2.

Definition bilist : Type := list binary. 

Fixpoint incr1 (b : bilist) : bilist :=
match b with
  | [] => [E1]
  | E1 :: t => let b' := incr1 t in
               if (length b' =? length t) then E1::b' else E2 :: (tl b')
  | E2 :: t => let b' := incr1 t in
               if (length b' =? length t) then E2::b' else E1::b'
end.

Fixpoint decr1 (b:bilist) :=
  match b with
  | [] => []
  | [E1] => []
  | [E2] => [E1]
  | E1::t => let b' := decr1 t in
            if (length b' =? length t) then E1::b' else E2::b'
  | E2::t => let b' := decr1 t in
            if (length b' =? length t) then E2::b' else E1::E2::b'
  end. 

Fixpoint incr2 (b : bilist) : bilist :=
match b with
  | [] => [E2]
  | [E1] => [E1; E1]
  | [E2] => [E1; E2]
  | E1 :: t => let b' := incr2 t in
               if (length b' =? length t) then E1::b' else E2 :: (tl b')
  | E2 :: t => let b' := incr2 t in
               if (length b' =? length t) then E2::b' else E1::b'
end.


Lemma neq_in: forall b : bilist,
  incr1 b <> [].
Proof.
  intros.
  induction b.
  simpl. discriminate.
  simpl.
  destruct a.
  destruct (length (incr1 b) =? length b).
  discriminate. discriminate.
  destruct (length (incr1 b) =? length b).
  discriminate. discriminate.
Qed.

Lemma neq_in_r: forall b : bilist,
  [] <> incr1 b.
Proof.
  intros.
  induction b.
  simpl. discriminate.
  simpl.
  destruct a.
  destruct (length (incr1 b) =? length b).
  discriminate. discriminate.
  destruct (length (incr1 b) =? length b).
  discriminate. discriminate.
Qed.


Lemma neq_zero_length: forall b : bilist,
  0 < length (incr1 b).
Proof.
  induction b.
  auto.
  simpl.
  destruct a.
  destruct (length (incr1 b) =? length b).
  simpl. auto.
  simpl. lia. 
  destruct (length (incr1 b) =? length b).
  simpl. auto.
  simpl. lia.
Qed.

Lemma E1_head_incr: forall b: bilist, 
  (length (incr1 (E1 :: b)) =? length (E1 :: b)) = true.
Proof.
  induction b.
  auto.
  simpl.
  simpl in IHb.
  destruct a.
  remember (length (incr1 b) =? length b) as q.
  destruct q.
  simpl. rewrite <- Heqq.
  simpl. symmetry; auto.
  rewrite IHb.
  auto.
  remember (length (incr1 b) =? length b) as q.
  destruct q.
  simpl. rewrite <- Heqq.
  simpl. symmetry; auto.
  simpl. simpl in IHb.
  rewrite <- Heqq.
  simpl.
  apply PeanoNat.Nat.eqb_eq.
  apply PeanoNat.Nat.eqb_eq in IHb.
  rewrite <- IHb.
  apply length_ge_zero.
  apply neq_zero_length.
Qed.

Lemma E1_head_eq: forall b, 
length (incr1 (E1 :: b))  = length (E1 :: b).
Proof.
    intros.
    rewrite <- PeanoNat.Nat.eqb_eq.
    
    apply E1_head_incr. 
Qed.

Lemma length_neq_incr: forall b : bilist,
  (length (incr1 b) =? length b) = false <-> length b < length (incr1 b).
Proof.
    split.
    intros.
    induction b.
    simpl. auto. 
    simpl.
    destruct a.
    rewrite E1_head_incr in H.
    inversion H.
    remember (length (incr1 b) =? length b) as q.
    destruct q.
    simpl.
    rewrite <-PeanoNat.Nat.succ_lt_mono.
    apply IHb.
    simpl in H.
    rewrite <- Heqq in H.
    simpl in H.
    rewrite <- Heqq in H.
    inversion H.
    simpl.
    rewrite <-PeanoNat.Nat.succ_lt_mono.
    apply IHb.
    auto.
    (***********)
    induction b.
    simpl.
    auto.
    intros.
    simpl.
    destruct a.
    rewrite E1_head_eq in H.
    apply PeanoNat.Nat.lt_irrefl in H.
    inversion H.
    remember (length (incr1 b) =? length b) as q.
    destruct q.
    simpl.
    simpl in H.
    rewrite <- Heqq in H.
    simpl in H.
    rewrite <-PeanoNat.Nat.succ_lt_mono in H.
    apply IHb in H.
    discriminate.
    simpl.
    simpl in H.
    rewrite <- Heqq in H.
    simpl in H.
    rewrite <-PeanoNat.Nat.succ_lt_mono in H. 
    apply PeanoNat.Nat.lt_neq in H.
    apply PeanoNat.Nat.eqb_neq. auto.
Qed.


Lemma length_tl_incr_true: forall b,
  (length (incr1 b) =? length b) = true -> (length (tl (incr1 b)) =? length b) = false.
Proof.
  induction b using list_ind_length.
  simpl.
  auto.
  intros.
  apply EqNat.beq_nat_true in H0.
  rewrite <- H0.
  apply tl_greater.
  apply neq_zero_length.
Qed.

Lemma tl_greater_eq: forall b : bilist,
  0 < length b -> S (length (tl b)) = (length b) .
Proof.
  intros.
  induction b.
  inversion H.
  simpl. auto.
Qed.

Lemma length_le_S: forall b,
  length b < length (incr1 b) -> S (length b) = length (incr1 b).
Proof.
  induction b.
  auto.
  intros.
  simpl.
  destruct a.
  remember (length (incr1 b) =? length b).
  destruct b0.
  simpl.
  apply eq_S.
  apply IHb.
  simpl in H.
  rewrite <- Heqb0 in H.
  simpl in H.
  apply Lt.lt_S_n in H.
  auto.
  simpl.
  simpl in H.
  rewrite <- Heqb0 in H.
  simpl in H.
  apply eq_S.
  apply Lt.lt_S_n in H.
  symmetry in Heqb0.
  apply length_neq_incr in Heqb0.
  apply IHb in Heqb0.
  apply Lt.lt_n_S in H.
  rewrite Heqb0 in H.
  rewrite <- tl_greater_eq in H.
  lia.
  apply neq_zero_length.
  remember (length (incr1 b) =? length b).
  destruct b0.
  simpl.
  apply eq_S.
  apply IHb.
  simpl in H.
  rewrite <- Heqb0 in H.
  simpl in H.
  apply Lt.lt_S_n in H.
  auto.
  simpl.
  simpl in H.
  rewrite <- Heqb0 in H.
  simpl in H.
  apply eq_S.
  apply Lt.lt_S_n in H.
  symmetry in Heqb0.
  apply length_neq_incr in Heqb0.
  apply IHb in Heqb0.
  auto.
Qed.

Lemma tl_S: forall b,
  S (length (tl (incr1 b))) = length (incr1 b).
Proof.
  induction b.
  auto.
  destruct a.
  simpl.
  remember (length (incr1 b) =? length b).
  destruct b0.
  simpl.
  auto.
  simpl.
  auto.
  simpl.
  remember (length (incr1 b) =? length b).
  destruct b0.
  simpl.
  auto.
  simpl.
  auto.
Qed.


Lemma length_eq_incr_S: forall b,
  (length (incr1 b) =? length b) = false -> length (incr1 b) = S (length b).
Proof.
  induction b using list_ind_length.
  auto.
  intros.
  destruct b.
  auto.
  destruct b.
  simpl.
  rewrite E1_head_incr in H0.
  inversion H0.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  simpl.
  rewrite PeanoNat.Nat.succ_inj_wd.
  apply H.
  auto.
  simpl in H0.
  rewrite <- Heqb in H0.
  simpl in H0.
  auto.
  simpl.
  rewrite PeanoNat.Nat.succ_inj_wd.
  simpl in H0.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  inversion Heqb.
  apply H.
  auto. auto.
Qed.

Lemma length_incr_tl: forall b, 
  length b < length (incr1 b) -> length (tl (incr1 b)) = length b .
Proof.
  induction b.
  auto.
  intros.
  destruct a.
  simpl.
  remember (length (incr1 b) =? length b ).
  destruct b0.
  simpl.
  rewrite E1_head_eq in H.
  lia.
  simpl.
  rewrite E1_head_eq in H.
  lia.
  simpl.
  remember (length (incr1 b) =? length b ).
  destruct b0.
  simpl.
  symmetry in Heqb0.
  rewrite PeanoNat.Nat.eqb_eq in Heqb0.
  apply length_eq_head with (h := E2) in Heqb0.
  simpl in Heqb0.
  apply eq_add_S in Heqb0.
  simpl in H.
  remember (length (incr1 b) =? length b ).
  destruct b0.
  simpl in H.
  rewrite Heqb0 in H.
  lia.
  simpl in H.
  lia.
  simpl.
  apply length_eq_incr_S.
  auto.
Qed.

Lemma incr1_cons2: forall b, length b < length (incr1 b) -> 
Forall (eq E2) b .
Proof.
  induction b.
  simpl.
  auto.
  intros.
  apply Forall_cons. 
  destruct a.
  simpl in H.
  remember (length (incr1 b) =? length b) as q.
  destruct q.
  simpl in H.
  rewrite <- PeanoNat.Nat.succ_lt_mono in H.
  rewrite <- length_neq_incr in H.
  rewrite <- Heqq in H.
  inversion H.
  simpl in H.
  rewrite <- PeanoNat.Nat.succ_lt_mono in H.
  symmetry in Heqq.
  apply length_neq_incr in Heqq.
  apply length_incr_tl in Heqq.
  lia.
  auto.
  apply IHb.
  rewrite <- length_neq_incr in H.
  rewrite <- length_neq_incr.
  simpl.
  destruct a.
  simpl in H.
  remember (length (incr1 b) =? length b ).
  destruct b0.
  simpl in H.
  rewrite H in Heqb0.
  auto.
  simpl in H. auto.
  simpl in H.
  remember (length (incr1 b) =? length b ).
  destruct b0.
  simpl in H.
  rewrite H in Heqb0.
  auto.
  auto.
Qed.

Lemma incr1_cons1: forall b,
  length b  < length (incr1 b) -> Forall (eq E1) (incr1 b).
Proof.
  induction b using list_ind_length.
  simpl. auto.
  intros.
  simpl.
  destruct b.
  simpl. auto.
  destruct b.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  apply Forall_cons. auto.
  apply H.
  auto.
  simpl in H0.
  rewrite <- Heqb in H0.
  simpl in H0.
  apply Lt.lt_S_n in H0.
  apply length_le_S in H0.
  rewrite <- H0 in Heqb.
  lia.
  simpl in H0.
  rewrite <- Heqb in H0.
  simpl in H0.  
  apply Lt.lt_S_n in H0.
  symmetry in Heqb.
  apply length_neq_incr in Heqb.
  apply length_incr_tl in Heqb.
  lia.
  simpl in H0.
  simpl.  
  remember (length (incr1 b0) =? length b0).
  destruct b.
  simpl in H0.
  symmetry in Heqb.
  apply Lt.lt_S_n in H0.
  apply PeanoNat.Nat.eqb_eq in Heqb.
  lia.
  apply Forall_cons.
  auto.
  apply H.
  auto.
  symmetry in Heqb.
  apply length_neq_incr in Heqb.
  auto.
Qed.  
  
Lemma incr1_tl_comm_E1: forall b, 1 < (length b) -> Forall (eq E1) b ->
  incr1 (tl b) = tl (incr1 b).
Proof.
  induction b using list_ind_length.
  simpl. intros. inversion H.
  intros.
  destruct b.
  simpl in H0. inversion H0.
  destruct b.
  simpl in *.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  simpl.
  auto.
  simpl.
  symmetry in Heqb.
  apply length_neq_incr in Heqb.
  apply incr1_cons2 in Heqb.
  inversion_clear H1.
  destruct b0.
  simpl in H0. lia.
  inversion_clear Heqb.
  inversion_clear H3.
  rewrite <- H1 in H5.
  inversion H5.
  inversion_clear H1.
  inversion H2.
Qed.

Lemma incr1_tl_comm_E2: forall b, 0 < (length b) -> Forall (eq E2) b ->
  incr1 (tl b) = tl (incr1 b).
Proof.
  induction b using list_ind_length.
  simpl. lia.
  intros.
  destruct b.
  auto.
  simpl.
  destruct b.
  inversion_clear H1.
  inversion H2.
  inversion_clear H1.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma incr1_length: forall b, length b <= length (incr1 b).
Proof.
  induction b using list_ind_length.
  simpl. lia.
  destruct b. simpl. auto. 
  simpl.
  destruct b.
  -
  remember (length (incr1 b0) =? length b0).
  destruct b.
  + enough (length b0 <= length (incr1 b0)).
  simpl. lia. apply H. simpl. auto.
  + symmetry in Heqb.
  apply PeanoNat.Nat.eqb_neq in Heqb.
  simpl.
  enough (length b0 < length (incr1 b0) ).
  destruct (incr1 b0); simpl. 
  destruct b0; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b0 <= length (incr1 b0)).
  lia. apply H. simpl. lia.
  - remember (length (incr1 b0) =? length b0).
  destruct b.
  + enough (length b0 <= length (incr1 b0)).
  simpl. lia. apply H. simpl. auto.
  + symmetry in Heqb.
  apply PeanoNat.Nat.eqb_neq in Heqb.
  simpl.
  enough (length b0 < length (incr1 b0) ).
  destruct (incr1 b0); simpl. 
  destruct b0; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b0 <= length (incr1 b0)).
  lia. apply H. simpl. lia.
Qed.



Lemma incr1_cons2_inv: forall b, Forall (eq E2) b -> length b < length (incr1 b).
Proof.
  intros.
  induction b using list_ind_length.
  simpl. lia.
  destruct b.
  simpl. lia.
  inversion_clear H.
  simpl.
  remember (length (incr1 b0) =? length b0).
  rewrite <- H1.
  enough (b1 = false).
  rewrite H.
  simpl.
  enough ((length b0) < (length (incr1 b0))).
  lia.
  apply H0. simpl. auto. auto.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_neq.
  enough (length b0 < length (incr1 b0)).
  lia. apply H0. simpl. auto.
  auto.
Qed.

Lemma incr1_cons_over: forall b b0, length (incr1 (b :: b0)) <> length (b :: b0) -> 
        length (incr1 b0) <> length b0.
Proof.
  intros.
  generalize dependent b.
  induction b0 using list_ind_length; intros.
  simpl. lia.
  enough (length (b :: b0) < length (incr1 (b :: b0)) ).
  apply incr1_cons2 in H1.
  inversion_clear H1.
  remember (incr1_cons2_inv b0).
  apply l in H3. lia.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia.
  apply incr1_length.
Qed.


Lemma decr1_incr1: forall b, decr1 (incr1 b) = b.
Proof.
  intros.
  induction b using list_ind_length.
  simpl. auto.

  destruct b. simpl. auto.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b; destruct b1.
  all: simpl.
  all: try rewrite H.
  all: auto.
  - 
  remember (incr1 b0).
  destruct b.
  destruct b0. simpl in Heqb. discriminate. 
  simpl in Heqb.
  destruct b; destruct (length (incr1 b0) =? length b0); discriminate.
  replace (length b0 =? length (b :: b1)) with true. auto.
  rewrite Heqb1. apply PeanoNat.Nat.eqb_sym.
  - destruct b0. simpl. auto.
  rewrite <- incr1_tl_comm_E2.
  simpl tl.
  remember (incr1 b0).
  destruct b1.
  destruct b0. simpl in Heqb0. discriminate.
  simpl in Heqb0.
  destruct b0; destruct (length (incr1 b1) =? length b1); discriminate.
  rewrite Heqb0.
  rewrite H.
  replace (length b0 =? length (incr1 b0)) with false.
  replace b with E2. auto.
  enough (Forall (eq E2) (b::b0)).
  inversion H0. auto.
  apply incr1_cons2.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia. apply incr1_length.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  apply incr1_cons_over in Heqb1.
  symmetry.
  apply PeanoNat.Nat.eqb_neq. lia.
  simpl. auto.
  simpl. lia.
  apply incr1_cons2.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  enough (length (b :: b0) <= length (incr1 (b :: b0))).
  lia. apply incr1_length.
  - remember (incr1 b0).
  destruct b.
  destruct b0. simpl in Heqb. discriminate.
  simpl in Heqb.
  destruct b; destruct (length (incr1 b0) =? length b0); discriminate.
  replace (length b0 =? length (b :: b1)) with true.
  auto.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  - destruct b0. simpl. auto.
  remember (incr1 (b::b0)).
  destruct b1.
  simpl in Heqb0. 
  destruct b; destruct (length (incr1 b0) =? length b0); discriminate.
  rewrite Heqb0. rewrite Heqb0 in Heqb1.
  replace (length (b :: b0) =? length (incr1 (b :: b0))) with false.
  auto. rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
Qed.  

Lemma incr1_decr1: forall b,
  0 < length b -> incr1 (decr1 b) = b.
Proof.
  intros.
  induction b using list_ind_length.
  simpl in H. lia.

  destruct b. simpl in H. lia.
  simpl.
  destruct b0.
  destruct b. auto. auto.
  remember (length (decr1 (b0 :: b1)) =? length (b0 :: b1)).
  remember ((b0 :: b1)).
  destruct b; destruct b2.
  -
  simpl. rewrite H0.
  replace (length l =? length (decr1 l)) with true.
  auto.
  rewrite Heqb2.
  apply PeanoNat.Nat.eqb_sym. auto.
  rewrite Heql. simpl. lia.
  -
  simpl. rewrite H0.
  replace (length l =? length (decr1 l)) with false.
  auto.
  rewrite Heqb2.
  apply PeanoNat.Nat.eqb_sym. auto.
  rewrite Heql. simpl. lia.
  - simpl. rewrite H0.
  replace (length l =? length (decr1 l)) with true.
  auto.
  rewrite Heqb2.
  apply PeanoNat.Nat.eqb_sym. auto.
  rewrite Heql. simpl. lia.
  - simpl. rewrite H0.
  replace (length l =? length (decr1 l)) with false.
  simpl.
  replace (length l =? length (decr1 l)) with false. 
  auto.
  rewrite Heqb2.
  apply PeanoNat.Nat.eqb_sym. 
  rewrite Heqb2.
  apply PeanoNat.Nat.eqb_sym.
  auto.
  rewrite Heql. simpl. lia.
Qed.



Lemma incr1_length_plus: forall b, length b < length (incr1 b) ->
                                    S (length b) =  length (incr1 b).
Proof.
  intros.
  induction b using list_ind_length. auto.
  destruct b. auto.
  simpl. simpl in H.
  remember (length (incr1 b0) =? length b0) as q.
  destruct b; destruct q.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H.
  - exfalso. lia.
  - 
  exfalso. 
  remember (length b0 =? length (incr1 b0)).
  destruct b.
  symmetry in Heqb. apply PeanoNat.Nat.eqb_eq in Heqb.
  congruence.
  symmetry in Heqb. apply PeanoNat.Nat.eqb_neq in Heqb.
  enough (length b0 < length (incr1 b0)).
  apply H0 in H1; auto.
  rewrite H1 in H.
  destruct b0. simpl in H. lia.
  remember (incr1 (b :: b0)).
  destruct b1. 
  simpl in Heqb1.
  destruct b; destruct (length (incr1 b0) =? length b0); discriminate.
  simpl in H. lia.
  enough (length b0 <= length (incr1 b0)).
  lia. apply incr1_length.
  - enough (length b0 < length (incr1 b0)).
  apply H0 in H1; auto.
  lia.
  - enough (length b0 < length (incr1 b0)).
  apply H0 in H1; auto.
  lia.
Qed.


Lemma incr2_length: forall b, length b <= length (incr2 b).
Proof.
  induction b using list_ind_length.
  simpl. lia.
  destruct b. simpl. auto. 
  simpl.
  destruct b.
  -
  remember (length (incr2 b0) =? length b0).
  destruct b.
  + 
  destruct b0. simpl. auto.
  remember (b :: b0) as b1.
  enough (length b1 <= length (incr2 b1)).
  simpl. lia. apply H. simpl. auto.
  + destruct b0. simpl. auto.
  remember (b :: b0) as b1.
  symmetry in Heqb.
  apply PeanoNat.Nat.eqb_neq in Heqb.
  simpl.
  enough (length b1 < length (incr2 b1) ).
  destruct (incr2 b1); simpl. 
  destruct b1; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b1 <= length (incr2 b1)).
  lia. apply H. simpl. lia.
  - destruct b0. simpl. auto.
  remember (b :: b0) as b1.
  remember (length (incr2 b1) =? length b1).
  destruct b2.
  + enough (length b1 <= length (incr2 b1)).
  simpl. lia. apply H. simpl. auto.
  + symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  simpl.
  enough (length b1 < length (incr2 b1)).
  destruct (incr2 b1); simpl. 
  destruct b1; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b1 <= length (incr2 b1)).
  lia. apply H. simpl. lia.
Qed.

Lemma incr2_length_plus: forall b, length b < length (incr2 b) ->
                                    S (length b) =  length (incr2 b).
Proof.
  intros.
  induction b using list_ind_length. auto.
  destruct b. auto.
  simpl. simpl in H.
  remember (length (incr2 b0) =? length b0) as q.
  destruct b; destruct q.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H.
  - exfalso. destruct b0. simpl in Heqq. lia.
  remember (b :: b0) as b1. simpl in H. lia.
  - 
  destruct b0. simpl. auto.
  exfalso.
  remember (b :: b0) as b1. simpl in H. 
  remember (length b1 =? length (incr2 b1)).
  destruct b2.
  symmetry in Heqb2. apply PeanoNat.Nat.eqb_eq in Heqb2.
  congruence.
  symmetry in Heqb2. apply PeanoNat.Nat.eqb_neq in Heqb2.
  enough (length b1 < length (incr2 b1)).
  apply H0 in H1; auto.
  rewrite H1 in H.
  remember (incr2 b1).
  destruct b2. 
  simpl in Heqb2.
  destruct b1; simpl in H1; discriminate.
  simpl in H. lia.
  enough (length b1 <= length (incr2 b1)).
  lia. apply incr2_length.
  -
  destruct b0. simpl. auto.
  remember (b :: b0) as b1. 
  enough (length b1 < length (incr2 b1)).
  apply H0 in H1; auto. simpl. congruence.
  simpl in H. lia.
  -
  destruct b0. simpl. auto.
  remember (b :: b0) as b1. 
  enough (length b1 < length (incr2 b1)).
  apply H0 in H1; simpl; auto.
  simpl in H. lia.
Qed.

Lemma incr2_incr1_length: forall b, length (incr1 b) <= length (incr2 b).
Proof.
  induction b using list_ind_length.
  simpl. lia.
  destruct b. simpl. auto. 
  simpl.
  destruct b.
  all: destruct b0; auto.
  simpl. lia.
  all: remember b0 as b2. 
  all: clear Heqb2.
  all: clear b0.
  all: remember (b :: b2) as b0. 
  -
  remember (length (incr1 b0) =? length b0) as p.
  remember (length (incr2 b0) =? length b0) as q.
  destruct p; destruct q.
  + enough (length (incr1 b0) <= length (incr2 b0)).
  simpl. lia. apply H. simpl. auto.
  + symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_eq in Heqp.
  apply PeanoNat.Nat.eqb_neq in Heqq.
  simpl.
  enough (length (incr1 b0) < length (incr2 b0) ).
  destruct (incr2 b0); simpl. 
  destruct b0; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b0 <= length (incr2 b0)).
  enough (length b0 <= length (incr1 b0)).
  lia. apply incr1_length. apply incr2_length.
  + symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_neq in Heqp.
  apply PeanoNat.Nat.eqb_eq in Heqq.
  exfalso.
  enough (length b0 <= length (incr2 b0)).
  enough (length b0 <= length (incr1 b0)).
  enough (length (incr1 b0) <= length (incr2 b0)).
  lia. apply H. auto. apply incr1_length. apply incr2_length.
  +  symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_neq in Heqp.
  apply PeanoNat.Nat.eqb_neq in Heqq.
  simpl.
  enough (length (incr1 b0) <= length (incr2 b0)).
  destruct (incr1 b0) ; destruct (incr2 b0); try lia; auto.
  simpl. destruct b1; simpl; lia.
  apply H; auto.
  - remember (length (incr1 b0) =? length b0) as p.
  remember (length (incr2 b0) =? length b0) as q.
  destruct p; destruct q.
  + enough (length (incr1 b0) <= length (incr2 b0)).
  simpl. lia. apply H. simpl. auto.
  + symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_eq in Heqp.
  apply PeanoNat.Nat.eqb_neq in Heqq.
  simpl.
  enough (length (incr1 b0) < length (incr2 b0) ).
  destruct (incr2 b0); simpl. 
  destruct b0; simpl in H0; lia.
  simpl in H0. lia.
  enough (length b0 <= length (incr2 b0)).
  enough (length b0 <= length (incr1 b0)).
  lia. apply incr1_length. apply incr2_length.
  + symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_neq in Heqp.
  apply PeanoNat.Nat.eqb_eq in Heqq.
  exfalso.
  enough (length b0 <= length (incr2 b0)).
  enough (length b0 <= length (incr1 b0)).
  enough (length (incr1 b0) <= length (incr2 b0)).
  lia. apply H. auto. apply incr1_length. apply incr2_length.
  +  symmetry in Heqp. symmetry in Heqq.
  apply PeanoNat.Nat.eqb_neq in Heqp.
  apply PeanoNat.Nat.eqb_neq in Heqq.
  simpl.
  enough (length (incr1 b0) <= length (incr2 b0)).
  destruct (incr1 b0) ; destruct (incr2 b0); try lia; auto.
  apply H; auto.
Qed.  


Lemma incr1_E1: forall b, 0 < length b -> Forall (eq E1) b -> 
    length b = length (incr1 b).
Proof.
    induction b using list_ind_length; intros. 
    simpl in H. lia.
    destruct b. simpl. simpl in H0. lia.
    inversion_clear H1.
    simpl.
    remember (length (incr1 b0) =? length b0) as q.
  destruct b; destruct q.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H0.
  - lia.
  - enough (length b0 < length (incr1 b0)).
  apply incr1_length_plus in H1.
  rewrite H1.
  destruct (incr1 b0). simpl in H1.
  lia. simpl. auto.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
  - congruence.
  - discriminate.
Qed.  

Lemma incr2_incr1: forall b, incr1 (incr1 b) = incr2 b.
Proof.
  induction b using list_ind_length.
  auto.
  destruct b. simpl. auto. simpl.

  destruct b0. simpl.
  destruct b; auto.

  all: remember b0 as b2. 
  all: clear Heqb2.
  all: clear b0.
  all: remember (b2 :: b1) as b0. 

  remember (length (incr1 b0) =? length b0) as q1.
  remember (length (incr2 b0) =? length b0) as q2.

  destruct b; destruct q1; destruct q2; simpl. 
  all: try rewrite H; auto.

  all: symmetry in Heqq1. 
  all: symmetry in Heqq2. 
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq1 | apply PeanoNat.Nat.eqb_neq in Heqq1 ].
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq2 | apply PeanoNat.Nat.eqb_neq in Heqq2 ].

  - 
  replace (length (incr2 b0) =? length (incr1 b0)) with true. auto.
  symmetry. apply PeanoNat.Nat.eqb_eq. congruence.

  -
  replace (length (incr2 b0) =? length (incr1 b0)) with false. auto. 
  symmetry. apply PeanoNat.Nat.eqb_neq. congruence.

  - exfalso.
  enough (length b0 <= length (incr1 b0)).
  enough (length b0 <= length (incr2 b0)).
  enough (length (incr1 b0) <= length (incr2 b0)).
  lia.
  apply incr2_incr1_length.
  apply incr2_length.
  apply incr1_length.
  
  - replace (length (incr1 (tl (incr1 b0))) =? length (tl (incr1 b0))) with true.
  destruct b0. simpl. discriminate.
  destruct b0. simpl. destruct b; auto.
  rewrite <- H.
  rewrite incr1_tl_comm_E1; auto.
  enough (length (b :: b0 :: b3) <= length (incr1 (b :: b0 :: b3))).
  simpl in H0. simpl. lia.
  apply incr1_length.
  apply incr1_cons1.
  enough (length (b :: b0 :: b3) <= length (incr1 (b :: b0 :: b3))).
  lia.  apply incr1_length.
  simpl. lia.
  symmetry.
  apply PeanoNat.Nat.eqb_eq .
  rewrite <- incr1_E1. auto.
  rewrite Heqb0.
  simpl.
  destruct b2; destruct (length (incr1 b1) =? length b1); simpl; auto.
  + destruct b1. simpl. auto. 
    simpl. destruct (length (incr1 b1) =? length b1); destruct b; simpl; try lia.
  + rewrite Heqb0 in Heqq1.
  enough (length (E1 :: b1) < length (incr1 (E1 :: b1)))  .
  apply incr1_cons2 in H0.
  inversion H0. discriminate.
  enough (length (E1 :: b1) <= length (incr1 (E1 :: b1))).
  lia.
  apply incr1_length.
  + destruct b1. auto.
  simpl. destruct b; destruct (length (incr1 b1) =? length b1); simpl; lia.
  + destruct b1. auto.
  simpl. destruct b; destruct (length (incr1 b1) =? length b1); simpl; lia.
  + 
  enough (length b0 < length (incr1 b0)).
  apply incr1_cons1 in H0.
  destruct (incr1 b0).
  auto.
  inversion H0. simpl. auto.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
  - replace (length (incr2 b0) =? length (incr1 b0)) with true.
  auto.
  symmetry. apply PeanoNat.Nat.eqb_eq. congruence.
  - replace (length (incr2 b0) =? length (incr1 b0)) with false.
  auto.
  symmetry. apply PeanoNat.Nat.eqb_neq. congruence.
  - exfalso.
  enough (length b0 < length (incr1 b0)).
  enough (length (incr1 b0) <= length (incr2 b0)).
  lia.
  apply incr2_incr1_length.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
  - replace (length (incr2 b0) =? length (incr1 b0)) with true.
  auto.
  symmetry. apply PeanoNat.Nat.eqb_eq.
  rewrite <- incr1_length_plus.
  rewrite <- incr2_length_plus.
  auto.
  enough (length b0 <= length (incr2 b0)).
  lia.
  apply incr2_length.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
Qed.


Lemma iter_decr1_nil: forall n, iter n decr1 [] = [].
Proof.
  intros.
  induction n; intros.
  simpl. auto.
  simpl. auto.
Qed.


Lemma decr1_length: forall a, length (decr1 a) <= length a.
Proof.
  intros.
  destruct a.
  simpl. lia.
  remember (b::a) as a'.
  rewrite <- incr1_decr1 with (b:=a') at 2.
  apply incr1_length.
  rewrite Heqa'.
  simpl. lia.
Qed.

Lemma incr2_in_next: forall y b, length (incr1 y) = length y ->
length (incr2 (y++[b])) = length (y ++[b]).
Proof.
  intros.
  generalize dependent b.
  induction y using list_ind_length; intros.
  simpl in H.
  lia.
  destruct y.
  simpl in H. lia.
  simpl.
  simpl in H.
  remember (length (incr1 y) =? length y).
  remember (length (incr2 (y ++ [b])) =? length (y ++ [b])).
  remember (y++[b]).
  destruct l.
  destruct y; simpl in Heql; discriminate.
  rewrite Heql.
  rewrite Heql in Heqb2.
  destruct b0; destruct b1; destruct b2.
  - (*8*)
  simpl in H.
  simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  lia.
  - (*7*)
  simpl in H.
  simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  inversion H.
  apply H0  with (b:=b) in H2.
  contradiction.
  simpl. lia.
  - (*6*)
  simpl in H.
  simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  lia.
  - (*5*)
  simpl in H.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  simpl.
  enough (length (incr2 (y ++ [b])) = S (length (y ++ [b]))).
  destruct (incr2 (y ++ [b])).
  simpl in H1.
  lia.
  simpl in H1. simpl.
  lia.
  rewrite incr2_length_plus.
  auto.
  enough (length (y ++ [b]) <= length (incr2 (y ++ [b]))).
  lia.
  apply incr2_length.
  - (*4*)
  simpl in H.
  simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  lia.
  - (*3*)
  simpl in H.
  inversion H.
  apply H0 with (b:=b) in H2 .
  simpl. lia.
  simpl. lia.
  - (*2*)
  simpl in H. simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  lia.
  - (*1*)
  simpl in H. simpl.
  symmetry in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  inversion H.
  apply H0  with (b:=b) in H2.
  contradiction.
  simpl. lia.
Qed.



Lemma incr2_in_next_inv: forall y b,  
length (incr2 (y++[b])) = length (y ++[b]) -> 
length (incr1 y) = length y.
Proof.
  intros.
  generalize dependent b.
  induction y using list_ind_length; intros.
  simpl. simpl in H.
  destruct b. 
  simpl in H. lia.
  simpl in H. lia.
  destruct y.
  simpl in H0. 
  destruct b; simpl in H0; lia.
  simpl.
  simpl in H0.
  remember (length (incr1 y) =? length y).
  remember (length (incr2 (y ++ [b])) =? length (y ++ [b])).
  remember (y++[b]).
  destruct l.
  destruct y; simpl in Heql; discriminate.
  rewrite Heql in H0.
  rewrite Heql in Heqb2.
  destruct b0; destruct b2; destruct b1.
  - (*8*)
  simpl in H0.
  simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  lia.
  - (*7*)
  simpl in H0.
  simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  inversion H0.
  apply H with (b:=b) in H2.
  contradiction.
  simpl. lia.
  - (*6*)
  simpl in H0.
  simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  lia.
  - (*5*)
  simpl in H0.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  simpl.
  enough (length (incr1 y) = S (length y)).
  destruct (incr1 y).
  simpl in H1.
  lia.
  simpl in H1. simpl.
  lia.
  rewrite incr1_length_plus.
  auto.
  enough (length y <= length (incr1 y)).
  lia.
  apply incr1_length.
  - (*4*)
  simpl in H0.
  simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  lia.
  - (*3*)
  simpl in H0.
  inversion H0.
  apply H with (b:=b) in H2 .
  simpl. lia.
  simpl. lia.
  - (*2*)
  simpl in H0. simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  lia.
  - (*1*)
  simpl in H0. simpl.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  inversion H0.
  apply H with (b:=b) in H2.
  contradiction.
  simpl. lia.
Qed.


Lemma iter_incr1_tail_helper1: forall b y, 
incr2 (y ++ [b]) = incr1 y ++ [b].
Proof.
  intros.
  generalize dependent b.
  induction y using list_ind_length; intros.
  simpl.
  destruct b; auto.
  destruct y.
  destruct b; auto.
  simpl.
  remember (y ++ [b]).
  destruct l.
  destruct y; simpl in Heql; discriminate.
  remember (length (incr2 (b1 :: l)) =? length (b1 :: l)).
  remember (length (incr1 y) =? length y).
  destruct b0; destruct b2; destruct b3.
  - (*8*)
  rewrite Heql.
  rewrite H.
  auto.
  simpl. lia.
  -(*7*)
  rewrite Heql in Heqb2.
  symmetry in Heqb2. symmetry in Heqb3.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  apply PeanoNat.Nat.eqb_neq in Heqb3.
  apply incr2_in_next_inv in Heqb2.
  contradiction.
  -(*6*)
  rewrite Heql in Heqb2.
  symmetry in Heqb2. symmetry in Heqb3.
  apply PeanoNat.Nat.eqb_eq in Heqb3.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  apply incr2_in_next with (b:=b) in Heqb3.
  contradiction.
  -(*5*)
  rewrite Heql in Heqb2.
  rewrite Heql.
  rewrite H.
  remember (incr1 y).
  destruct b0.
  simpl.
  exfalso.
  destruct y. simpl in Heqb0. discriminate.
  simpl in Heqb0.
  destruct b0; destruct (length (incr1 y) =? length y); discriminate.
  simpl.
  auto.
  simpl. lia.
  -(*4*)
  rewrite Heql.
  rewrite H.
  auto.
  simpl. lia.
  - (*3*)
  rewrite Heql in Heqb2.
  symmetry in Heqb2. symmetry in Heqb3.
  apply PeanoNat.Nat.eqb_neq in Heqb3.
  apply PeanoNat.Nat.eqb_eq in Heqb2.
  apply incr2_in_next_inv in Heqb2.
  contradiction.
  - (*2*)
  rewrite Heql in Heqb2.
  symmetry in Heqb2. symmetry in Heqb3.
  apply PeanoNat.Nat.eqb_eq in Heqb3.
  apply PeanoNat.Nat.eqb_neq in Heqb2.
  apply incr2_in_next with (b:=b) in Heqb3.
  contradiction.
  -(*1*)
  rewrite Heql in Heqb2.
  rewrite Heql.
  rewrite H.
  remember (incr1 y).
  destruct b0.
  simpl. auto. auto.
  simpl. lia.
Qed.  



Lemma iter_incr1_tail_helper2: forall b y n1, 
n1 <= length y ->
incr2 (b :: firstn n1 y) ++ skipn n1 y = incr1 (firstn n1 (b :: y)) ++ skipn n1 (b :: y).
Proof.
  intros.
  remember (firstn n1 (b :: y)).
  enough (exists x, b :: firstn n1 y = l ++ [x]).
  destruct H0.
  rewrite H0.
  rewrite iter_incr1_tail_helper1.
  rewrite app_ass.
  enough ([x] ++ skipn n1 y =  skipn n1 (b :: y)).
  rewrite H1. auto.
  subst l.
  generalize dependent y.
  generalize dependent b.
  generalize dependent x.
  induction n1; intros.
  simpl.
  simpl in H0.
  inversion H0. auto.
  destruct y.
  simpl in H. lia.
  simpl in H0.
  enough (b0 :: firstn n1 y = firstn n1 (b0 :: y) ++ [x]).
  apply IHn1 in H1.
  simpl.
  simpl in H1. auto.
  simpl in H. lia.
  inversion H0. auto.
  subst l.
  generalize dependent y.
  generalize dependent b.
  induction n1; intros.
  simpl.
  exists b. auto.
  destruct y.
  simpl in H. lia.
  simpl in H.
  enough (n1 <=length y).
  simpl.
  apply IHn1 with (b:=b0) in H0.
  destruct H0.
  rewrite H0.
  exists x.
  auto.
  lia.
Qed. 
  

Lemma iter_incr1_tail_helper3: forall n1 b y, n1 <= length y ->
exists (h : binary) (t : list binary), skipn n1 (b :: y) = h :: t.
Proof.
  intros.
  generalize dependent b.
  generalize dependent y.
  induction n1; intros.
  simpl.
  exists b, y. auto.
  destruct y.
  simpl in H. lia.
  simpl.
  simpl in H.
  enough (n1 <= length y).
  apply IHn1 with (b:=b0) in H0.
  destruct H0.
  destruct H0.
  rewrite H0.
  exists x,x0. auto.
  lia.
Qed.


Lemma iter_incr1_tail: forall y n,
n <= length y ->
iter (pow 2 n) incr1 y = (incr1 (firstn (length y - n) y)) ++ 
                          (skipn (length y - n) y) /\
iter (pow 2 n + pow 2 n) incr1 y = (incr2 (firstn (length y - n) y)) ++ 
                          (skipn (length y - n) y) .                       
Proof.
    intros.
    generalize dependent y.
    induction n ; intros.
    simpl.
    replace (length y - 0) with (length y).
    rewrite firstn_all_length.
    rewrite skipn_all_length.
    rewrite ?app_nil_r.
    split.
    auto.
    rewrite incr2_incr1. auto.
    lia.

    destruct y.
    simpl.
    simpl in H.
    lia.
    simpl in H.
    simpl.
    replace ((2 ^ n + (2 ^ n + 0))) with (2 ^ n + 2 ^ n ); [| lia].
    split.
    - (*2*)
    assert (iter (2 ^ n + 2 ^ n) incr1 (b::y) = incr2 (firstn (length (b::y) - n) (b::y)) ++ skipn (length (b::y) - n) (b::y)).
    apply IHn.
    simpl. lia.
    rewrite H0.
    remember (length (b :: y) - n).
    remember (length y - n).
    assert (S n1 = n0).
    rewrite Heqn0. rewrite Heqn1. simpl.
    destruct n. lia. lia.
    rewrite <- H1.
    Opaque incr2 incr1.
    simpl. 
    Transparent incr2 incr1.
    apply iter_incr1_tail_helper2.
    lia.
    - (*1*)
    rewrite iter_plus.
    assert (iter (2 ^ n + 2 ^ n) incr1 (b::y) = incr2 (firstn (length (b::y) - n) (b::y)) ++ skipn (length (b::y) - n) (b::y)).
    apply IHn.
    simpl. lia.
    rewrite  H0.
    simpl length.
    replace (S (length y) - n) with (S (length y - n)); [|lia].
    simpl firstn.
    simpl skipn.
    remember (incr2 (b :: firstn (length y - n) y) ++ skipn (length y - n) y).
    assert (iter (2 ^ n + 2 ^ n) incr1 l = incr2 (firstn (length l - n) l) ++ skipn (length l - n) l).
    apply IHn.
    all: cycle 1.
    rewrite H1.
    rewrite iter_incr1_tail_helper2 in Heql; [| lia].
    remember (length l - n).
    remember (length y - n).
    rewrite Heql.
    simpl.
    enough (length l > length y) as H10.
    enough (length (skipn n1 (b :: y)) = S n).
    enough (length (incr1 (firstn n1 (b :: y))) = length l - S n).
    enough (exists h t, skipn n1 (b :: y) = h::t).
    destruct H4.
    destruct H4.
    enough (skipn n0 (incr1 (firstn n1 (b :: y)) ++ skipn n1 (b :: y)) = x0).
    rewrite H5.
    enough (firstn n0 (incr1 (firstn n1 (b :: y)) ++ skipn n1 (b :: y)) = incr1 (firstn n1 (b :: y)) ++ [x] ).
    rewrite H6.
    rewrite H4.
    rewrite iter_incr1_tail_helper1.
    rewrite incr2_incr1.
    rewrite app_ass.
    auto.
    remember (incr1 (firstn n1 (b :: y))).
    enough (length b0  = n0 - 1).
    rewrite firstn_app.
    rewrite firstn_all2.
    rewrite H6.
    rewrite H4.
    replace (n0 - (n0 - 1)) with 1.
    simpl. auto.
    enough (n0 >= 1).
    lia.
    subst n0.
    lia.
    lia.
    lia.
    rewrite H4.
    rewrite skipn_app.
    rewrite skipn_all2.
    rewrite H3.
    rewrite Heqn0.
    replace (length l - n - (length l - S n)) with 1.
    simpl. auto.
    lia.
    lia.
    apply iter_incr1_tail_helper3.
    lia.
    assert (length l = length (incr1 (firstn n1 (b :: y))) + S n).
    rewrite Heql.
    rewrite <- H2.
    rewrite app_length. auto.
    lia.
    rewrite Heqn1.
    rewrite skipn_length.
    simpl length.
    lia.
    rewrite Heql.
    rewrite app_length.
    enough (length (incr1 (firstn n1 (b :: y))) >= length (firstn n1 (b :: y))).
    enough  (length ((firstn n1 (b :: y))) + length (skipn n1 (b :: y)) > length y).
    lia.
    rewrite <- app_length.
    rewrite firstn_skipn. simpl. lia.
    apply incr1_length.
    rewrite Heql.
    rewrite app_length.
    enough (length (incr2 (b :: firstn (length y - n) y)) >= length ( (b :: firstn (length y - n) y))) .
    enough (length (incr2 (b :: firstn (length y - n) y)) +
    length (skipn (length y - n) y) >= length y).
    lia.
    enough (length ( (b :: firstn (length y - n) y)) +
    length (skipn (length y - n) y) = S (length y)).
    lia.
    simpl length . simpl.
    rewrite <- app_length.
    rewrite firstn_skipn.
    auto.
    apply incr2_length.   
Qed.


Lemma iter_decr1_incr1: forall b n, 
iter n decr1 (iter n incr1 b) = b.
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  simpl. auto.
  rewrite iterS. simpl.
  rewrite IHn.
  rewrite decr1_incr1.
  auto.
Qed.

Lemma iter_incr1_tail1: forall y,
iter (pow 2 (length y)) incr1 y = E1::y.
Proof.
  intros.
  remember (iter_incr1_tail y (length y)).
  assert (iter (2 ^ length y) incr1 y = incr1 (firstn (length y - length y) y) ++ skipn (length y - length y) y).
  apply a. lia.
  rewrite H.
  replace (length y - length y)  with 0.
  simpl. auto.
  lia.
Qed.

Lemma iter_incr1_tail2: forall y,
iter (pow 2 (length y) + pow 2 (length y)) incr1 y = E2::y.
Proof.
  intros.
  remember (iter_incr1_tail y (length y)).
  assert (iter (2 ^ length y + 2 ^ length y) incr1 y =
  incr2 (firstn (length y - length y) y) ++ skipn (length y - length y) y).
  apply a. lia.
  rewrite H.
  replace (length y - length y)  with 0.
  simpl. auto.
  lia.
Qed.

Lemma remove_head1: forall b y, exists n,
  iter n decr1 (b::y) = y. 
Proof.
  intros.
  destruct b.
  exists (2^(length y)).
  rewrite <- iter_incr1_tail1.
  rewrite iter_decr1_incr1. auto.
  exists (2^(length y) + 2^(length y)).
  rewrite <- iter_incr1_tail2.
  rewrite iter_decr1_incr1. auto.
Qed.

Lemma skipn_n: forall {X} (b : list X),
  skipn (length b - 0) b = [] .
Proof.
  induction b.
  auto.
  simpl.
  rewrite PeanoNat.Nat.sub_0_r  with (length b) in IHb.
  auto.
Qed.

Lemma firstn_n: forall {X} (b : list X),
  firstn (length b) b = b.
Proof.
  induction b.
  auto.
  simpl.
  rewrite IHb. auto.
Qed.

Lemma decr1_E2_snoc_length: forall x,
true = (length (decr1 (x ++ [E2])) =? length (x ++ [E2])).
Proof.
  intros.

  induction x using list_ind_length.
  simpl. auto.
  destruct x. simpl. auto.
  simpl.

  rewrite <- H.

  remember (snoc_cons x E2). clear Heqe.
  inversion_clear e. inversion_clear H0.
  rewrite H1.
  destruct b.
  rewrite <- H1.
  simpl. auto.
  rewrite <- H1.
  simpl. auto.
  simpl. lia.
Qed.


(* #[ using = "snoc_cons" ] *)
Lemma decr1_E2_snoc: forall x, decr1 (x ++ [E2]) = x ++ [E1].
Proof.
  intros.
  induction x using list_ind_length.
  simpl. auto.
  destruct x. simpl. auto.
  simpl. 
  replace (length (decr1 (x ++ [E2])) =? length (x ++ [E2])) with true.
  remember (snoc_cons x E2).
  clear Heqe.
  inversion_clear e.
  inversion_clear H0.
  rewrite H1.
  rewrite <- H1.
  rewrite H.
  destruct b; auto.
  simpl. lia.
  apply decr1_E2_snoc_length.
Qed.

Lemma incr1_E1_snoc: forall x, incr1 (x ++ [E1]) = x ++ [E2].
Proof.
  intros.
  rewrite <- decr1_E2_snoc.
  apply incr1_decr1.
  rewrite app_length.
  simpl. lia.
Qed.

Lemma decr1_E1_snoc: forall x, 
0 < length x ->
decr1 (x ++ [E1]) = (decr1 x) ++ [E2].
Proof.
  intros.
  induction x using list_ind_length.
  simpl in H. lia.

  destruct x. simpl in H. lia.
  simpl.
  remember (snoc_cons x E1).
  clear Heqe.
  inversion_clear e.
  inversion_clear H1.
  rewrite H2.
  rewrite <- H2.
  remember (length (decr1 (x ++ [E1])) =? length (x ++ [E1])).
  remember (length (decr1 x) =? length x).
  destruct b. destruct b0. destruct x. simpl.
  simpl in Heqb0. discriminate.
  destruct b1.
  rewrite H0. auto.
  simpl. lia. simpl. lia.
  exfalso.
  rewrite H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  remember (b::x).
  simpl in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  replace (length (decr1 l)) with (length l) in Heqb1.
  symmetry in Heqb1.
  rewrite PeanoNat.Nat.eqb_refl in Heqb1. 
  discriminate.
  lia.
  simpl. lia.
  simpl. lia.
  destruct x.
  simpl. auto.
  destruct b1.
  exfalso.
  rewrite H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  remember (b::x).
  simpl in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_neq in Heqb0.
  replace (length (decr1 l)) with (length l) in Heqb0.
  contradiction.
  apply PeanoNat.Nat.eqb_eq.
  rewrite Heqb1.
  apply PeanoNat.Nat.eqb_sym.
  simpl. lia.
  simpl. lia.
  rewrite H0.
  auto.
  simpl. lia.
  simpl. lia.
  destruct b0.
  destruct x.
  simpl.
  simpl in Heqb0. discriminate.
  destruct b1.
  rewrite H0. auto.
  simpl. lia.
  simpl. lia.
  exfalso.
  rewrite H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  remember (b::x).
  replace (length (decr1 l)) with (length l) in Heqb1.
  rewrite PeanoNat.Nat.eqb_refl in Heqb1.
  discriminate.
  simpl in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  lia.
  simpl. lia.
  simpl. lia.
  destruct x.
  simpl. auto.
  destruct b1.
  exfalso.
  rewrite H0 in Heqb0.
  remember (b::x).
  rewrite ?app_length in Heqb0.
  simpl in Heqb0.
  symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  rewrite Heqb1 in Heqb0.
  symmetry in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  simpl. lia.
  simpl. lia.
  rewrite H0.
  auto.
  simpl. lia.
  simpl. lia.
Qed.  

Lemma incr1_E2_snoc: forall x, 
incr1 (x ++ [E2]) = (incr1 x) ++ [E1].
Proof.
  intros.
  replace (incr1 x ++ [E1]) with (incr1 (decr1 (incr1 x ++ [E1]))).
  rewrite decr1_E1_snoc.
  rewrite decr1_incr1. auto.
  destruct x.
  simpl. lia.
  simpl.
  destruct b; destruct (length (incr1 x) =? length x); simpl; lia.
  rewrite incr1_decr1. auto.
  rewrite app_length.
  simpl. lia.
Qed.

Lemma decr1_ge2digit: forall a b x, 0 < length (decr1 (a :: b :: x)).
Proof.
  intros.
  remember (decr1 (a::b::x)).
  assert (a :: b :: x = incr1 l).
  rewrite Heql.
  rewrite incr1_decr1.
  auto.
  simpl. lia.
  assert (length l <= length (a::b::x)).
  rewrite H.
  apply incr1_length.
  assert (length l < length (a::b::x) \/ length l = length (a::b::x)).
  lia.
  inversion_clear H1.
  rewrite H in H2.
  apply length_le_S in H2.
  rewrite <- H in H2.
  simpl in H2. lia.
  simpl in H2. lia.
Qed.

Lemma decr2_ge2digit: forall a b x, 0 < length (decr1 (decr1 (a :: b :: x))).
Proof.
  intros.
  remember (decr1 (decr1 (a::b::x))).
  assert (a :: b :: x = incr1 (incr1 l)).
  rewrite Heql.
  repeat rewrite incr1_decr1.
  auto.
  simpl. lia.
  apply decr1_ge2digit.
  assert (length (incr1 l) <= length (a::b::x)).
  rewrite H.
  apply incr1_length.
  assert (length l  <= length (incr1 l)).
  apply incr1_length.
  assert (length l < length (incr1 l) \/ length l = length (incr1 l)).
  lia.
  assert (length (incr1 l) < length (a :: b :: x) \/ length (incr1 l) = length (a::b::x)).
  lia.
  clear H0 H1.
  inversion_clear H2; inversion_clear H3.
  - apply incr1_cons1 in H0.
  rewrite H in H1.
  apply incr1_cons2 in H1.
  exfalso.
  destruct (incr1 l).
  inversion H.
  inversion H0. inversion H1.
  rewrite <- H4 in H8.
  discriminate.
  - simpl in H1.
  apply length_le_S in H0.
   lia.
  - rewrite H in H1. 
  apply length_le_S in H1.
  rewrite <- H in H1.
  simpl in H1.
   lia.
  - simpl in H1.
  lia. 
Qed.

Lemma firstn_snoc: forall {X} x m (a:X), 
m <= length x ->
firstn m x = firstn m (x ++ [a]).
Proof.
  intros.
  generalize dependent x.
  generalize dependent a.
  induction m; intros.
  simpl. auto.
  destruct x. simpl in H. lia.
  simpl in H. 
  assert (m <= length x0) by  lia.
  simpl.
  erewrite IHm.
  reflexivity. auto.
Qed.


Lemma skipn_snoc: forall {X} x m (a:X), 
m <= length x ->
skipn m (x++[a]) = skipn m x ++ [a].
Proof.
  intros.
  generalize dependent x.
  generalize dependent a.
  induction m; intros.
  simpl. auto.
  destruct x. simpl in H. lia.
  simpl in H. 
  assert (m <= length x0) by  lia.
  simpl.
  erewrite IHm.
  reflexivity. auto.
Qed.

Lemma decr1_nil: forall b, decr1 b = [] ->  b = [] \/ b = [E1].
Proof.
  intros.
  destruct b. left. auto.
  destruct b0. 
  destruct b. right. auto.
  discriminate.
  remember (decr1_ge2digit b b0 b1).
  clear Heql.
  rewrite H in l.
  simpl in l. lia.  
Qed.


Lemma incr1_cons1_inv: forall b,
Forall (eq E1) (incr1 b) -> length b  < length (incr1 b).
Proof.
  intros.
  induction b using list_ind_length.
  simpl. lia.
  destruct b.
  simpl. lia.
  remember (cons_snoc b0 b).
  clear Heqe.
  inversion_clear e. inversion_clear H1.
  rewrite <- H2 in H.
  destruct x.
  -
  rewrite incr1_E1_snoc in H.
  exfalso.
  revert H.
  generalize x0.
  intros.
  induction x1.
  inversion H. discriminate.
  inversion H.
  apply IHx1. auto.
  -
  rewrite incr1_E2_snoc in H.
  rewrite <- H2.
  rewrite incr1_E2_snoc.

  enough (Forall (eq E1) (incr1 x0)).
  apply H0 in H1.
  rewrite ?app_length.
  simpl. lia.
  rewrite <- H2.
  rewrite app_length.
  simpl. lia.

  remember (incr1 x0).
  revert H.
  generalize b1.
  intros.
  induction b2.
  auto.
  inversion H.
  constructor. auto.
  apply IHb2.
  auto.
Qed.

Lemma decr1_in_tail: forall l b b',
l ++ b = decr1 (l ++ b') -> 
b = decr1 b'.
Proof.
  intros.
  generalize dependent b.
  generalize dependent b'.
  induction l using list_ind_length; intros.
  simpl in H.
  auto.
  destruct l.
  auto.

  simpl in H0.
  destruct b0.
  -
  remember (l++b').
  destruct l0.
  +
  discriminate.
  +
  remember (length (decr1 (b0 :: l0)) =? length (b0 :: l0)).
  destruct b1.
  Opaque decr1.
  inversion H0.
  Transparent decr1.
  rewrite Heql0 in H2.
  apply H in H2.
  auto.
  simpl. lia.
  Opaque decr1.
  inversion H0.
  Transparent decr1.
  -
  remember (l++b').
  destruct l0.
  +
  discriminate.
  +
  remember (length (decr1 (b0 :: l0)) =? length (b0 :: l0)).
  destruct b1.
  Opaque decr1.
  inversion H0.
  Transparent decr1.
  rewrite Heql0 in H2.
  apply H in H2.
  auto.
  simpl. lia.
  Opaque decr1.
  inversion H0.
  Transparent decr1.
Qed.

Lemma decr1_cons1: forall b, length (decr1 b) < length b ->  Forall (eq E1) b.
Proof.
  intros.
  destruct b.
  auto.
  remember (b::b0).
  replace l with (incr1(decr1 l)).
  apply incr1_cons1.
  rewrite incr1_decr1.
  auto.
  rewrite Heql.
  simpl. lia.
  apply incr1_decr1.
  rewrite Heql. simpl. lia.
Qed.

Lemma decr1_cons1_inv: forall b, 
0 < length b ->
Forall (eq E1) b -> length (decr1 b) < length b .
Proof.
  intros.
  destruct b.
  auto.
  remember (b::b0).
  remember (decr1 l).
  enough (l = incr1 l0).
  rewrite H1.
  rewrite H1 in H0.
  apply incr1_cons1_inv.
  auto.
  rewrite Heql0.
  symmetry.
  apply incr1_decr1.
  rewrite Heql. simpl. lia.
Qed.

Lemma decr1_cons2_inv: forall b, 
0 < length b ->
Forall (eq E2) (decr1 b) -> length (decr1 b) < length b .
Proof.
  intros.
  destruct b.
  auto.
  remember (b::b0).
  remember (decr1 l).
  enough (l = incr1 l0).
  rewrite H1.
  apply incr1_cons2_inv.
  auto.
  rewrite Heql0.
  symmetry.
  apply incr1_decr1.
  rewrite Heql. simpl. lia.
Qed.


Lemma decr1_cons2: forall b, length (decr1 b) < length b ->  Forall (eq E2) (decr1 b).
Proof.
  intros.
  destruct b.
  simpl. auto.
  remember (decr1 (b :: b0)).
  apply incr1_cons2.
  rewrite Heql.
  rewrite incr1_decr1.
  rewrite Heql in H.
  auto.
  simpl. lia.
Qed.

Lemma decr1_length_plus : forall b : list binary,
length (decr1 b) < length b -> S (length (decr1 b)) = length b .
Proof.
  intros.
  remember (decr1 b).
  destruct b.
  simpl in H. lia.
  remember (b::b0).
  enough (l0 = incr1 l).
  rewrite H0.
  apply incr1_length_plus.
  rewrite H0 in H.
  auto.
  rewrite Heql.
  symmetry.
  apply incr1_decr1.
  rewrite Heql0.
  simpl. lia.
Qed.

Lemma ForallE2_not_ForallE1_decr1: forall b, 
1 < length b ->
Forall (eq E2) b ->
~ Forall (eq E1) (decr1 b).
Proof.
  intros.
  unfold not.
  intros.
  induction b using list_ind_length.
  simpl in H. lia.
  destruct b.
  simpl in H. lia.
  destruct b0.
  simpl in H. lia.
  simpl in H1.
  inversion H0.
  inversion H6.
  rewrite <- H5 in H1.
  rewrite <- H9 in H1.
  destruct b1.
  simpl in H1.
  inversion H1.
  discriminate.
  rewrite <- H8 in H1.
  remember (length (decr1 l0) =? length l0).
  destruct b3.
  remember (length (E2 :: decr1 l0) =? S (length l0)).
  destruct b3.
  inversion H1.
  discriminate.
  inversion_clear H1.
  inversion_clear H12.
  discriminate.
  remember (length (E1 :: E2 :: decr1 l0) =? S (length l0)).
  destruct b3.
  inversion H1.
  discriminate.
  inversion H1.
  inversion H14.
  discriminate.
Qed.

Lemma decr1_ltlength_S : forall b, 
false = (length (decr1 b) =? length b) ->
S (length (decr1 b)) = length b.
Proof.
  intros.
  apply decr1_length_plus.
  enough (length (decr1 b) < length b \/ length (decr1 b) = length b).
  inversion_clear H0; auto.
  exfalso.
  rewrite H1 in H.
  rewrite PeanoNat.Nat.eqb_refl in H.
  discriminate.
  enough (length (decr1 b) <= length b).
  lia.
  apply decr1_length.
Qed.

Lemma decr1_special: forall b b',
length b = length b' ->
Forall (eq E2) b ->
Forall (eq E1) b' ->  
E1 :: b = decr1 (E2 :: b').
Proof.
  intros.
  generalize dependent b.
  induction b' using list_ind_length; intros.
  destruct b; auto.
  simpl in H. lia.

  destruct b'; destruct b; auto.
  simpl in H0. lia.
  simpl in H0. lia.
  inversion H1.
  rewrite <- H5.
  inversion H2.
  rewrite <- H9.
  simpl.

  destruct b'.
  simpl.
  assert (b1=[]).
  destruct b1; auto.
  simpl in H0. lia.
  rewrite H11.
  auto.

  rewrite <- H4 in *.
  enough (S (length (decr1 l)) = length l).
  rewrite <- H11.
  
  replace (length (decr1 l) =? S (length (decr1 l))) with false.
  simpl.
  replace (length (decr1 l) =? S (length (decr1 l))) with false.

  enough (E2 :: b1 = E2 :: E2 :: decr1 l).
  rewrite H12. auto.
  apply Forall_eq with (x1:=E2).
  simpl.
  rewrite H11.
  simpl in H0. auto.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  apply decr1_cons2.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  apply decr1_length_plus.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
Qed.


Lemma decr1_special2: forall b b',
length b = length b' ->
Forall (eq E2) b ->
Forall (eq E1) b' ->  
E1 :: E1 :: b = decr1 (E1 :: E2 :: b').
Proof.
  intros.
  generalize dependent b.
  induction b' using list_ind_length; intros.
  destruct b; auto.
  simpl in H. lia.

  destruct b'; destruct b; auto.
  simpl in H0. lia.
  simpl in H0. lia.
  inversion H1.
  rewrite <- H5.
  inversion H2.
  rewrite <- H9.
  simpl.

  destruct b'.
  simpl.
  assert (b1=[]).
  destruct b1; auto.
  simpl in H0. lia.
  rewrite H11.
  auto.

  rewrite <- H4 in *.
  enough (S (length (decr1 l)) = length l).
  rewrite <- H11.
  
  replace (length (decr1 l) =? S (length (decr1 l))) with false.
  simpl.
  replace (length (decr1 l) =? S (length (decr1 l))) with false.

  simpl.
  rewrite PeanoNat.Nat.eqb_refl.

  enough ( E2 :: b1 = E2 :: E2 :: decr1 l).
  rewrite H12. auto.
  apply Forall_eq with (x1:=E2).
  simpl.
  rewrite H11.
  simpl in H0. auto.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  apply decr1_cons2.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  apply decr1_length_plus.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
Qed.


Lemma decr1_special3: forall b b',
length b = length b' ->
Forall (eq E2) b ->
Forall (eq E1) b' ->  
b = decr1 (E1 :: b').
Proof.
  intros.

  generalize dependent b.
  induction b' using list_ind_length; intros.
  destruct b; auto.
  simpl in H. lia.

  destruct b'; destruct b; auto.
  simpl in H0. lia.
  simpl in H0. lia.
  inversion H1.
  rewrite <- H5.
  inversion H2.
  rewrite <- H9.

  simpl.
  destruct b'.
  simpl.
  assert (b1=[]).
  destruct b1; auto.
  simpl in H0. lia.
  rewrite H11.
  auto.

  rewrite <- H4 in *.
  enough (S (length (decr1 l)) = length l).
  rewrite <- H11.
  
  replace (length (decr1 l) =? S (length (decr1 l))) with false.
  simpl.
  replace (length (decr1 l) =? S (length (decr1 l))) with false.

  enough (b1 = E2 :: decr1 l).
  rewrite H12. auto.
  apply Forall_eq with (x1:=E2).
  simpl.
  rewrite H11.
  simpl in H0. lia.
  auto.
  constructor; auto.
  apply decr1_cons2.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
  apply decr1_length_plus.
  apply decr1_cons1_inv; auto.
  rewrite H4. simpl. lia.
Qed.  


Lemma decr_iter_comm: forall (a : bilist) (n : nat),
  decr1 (iter n decr1 a) = iter n decr1 (decr1 a).
Proof.
  intros.
  generalize dependent a.
  induction n.
  auto.
  intros.
  simpl.
  rewrite IHn.
  auto.
Qed.