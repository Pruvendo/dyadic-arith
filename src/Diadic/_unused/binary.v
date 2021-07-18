From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.

Local Open Scope nat_scope.

Locate ">?" .

Check ( 5 <? 5)%nat.


Ltac conj_hyp H1 H2 :=
  let t1 := type of H1 in
  let t2 := type of H2 in
  assert (t1 /\ t2) by tauto.
  
Ltac conj_hyp2 H1 H2 :=
  let H:=fresh"H" in
  let eqH:=fresh"eqH" in
  remember (conj H1 H2) as H eqn:eqH; clear eqH.

Lemma foo: forall a b, a = 5 -> b = 6 -> a + b = 11.
Proof.
  intros.
  conj_hyp2 H H0.
  subst.
  auto.
Qed.



Inductive binary : Type :=
  | E1
  | E2.

Definition bilist : Type := list binary. 


Fixpoint incr (b : bilist) : bilist :=
  match b with
  | nil => [E1]
  | cons E1 nil => cons E2 nil
  | cons E2 nil => cons E1 (cons E1 nil)
  | cons E1 t => if Nat.eqb (length (incr t)) (length t) then  cons E1 (incr t) 
                 else
      match (incr t) with
      | nil => nil
      | cons E1 t' => cons E2 t'
      | cons E2 t' => cons E1 t' end
  | cons E2 t => if Nat.eqb (length (incr t)) (length t) then cons E2 (incr t) 
                 else cons E1 (incr t)
end. 


Fixpoint incr1 (b : bilist) : bilist :=
match b with
  | [] => [E1]
  | E1 :: t => let b' := incr1 t in
               if (length b' =? length t) then E1::b' else E2 :: (tl b')
  | E2 :: t => let b' := incr1 t in
               if (length b' =? length t) then E2::b' else E1::b'
end.


Compute incr [E1;E2]. (* 4 -> 5 *)
Compute incr1 [E1;E2]. 

Compute incr [E1;E2;E2]. (* 10 -> 11 *)
Compute incr1 [E1;E2;E2]. 

Compute incr1 (incr1 [E2]). 

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


Axiom list_ind_length: forall (X:Type) (P: list X -> Prop),
    P []  -> (forall (l2: list X), (forall (l1:list X),  length l1 < length l2 -> P l1) -> P l2) ->
    forall l : list X, P l.



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

Lemma incr1_cons1: forall b, length b < length (incr1 b) ->
Forall (eq E1) (incr1 b) .
Proof.
  induction b using list_ind_length; intros.
  simpl. auto.
  destruct b.
  simpl. auto.
  simpl. simpl in H0.
  remember (length (incr1 b0) =? length b0) as q.
  destruct b; destruct q.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H0.
  - exfalso. lia.
  - exfalso. 
  enough (S (length b0) = length (incr1 b0)).
  rewrite H1 in H0.
  destruct (incr1 b0); try lia.
  simpl in H1. lia. simpl in H0. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)).
  lia. apply incr1_length.
  - exfalso.
  rewrite Heqq in H0. lia.
  - enough (length b0 < length (incr1 b0)); try lia.
  clear H0. clear Heqq.
  apply H in H1; auto.
Qed.

Lemma incr1_cons2: forall b, length b < length (incr1 b) ->
Forall (eq E2) b .
Proof.
  induction b using list_ind_length; intros.
  simpl. auto.
  destruct b.
  simpl. auto.
  simpl. simpl in H0.
  remember (length (incr1 b0) =? length b0) as q.
  destruct b; destruct q.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H0.
  - exfalso. lia.
  - exfalso. 
  enough (S (length b0) = length (incr1 b0)).
  rewrite H1 in H0.
  destruct (incr1 b0); try lia.
  simpl in H1. lia. simpl in H0. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)).
  lia. apply incr1_length.
  - exfalso.
  rewrite Heqq in H0. lia.
  - enough (length b0 < length (incr1 b0)); try lia.
  clear H0. clear Heqq.
  apply H in H1; auto.
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

Lemma incr1_tl_comm_E1: forall b, 1 < length b -> Forall (eq E1) b -> 
   incr1 (tl b) = tl (incr1 b).
Proof.
  induction b using list_ind_length; intros. 
  simpl in H. lia.
  destruct b. simpl. simpl in H0. lia.
  inversion_clear H1.
  simpl.
  remember (length (incr1 b0) =? length b0) as q.
  destruct b; destruct q; auto.
  all: symmetry in Heqq.
  all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
  all: simpl.
  all: simpl in H0.
  destruct b0.
  simpl. simpl in H0. lia.
  destruct b0. inversion_clear H3.
  rewrite <- H1 in Heqq. simpl in Heqq. lia.
  exfalso.
  enough (length (incr1 (b :: b0 :: b1)) = length (b :: b0 :: b1)).
  lia. symmetry.
  apply incr1_E1.
  lia. auto.
Qed.

Lemma incr1_tl_comm_E2: forall b, 0 < length b -> Forall (eq E2) b -> 
   incr1 (tl b) = tl (incr1 b).
Proof.
    induction b using list_ind_length; intros. 
    simpl in H. lia.
    destruct b. simpl. simpl in H0. lia.
    inversion_clear H1.
    simpl.
    remember (length (incr1 b0) =? length b0) as q.
    destruct b; destruct q; auto.
    all: symmetry in Heqq.
    all: first [ apply PeanoNat.Nat.eqb_eq in Heqq | apply PeanoNat.Nat.eqb_neq in Heqq ].
    all: simpl.
    all: simpl in H0.
    destruct b0.
    simpl. simpl in H0. discriminate. discriminate.
Qed.

(*[E1]*)

(* Lemma foo: forall b, length (incr1 b) =? length b = true -> tl (incr1 b) = incr1 (tl b).
Proof.
  intros.
  induction b.
  simpl. simpl in H. discriminate.
  destruct a.
  simpl.
  rewrite IHb.
  simpl. simpl in H. destruct (length (incr1 b) =? length b).
  auto.
  simpl.
  simpl in H.
Qed. *)


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

Print nat_ind.

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
  simpl. apply binary_lt_cons. auto.
  destruct b.
  simpl.  apply binary_lt_cons. auto.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b; destruct b1.
  - apply binary_lt_cons2.
  apply H.
  auto.
  - symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  apply binary_lt_E. 
  enough (S (length b0) = length (incr1 b0)).
  destruct (incr1 b0).
  discriminate.
  simpl.  simpl in H0. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
  - symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_eq in Heqb1.
  apply binary_lt_cons2.
  apply H.
  auto.
  - symmetry in Heqb1.
  apply PeanoNat.Nat.eqb_neq in Heqb1.
  apply binary_lt_cons. 
  enough (S (length b0) = length (incr1 b0)).
  destruct (incr1 b0).
  discriminate.
  simpl.  simpl in H0. lia.
  apply incr1_length_plus.
  enough (length b0 <= length (incr1 b0)).
  lia.
  apply incr1_length.
Qed.


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

Lemma incr1_decr1: forall b, 0 < length b -> incr1 (decr1 b) = b.
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


Inductive iter_relation {X} (R: X -> X -> Prop): nat -> X -> X -> Prop :=
| iter_relation0 : forall x y, R x y -> iter_relation R 0 x y
| iter_relationS : forall x y' y n, R y' y -> iter_relation R n x y' -> iter_relation R (S n) x y.


Definition bilist_reducible_prop (R: bilist -> bilist -> Prop) : Prop := 
  forall y, exists n, forall x, (iter_relation R n x y -> False).

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

Lemma iter_relation_S: forall n x y,  
iter_relation binary_lt (S n) x y ->
        exists y', iter_relation binary_lt n y' y.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction n; intros.
  inversion H.
  exists y'. constructor. auto.
  inversion H.
  apply IHn in H2.
  inversion H2.
  exists x1.
  apply iter_relationS with (y'0:=y'); auto. 
Qed.

Lemma iter_relation_S2: forall n x y,  
iter_relation binary_lt (S n) x y ->
        exists y', iter_relation binary_lt n y' y /\ binary_lt x y'.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction n; intros.
  inversion H.
  exists y'. split. constructor. auto.
  inversion H2. auto.

  inversion H.
  apply IHn in H2.
  inversion H2. inversion_clear H5.
  exists x1. split.
  apply iter_relationS with (y'0:=y'); auto.
  auto. 
Qed.

Lemma iter_relation_plus: forall n m x y,  
iter_relation binary_lt (n + m) x y ->
        exists y', iter_relation binary_lt m y' y.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction n; intros.
  exists x. simpl in H. auto.
  simpl in H.
  inversion H.
  apply IHn in H2.
  destruct H2.
  (* x1 < ... < y' < y *)
  destruct m.
  exists y'.
  constructor. auto.
  apply iter_relation_S in H2.
  inversion H2.
  exists x2.
  apply iter_relationS with (y'0:=y'); auto. 
Qed.

Lemma iter_relation_S_inv: forall n x y x',  
iter_relation binary_lt n x' y ->
binary_lt x x' ->
iter_relation binary_lt (S n) x y.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction n; intros.
  apply iter_relationS with (y':=x').
  inversion H. auto.
  constructor. auto.
  inversion H.
  apply IHn  with (x:=x) in H3.
  apply iter_relationS with (y'0:=y').
  auto. auto. auto.
Qed.


Lemma iter_relation_trans: forall n m x y z,  
iter_relation binary_lt (n + m) x z ->
(forall x0 : bilist, iter_relation binary_lt m x0 z -> binary_lt x0 y ) ->
iter_relation binary_lt n x y.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent z.
  induction n; intros.
  apply H0 in H.
  constructor. auto.
  simpl in H.
  inversion H.
  apply iter_relation_S2 in H.
  inversion H. inversion_clear H6.
   
  apply IHn with (y:=y) in H7 ; auto.

  apply iter_relation_S_inv with (x':=x1) .
  auto. auto.
Qed.

Check Nat.pow.

Compute pow 2 1.

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

Lemma binary_lt_trans: forall a b c, 
binary_lt a b -> 
binary_lt b c -> 
binary_lt a c.
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction c using list_ind_length; intros.
  inversion H0.
  destruct c.
  inversion H0.
  destruct a.
  constructor. simpl. lia.
  destruct b.
  inversion H1.
  destruct b; destruct b0; destruct b1.
  - (*8*)
  inversion H0.
  +
  inversion H1.
  *
  apply binary_lt_cons.
  simpl in H4.
  simpl in H8.
  simpl. lia.
  * 
  apply binary_lt_cons2.
  apply H with (l1:=c) (b:=b2).
  simpl. lia.
  destruct c.
  simpl in H4. lia.
  apply binary_lt_cons.
  simpl in H4. lia. auto.
  +
  inversion H1.
  *
  apply binary_lt_cons2.
  apply H with (l1:=c) (b:=b2).
  simpl. lia.
  auto.
  destruct b2.
  simpl in H8.
  lia.
  apply binary_lt_cons.
  simpl in H8.
  lia.
  *
  apply binary_lt_cons2.
  apply H with (l1:=c) (b:=b2).
  simpl. lia.
  auto. auto. 
  - (* 7 *)
  inversion H0.
  +
  inversion H1.
  simpl in H8.
  simpl in H4.
  apply binary_lt_cons.
  simpl.
  lia.
  +
  inversion H1.
  simpl in H8.
  apply binary_lt_cons.
  apply binary_lt_length in H3.
  simpl. lia.
  - (* 6 *)
  inversion H0.
  +
  inversion H1.
  *
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons. 
  simpl.
  lia.
  *
  simpl in H4.
  apply binary_lt_length in H7.
  simpl. apply binary_lt_cons.
  simpl. lia.
  +
  inversion H1.
  *
  simpl in H7.
  apply binary_lt_cons. 
  simpl.
  lia.
  *
  remember H6.
  clear Heqb0.
  apply binary_lt_length in b0.
  assert (length a = length b2 \/ length a < length b2).
  lia.
  inversion_clear H9.
  apply binary_lt_E. lia.
  apply binary_lt_cons.
  simpl. lia.
  - (* 5 *)
  inversion H0.
  +
  inversion H1.
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons.
  simpl. lia.
  +
  inversion H1.
  simpl in H7.
  apply binary_lt_cons.
  simpl. lia.
  - (* 4 *)
  inversion H0.
  inversion H1.
  +
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons.
  simpl. lia.
  +
  simpl in H4.
  apply binary_lt_cons.
  simpl. lia.
  - (* 3 *)
  inversion H0.
  inversion H1.
  +
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons.
  simpl. lia.
  +
  simpl in H4.
  apply binary_lt_length in H7.
  apply binary_lt_cons.
  simpl. lia.
  - (* 2 *)
  inversion H0.
  +
  inversion H1.
  *
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons.
  simpl. lia.
  *
  simpl in H4.
  apply binary_lt_cons.
  simpl. lia.
  +
  inversion H1.
  *
  simpl in H8.
  apply binary_lt_length in H3.
  apply binary_lt_cons.
  simpl. lia.
  *
  remember H3.
  clear Heqb0.
  apply binary_lt_length in b0.
  assert (length b2 = length c \/ length b2 < length c).
  lia.
  inversion_clear H9.
  apply binary_lt_E. lia.
  apply binary_lt_cons.
  simpl. lia.
  - (* 1 *)
  inversion H0.
  +
  inversion H1.
  *
  simpl in H4.
  simpl in H8.
  apply binary_lt_cons.
  simpl. lia.
  *
  simpl in H4.
  apply binary_lt_length in H7.
  apply binary_lt_cons.
  simpl. lia.
  +
  inversion H1.
  *
  simpl in H8.
  apply binary_lt_length in H3.
  apply binary_lt_cons.
  simpl. lia.
  *
  apply binary_lt_cons2.
  apply H with (b:=b2).
  simpl. lia.
  auto. auto.
Qed.

Fixpoint iter {X} (n: nat) (f:X->X) x :=
  match n with
  | O => x
  | S n' => iter n' f (f x)
  end.

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
  

Lemma Forall_eq_length: forall X (l l': list X) x, 
length l = length l' -> 
Forall (eq x) l -> Forall (eq x) l' -> l = l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; intros.
  destruct l'. auto.
  simpl in H.
  lia.
  destruct l'.
  simpl in H. lia.
  simpl in H.
  inversion H.
  apply IHl in H3.
  inversion_clear H0.
  inversion_clear H1.
  congruence.
  inversion_clear H0. auto.
  inversion_clear H1. auto.
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

Lemma iterS: forall X f (x:X) n, iter (S n) f x = f (iter n f x).
Proof.
  intros.
  generalize dependent x.
  induction n; intros.
  simpl. auto.
  simpl.
  rewrite <-IHn. simpl. auto.
  
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

Lemma iter_decr1_nil: forall n, iter n decr1 [] = [].
Proof.
  intros.
  induction n; intros.
  simpl. auto.
  simpl. auto.
Qed.

Check binary_lt_decr1.

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


Lemma firstn_all_length: forall X (y: list X), firstn (length y) y = y.
Proof.
  intros.
  induction y.
  simpl. auto.
  simpl.
  rewrite IHy. auto.
Qed.
  
Lemma skipn_all_length: forall X (y: list X), skipn (length y) y = [].
Proof.
  intros.
  induction y.
  simpl. auto.
  simpl.
  rewrite IHy. auto.
Qed.


Lemma iter_plus: forall X m n f (x:X), 
iter (m+n) f x = iter m f (iter n f x).
Proof.
  intros.
  generalize dependent x.
  induction m; intros.
  simpl. auto.
  simpl.
  rewrite IHm.
  rewrite <- iterS.
  simpl.
  auto.
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

Lemma iter_relation_binary_lt_lt: forall n x y,
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
  apply binary_lt_trans with (b:=x0).
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

  apply iter_relation_trans with (y:=y') in H1.
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
  apply iter_relation_trans with (y:=y') in i.
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

Compute incr (cons E1 nil).
Compute incr (cons E2 nil).
Compute incr (cons E1 (cons E2 nil)).
Compute incr (cons E2 (cons E1 (cons E2 nil))).
Compute incr [E2; E1].

Fixpoint del_h (b b' : bilist) : bilist :=
  match b' with
  | [] => []
  | h :: t => if (length b =? length t + 1) then h :: t else del_h b t 
end.
Compute del_h [] [E1].
Compute del_h [E1; E1] [E1].
Compute del_h [E1; E2] [E1; E1; E1].
Fixpoint del_t (b b' : bilist) : bilist :=
  match b' with
  | [] => []
  | h :: t => if length (del_h b b') =? length t then [h] else h :: del_t b t
end.

Compute firstn 1 [].
Compute firstn 2 [E1;E2].
Compute skipn 1 [].
Compute skipn 1 [E1; E2].
Compute skipn 2 [E1; E2].

Fixpoint plus_eql (b b' : bilist) : bilist :=
  match b with
  | [] => []
  | [E1] => incr b'
  | [E2] => incr (incr b')
  | E1 :: t => if length (plus_eql t (skipn 1 b')) =? length t then 
      match b' with
      | [] => b
      | [E1] => incr b
      | [E2] => incr (incr b)
      | E1 :: t' => E2 :: (plus_eql t t')
      | E2 :: t' => [E1; E1] ++ (plus_eql t t')
      end
    else
      match b' with
      | [] => b
      | [E1] => incr b
      | [E2] => incr (incr b)
      | E1 :: t' =>  [E1] ++ (plus_eql t t')
      | E2 :: t' =>  [E1;E2] ++ (skipn 1 (plus_eql t t')) end
  | E2 :: t => if length (plus_eql t (skipn 1 b')) =? length t then 
      match b' with
      | [] => b
      | [E1] => incr b
      | [E2] => incr (incr b)
      | E1 :: t' => [E1;E1] ++ (plus_eql t t')
      | E2 :: t' => [E1; E2] ++ (plus_eql t t')
      end
    else
      match b' with
      | [] => b
      | [E1] => incr b
      | [E2] => incr (incr b)
      | E1 :: t' => [E1;E2] ++ (skipn 1 (plus_eql t t'))
      | E2 :: t' => [E2;E1] ++ (skipn 1 (plus_eql t t')) end
end.
(*
Definition split: forall {X}, nat -> list X -> list X * list X := 
  fun (n : nat) (t: list Type) => (firstn n t, skipn n t).*)
Definition split (n: nat) (t : bilist) : bilist * bilist :=
  (firstn n t, skipn n t).             

Compute split 1 [E1].

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

Lemma skipn_n: forall b : bilist,
  skipn (length b - 0) b = [] .
Proof.
  induction b.
  auto.
  simpl.
  rewrite PeanoNat.Nat.sub_0_r  with (length b) in IHb.
  auto.
Qed.

Lemma firstn_n: forall b : bilist,
  firstn (length b) b = b.
Proof.
  induction b.
  auto.
  simpl.
  rewrite IHb. auto.
Qed.

Theorem incr_plus_r: forall b : bilist,
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

(*
Lemma len_true: forall b : bilist,
  (length (incr b) =? length b) = true -> length (incr b) - length b = 0  .
Proof.
  intros.
  Search (?n - ?m = 0). apply PeanoNat.Nat.sub_0_le. 
  assert ((length (incr b) =? length b) = true -> length (incr b) = length b).
  intros.
  unfold eqb in H.
  (fix eqb (n m : nat) {struct n} : bool := 
  match n with 
  | 0 => match m with 
        | 0 => true 
        | S _ => false end 
  | S n' => match m with 
        | 0 => false | S m' => eqb n' m' end end) 
        (length (incr b)) (length b) = true

  Search (_ = _ -> _ <= _).  apply PeanoNat.Nat.eq_le_incl. auto.
Qed.*)


Lemma skipn_1: forall X (l: list X), 0 < length l -> tl l = skipn 1 l.
Proof.
  intros.
  induction l.
  simpl in H. lia.
  simpl. auto.
Qed.

Lemma forall_head: forall X (x:X) l, 0 < length l -> Forall (eq x) l -> [x] = firstn 1 l.
Proof.
  intros.
  induction l.
  simpl in H. lia.
  inversion_clear H0.
  simpl. 
  congruence.
Qed.

Lemma head_tail: forall X (l:list X), 0 < length l -> (l = (firstn 1 l) ++ (tl l)).
Proof.
  intros.
  induction l.
  simpl in H. lia.
  simpl. auto.
Qed.  

Theorem incr_plus_l: forall b : bilist, incr1 b = plus b [E1].
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
   
Inductive biZ := biNat : bilist -> biZ | biNeg : bilist -> biZ.

(* Require Import NArith.
Print N.
(* Inductive N : Set :=  N0 : N | Npos : positive -> N *)
Check N.pow. *)

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


Require Import ZArith.

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
Delimit Scope diadic_scope with ddd.

Numeral Notation diadic Z2diadic diadic2Z : diadic_scope.
Local Open Scope ddd.

Definition dplus (a b: diadic) : diadic := 
  let (a') := a in
  let (b') := b in
  Diadic (plus a' b').

(* Close Scope nat_scope.
Close Scope type_scope. *)

Notation " a + b " := (dplus a b) (at level 50, left associativity): diadic_scope.

Check 5: diadic.

Check (_ + _)%ddd.

Compute (5 + 5).

