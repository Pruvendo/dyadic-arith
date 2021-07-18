From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Local Open Scope nat_scope.

Locate ">?" .

Check ( 5 <? 5)%nat.

Fixpoint iter {X} (n: nat) (f:X->X) x :=
  match n with
  | O => x
  | S n' => iter n' f (f x)
  end.

Theorem list_ind_length: forall (X:Type) (P: list X -> Prop),
    P []  -> (forall (l2: list X), (forall (l1:list X),  length l1 < length l2 -> P l1) -> P l2) ->
    forall l : list X, P l.
Proof.
  intros.
  apply H0.
  induction l.
  intros.
  inversion H1.
  intros.
  apply H0.
  intros.
  apply IHl.
  simpl in H1.
  lia.
Qed.

Inductive binary : Type :=
  | E1
  | E2.

Definition bilist : Type := list binary. 

Check length. 

Check tl.

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

Lemma empty_tl: forall b : bilist,
  [] = tl b -> length b <= 1.
Proof.
  intros.
  induction b.
  auto.
  simpl in H.
  simpl. rewrite <- H.
  simpl. auto. Qed.

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

Lemma length_ge_zero: forall b : bilist,
  0 < length b -> length b = S (length (tl b)).
Proof.
  intros.
  induction b.
  inversion H.
  auto.
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
  Search ((_ =? _) = true ). apply PeanoNat.Nat.eqb_eq.
  apply PeanoNat.Nat.eqb_eq in IHb.
  rewrite <- IHb.
  apply length_ge_zero.
  apply neq_zero_length.
Qed.

Lemma E1_head_eq: forall b, 
length (incr1 (E1 :: b))  = length (E1 :: b).
Proof.
    Search (_ =? _ = true).
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
    Search (S _ < S _). rewrite <-PeanoNat.Nat.succ_lt_mono.
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
    Search (?x < ?x).
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
    Search (?x < ?y -> ?x <> ?y).
    apply PeanoNat.Nat.lt_neq in H.
    apply PeanoNat.Nat.eqb_neq. auto.
Qed.

Lemma eq_E1_head: forall (b b' : bilist) (h : binary),
  b = b' -> h :: b = h ::b'.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma length_eq_head: forall (b b' : bilist) (h : binary), 
    length b = length b' -> length (h :: b) = length (h :: b').
Proof.
    intros.
    simpl.
    auto.
Qed.

Lemma tl_greater: forall b : bilist,
  0 < length b -> length (tl  b) =? length b = false.
Proof.
  intros.
  destruct b.
  inversion H.
  simpl.
  induction (length b0).
  auto.
  auto.
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
  Search (S _ = S _).
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
  Check Forall.
  apply Forall_cons. 
  destruct a.
  simpl in H.
  remember (length (incr1 b) =? length b) as q.
  destruct q.
  simpl in H.
  Search (S _ < S _ ).
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
  Search (S _ < S _).
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
  Search (_ =? _ = true).
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


Inductive binary_lt: bilist -> bilist -> Prop :=
  | binary_lt_cons: forall x y b, length x <= length y -> binary_lt x (b::y)
  | binary_lt_E: forall x y, (length x = length y) -> binary_lt (E1::x) (E2::y)
  | binary_lt_cons2: forall x y b, binary_lt x y -> binary_lt (b::x) (b::y).


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

Lemma lt_decr1: forall b, 
  0 < length b ->
  binary_lt (decr1 b) b.
Proof.
  intros.
  rewrite <- incr1_decr1.
  apply lt_incr1.
  assumption.
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

Print nat_ind.

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
  Search (?n - 0 = ?n).
  Check length b.
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
  Search (?l ++ [] = ?l).
  rewrite app_nil_r. auto.
Qed.


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
    
Compute split 2 [E1;E2;E1].


Fixpoint minus_one_digit' (b : bilist) (n: nat) (d: binary) {struct n}:  bilist := 
  match n with
  | O => match d with
         | E1 => decr1 b
         | E2 => decr1 (decr1 b)
         end
  (* | 1 => match d with
         | E1 => decr1 (decr1 b)
         | E2 => decr1 (decr1 (decr1 (decr1 b)))
         end        *)
  | S n' => match d with
            | E1 => let (h, t) := split (length b - n) b in
                    match h with
                    | [] => minus_one_digit' t n' E2
                    | _ => (decr1 h) ++ t
                    end
            | E2 => let (h, t) := split (length b - n) b in
                    match h with
                    | [] => []
                    | [E1] => minus_one_digit' t n' E2
                    | _ =>  (decr1 (decr1 h)) ++ t
                    end
            end 
  end.
  
Compute  minus_one_digit' [E1; E1] 0 E1.
Compute  minus_one_digit' [E1; E1] 0 E2.
Compute  minus_one_digit' [E2; E2; E2] 2 E2.
Compute  minus_one_digit' [E2; E2; E2] 3 E2.
Compute  minus_one_digit' [E2; E2; E2] 3 E1.


Definition minus_one_digit (b : bilist) (n: nat) (d: binary):  bilist := 
  let (h, t) := split (length b - n) b in
  match h, d with
  | [], _ => []
  | [E1], E2 => []
  | _, E1 => (decr1 h) ++ t
  | _, E2 => (decr1 (decr1 h)) ++ t
  end. 

(* Fixpoint minus' (b b' : bilist) :  bilist := 
  match b' with
  | [] => b
  | d :: t' => minus_one_digit (minus' b t') (length t') d
  end. *)

Fixpoint minus'' (b b' : bilist) :  bilist := 
  match b' with
  | [] => b
  | d :: t' => minus_one_digit' (minus'' b t') (length t') d
  end.  

Example check_min_dig: minus_one_digit' [E2;E2] 1 E2 = [E2].
Proof.
  (* Eval compute in split (length [E2;E2] - 1) [E2;E2]. *)
  compute.
  reflexivity.
Qed.

Example  check_min_dig': minus_one_digit' [E2;E2] 1 E2 = [E2].
Proof.
  compute.
  reflexivity.
Qed.

Example  check_min_dig1: minus_one_digit [E2;E2] 2 E1 = [E2].
Proof.
  compute.
  Fail reflexivity.
Abort.

Example  check_min_dig1': minus_one_digit' [E2;E2] 2 E1 = [E2].
Proof.
  compute.
  reflexivity.
Qed.

Example check_min'0: minus'' [E1; E1; E1] [E2;E1] = [E2].
Proof.
compute.
reflexivity.
Qed. 

Example check_min': minus'' [E2] [E1] = [E1].
Proof.
  reflexivity.
Qed.
  
Example check_min1': minus'' [E2;E1] [E1] = [E1;E2].
Proof.
  reflexivity.
Qed.
  
Example check_min2': minus'' [E1;E2] [E1] = [E1;E1].
Proof.
  reflexivity.
Qed.
  
Example check_min3': minus'' [E2] [E1;E1] = [].
Proof.
  simpl. reflexivity.
Qed.  


Fixpoint minus (b b' : bilist) :  bilist := 
match b' with
| [] => b
| E1 :: t => minus (iter (pow 2 (length t)) decr1 b) t
| E2 :: t => minus (iter (pow 2 (1 + length t)) decr1 b) t
end.

Lemma minus_one_digit0: forall n a, 
       minus_one_digit' [] n a = [].
Proof.
  intros.
  generalize dependent a.
  induction n; intros.
  simpl. destruct a; auto.
  simpl. rewrite IHn. destruct a; auto.
Qed.


(* Definition minus_one_digit_ok' (b : bilist) (n: nat) (d: binary):  bool := 
match n with
| O => match d with
        | E1 => match b with
                | [] => false
                | _ => true
                end
        | E2 => match b with
                | [] | [E1] => false
                | _ => true
                end
        end
| S n' => match d with
          | E1 => let (h, t) := split (length b - n') b in
                  match h with
                  | [] | [E1] => false
                  | _ =>  true
                  end
          | E2 =>  let (h, t) := split (length b - n) b in
                    match h with
                    | [] | [E1] => false
                    | _ => true
                    end
          end
end. *)  

(* Fixpoint minus_one_digit_ok' (b : bilist) (n: nat) (d: binary) {struct n}: bool := 
  match n with
  | O => match d, b with
         | _, [] => false
         | E1, _ => true
         | E2, [E1] => false
         | E2, _ => true
         end
  | 1 => match d, b with
         | _, [] => false
         | E1, [E2] => true
         | _, [_] => false
         | E1, _ => true
         | E2, [E1;E1] => false
         | E2, _ => true
         end       
  | S (S n' as n0) => match d with
            | E1 => let (h, t) := split (length b - n0) b in
                    match h with
                    | [] => false
                    | [E1] => minus_one_digit_ok' t n' E2
                    | _ =>  true
                    end
            | E2 => let (h, t) := split (length b - n) b in
                    match h with
                    | [] => false
                    | [E1] => minus_one_digit_ok' t n0 E2
                    | _ =>  true
                    end
            end 
  end. *)

Fixpoint minus_one_digit_ok' (b : bilist) (n: nat) (d: binary) {struct n}: bool := 
  match n with
  | O => match b, d with
         | [], _ => false
         | _, E1 => true
         | [E1], E2 => false
         | _, _ => true
         end
  | S n' => match d with
            | E1 => let (h, t) := split (length b - n) b in
                    match h with
                    | [] => minus_one_digit_ok' t n' E2
                    | _ => true
                    end
            | E2 => let (h, t) := split (length b - n) b in
                    match h with
                    | [] => false
                    | [E1] => minus_one_digit_ok' t n' E2
                    | _ =>  true
                    end
            end 
  end.


Lemma snoc_cons: forall {X} x (b: X), exists y t, x++[b] = y::t.
Proof.
  intros.
  induction x.
  exists b, []. auto.
  inversion_clear IHx.
  inversion_clear H.
  simpl.
  rewrite H0.
  exists a, (x0::x1).
  auto.
Qed.

Lemma cons_snoc: forall {X} t (y: X), exists b x, x++[b] = y::t.
Proof.
  intros.
  generalize dependent y.
  induction t; intros.
  exists y, []. auto.
  remember (IHt a). clear Heqe.
  inversion_clear e.
  inversion_clear H.
  rewrite <- H0.
  exists x, (y::x0).
  auto.
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

Lemma snoc_eq: forall {X} (x y: X) t l, t++[x] = l++[y] -> t = l /\ x = y .
Proof.
  intros.
  generalize dependent l.
  generalize dependent x.
  generalize dependent y.
  induction t; intros.
  destruct l.
  inversion H.
  auto.
  inversion H.
  destruct l; discriminate.
  destruct l.
  inversion H.
  destruct t; discriminate.
  inversion H.
  split.
  enough (t = l).
  congruence.
  apply IHt in H2.
  inversion_clear H2. auto.
  apply IHt in H2.
  inversion_clear H2. auto.
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

Lemma firstn_nil: forall {X} n (x: list X),
firstn n x = [] -> n = 0 \/ x = [].
Proof.
  intros.
  generalize dependent x.
  induction n; intros.
  left. auto.
  destruct x.
  right.  auto.
  simpl in H.
  discriminate.
Qed.

Lemma firstn_1: forall {X} a n (x: list X),
firstn n x = [a] <-> (n = 1 /\ exists y, x = a::y) \/ (x = [a] /\ n > 0).
Proof.
  intros. split.
  generalize dependent x.
  induction n; intros.
  simpl in H. discriminate.
  destruct x.
  simpl in H. discriminate.
  simpl in H.
  inversion H.
  apply firstn_nil in H2.
  inversion H2.
  left. split. lia. 
  exists x0. auto.
  rewrite H0.
  right.
  split.
  destruct n; auto.
  lia.
  intros.
  inversion_clear H.
  inversion_clear H0.
  rewrite H.
  inversion_clear H1.
  rewrite H0. simpl. auto.
  inversion_clear H0.
  rewrite H.
  destruct n.
  lia.
  simpl.
  destruct n.
  simpl. auto.
  simpl. auto.
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

Lemma minus_one_digit_ok_E1: forall b n, 
minus_one_digit_ok' b (S n) E1 = minus_one_digit_ok' b n E2 .
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  -
  simpl.
  remember (firstn (length b - 1) b). 
  destruct l; destruct b; auto.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  rewrite H.
  simpl. destruct b; auto.
  discriminate.
  discriminate.
  destruct b; auto.
  destruct b1; auto.
  discriminate.
  -
  simpl.
  remember (firstn (length b - S (S n)) b) as f2.
  remember (skipn (length b - S (S n)) b) as s2.
  remember (firstn (length b - S n) b) as f1.
  remember (skipn (length b - S n) b) as s1.
  remember (firstn (length s2 - S n) s2) as f21.
  remember (skipn (length s2 - S n) s2) as s21.

  assert (f2++s2 = b).
  subst f2 s2.
  apply firstn_skipn.

  assert (f1++s1 = b).
  subst f1 s1.
  apply firstn_skipn.

  assert (f21++s21 = s2).
  subst f21 s21.
  apply firstn_skipn.

  assert (length s2 <= S (S n)).
  subst s2.
  rewrite skipn_length.
  lia.

  assert  (length f21 <= 1).
  subst f21.
  rewrite firstn_length.
  lia.

  destruct f2; destruct f1; auto.
  +
  destruct f21; auto; destruct b0; auto.
  destruct f21; auto.
  exfalso.
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.
  exfalso.
  simpl in H3. lia.
  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.
  +
  destruct f21; auto; destruct b0; auto.
  destruct f1; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct b1; destruct f1; auto.
  destruct f21; auto.

  simpl in H.
  rewrite H in H1.
  destruct b. discriminate.
  inversion H0.
  inversion H1.
  auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct f21; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct b1; auto.
  destruct f21; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  +
  exfalso.
  assert (length b <= S n).
  rewrite <- H0.
  subst s1.
  simpl.
  rewrite skipn_length.
  lia.

  assert (length b > S (S n)).
  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia. lia.

  +
  destruct b1; auto.
  destruct f1; auto.

  exfalso.
  assert (length b <= S (S n)).
  rewrite <- H0.
  subst s1.
  rewrite app_length.
  simpl.
  rewrite skipn_length.
  lia.

  assert (length b > S (S n)).
  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia. lia.
Qed.

Lemma app_inv_head_length:
forall {X} (l1 l2 s0 s3 : list X), 
l2 ++ s0 = l1 ++ s3 -> 
length s0 = length s3 -> 
s0 = s3 /\ l2 = l1.
Proof.

  intros.
  generalize dependent s0.
  generalize dependent s3.
  generalize dependent l2.
  induction l1; intros.

  assert (l2=[]).
  assert (length (l2++s0) = length s3).
  rewrite H.
  auto.
  rewrite app_length in H1.
  assert (length l2 = 0).
  lia.
  destruct l2; [auto | simpl in H2; lia].
  rewrite H1 in H.
  auto.
  destruct l2.
  exfalso.
  assert (length s0 = length ((a::l1) ++ s3)).
  rewrite <- H.
  auto.
  rewrite app_length in H1.
  simpl in H1. lia.
  inversion H. apply IHl1 in H3.
  inversion H3; split; congruence.
  auto.
Qed.  

Lemma minus_one_digit_E12: forall b n, 
minus_one_digit' b (S n) E1 = minus_one_digit' b n E2.
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  -
  simpl.
  remember (firstn (length b - 1) b). 
  destruct l; destruct b; auto.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  rewrite H.
  simpl skipn. auto.
  discriminate.
  discriminate.
 (*  replace b0 with b. *)
  remember (skipn (length (b :: b1) - 1) (b :: b1)).
  assert ((b0::l)++l0 = b::b1).
  rewrite Heql. rewrite Heql0.
  apply firstn_skipn.
  assert (length l0 = 1).
  subst l0.
  rewrite skipn_length.
  simpl length . lia.
  destruct l0. simpl in H0. lia.
  destruct l0.
  all: cycle 1.
  simpl in H0. lia.
  rewrite <- H.
  remember (b0::l).
  destruct b2.
  rewrite decr1_E1_snoc.
  rewrite decr1_E2_snoc.
  auto.
  rewrite Heql1.
  simpl. lia.

  rewrite decr1_E2_snoc.
  rewrite decr1_E1_snoc.
  auto.
  rewrite Heql1.
  simpl. lia.

  -
  simpl.
  remember (firstn (length b - S (S n)) b) as f2.
  remember (skipn (length b - S (S n)) b) as s2.
  remember (firstn (length b - S n) b) as f1.
  remember (skipn (length b - S n) b) as s1.
  remember (firstn (length s2 - S n) s2) as f21.
  remember (skipn (length s2 - S n) s2) as s21.

  assert (f2++s2 = b).
  subst f2 s2.
  apply firstn_skipn.

  assert (f1++s1 = b).
  subst f1 s1.
  apply firstn_skipn.

  assert (f21++s21 = s2).
  subst f21 s21.
  apply firstn_skipn.

  assert (length s2 <= S (S n)).
  subst s2.
  rewrite skipn_length.
  lia.

  assert  (length f21 <= 1).
  subst f21.
  rewrite firstn_length.
  lia.

  destruct f2; destruct f1; auto.
  +
  destruct f21; auto; destruct b0; auto.
  destruct f21; auto.
  exfalso.
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.
  exfalso.
  simpl in H3. lia.
  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.
  +
  destruct f21; auto; destruct b0; auto.
  destruct f1; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct b1; destruct f1; auto.
  destruct f21; auto.

  simpl in H.
  rewrite H in H1.
  destruct b. discriminate.
  inversion H0.
  inversion H1.
  auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct f21; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso.
  simpl in H3.
  lia. 

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  destruct b1; auto.
  destruct f21; auto.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  exfalso. 
  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  discriminate.

  simpl in H.
  rewrite H in Heqf21.
  rewrite <- Heqf21 in Heqf1.
  inversion_clear Heqf1.
  replace s21 with s1.
  auto.
  subst s1. subst s21.
  congruence.

  +
  exfalso.
  assert (length b <= S n).
  rewrite <- H0.
  subst s1.
  simpl.
  rewrite skipn_length.
  lia.

  assert (length b > S (S n)).
  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia. 
  
  lia.

  +
  destruct b1; auto.
  destruct f1; auto.

  *
  exfalso.
  assert (length b <= S (S n)).
  rewrite <- H0.
  subst s1.
  rewrite app_length.
  simpl.
  rewrite skipn_length.
  lia.

  assert (length b > S (S n)).
  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia. 
  
  lia.

  *

  assert ((b0::f2) ++ s2 = (E1 :: b1 :: f1) ++ s1).
  rewrite H. rewrite H0. auto.
  assert (length s2 = S(length s1)).
  subst s1. subst s2.
  rewrite ?skipn_length.
  enough (length b >= S (S n)).
  lia.

  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia.
  
  enough (exists x, x::s1 = s2).
  inversion_clear H6.
  enough ( (b0 :: f2) ++[x]= (E1 :: b1 :: f1) ).
  rewrite <-H6. rewrite <- H7.
  remember (b0 :: f2).

  destruct x.
  rewrite decr1_E1_snoc.
  rewrite decr1_E2_snoc.
  rewrite app_ass.
  auto.
  rewrite Heql.
  simpl. lia.

  rewrite decr1_E2_snoc.
  rewrite decr1_E1_snoc.
  rewrite app_ass.
  auto.
  rewrite Heql.
  simpl. lia.

  rewrite <- H7 in H4.

  replace ((b0 :: f2) ++ x :: s1) with (((b0 :: f2) ++ [x]) ++ s1) in H4.
  (* Search app. *)
  apply app_inv_tail in H4.
  auto.
  rewrite app_ass. simpl. auto.

  destruct s2.
  simpl in H5. lia.
  simpl in H5.
  inversion H5.
  replace ((b0 :: f2) ++ b2 :: s2) with (((b0 :: f2) ++ [b2]) ++ s2) in H4.

  remember((b0 :: f2) ++ [b2]).
  remember (E1 :: b1 :: f1).


  exists b2.
  replace s1 with s2. auto.
  enough (s2=s1/\l=l0). tauto.
  apply app_inv_head_length; auto.
  rewrite app_ass.
  auto.
  *

  assert ((b0::f2) ++ s2 = (E2::f1) ++ s1).
  rewrite H. rewrite H0. auto.
  assert (length s2 = S(length s1)).
  subst s1. subst s2.
  rewrite ?skipn_length.
  enough (length b >= S (S n)).
  lia.

  assert (length (b0::f2) <= length b - S (S n)).
  rewrite Heqf2.
  apply firstn_le_length.
  simpl in H5.
  lia.
  
  enough (exists x, x::s1 = s2).
  inversion_clear H6.
  enough ( (b0 :: f2) ++[x]= (E2 :: f1) ).
  rewrite <-H6. rewrite <- H7.
  remember (b0 :: f2).

  destruct x.
  rewrite decr1_E1_snoc.
  rewrite decr1_E2_snoc.
  rewrite app_ass.
  auto.
  rewrite Heql.
  simpl. lia.

  rewrite decr1_E2_snoc.
  rewrite decr1_E1_snoc.
  rewrite app_ass.
  auto.
  rewrite Heql.
  simpl. lia.

  rewrite <- H7 in H4.

  replace ((b0 :: f2) ++ x :: s1) with (((b0 :: f2) ++ [x]) ++ s1) in H4.
  (* Search app. *)
  apply app_inv_tail in H4.
  auto.
  rewrite app_ass. simpl. auto.

  destruct s2.
  simpl in H5. lia.
  simpl in H5.
  inversion H5.
  replace ((b0 :: f2) ++ b1 :: s2) with (((b0 :: f2) ++ [b1]) ++ s2) in H4.

  remember((b0 :: f2) ++ [b1]).
  remember (E2 :: f1).


  exists b1.
  replace s1 with s2. auto.
  enough (s2=s1/\l=l0). tauto.
  apply app_inv_head_length; auto.
  rewrite app_ass.
  auto.
Qed.

Lemma minus_one_digit_ok_snoc: forall a b d n, 
minus_one_digit_ok' b n a = true ->
minus_one_digit_ok' (b++[d]) (S n) a = true.
Proof.
  intros.
  generalize dependent b.
  generalize dependent a.
  generalize dependent d.
  induction n; intros.
  -
  simpl minus_one_digit_ok'.
  replace (length (b ++ [d]) - 1) with (length b ).
  erewrite <- firstn_snoc.
  rewrite firstn_all.
  destruct a; auto.
  destruct b; auto.
  simpl.
  destruct d; auto.
  destruct b; auto.
  destruct b; auto.
  destruct b0; auto.
  simpl.
  destruct d; auto.
  lia.
  rewrite app_length.
  simpl. lia.
  -
  simpl. simpl in H.
  enough (length (b ++ [d]) - (S (S n))=length b - S n). rewrite H0.
  erewrite <- firstn_snoc.
  remember (firstn (length b - S n) b).

  destruct a; auto.
  destruct l; auto.
  remember ((skipn (length b - S n) (b ++ [d]))).
  remember ((skipn (length l - S n) l)).
  rewrite skipn_snoc in Heql0.
  enough (skipn (length b - S n) b = b).
  rewrite H1 in Heql0.
  rewrite  Heql0.
  enough (length (b ++ [d]) - S n=length b - n). rewrite H2.
  rewrite <- firstn_snoc.
  rewrite H1 in H.
  rewrite Heql0 in Heql1.
  remember (firstn (length b - n) b).
  destruct l1; auto.

  exfalso.
  assert ([] ++ skipn (length b - n) b = b).
  rewrite Heql2.
  apply firstn_skipn.
  simpl in H3.

  apply IHn with (d:=d) in H.
  simpl in H.
  rewrite H2 in H.
  rewrite <- firstn_snoc in H.
  rewrite <- Heql2 in H.
  discriminate.
  lia.

  remember H. clear Heqe.
  apply IHn with (d:=d) in H.
  simpl in H.
  rewrite H2 in H.
  rewrite <- firstn_snoc in H.
  rewrite <- Heql2 in H.

  destruct b0; auto.
  rewrite <- H2 in H.
  rewrite <- Heql1 in H. 
  destruct l1; auto.
  lia. lia.
  rewrite app_length. simpl. lia.
  assert ([]++skipn (length b - S n) b = b).
  rewrite Heql.
  apply firstn_skipn. auto.
  lia.

  destruct l; auto.
  destruct b0; auto.
  destruct l; auto.

  rewrite skipn_snoc.
  remember (skipn (length b - S n) b).
  enough (length (l ++ [d]) - S n = length l -n).
  rewrite H1.
  rewrite <- firstn_snoc.
  rewrite skipn_snoc.
  remember (skipn (length l - n) l ).
  remember (firstn (length l - n) l).
  destruct l1; auto.

  exfalso.
  apply IHn with (d:=d) in H.
  simpl in H.
  rewrite H1 in H.
  rewrite <- firstn_snoc in H.
  rewrite <- Heql2 in H.
  discriminate.
  lia.

  destruct b0; auto.
  destruct l1; auto.

  apply IHn with (d:=d) in H.
  simpl in H.
  rewrite H1 in H.
  rewrite <- firstn_snoc in H.
  rewrite <- Heql2 in H.
  rewrite skipn_snoc in H.
  rewrite <- Heql1 in H.
  auto.
  all: try lia.
  all: rewrite app_length.
  all: simpl.
  all: lia.

Qed.
 
Lemma minus_one_digit_ok_S: forall a b  n, 
minus_one_digit_ok' b (S n) a = true ->
minus_one_digit_ok' b n a = true.
Proof.
  intros.
  generalize dependent b.
  generalize dependent a.
  induction n; intros.
  -
  simpl. simpl in H.
  destruct b; auto.
  simpl in H.
  destruct a; auto.
  simpl in H.
  destruct b; auto.
  destruct b0; auto.
  all: destruct a; auto.
  -
  simpl. simpl in H.
  destruct a; auto.
  remember (firstn (length b - S n) b).
  destruct l; auto.
  remember (firstn (length b - S (S n)) b).
  destruct l; auto.
  remember ((skipn (length b - S (S n)) b)).
  remember (firstn (length l - S n) l).
  destruct l0; auto.

  discriminate.
  destruct l0; auto.
  destruct b0; auto.
  replace b with l. auto.
  enough ([]++l=b).
  auto.
  rewrite Heql0. rewrite Heql1.
  apply firstn_skipn.

  enough (b = l).
  rewrite H0 in Heql.
  rewrite <- Heql in Heql2.
  discriminate.
  enough ([]++l=b). auto.
  rewrite Heql0. rewrite Heql1.
  apply firstn_skipn.

  enough (b = l).
  rewrite H0 in Heql.
  rewrite <- Heql in Heql2.
  discriminate.
  enough ([]++l=b). auto.
  rewrite Heql0. rewrite Heql1.
  apply firstn_skipn.


  exfalso.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  assert (length b - S (S n) = 0).
  lia.
  rewrite H1 in Heql0.
  discriminate.
  rewrite H0 in Heql0.
  discriminate.

  remember (firstn (length b - S n) b).
  destruct l; auto.

  exfalso.
  remember (firstn (length b - S (S n)) b).
  destruct l. discriminate.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  assert (length b - S (S n) = 0).
  lia.
  rewrite H1 in Heql0.
  discriminate.
  rewrite H0 in Heql0.
  discriminate.

  destruct b0; auto.
  destruct l; auto.
  remember (firstn (length b - S (S n)) b).
  destruct l. discriminate.
  destruct b0; try discriminate.
  destruct l; try discriminate.
  remember (skipn (length b - S (S n)) b).
  remember (firstn (length l - S n) l).
  destruct l0; try discriminate.
  destruct b0;  try discriminate.
  destruct l0; try discriminate.

  +
  exfalso.
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H0.
  replace (length b - S (S n)) with 0 in Heql0 by lia.
  discriminate.
  inversion_clear H0.
  rewrite H1 in H2. simpl in H2. lia.

  +

  exfalso.
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H0.
  replace (length b - S (S n)) with 0 in Heql0 by lia.
  discriminate.
  inversion_clear H0.
  rewrite H1 in H2. simpl in H2. lia.

  +
  exfalso.
  enough (l=[]).
  rewrite H0 in Heql2.
  simpl in Heql2. discriminate.
  destruct l; auto.

  exfalso.
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H0.
  replace (length b - S (S n)) with 0 in Heql0 by lia.
  discriminate.
  inversion_clear H0.
  rewrite H1 in H2. simpl in H2. lia.

  +
  exfalso.
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H0.
  replace (length b - S (S n)) with 0 in Heql0 by lia.
  discriminate.
  inversion_clear H0.
  rewrite H1 in H2. simpl in H2. lia.

  +
  exfalso.
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H0.
  replace (length b - S (S n)) with 0 in Heql0 by lia.
  discriminate.
  inversion_clear H0.
  rewrite H1 in H2. simpl in H2. lia.

Qed.  

Lemma minus_one_digit_ok_nil_false: 
forall n a,
minus_one_digit_ok' [] n a = false.
Proof.
  intros.
  generalize dependent a.
  induction n; intros.
  simpl. auto.
  simpl.
  rewrite IHn.
  destruct a; auto.
Qed.

Lemma minus_one_digit_nil: 
forall n a,
minus_one_digit' [] n a = [].
Proof.
  intros.
  generalize dependent a.
  induction n; intros.
  simpl. destruct a; auto.
  simpl.
  rewrite IHn.
  destruct a; auto.
Qed.

Lemma minus_one_digit_ok_E12_false: forall n,  minus_one_digit_ok' [E1] n E2 = false.
Proof.
  intros.

  induction n; intros.
  simpl. auto.
  simpl. auto.
Qed.

Lemma minus_one_digit_E12_false: forall n,  minus_one_digit' [E1] n E2 = [].
Proof.
  intros.

  destruct n.
  simpl. auto.
  simpl. auto.
Qed.

Lemma minus_one_digit_ok_always: forall l n, 
length l = n -> 
(minus_one_digit_ok' l n E1 = false <-> Forall (eq E1) l).
Proof.
  intros.
  split.
  -
  generalize dependent l.
  induction n; intros.
  +
  enough (l = []).
  rewrite H1 in H0.
  simpl in H0.
  rewrite H1.
  constructor.
  destruct l ; auto.
  simpl in H. discriminate.
  +
  destruct l.
  simpl in H. discriminate.
  simpl in H.
  assert (length l = n) by lia.
  simpl in H0.
  remember (firstn (length l - n) (b :: l)).
  remember (skipn (length l - n) (b :: l)).

  destruct l0 ; try discriminate.
  assert ([]++l1 = b::l).
  rewrite Heql0. rewrite Heql1. apply firstn_skipn.
  simpl in H2.
  rewrite H2 in H0.
  destruct n.
  *
  assert (l=[]).
  replace (length l - 0) with (length l) in Heql0 by lia.
  symmetry in Heql0.
  apply firstn_nil in Heql0.
  inversion_clear Heql0.
  destruct l; auto.
  simpl in H3. lia.
  discriminate.
  rewrite H3 in H0.
  simpl in H0.
  destruct b; try discriminate.
  rewrite H3.
  constructor;  auto.
  *
  simpl in H0.
  remember (firstn (length l - n) (b :: l)).
  destruct l0; try discriminate.
  exfalso.
  symmetry in Heql2.
  apply  firstn_nil in Heql2.
  inversion_clear Heql2.
  lia.
  discriminate.
  destruct b0.
  destruct l0; try discriminate.
  remember (skipn (length l - n) (b :: l)).

  assert (b=E1).
  symmetry in Heql0.
  symmetry in Heql2.
  apply firstn_nil in Heql0.
  apply firstn_1 in Heql2.

  inversion_clear Heql0; inversion_clear Heql2.
  **
  inversion_clear H4.
  inversion_clear H6.
  inversion_clear H4.
  auto.
  **
  inversion_clear H4.
  inversion_clear H5.
  auto.
  **
  discriminate.
  **
  discriminate.
  **
  rewrite H3.
  constructor.
  auto.

  assert ([E1]++l0 = b::l).
  rewrite Heql2.
  rewrite Heql3.
  apply firstn_skipn.
  simpl in H4.
  inversion H4.
  rewrite H7 in H0.
  rewrite <- minus_one_digit_ok_E1 in H0.
  apply IHn in H0; auto.

  **
  discriminate.

  -
  intros.
  generalize dependent l.
  induction n; intros.
  enough (l = []).
  rewrite H1.
  simpl. auto.
  destruct l; auto.
  simpl in H. lia.

  destruct l.
  simpl in H. discriminate.
  simpl in H.
  inversion H. clear H.
  rewrite H2.

  inversion_clear H0.
  simpl.

  remember (firstn (length l - n) (b :: l)).
  destruct l0; auto.
  remember (skipn (length l - n) (b :: l)).

  assert ([]++l0=b::l).
  rewrite Heql0.
  rewrite Heql1.
  apply firstn_skipn.
  simpl in H0.

  rewrite H0.
  destruct n.

  enough (l = []).
  rewrite H3.
  rewrite <- H.

  apply minus_one_digit_ok_E12_false.
  destruct l; auto.
  simpl in H2. lia.

  simpl.
  remember (firstn (length l - n) (b :: l)).
  destruct l1; auto.
  destruct b0; auto.
  destruct l1; auto.

  *
  remember (skipn (length l - n) (b :: l)).
  assert ([E1]++l1 = b::l).
  rewrite Heql2.
  rewrite Heql3.
  apply firstn_skipn.

  simpl in H3.
  inversion H3.

  rewrite <- minus_one_digit_ok_E1.
  apply IHn; auto.
  *
  (*symmetry in Heql0.
  apply firstn_nil in Heql0.
  inversion_clear Heql0. *)
  rewrite H2 in Heql2.
  replace (S n - n) with 1 in Heql2 by lia.
  simpl in Heql2.
  discriminate.
  *
  rewrite H2 in Heql2.
  replace (S n - n) with 1 in Heql2 by lia.
  simpl in Heql2.
  inversion Heql2.
  rewrite <- H in H4.
  discriminate.
  *
  rewrite H2 in Heql0.
  replace (n - n) with 0 in Heql0 by lia.
  simpl in Heql0.
  discriminate.
Qed.


Lemma minus_one_digit_ok_false: forall l n, 
length l <= n -> 
minus_one_digit_ok' l n E2 = false.
Proof.
  intros.
  generalize dependent l.
  induction n ; intros.
  -
  simpl.
  destruct l; auto.
  simpl in H. lia.
  
  -
  destruct l.
  simpl. auto.
  simpl in H. 
  assert (length l <= n) by lia.
  apply IHn in H0.
  simpl.
  remember (firstn (length l - n) (b :: l) ).
  destruct l0; auto.
  destruct b0; auto.
  destruct l0; auto.
  remember (skipn (length l - n) (b :: l)).
  assert ([E1] ++ l0 = b::l).
  rewrite Heql0.
  rewrite Heql1.
  apply firstn_skipn.
  inversion H1.
  auto.

  exfalso.
  (* rewrite <- minus_one_digit_ok_E1 in H0. *)
  assert (length l <= n) by lia.
  replace (length l - n) with 0 in Heql0 by lia.
  simpl in Heql0. discriminate.

  exfalso.
  (* rewrite <- minus_one_digit_ok_E1 in H0. *)
  assert (length l <= n) by lia.
  replace (length l - n) with 0 in Heql0 by lia.
  simpl in Heql0. discriminate.
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


Lemma minus_one_digit_ok'_incr1_true: forall x n a,
minus_one_digit_ok' x n a = true -> minus_one_digit_ok' (incr1 x) n a = true.
Proof.
  intros.
  generalize dependent x.
  generalize dependent a.
  induction n; intros.
  -
  simpl. destruct a.
  +
  remember (incr1 x).
  destruct b; auto.
  destruct x. discriminate.
  simpl in Heqb.
  destruct b; destruct (length (incr1 x) =? length x); discriminate.
  destruct b; auto.
  destruct b0; auto.
  +
  remember (incr1 x).
  destruct b; auto.
  destruct x. discriminate.
  simpl in Heqb.
  destruct b; destruct (length (incr1 x) =? length x); discriminate.
  destruct b; auto.
  destruct b0; auto.
  enough (x = []).
  rewrite H0 in H.
  simpl in H. auto.
  destruct x. auto.
  simpl in Heqb.
  destruct b; destruct (length (incr1 x) =? length x).
  all: inversion Heqb.
  clear Heqb.
  destruct x. discriminate.
  simpl in H1.
  destruct b; destruct (length (incr1 x) =? length x); discriminate.
  destruct x. discriminate.
  simpl in H1.
  destruct b; destruct (length (incr1 x) =? length x); discriminate.
  -
  remember (incr1 x).
  simpl.
  destruct a.
  all: remember (firstn (length b - S n) b).
  all: destruct l; auto.
  +
  remember (skipn (length b - S n) b).
  assert ([]++l = b).
  rewrite Heql.
  rewrite Heql0.
  apply firstn_skipn.
  simpl in  H0. rewrite H0.
  rewrite Heqb.
  apply IHn.
  rewrite <- minus_one_digit_ok_E1.
  auto.
  +
  exfalso.
  simpl in H.
  remember (firstn (length x - S n) x).
  destruct l; try discriminate.
  destruct b0; try discriminate.
  destruct l; try discriminate.
  remember (skipn (length x - S n) x).
  assert ([E1]++ l = x).
  rewrite Heql0.
  rewrite Heql1.
  apply firstn_skipn.

  symmetry in Heql0.
  apply firstn_1 in Heql0.
  inversion_clear Heql0.
  inversion_clear H1.
  enough (length x = length b \/ S (length x) = length b).
  inversion_clear H1.
  rewrite <- H4 in Heql.
  rewrite H2 in Heql.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  *
  lia.
  *
  rewrite H1 in Heqb.
  destruct x. discriminate.
  simpl in Heqb.
  destruct b; destruct  (length (incr1 x) =? length x); discriminate.
  *
  rewrite <- H4 in Heql.
  replace (S (length x) - S n) with 2 in Heql by lia.
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  lia.
  rewrite H1 in H4.
  discriminate.
  *
  enough (length x < length b \/ length x = length b).
  inversion_clear H1.
  rewrite Heqb in H4.
  apply incr1_length_plus in H4.
  right. auto.
  congruence.
  left. auto.
  enough (length x <= length b).
  lia.
  subst b.
  apply incr1_length.
  *
  inversion_clear H1.
  rewrite H2 in H3.
  simpl in H3. lia.
  *
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  enough (length x < length b \/ length x = length b).
  inversion_clear H1.
  replace (length x - S n ) with 0 in Heql0 by lia.
  simpl in Heql0.
  discriminate.
  rewrite H2 in Heql0.
  rewrite H0 in Heql0.
  discriminate.
  enough (length x <= length b).
  lia.
  subst b.
  apply incr1_length.
  rewrite H0 in Heqb.
  destruct x. discriminate.
  simpl in Heqb.
  destruct b1; destruct (length (incr1 x) =? length x); discriminate.
  *
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  enough (length x < length b \/ length x = length b).
  inversion_clear H1.
  replace (length x - S n ) with 0 in Heql0 by lia.
  simpl in Heql0.
  discriminate.
  rewrite H2 in Heql0.
  rewrite H0 in Heql0.
  discriminate.
  enough (length x <= length b).
  lia.
  subst b.
  apply incr1_length.
  rewrite H0 in Heqb.
  destruct x. discriminate.
  simpl in Heqb.
  destruct b0; destruct (length (incr1 x) =? length x); discriminate.
  +
  destruct b0 ; auto.
  destruct l; auto.
  remember (skipn (length b - S n) b).
  assert ([E1]++ l = b).
  rewrite Heql. rewrite Heql0.
  apply firstn_skipn.
  assert (length b = S (S n)).
  symmetry in Heql.
  apply firstn_1 in Heql.
  inversion_clear Heql.
  inversion_clear H1.
  lia.
  inversion_clear H1.
  rewrite H2 in H3. simpl in H3.
  lia.
  assert ( x = decr1 b ).
  rewrite Heqb.
  rewrite decr1_incr1.
  auto.
  rewrite H2 in H.
  simpl  in H0.
  rewrite <- H0 in H.
  remember (decr1 (E1 :: l)).
  assert (length l =  S n).
  rewrite  <- H0 in H1.
  simpl in H1. lia.
  rewrite <- minus_one_digit_ok_E1.
  remember (minus_one_digit_ok' l (S n) E1).
  destruct b0; auto.

  exfalso.
  symmetry in Heqb0.
  apply minus_one_digit_ok_always in Heqb0; auto.

  enough (Forall (eq E2) l0).
  enough (length l0 = S n).
  assert (length l0 <= S n) by lia.
  apply minus_one_digit_ok_false in H6.
  rewrite H6 in H. discriminate.

  assert (length (E1::l) = S(length l0)).
  replace (E1::l) with (incr1 l0).
  symmetry.
  apply incr1_length_plus.
  apply incr1_cons2_inv.
  auto.
  rewrite Heql1.
  apply incr1_decr1.
  simpl. lia.
  simpl in H5. lia.
  apply incr1_cons2.
  apply incr1_cons1_inv.
  replace (incr1 l0) with (E1::l).
  constructor; auto.
  rewrite Heql1.
  rewrite incr1_decr1.
  auto.
  simpl. lia.
Qed.

Lemma minus_one_digit_ok'_incr1_false: forall x n a,
minus_one_digit_ok' (incr1 x) n a = false -> 
minus_one_digit_ok' x n a = false.
Proof.
  intros.
  remember (minus_one_digit_ok' x n a).
  destruct b; auto.
  symmetry in Heqb.
  apply minus_one_digit_ok'_incr1_true in Heqb.
  rewrite H in Heqb.
  discriminate.
Qed.  

Lemma minus_one_digit_ltn2: forall b n,
length b <= S n ->
length (minus_one_digit' b (S n) E1) <  S n.
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  destruct b.
  simpl. lia.
  destruct b0.
  simpl.
  destruct b; auto.
  simpl in H. lia.
  destruct b.
  rewrite minus_one_digit_nil.
  simpl. lia.
  simpl in H.
  assert (length b0 <= S n) by lia.
  simpl.
  replace (length b0 - S n) with 0 by lia.
  simpl.
  assert (length b0 - n = 0 \/ length b0 - n = 1) by lia.
  inversion_clear H1.
  -
  rewrite H2.
  simpl. lia.
  -
  rewrite H2.
  simpl.
  destruct b.
  +
  rewrite <- minus_one_digit_E12.
  remember (IHn b0).
  assert (length (minus_one_digit' b0 (S n) E1) < S n).
  apply l.
  lia.
  lia.
  +
  rewrite app_length.
  simpl.
  lia.
Qed.

Lemma minus_one_digit_iter_decr_helper: forall b0 l l0 n,
length l0 = n ->
minus_one_digit' ((b0 :: l) ++ l0) n E1 = decr1 (b0 :: l) ++ l0.
Proof.
  intros.
  destruct n.
  -
  remember (b0::l).
  simpl.
  enough (l0 = []).
  rewrite H0.
  rewrite app_nil_r.
  rewrite app_nil_r.
  auto.
  destruct l0; auto.
  simpl in H. discriminate.
  -
  remember (b0::l).
  simpl.
  rewrite app_length.
  rewrite H.
  replace (length l1 + S n - S n) with (length l1) by lia.
  rewrite ?firstn_app.
  rewrite ?skipn_app.
  replace (length l1 - length l1) with 0 by lia.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_all.
  simpl.
  rewrite Heql1.
  auto.
Qed.

Lemma minus_one_digit_iter_decr_helper2: forall b0 b1 l l0 n,
length l0 = n ->
minus_one_digit' ((b0 :: b1 :: l) ++ l0) n E2 = 
decr1 (decr1 (b0 :: b1 :: l)) ++ l0.
Proof.
  intros.
  destruct n.
  -
  remember (b0 :: b1 :: l).
  simpl.
  enough (l0 = []).
  rewrite H0.
  rewrite app_nil_r.
  rewrite app_nil_r.
  auto.
  destruct l0; auto.
  simpl in H. discriminate.
  -
  remember (b0 :: b1 :: l).
  simpl.
  rewrite app_length.
  rewrite H.
  replace (length l1 + S n - S n) with (length l1) by lia.
  rewrite ?firstn_app.
  rewrite ?skipn_app.
  replace (length l1 - length l1) with 0 by lia.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_all.
  simpl.
  rewrite Heql1.
  destruct b0;
  auto.
Qed.


Lemma minus_one_digit_iter_decr_helper3: forall l0 n,
length l0 = n ->
minus_one_digit' (E2::l0) n E2 = l0.
Proof.
  intros.
  destruct n.
  -
  simpl.
  enough (l0 = []).
  rewrite H0.
  auto.
  destruct l0; auto.
  simpl in H. discriminate.
  -

  simpl.
  rewrite H.
  replace (S n - n) with 1 by lia.
  simpl.
  auto.
Qed.


Lemma minus_one_digit_ltn: forall b n,
length b < n ->
minus_one_digit' b n E1 = [].
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  lia.
  destruct b.
  simpl.
  rewrite minus_one_digit_nil. auto.
  simpl in H.
  assert (length b0 < n) by lia.
  apply IHn in H0.
  simpl.
  replace (length b0 - n) with 0 by lia.
  simpl.
  destruct n.
  lia.
  simpl.
  assert (length b0 - n = 0) by lia.
  rewrite H1.
  simpl.
  auto.
Qed.

Lemma Forall_skipn: forall {X} P (l: list X) n,
Forall P l ->
Forall P (skipn n l).
Proof.
  intros.
  generalize dependent l.
  induction n; intros.
  simpl.
  auto.
  destruct l.
  simpl. auto.
  inversion H.
  simpl.
  apply IHn.
  auto.
Qed.


Lemma Forall_firstn: forall {X} P (l: list X) n,
Forall P l ->
Forall P (firstn n l).
Proof.
  intros.
  generalize dependent l.
  induction n; intros.
  simpl.
  auto.
  destruct l.
  simpl. auto.
  inversion H.
  simpl.
  constructor. auto.
  apply IHn.
  auto.
Qed.

Transparent decr1.

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

Check incr1_cons1.


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

Check incr1_length_plus.

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

Lemma  Forall_app: forall {X} P (l m: list X),
Forall P l -> Forall P m -> Forall P (l++m).
Proof.
  intros.
  generalize dependent m.
  induction l; intros.
  simpl. auto.
  simpl.
  inversion H.
  constructor.
  auto.
  apply IHl.
  auto.
  auto.
Qed.

Lemma Forall_eq: forall {X} x (l m: list X),
length m = length l -> Forall (eq x) l -> Forall (eq x) m -> l = m.
Proof.
  intros.
  generalize dependent m.
  induction l; intros.
  destruct m; auto.
  simpl in H.
  lia.
  destruct m.
  simpl in H. lia.
  simpl in H.
  inversion H.
  apply IHl in H3.
  inversion H1.
  inversion H0.
  subst.
  auto.
  inversion H0; auto.
  inversion H1; auto.
Qed.

Lemma Forall_sub: forall {X} (l m: list X) P,
Forall P (l++m) -> Forall P l /\ Forall P m.
Proof.
  intros.
  generalize dependent m.
  induction l; intros.
  split.
  auto.
  auto.
  simpl in H.
  inversion H.
  split.
  constructor; auto.
  apply IHl with (m:=m).
  auto.
  apply IHl.
  auto.
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


Lemma minus_one_digit_decr1_helper: forall l b b2 b0 l0 l2 b3 b1 l1 l3
(Heql: l = decr1 b)
(H: (b2 :: b0 :: l0) ++ l2 = l)
(H0: (b3 :: b1 :: l1) ++ l3 = b)
(H3: length l2 = length l3),

decr1 (decr1 (b2 :: b0 :: l0)) ++ l2 =
decr1 (decr1 (decr1 (b3 :: b1 :: l1)) ++ l3).
Proof.

  intros.
  generalize dependent b2.
  generalize dependent b3.
  generalize dependent b0.
  generalize dependent b1.
  generalize dependent l2.
  generalize dependent l3.
  generalize dependent l0.
  generalize dependent l1.
  generalize dependent l.

  induction b using list_ind_length; intros.
  discriminate.
  destruct b.
  discriminate.
  inversion H0.
  clear H0.

  simpl in Heql.
  destruct b.
  ****
  destruct b4.
  *****
  discriminate.
  *****
  remember (b::b4).
  remember (length (decr1 l4) =? length l4).
  destruct b5.
  ******
  rewrite Heql in H1.
  inversion H1.
  clear H1.
  destruct l1; destruct l0.
  *******
  simpl in H5.
  simpl in H6.
  rewrite <- H5 in H6.
  simpl in H6.
  destruct b1.
  ********
  destruct l3.
  discriminate.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl decr1.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  auto.
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  auto.
  ********
  destruct l3.
  simpl.
  inversion H6.
  simpl. auto.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl. rewrite <- Heqb0.
  destruct l0.
  discriminate.
  auto.
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  auto.
  *******
  simpl in H5.
  exfalso.
  enough (length l4 < length (decr1 l4)).
  assert (length (decr1 l4) <= length l4).
  apply decr1_length.
  lia.
  rewrite <- H6.
  rewrite <- H5.
  simpl length.
  rewrite app_length.
  lia.
  *******
  simpl in H6.
  destruct l2.
  enough (l3 = []).
  subst l3.
  rewrite ?app_nil_r in *.
  destruct b0.
  enough (l4 = [E2]).
  rewrite H0 in H5.
  discriminate.
  replace [E2] with (incr1 [E1]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  enough (l4 = [E1;E1]).
  rewrite H0 in H5.
  inversion H5.
  simpl.
  subst.
  rewrite H0 in Heqb5.
  simpl in Heqb5.
  discriminate.
  replace [E1;E1] with (incr1 [E2]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  destruct l3; auto.
  simpl in H3. lia.
  simpl in H5.
  exfalso.
  rewrite <- H6 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  rewrite app_length in Heqb5.
  rewrite <- H3 in Heqb5.
  simpl in Heqb5.
  symmetry in Heqb5.
  apply PeanoNat.Nat.eqb_eq in Heqb5.
  lia.
  *******
  assert (decr1 (decr1 (b0 :: b6 :: l0)) ++ l2 =
  decr1 (decr1 (decr1 (b1 :: b5 :: l1)) ++ l3)).
  eapply H with (l1:=l4) (l:=decr1 l4); auto.
  remember (b0 :: b6 :: l0).
  remember (b1 :: b5 :: l1).
  simpl in H5.
  simpl in H6.
  assert (l5++l2=decr1 l4).
  rewrite Heql5.
  rewrite <- H6.
  auto.
  assert (l6++l3=l4).
  rewrite Heql6.
  rewrite <- H5.
  auto.
  simpl.
  rewrite Heql5.
  rewrite Heql6.
  rewrite <- Heql5.
  rewrite <- Heql6.
  remember (length (decr1 l5) =? length l5).
  remember (length (decr1 l6) =? length l6).
  destruct b7; destruct b8.
  ********
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  *********
  simpl in H0. simpl. auto.
  *********
  exfalso.
  enough (l5 = []).
  rewrite H8 in Heql5.
  discriminate.
  destruct l5; auto; try discriminate.
  *********
  exfalso.
  enough (l6 = []).
  rewrite H8 in Heql6.
  discriminate.
  destruct l6; auto; try discriminate.
  *********
  rewrite Heql7.
  rewrite Heql8.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.
  **********
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H8. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  remember (length (decr1 (b9 :: l9)) =? length (b9 :: l9)).
  destruct b10.
  ***********
  rewrite Heql9.
  rewrite <- Heql8.
  rewrite <- H0.
  rewrite <- Heql7.
  auto.
  ***********
  exfalso.
  enough (length (decr1 (b9 :: l9)) < length (b9 :: l9)).
  rewrite Heql9 in H8.
  rewrite Heql8 in H0.
  rewrite <- H0 in H8.
  rewrite Heql7 in H8.
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite ?app_length in H8.
  rewrite Heqb9 in H8.
  rewrite Heqb10 in H8.
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  rewrite Heqb7 in H8.
  rewrite Heqb8 in H8.
  symmetry in Heqb5.
  apply PeanoNat.Nat.eqb_eq in Heqb5.
  rewrite <- H1 in Heqb5.
  rewrite <- H7 in Heqb5.
  rewrite ?app_length in Heqb5.
  lia.
  remember (b9::l9).
  enough (length (decr1 l10) < length l10 \/ length (decr1 l10) = length l10).
  inversion H8; auto.
  rewrite H9 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 l10) <= length l10).
  lia.
  apply decr1_length.
  **********
  exfalso.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6)).
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite Heql8 in H0.
  rewrite Heql7 in H0.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l5) ++ l2)).
  rewrite H0 in H9.
  lia.
  rewrite app_length.
  enough (length l6 = length l5).
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  rewrite Heqb9.
  rewrite Heqb7.
  rewrite <- H9.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  rewrite app_length in H10.
  lia.
  apply decr1_length.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H9.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion H8; auto.
  rewrite H9 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough (length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.
  **********
  rewrite Heql7 in H0.
  rewrite Heql8 in H0.
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  enough (Forall (eq E1) (decr1 (decr1 l6))).
  enough (Forall (eq E2) (decr1 (decr1 l5))).
  enough (Forall (eq E1) l3).
  enough (Forall (eq E2) l2).
  assert (length ((E2 :: decr1 (decr1 l5)) ++ l2) = length (decr1 ((E1 :: decr1 (decr1 l6)) ++ l3))).
  rewrite ?app_length.
  simpl length at 1.
  enough (length (decr1 ((E1 :: decr1 (decr1 l6)) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  rewrite H12.
  enough (S (length (decr1 (decr1 l5))) = length (decr1 l5)).
  rewrite H13.
  rewrite app_length.
  rewrite Heqb10.
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H14.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  apply decr1_length_plus. 
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).  
  inversion H13; auto.
  rewrite H14 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.
  enough (S (length (decr1 ((E1 :: decr1 (decr1 l6)) ++ l3))) = length ((E1 :: decr1 (decr1 l6)) ++ l3)).
  rewrite ?app_length in H12.
  simpl length at 2 in H12.
  assert ((length (decr1 ((E1 :: decr1 (decr1 l6)) ++ l3))) = (length (decr1 (decr1 l6))) + length l3) by lia.
  rewrite H13.
  rewrite app_length.
  auto.
  apply decr1_length_plus.
  apply decr1_cons1_inv.
  simpl. lia.
  apply Forall_app.
  auto.
  auto.
  eapply  Forall_eq; auto.
  apply Forall_app.
  constructor.
  reflexivity.
  auto.
  auto.
  enough (Forall (eq E1) ((E1 :: decr1 (decr1 l6)) ++ l3)).
  apply decr1_cons2.
  apply decr1_cons1_inv.
  simpl. lia.
  auto.
  simpl.
  constructor.
  auto.
  apply Forall_app.
  auto. auto. auto.

  enough (Forall (eq E2) (decr1 (decr1 l5) ++ l2)).
  apply Forall_sub in H11.
  apply H11.
  rewrite H0.
  apply decr1_cons2.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3) \/ length (decr1 (decr1 (decr1 l6) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  inversion H11; auto.
  exfalso.
  rewrite <- H0 in H12. 
  rewrite ?app_length in H12.
  rewrite Heqb10 in H12.
  enough(length (decr1 (decr1 l5)) < length (decr1 l5)).
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H14.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion H13; auto.
  rewrite H14 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  lia.
  apply decr1_length.

  enough (Forall (eq E1) (decr1 (decr1 l6) ++ l3)).
  apply Forall_sub in H10.
  apply H10.
  apply decr1_cons1.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3) \/ length (decr1 (decr1 (decr1 l6) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  inversion H10; auto.
  exfalso.
  rewrite <- H0 in H11. 
  rewrite ?app_length in H11.
  rewrite Heqb10 in H11.
  enough(length (decr1 (decr1 l5)) < length (decr1 l5)).
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H13.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion H12; auto.
  rewrite H13 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  lia.
  apply decr1_length.

  enough (Forall (eq E2) (decr1 (decr1 l5) ++ l2)).
  apply Forall_sub in H9.
  apply H9.
  rewrite H0.
  apply decr1_cons2.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3) \/ length (decr1 (decr1 (decr1 l6) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  inversion H9; auto.
  exfalso.
  rewrite <- H0 in H10. 
  rewrite ?app_length in H10.
  rewrite Heqb10 in H10.
  enough(length (decr1 (decr1 l5)) < length (decr1 l5)).
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H12.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion H11; auto.
  rewrite H12 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  lia.
  apply decr1_length.

  enough (Forall (eq E1) (decr1 (decr1 l6) ++ l3)).
  apply Forall_sub in H8.
  apply H8.
  apply decr1_cons1.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3) \/ length (decr1 (decr1 (decr1 l6) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  inversion H8; auto.
  exfalso.
  rewrite <- H0 in H9. 
  rewrite ?app_length in H9.
  rewrite Heqb10 in H9.
  enough(length (decr1 (decr1 l5)) < length (decr1 l5)).
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H11.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion H10; auto.
  rewrite H11 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  lia.
  apply decr1_length.

  **********
  rewrite Heql7 in H0.
  rewrite Heql8 in H0.
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  simpl app.
  rewrite H0.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (length(decr1 (decr1 l5)) = 0).
  rewrite Heql5 in H8.
  assert (0 < length (decr1 (decr1 (b0 :: b6 :: l0)))).
  apply decr2_ge2digit.
  lia.
  assert (length (decr1 (decr1 l5) ++ l2) = 0).
  rewrite H0. auto.
  rewrite app_length in H8.
  lia.
  rewrite Heql9.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  auto.
  exfalso.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9 in H0.
  rewrite <- H0 in H8.
  rewrite ?app_length in H8.
  enough (length (decr1 (decr1 l5)) = length (decr1 (decr1 l6))).
  lia.
  enough (S (length (decr1 (decr1 l5))) = length (decr1 l5)).
  enough (S (length (decr1 (decr1 l6))) = length (decr1 l6)).
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H11.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion H10; auto.
  rewrite H11 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough (length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion H9; auto.
  rewrite H10 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.

  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_neq in Heqb0.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l6) ++ l3) \/ length (decr1 (decr1 (decr1 l6) ++ l3)) = length (decr1 (decr1 l6) ++ l3)).
  inversion_clear H8; auto.
  contradiction.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  lia.
  apply decr1_length.
  ********
  assert (Forall (eq E2) (decr1 l6)).
  apply decr1_cons2.
  enough (length (decr1 l6) < length l6 \/ length (decr1 l6) = length l6).
  inversion_clear H8; auto.
  exfalso.
  rewrite H9 in Heqb8.
  rewrite PeanoNat.Nat.eqb_refl in Heqb8.
  discriminate.
  enough (length (decr1 l6) <= length l6 ).
  lia.
  apply decr1_length.
  assert (S (length (decr1 l6)) = length l6 ).
  apply decr1_length_plus.
  apply decr1_cons2_inv; auto.
  subst l6.
  simpl. lia.

  simpl.
  assert (0 < length (decr1 l5)).
  rewrite Heql5.
  apply decr1_ge2digit.
  remember (decr1 l5).
  destruct l7.
  simpl in H10. lia.
  rewrite Heql7.
  assert (0 < length (decr1 l6)).
  rewrite Heql6.
  apply decr1_ge2digit.
  remember (decr1 l6).
  destruct l8.
  simpl in H11. lia.
  rewrite Heql8.

  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).

  assert (length l5 = length l6).

  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H12.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  assert (0 < length (decr1 (decr1 l6))).
  subst l6.
  apply decr2_ge2digit.
  destruct b9; destruct b10.
  *********
  clear H10 H11. 
  rewrite Heql8 in *.
  rewrite Heql7 in *.
  simpl app.
  rewrite H0.
  remember (decr1 (decr1 l6)).
  simpl.
  destruct l9.
  simpl in H13. lia.
  Opaque decr1 length.
  simpl.
  replace (b9 :: l9 ++ l3) with ((b9 :: l9) ++ l3) by auto.
  remember (b9::l9).
  remember (length (decr1 (l10 ++ l3)) =? length (l10 ++ l3)).
  destruct b10.
  exfalso.
  clear H13.
  rewrite <- H0 in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite ?app_length in Heqb0.
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite Heqb9 in Heqb0.
  rewrite Heqb7 in Heqb0.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  lia.
  exfalso.
  enough (Forall (eq E1) (l10 ++ l3)).
  rewrite Heql9 in H10.
  apply Forall_sub in H10.
  inversion_clear H10.
  apply ForallE2_not_ForallE1_decr1 in H8.
  apply H8.
  auto.
  rewrite <- Heql8.
  destruct l8.
  exfalso.
  rewrite <- Heql8 in H8.
  inversion H8.
  rewrite <- H16 in Heql8.
  rewrite <- Heql8 in Heql9.
  Transparent length decr1.
  simpl in Heql9.
  enough (l6 = [E1;E1]).
  enough (S(length (decr1 (l10 ++ l3))) = length (l10++l3)).
  enough (length (decr1 (l10 ++ l3)) = length l3).
  rewrite <- H0 in H20.
  rewrite app_length in H20.
  assert (length (decr1 (decr1 l5)) = 0) by lia.
  assert (0 < length (decr1 (decr1 l5))).
  rewrite Heql5.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9  in H19 at 2.
  rewrite app_length in H19.
  simpl in H19.
  lia.
  apply decr1_length_plus.
  enough (length (decr1 (l10 ++ l3)) < length (l10 ++ l3) \/ length (decr1 (l10 ++ l3)) = length (l10 ++ l3)).
  inversion H19; auto.
  exfalso.
  rewrite H20 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 (l10 ++ l3)) <= length (l10 ++ l3)).
  lia.
  apply decr1_length.
  replace [E1;E1] with (incr1 [E2]) by auto.
  rewrite Heql8.
  rewrite incr1_decr1.
  auto.
  rewrite  Heql6.
  simpl. lia.
  simpl. lia.
  apply decr1_cons1.
  enough (length (decr1 (l10 ++ l3)) < length (l10 ++ l3) \/ length (decr1 (l10 ++ l3)) = length (l10 ++ l3)).
  inversion H10; auto.
  rewrite H11 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 (l10 ++ l3)) <= length (l10 ++ l3) ).
  lia.
  apply decr1_length.
  *********
  clear H10 H11. 
  rewrite Heql8 in *.
  rewrite Heql7 in *.
  simpl app.
  rewrite H0.
  remember (decr1 (decr1 l6)).
  simpl.
  destruct l9.
  simpl in H13. lia.
  Opaque decr1 length.
  simpl.
  replace (b9 :: l9 ++ l3) with ((b9 :: l9) ++ l3) by auto.
  remember (b9::l9).
  remember (length (decr1 (l10 ++ l3)) =? length (l10 ++ l3)).
  destruct b10.
  exfalso.
  clear H13.
  rewrite <- H0 in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite ?app_length in Heqb0.
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite Heqb9 in Heqb0.
  rewrite Heqb7 in Heqb0.
  symmetry in Heqb10.
  enough (length l10 < length (decr1 l6)).
  lia.
  enough(length l10 < length (decr1 l6) \/ length l10 = length (decr1 l6)).
  inversion_clear H10; auto.
  exfalso.
  rewrite H11 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough(length l10 <= length (decr1 l6)).
  lia.
  rewrite Heql9.
  apply decr1_length.

  exfalso.
  enough(S (length (decr1 (l10 ++ l3))) = length (l10 ++ l3)).
  rewrite <- H0 in H10.
  rewrite ?app_length in H10.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite Heqb9 in H10.
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  rewrite Heqb7 in H10.
  enough (S(length l10) = length (decr1 l6)).
  lia.
  rewrite Heql9.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion_clear H11; auto.
  rewrite Heql9 in Heqb10.
  rewrite H14 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough(length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.

  apply decr1_length_plus.
  enough (length (decr1 (l10++l3)) < length (l10++l3) \/ length (decr1 (l10++l3)) = length (l10++l3)).
  inversion_clear H10; auto.
  rewrite H11 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough(length (decr1 (l10++l3)) <= length (l10++l3)).
  lia.
  apply decr1_length.
  *********
  clear H10 H11. 
  rewrite Heql8 in *.
  rewrite Heql7 in *.
  simpl app.
  rewrite H0.
  remember (decr1 (decr1 l6)).
  Transparent decr1 length.
  simpl.
  destruct l9.
  simpl in H13. lia.
  Opaque decr1 length.
  simpl.
  replace (b9 :: l9 ++ l3) with ((b9 :: l9) ++ l3) by auto.
  remember (b9::l9).
  remember (length (decr1 (l10 ++ l3)) =? length (l10 ++ l3)).
  destruct b10.
  auto.
  exfalso.
  clear H13.
  rewrite <- H0 in Heqb0.
  symmetry in Heqb0.
  enough(S (length (decr1 (l10 ++ l3))) = length (l10 ++ l3)).
  rewrite <- H0 in H10.
  rewrite ?app_length in H10.
  enough (S(length (decr1 (decr1 l5))) = length (decr1 l5)).
  rewrite <- plus_Sn_m in H10.
  rewrite H11 in H10.
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  rewrite Heqb7 in H10.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite Heqb10 in H10.
  lia.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion_clear H11; auto.
  exfalso.
  rewrite H13 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.

  apply decr1_length_plus.
  enough (length (decr1 (l10++l3)) < length (l10++l3) \/ length (decr1 (l10++l3)) = length (l10++l3)).
  inversion_clear H10; auto.
  exfalso.
  rewrite H0 in Heqb0.
  rewrite H11 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 (l10 ++ l3)) <= length (l10 ++ l3)).
  lia.
  apply decr1_length.
  *********
  clear H10 H11. 
  rewrite Heql8 in *.
  rewrite Heql7 in *.
  simpl app.
  rewrite H0.
  remember (decr1 (decr1 l6)).
  Transparent decr1 length.
  simpl.
  destruct l9.
  simpl in H13. lia.
  Opaque decr1 length.
  simpl.
  replace (b9 :: l9 ++ l3) with ((b9 :: l9) ++ l3) by auto.
  remember (b9::l9).
  remember (length (decr1 (l10 ++ l3)) =? length (l10 ++ l3)).
  destruct b10.
  exfalso.
  clear H13.
  rewrite <- H0 in Heqb0.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite ?app_length in Heqb0.
  enough (S (length (decr1 (decr1 l5))) = length (decr1 l5)).
  enough (S (length l10) = length (decr1 l6)).
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  lia.

  rewrite Heql9.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion_clear H11; auto.
  exfalso.
  rewrite Heql9 in Heqb10.
  rewrite H13 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough (length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.

  apply decr1_length_plus.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion_clear H10; auto.
  exfalso.
  rewrite H11 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.

  exfalso.
  clear H13.
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  enough (S (length (decr1 (decr1 l5))) = length (decr1 l5)).
  enough (S(length (decr1 (l10 ++ l3))) = length (l10 ++ l3)).
  rewrite <- H0 in H11.
  rewrite ?app_length in H11.
  enough (S (length l10) = length (decr1 l6)).
  lia.

  rewrite Heql9.
  apply decr1_length_plus.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ 
          length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion_clear H13; auto.
  exfalso.
  rewrite Heql9 in Heqb10. 
  rewrite H14 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough (length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.

  apply decr1_length_plus.
  enough (length (decr1 (l10 ++ l3)) < length (l10 ++ l3) \/ 
          length (decr1 (l10 ++ l3)) = length (l10 ++ l3)).
  inversion_clear H11; auto.
  exfalso.
  rewrite H13 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 (l10 ++ l3)) <= length (l10 ++ l3)).
  lia.
  apply decr1_length.

  apply decr1_length_plus.
  enough (length (decr1 (decr1 l5)) < length (decr1 l5) \/ 
          length (decr1 (decr1 l5)) = length (decr1 l5)).
  inversion_clear H10; auto.
  exfalso.
  rewrite H11 in Heqb9.
  rewrite PeanoNat.Nat.eqb_refl in Heqb9.
  discriminate.
  enough (length (decr1 (decr1 l5)) <= length (decr1 l5)).
  lia.
  apply decr1_length.

  ********
  symmetry in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  enough (S (length (decr1 l5)) = length l5).
  enough (length l5 = length l6).
  Transparent decr1.
  simpl.
  remember (decr1 l5).
  assert (0 < length l7).
  rewrite Heql7.
  rewrite Heql5.
  apply decr1_ge2digit.
  destruct l7.
  Transparent length.
  simpl in H10. lia.
  rewrite Heql7 in *.
  remember (decr1 l6).
  assert (0 < length l8).
  rewrite Heql8.
  rewrite Heql6.
  apply decr1_ge2digit.
  destruct l8.
  simpl in H11. lia.
  rewrite Heql8 in *.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.

  *********
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  clear H11 H10.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H10.
  rewrite app_length in H10.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  rewrite H0.
  auto.

  *********
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  clear H10 H11.
  enough (S (length (decr1 (decr1 l6))) = length (decr1 l6)).
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H11.
  rewrite app_length in H11.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  rewrite H0.
  auto.
  exfalso.
  enough (S(length (decr1 (decr1 (decr1 l6) ++ l3))) = length (decr1 (decr1 l6) ++ l3)).
  rewrite <- H0 in H11.
  rewrite ?app_length in H11.
  lia.
  apply decr1_ltlength_S. auto.
  apply decr1_ltlength_S. auto.
  *********
  simpl.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =?
  length (decr1 (decr1 l6) ++ l3)).
  exfalso.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  apply decr1_ltlength_S in Heqb9.
  destruct b9.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ? app_length in Heqb0.
  lia.  
  apply decr1_ltlength_S in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ? app_length in Heqb0.
  lia.
  *********
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H12.
  rewrite app_length in H12.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  apply decr1_ltlength_S in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  destruct b10; try congruence.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H9.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  *********
  apply decr1_ltlength_S. auto.
  ********
  enough (H100: length l5 = length l6).
  apply decr1_ltlength_S in Heqb7.
  apply decr1_ltlength_S in Heqb8.
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  assert (0 < length l7).
  rewrite Heql7.
  rewrite Heql5.
  apply decr1_ge2digit.
  assert (0 < length l8).
  rewrite Heql8.
  rewrite Heql6.
  apply decr1_ge2digit.
  destruct l7; destruct l8.
  exfalso. simpl in H8. lia.
  exfalso. simpl in H8. lia.
  exfalso. simpl in H9. lia.
  clear H8 H9.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.
  *********
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H8.
  rewrite app_length in H8.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10; try congruence.
  exfalso.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  symmetry in Heqb10. apply PeanoNat.Nat.eqb_eq in Heqb10.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  simpl.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (H200: length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H200.
  rewrite app_length in H200.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  simpl.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =?
  length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  exfalso.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  simpl length.
  apply decr1_ltlength_S in Heqb0.
  rewrite Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  apply decr1_ltlength_S in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (H200:length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H200.
  rewrite app_length in H200.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10; try congruence.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (H200:length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H200.
  rewrite app_length in H200.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =?
  length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  congruence.
  simpl length.
  apply decr1_ltlength_S in Heqb0.
  rewrite Heqb0.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  apply decr1_ltlength_S in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  lia.
  *********
  enough (H201:length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H201.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  ******
  apply decr1_ltlength_S in Heqb5.
  rewrite Heql in H1.
  inversion H1.
  clear H1.
  destruct l1; destruct l0.
  *******
  simpl in H5.
  simpl in H6.
  rewrite <- H5 in H6.
  simpl in H6.
  destruct b1.
  ********
  destruct l3.
  discriminate.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl decr1.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  apply decr1_cons1_inv in H11.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  lia.
  simpl. lia. 
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  exfalso.
  rewrite <- H3 in Heqb0.
  rewrite <- H7 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  ********
  destruct l3.
  simpl.
  inversion H6.
  simpl.
  exfalso.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  lia. 
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl. rewrite <- Heqb0.
  destruct l0.
  discriminate.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  discriminate.
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  discriminate.
  *******
  simpl in H5.
  exfalso.
  enough (length l4 < length (decr1 l4)).
  assert (length (decr1 l4) <= length l4).
  apply decr1_length.
  lia.
  rewrite <- H6.
  rewrite <- H5.
  simpl length.
  rewrite app_length.
  lia.
  *******
  simpl in H6.
  destruct l2.
  enough (l3 = []).
  subst l3.
  rewrite ?app_nil_r in *.
  destruct b0.
  enough (l4 = [E2]).
  rewrite H0 in H5.
  discriminate.
  replace [E2] with (incr1 [E1]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  enough (l4 = [E1;E1]).
  rewrite H0 in H5.
  inversion H5.
  simpl. auto.
  replace [E1;E1] with (incr1 [E2]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  destruct l3; auto.
  simpl in H3. lia.
  simpl in H5.

  enough(Forall (eq E1) l4).
  enough(Forall (eq E2) (decr1 l4)).
  enough(l1=[]).
  rewrite H7 in *.
  rewrite <- H5 in H0.
  simpl in H0.
  inversion H0.
  rewrite <- H10.
  inversion H11.
  rewrite <- H14.
  rewrite <- H6 in H1.
  inversion H1.
  rewrite <- H18.
  inversion H19.
  rewrite <- H22.
  remember (decr1 (decr1 [E2; E2])).
  simpl in Heql8.
  subst l8.
  remember (decr1 (decr1 [E1; E1; E1])).
  simpl in Heql8.
  subst l8.
  Opaque decr1.
  simpl.
  Transparent decr1.
  apply decr1_special.
  simpl. simpl in H3. lia.
  constructor; auto.
  constructor; auto.
  destruct l1; auto.
  exfalso.
  rewrite <- H6 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  rewrite app_length in Heqb5.
  simpl in H3.
  rewrite H3 in Heqb5.
  lia.
  apply decr1_cons2.
  lia.
  apply decr1_cons1.
  lia.
  *******
  assert (decr1 (decr1 (b0 :: b6 :: l0)) ++ l2 =
  decr1 (decr1 (decr1 (b1 :: b5 :: l1)) ++ l3)).
  eapply H with (l1:=l4) (l:=decr1 l4); auto.
  remember (b0 :: b6 :: l0).
  remember (b1 :: b5 :: l1).
  simpl in H5.
  simpl in H6.
  assert (l5++l2=decr1 l4).
  rewrite Heql5.
  rewrite <- H6.
  auto.
  assert (l6++l3=l4).
  rewrite Heql6.
  rewrite <- H5.
  auto.
  assert (S(length l5) = length l6).
  enough (length (l6++l3) = S (length (l5++l2))).
  rewrite ?app_length  in H8.
  lia.
  rewrite H7.
  rewrite H1.
  lia.

  simpl.
  rewrite Heql5.
  rewrite Heql6.
  rewrite <- Heql5.
  rewrite <- Heql6.

  assert (S (length (decr1 l6)) = length l6).
  apply decr1_length_plus.
  apply decr1_cons1_inv.
  rewrite Heql6. simpl. lia.
  enough (Forall (eq E1) l4).
  rewrite <- H7 in H9.
  apply Forall_sub in H9.
  apply H9.
  apply decr1_cons1.
  lia.

  assert ((length (decr1 l5)) = length l5).
  remember (length (decr1 l5) =? length l5).
  destruct b7.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb7.
  assert (length (decr1 l5) < length l5) by lia.
  apply decr1_cons1 in H10.
  assert (Forall (eq E2) (decr1 l4)).
  apply decr1_cons2.
  lia.
  rewrite <- H1 in H11.
  apply Forall_sub in H11.
  inversion_clear H11.
  destruct l5.
  discriminate.
  inversion H10.
  inversion H12.
  rewrite <- H19 in H15.
  discriminate.
  rewrite H10.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite <- H9.
  replace  (length (decr1 l6) =? S (length (decr1 l6))) with false.
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  exfalso.
  rewrite Heql5 in H10.
  simpl in H10. lia.
  rewrite Heql5 in H10.
  simpl in H10. lia.
  rewrite Heql6 in H9.
  simpl in H9. lia.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  (*Forall (eq E1) l6*)
  (*Forall (eq E2) (decr1 l6)*)
  enough (length (decr1 (decr1 l6)) = length (decr1 l6)).
  rewrite H11.
  rewrite PeanoNat.Nat.eqb_refl.
  (*Forall (eq E2) l5*)
  (*~Forall (eq E1) (decr1 l5)*)
  enough (length (decr1 (decr1 l5)) = length (decr1 l5)).
  rewrite H12.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl app.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (H200:length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H200.
  rewrite app_length in H200.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10; try congruence.
  exfalso.
  apply decr1_ltlength_S in Heqb10.
  rewrite <- H0 in Heqb10.
  rewrite ? app_length in Heqb10.
  lia.

  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  destruct b9.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb9.
  assert (length (decr1 (decr1 l5)) < length (decr1 l5)) by lia.
  apply decr1_cons1 in H12.
  assert (Forall (eq E2) l5).
  enough (Forall  (eq E2)  (decr1 l4)).
  rewrite <- H1 in H13.
  apply Forall_sub in H13.
  apply H13.
  apply decr1_cons2.
  lia.
  apply ForallE2_not_ForallE1_decr1 in H13.
  contradiction.
  rewrite Heql5.
  simpl. lia.

  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb9.
  assert (length (decr1 (decr1 l6)) < length (decr1 l6)) by lia.
  apply decr1_cons1 in H11.
  assert (Forall (eq E2) (decr1 l6)).
  apply decr1_cons2.
  lia.
  rewrite <- Heql8 in *.
  inversion H11.
  inversion H12.
  rewrite <- H19 in H15.
  discriminate.

  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.


  ****
  destruct b4.
  *****
  discriminate.
  *****
  remember (b::b4).
  remember (length (decr1 l4) =? length l4).
  destruct b5.
  ******
  rewrite Heql in H1.
  inversion H1.
  clear H1.
  destruct l1; destruct l0.
  *******
  simpl in H5.
  simpl in H6.
  rewrite <- H5 in H6.
  simpl in H6.
  destruct b1.
  ********
  destruct l3.
  discriminate.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl decr1.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  remember (b5 :: l0).
  remember (length (E1 :: decr1 l1) =? S (length l1)).
  destruct b6; auto.
  exfalso.
  simpl in Heqb6.
  rewrite <- Heqb0 in Heqb6.
  discriminate.
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.

  remember (b5 :: l0).
  remember (length (E2 :: decr1 l1) =? S (length l1)).
  destruct b6; auto.
  exfalso.
  simpl in Heqb6.
  rewrite <- H7 in Heqb6.
  rewrite H3 in Heqb6.
  rewrite PeanoNat.Nat.eqb_refl in Heqb6.
  discriminate.
  ********
  destruct l3.
  simpl.
  inversion H6.
  simpl. auto.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  inversion H6.
  simpl. rewrite <- Heqb0.
  destruct l0.
  discriminate.


  remember (b5 :: l0).
  remember (length (E2 :: decr1 l1) =? S (length l1)).
  destruct b6; auto.
  exfalso.
  simpl in Heqb6.
  rewrite <- Heqb0 in Heqb6.
  discriminate.
  inversion H6.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.

  remember (b5 :: l0).
  remember (length (E1 :: E2 :: decr1 l1) =? S (length l1)).
  destruct b6; auto.
  exfalso.
  simpl length in Heqb6.
  rewrite <- H3 in Heqb6.
  rewrite H7 in Heqb6.
  simpl in Heqb6.
  rewrite PeanoNat.Nat.eqb_refl in Heqb6.
  discriminate.

  *******
  simpl in H5.
  exfalso.
  enough (length l4 < length (decr1 l4)).
  assert (length (decr1 l4) <= length l4).
  apply decr1_length.
  lia.
  rewrite <- H6.
  rewrite <- H5.
  simpl length.
  rewrite app_length.
  lia.
  *******
  simpl in H6.
  destruct l2.
  enough (l3 = []).
  subst l3.
  rewrite ?app_nil_r in *.
  destruct b0.
  enough (l4 = [E2]).
  rewrite H0 in H5.
  discriminate.
  replace [E2] with (incr1 [E1]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  enough (l4 = [E1;E1]).
  rewrite H0 in H5.
  inversion H5.
  simpl.
  subst.
  rewrite H0 in Heqb5.
  simpl in Heqb5.
  discriminate.
  replace [E1;E1] with (incr1 [E2]) by auto.
  rewrite H6.
  rewrite incr1_decr1.
  auto.
  rewrite Heql4.
  simpl. lia.
  destruct l3; auto.
  simpl in H3. lia.
  simpl in H5.
  exfalso.
  rewrite <- H6 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  rewrite app_length in Heqb5.
  rewrite <- H3 in Heqb5.
  simpl in Heqb5.
  symmetry in Heqb5.
  apply PeanoNat.Nat.eqb_eq in Heqb5.
  lia.
  *******
  assert (decr1 (decr1 (b0 :: b6 :: l0)) ++ l2 =
  decr1 (decr1 (decr1 (b1 :: b5 :: l1)) ++ l3)).
  eapply H with (l1:=l4) (l:=decr1 l4); auto.
  remember (b0 :: b6 :: l0).
  remember (b1 :: b5 :: l1).
  simpl in H5.
  simpl in H6.
  assert (l5++l2=decr1 l4).
  rewrite Heql5.
  rewrite <- H6.
  auto.
  assert (l6++l3=l4).
  rewrite Heql6.
  rewrite <- H5.
  auto.
  simpl.
  rewrite Heql5.
  rewrite Heql6.
  rewrite <- Heql5.
  rewrite <- Heql6.
  remember (length (decr1 l5) =? length l5).
  remember (length (decr1 l6) =? length l6).
  destruct b7; destruct b8.
  ********
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  *********
  simpl in H0. 
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  *********
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  *********
  exfalso.
  rewrite Heql6 in Heqb8.
  simpl in Heqb8.
  discriminate.
  *********
  rewrite Heql7.
  rewrite Heql8.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.
  **********
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H8. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  remember (length (decr1 (b9 :: l9)) =? length (b9 :: l9)).
  destruct b10.
  ***********
  rewrite Heql9.
  rewrite <- Heql8.
  rewrite <- H0.
  rewrite <- Heql7.
  auto.
  ***********
  exfalso.
  enough (length (decr1 (b9 :: l9)) < length (b9 :: l9)).
  rewrite Heql9 in H8.
  rewrite Heql8 in H0.
  rewrite <- H0 in H8.
  rewrite Heql7 in H8.
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite ?app_length in H8.
  rewrite Heqb9 in H8.
  rewrite Heqb10 in H8.
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  rewrite Heqb7 in H8.
  rewrite Heqb8 in H8.
  symmetry in Heqb5.
  apply PeanoNat.Nat.eqb_eq in Heqb5.
  rewrite <- H1 in Heqb5.
  rewrite <- H7 in Heqb5.
  rewrite ?app_length in Heqb5.
  lia.
  remember (b9::l9).
  enough (length (decr1 l10) < length l10 \/ length (decr1 l10) = length l10).
  inversion H8; auto.
  rewrite H9 in Heqb0.
  rewrite PeanoNat.Nat.eqb_refl in Heqb0.
  discriminate.
  enough (length (decr1 l10) <= length l10).
  lia.
  apply decr1_length.
  **********
  exfalso.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6)).
  symmetry in Heqb7.
  symmetry in Heqb8.
  symmetry in Heqb9.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite Heql8 in H0.
  rewrite Heql7 in H0.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) < length (decr1 (decr1 l5) ++ l2)).
  rewrite H0 in H9.
  lia.
  rewrite app_length.
  enough (length l6 = length l5).
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  rewrite Heqb9.
  rewrite Heqb7.
  rewrite <- H9.
  enough (length (decr1 (decr1 (decr1 l6) ++ l3)) <= length (decr1 (decr1 l6) ++ l3)).
  rewrite app_length in H10.
  lia.
  apply decr1_length.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H9.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  enough (length (decr1 (decr1 l6)) < length (decr1 l6) \/ length (decr1 (decr1 l6)) = length (decr1 l6)).
  inversion H8; auto.
  rewrite H9 in Heqb10.
  rewrite PeanoNat.Nat.eqb_refl in Heqb10.
  discriminate.
  enough (length (decr1 (decr1 l6)) <= length (decr1 l6)).
  lia.
  apply decr1_length.
  **********
  rewrite Heql7 in H0.
  rewrite Heql8 in H0.
  rewrite Heql7 in Heqb7.
  rewrite Heql8 in Heqb8.
  symmetry in Heqb7.
  symmetry in Heqb8.

  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H8. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10; try congruence.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  apply decr1_ltlength_S in Heqb9.
  enough (length l5 = length l6).
  lia.
  enough (length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H8.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  **********
  simpl.
  symmetry in Heqb7. apply PeanoNat.Nat.eqb_eq in Heqb7.
  symmetry in Heqb8. apply PeanoNat.Nat.eqb_eq in Heqb8.
  apply decr1_ltlength_S in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H8. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =?
  length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  congruence.
  simpl length.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  rewrite H0.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  enough (length l5 = length l6).
  lia.
  enough (H100:length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H100.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  ********
  symmetry in Heqb7.
  apply PeanoNat.Nat.eqb_eq in Heqb7.
  apply decr1_ltlength_S in Heqb8.
  assert (H100: length l5 = length l6).
  enough (H101: length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H101.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql6 in Heqb8.
  simpl in Heqb8.
  discriminate.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.
  *********
  simpl length.
  simpl.
  rewrite <- Heqb10.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  exfalso.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  symmetry in Heqb10. apply PeanoNat.Nat.eqb_eq in Heqb10.
  symmetry in Heqb0. apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  symmetry in Heqb10. apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  simpl length.
  apply decr1_ltlength_S in Heqb10.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite <- Heqb10.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  symmetry in Heqb0.
  simpl.
  (* apply PeanoNat.Nat.eqb_eq in Heqb0.
  simpl. *)
  rewrite Heqb0.
  simpl.
  rewrite Heqb0.
  exfalso.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  apply decr1_ltlength_S in Heqb9.
  simpl.
  rewrite <- Heqb10.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  congruence.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  *********
  apply decr1_ltlength_S in Heqb9.
  apply decr1_ltlength_S in Heqb10.
  rewrite <- Heqb10.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  simpl.
  rewrite <- Heqb0.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  ********
  apply decr1_ltlength_S in Heqb7.
  symmetry in Heqb8. apply PeanoNat.Nat.eqb_eq in Heqb8.
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql6 in Heqb8.
  simpl in Heqb8.
  discriminate.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  assert (H100:length l5 = length l6).
  enough (H103:length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H103.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  destruct b9; destruct b10.
  *********
  simpl.
  rewrite <- Heqb9.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  exfalso.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  symmetry in Heqb10. apply PeanoNat.Nat.eqb_eq in Heqb10.
  symmetry in Heqb0. apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.
  simpl.
  congruence.
  *********
  apply decr1_ltlength_S in Heqb10.
  simpl.
  rewrite <- Heqb9.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  congruence.

  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.

  exfalso.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  *********
  apply decr1_ltlength_S in Heqb9.
  rewrite <- Heqb9.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.
  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  lia.
  exfalso.
  apply decr1_ltlength_S in Heqb0.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  *********
  apply decr1_ltlength_S in Heqb9.
  rewrite <- Heqb9.
  apply decr1_ltlength_S in Heqb10.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  congruence.

  ********
  apply decr1_ltlength_S in Heqb7.
  apply decr1_ltlength_S in Heqb8.
  simpl.
  assert (H100: length l5 = length l6).
  enough (H101: length (l5++l2) = length (l6++l3)).
  rewrite ?app_length in H101.
  lia.
  rewrite H1.
  rewrite H7.
  apply PeanoNat.Nat.eqb_eq.
  auto.

  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql5 in Heqb7.
  simpl in Heqb7.
  discriminate.
  exfalso.
  rewrite Heql6 in Heqb8.
  simpl in Heqb8.
  discriminate.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b9; destruct b10.
  *********
  simpl.
  rewrite <- Heqb9.
  rewrite <- Heqb10.
  simpl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  congruence.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  symmetry in Heqb9. apply PeanoNat.Nat.eqb_eq in Heqb9.
  symmetry in Heqb10. apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.


  *********
  apply decr1_ltlength_S in Heqb10.
  rewrite <- Heqb10.
  simpl.
  rewrite <- Heqb9.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  simpl.
  rewrite <- Heqb0.

  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  lia.

  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  exfalso.

  symmetry in Heqb9.
  apply PeanoNat.Nat.eqb_eq in Heqb9.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  *********
  apply decr1_ltlength_S in Heqb9.
  rewrite <- Heqb9.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite <- Heqb10.

  simpl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  exfalso.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  apply decr1_ltlength_S in Heqb0.

  symmetry in Heqb10.
  apply PeanoNat.Nat.eqb_eq in Heqb10.
  rewrite <- Heqb0.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  congruence.

  *********

  apply decr1_ltlength_S in Heqb9.
  rewrite <- Heqb9.

  apply decr1_ltlength_S in Heqb10.
  rewrite <- Heqb10.

  simpl.
  rewrite ?PeanoNat.Nat.eqb_refl.
  simpl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  enough (H102: 1 <= length (decr1 (decr1 l6))).
  destruct (decr1 (decr1 l6)).
  simpl in H102. lia.
  discriminate.
  subst l6.
  apply decr2_ge2digit.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b10.
  simpl.
  rewrite <- Heqb0.
  simpl.
  rewrite <- Heqb0.
  congruence.

  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  simpl.
  rewrite ?PeanoNat.Nat.eqb_refl.
  exfalso.
  rewrite <- H0 in Heqb0.
  rewrite ?app_length in Heqb0.
  lia.

  ******
  apply decr1_ltlength_S in Heqb5.
  rewrite Heql in H1.
  inversion H1.
  clear H1.
  destruct l1; destruct l0.
  *******
  simpl in H5.
  simpl in H7.
  rewrite <- H5 in H7.
  simpl in H7.
  destruct b1.
  ********
  destruct l3.
  rewrite H7.
  auto.
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.
  simpl decr1.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  setoid_rewrite <- Heqb0.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  apply decr1_cons1_inv in H10.
  symmetry in Heqb0.
  apply PeanoNat.Nat.eqb_eq in Heqb0.
  lia.
  simpl. lia. 
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  setoid_rewrite <- Heqb0.
  rewrite H7.
  auto.
  ********
  destruct l3.
  simpl.
  exfalso.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  lia. 
  remember (b1 :: l3).
  remember (length (decr1 l0) =? length l0).
  destruct b5.

  simpl. rewrite <- Heqb0.
  destruct l0.
  discriminate.
  setoid_rewrite <- Heqb0.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  discriminate.
  simpl.
  rewrite <- Heqb0.
  destruct l0.
  discriminate.
  apply decr1_ltlength_S in Heqb0.
  rewrite <- Heqb0.
  setoid_rewrite PeanoNat.Nat.eqb_refl.
  exfalso.
  assert (length (decr1 l4) < length l4) by lia.
  apply decr1_cons1 in H0.
  rewrite <- H5 in H0.
  inversion H0.
  discriminate.
  *******
  simpl in H5.
  enough (l0=[]).
  rewrite H0.
  rewrite H0 in H7.
  rewrite <- H7 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  lia.
  destruct l0; auto.
  exfalso.
  enough (length l4 < length (decr1 l4)).
  assert (length (decr1 l4) <= length l4).
  apply decr1_length.
  lia. 
  rewrite <- H7.
  rewrite <- H5.
  simpl length.
  rewrite app_length.
  lia.
  *******
  simpl in H7.
  destruct l2.
  enough (l3 = []).
  subst l3.
  rewrite ?app_nil_r in *.
  symmetry in H7.
  apply decr1_nil in H7.
  inversion_clear H7.
  exfalso.
  subst l4.
  discriminate.
  rewrite H0 in H5.
  discriminate.
  destruct l3; auto.
  simpl in H3. lia.

  exfalso.
  rewrite <- H7 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  rewrite ?app_length in Heqb5.
  rewrite <- H3 in Heqb5.
  simpl in Heqb5.
  lia.
  *******
  destruct l0.
  ********
  destruct l1.

  enough (Forall (eq E1) l4).
  enough (Forall (eq E2) (decr1 l4)).
  rewrite <- H5 in H0.
  rewrite <- H7 in H1.
  inversion H0.
  rewrite <- H10.
  inversion H1.
  rewrite <- H14.
  inversion H11.
  rewrite <- H18.

  remember (decr1 (decr1 [E1; E2; E2])).
  simpl in Heql6.
  subst l6.
  remember (decr1 (decr1 [E2; E1; E1])).
  simpl in Heql6.
  subst l6.
  apply decr1_special2.
  simpl.
  lia.
  constructor; auto.
  constructor; auto.
  apply decr1_cons2.
  lia.
  apply decr1_cons1.
  lia.

  exfalso.
  rewrite <- H7 in Heqb5.
  rewrite <- H5 in Heqb5.
  simpl in Heqb5.
  rewrite ?app_length in Heqb5.
  rewrite <- H3 in Heqb5.
  simpl in Heqb5.
  lia.

  ********
  assert (decr1 (decr1 (b6 :: b7 :: l0)) ++ l2 =
  decr1 (decr1 (decr1 (b1 :: b5 :: l1)) ++ l3)).
  eapply H with (l1:=l4) (l:=decr1 l4); auto.
  remember (b6 :: b7 :: l0).
  remember (b1 :: b5 :: l1).
  simpl in H5.
  assert (l6++l3=l4).
  rewrite Heql6.
  rewrite <- H5.
  auto.
  assert (S(length l5) = length l6).
  enough (length (l6++l3) = S (length (l5++l2))).
  rewrite ?app_length  in H8.
  lia.
  rewrite H7.
  rewrite H1.
  lia.

  simpl.
  rewrite Heql5.
  rewrite Heql6.
  rewrite <- Heql5.
  rewrite <- Heql6.

  assert (S (length (decr1 l6)) = length l6).
  apply decr1_length_plus.
  apply decr1_cons1_inv.
  rewrite Heql6. simpl. lia.
  enough (Forall (eq E1) l4).
  rewrite <- H1 in H9.
  apply Forall_sub in H9.
  apply H9.
  apply decr1_cons1.
  lia.

  assert ((length (decr1 l5)) = length l5).
  remember (length (decr1 l5) =? length l5).
  destruct b8.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb8.
  assert (length (decr1 l5) < length l5) by lia.
  apply decr1_cons1 in H10.
  assert (Forall (eq E2) (decr1 l4)).
  apply decr1_cons2.
  lia.
  rewrite <- H7 in H11.
  apply Forall_sub in H11.
  inversion_clear H11.
  destruct l5.
  discriminate.
  inversion H10.
  inversion H12.
  rewrite <- H19 in H15.
  discriminate.
  rewrite H10.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite <- H9.
  replace  (length (decr1 l6) =? S (length (decr1 l6))) with false.
  rewrite <- H10.
  setoid_rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  remember (decr1 l5).
  remember (decr1 l6).
  destruct l7; destruct l8.
  exfalso.
  rewrite Heql5 in H10.
  simpl in H10. lia.
  exfalso.
  rewrite Heql5 in H10.
  simpl in H10. lia.
  exfalso.
  rewrite Heql6 in H9.
  simpl in H9. lia.
  rewrite Heql7 in *.
  rewrite Heql8 in *.
  (*Forall (eq E1) l6*)
  (*Forall (eq E2) (decr1 l6)*)
  enough (length (decr1 (decr1 l6)) = length (decr1 l6)).
  rewrite H11.
  rewrite PeanoNat.Nat.eqb_refl.
  (*Forall (eq E2) l5*)
  (*~Forall (eq E1) (decr1 l5)*)
  enough (length (decr1 (decr1 l5)) = length (decr1 l5)).
  rewrite H12.
  rewrite PeanoNat.Nat.eqb_refl.
  simpl app.
  simpl.

  rewrite <- H12.
  rewrite <- H11.
  rewrite ?PeanoNat.Nat.eqb_refl.
  simpl.

  remember (decr1 (decr1 l6) ++ l3).
  destruct l9.
  exfalso.
  assert (H200:length (@nil binary) = length (decr1 (decr1 l6) ++ l3)).
  rewrite Heql9.
  auto.
  simpl in H200.
  rewrite app_length in H200.
  assert (0 < length (decr1 (decr1 l6))).
  rewrite Heql6.
  apply decr2_ge2digit.
  lia.
  rewrite Heql9 in *.

  remember (length (decr1 (decr1 (decr1 l6) ++ l3)) =? length (decr1 (decr1 l6) ++ l3)).
  destruct b11.
  simpl.
  rewrite <- Heqb11.
  congruence.

  exfalso.
  apply decr1_ltlength_S in Heqb11.
  rewrite <- H0 in Heqb11.
  rewrite ? app_length in Heqb11.
  lia.

  remember (length (decr1 (decr1 l5)) =? length (decr1 l5)).
  destruct b10.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb10.
  assert (length (decr1 (decr1 l5)) < length (decr1 l5)) by lia.
  apply decr1_cons1 in H12.
  assert (Forall (eq E2) l5).
  enough (Forall  (eq E2)  (decr1 l4)).
  rewrite <- H7 in H13.
  apply Forall_sub in H13.
  apply H13.
  apply decr1_cons2.
  lia.
  apply ForallE2_not_ForallE1_decr1 in H13.
  contradiction.
  rewrite Heql5.
  simpl. lia.

  remember (length (decr1 (decr1 l6)) =? length (decr1 l6)).
  destruct b10.
  apply PeanoNat.Nat.eqb_eq. auto.
  exfalso.
  apply decr1_ltlength_S in Heqb10.
  assert (length (decr1 (decr1 l6)) < length (decr1 l6)) by lia.
  apply decr1_cons1 in H11.
  assert (Forall (eq E2) (decr1 l6)).
  apply decr1_cons2.
  lia.
  rewrite <- Heql8 in *.
  inversion H11.
  inversion H12.
  rewrite <- H19 in H15.
  discriminate.

  symmetry.
  apply PeanoNat.Nat.eqb_neq.
  lia.
Qed.



Lemma minus_one_digit_decr1: forall b a n, 
minus_one_digit' (decr1 b) n a = decr1 (minus_one_digit' b n a).
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction n; intros.

  simpl minus_one_digit'.
  destruct a; auto.

  remember (decr1 b).
  simpl.

  destruct a.
  -

  remember (firstn (length l - S n) l).
  remember (firstn (length b - S n) b).

  destruct l0; destruct l1; auto.

  + (*1/4*)
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  assert ([]++l0=l).
  rewrite Heql0. rewrite Heql2.
  apply firstn_skipn.
  simpl in H.
  assert ([]++l1=b).
  rewrite Heql1. rewrite Heql3.
  apply firstn_skipn.
  simpl in H0.
  rewrite H. rewrite H0.
  rewrite Heql.
  auto.

  + (*2/4*)
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  assert ([]++l0=l).
  rewrite Heql0. rewrite Heql2.
  apply firstn_skipn.
  simpl in H.
  assert ((b0::l1)++l2=b).
  rewrite Heql1. rewrite Heql3.
  apply firstn_skipn.

  symmetry in Heql0.
  apply firstn_nil in Heql0.
  inversion_clear Heql0.

  *
  enough (length b - S n = 0 \/ length b - S n = 1).
  inversion_clear H2.
  rewrite H3 in Heql1.
  discriminate.
  rewrite H3 in Heql1.
  enough (l1 = []).
  rewrite H2.
  rewrite H2 in H0.
  remember (incr1 l0).
  replace l0 with (decr1 b1).
  rewrite IHn.

  rewrite Heqb1.
  rewrite H.
  rewrite Heql.
  rewrite incr1_decr1.
  simpl in H0.
  rewrite <- H0.
  assert (length b = S (S n)) by lia.
  assert (length l2 = S n).
  rewrite <- H0 in H4.
  simpl in H4.
  lia.

  rewrite <- minus_one_digit_E12.
  simpl minus_one_digit'.
  rewrite H5.
  replace (S n - n) with 1.
  simpl.
  auto.
  lia.
  lia.
  rewrite Heqb1.
  rewrite decr1_incr1.
  auto.
  simpl in Heql1.
  destruct b.
  discriminate.
  inversion Heql1.
  auto.
  assert (b = incr1 l).
  rewrite Heql.
  rewrite incr1_decr1. auto.
  rewrite <- H0.
  simpl. lia.
  enough (length b = length l \/ length b = S (length l)).
  lia.
  enough (length l = length b \/ length l < length b).
  inversion_clear H3.
  left. auto.
  rewrite H2 in H4.
  apply incr1_length_plus in H4.
  right. rewrite H2. auto.
  enough (length l <= length b) by lia.
  rewrite H2.
  apply incr1_length.
  
  *
  rewrite H1 in Heql.
  symmetry in Heql.
  apply decr1_nil in Heql.
  inversion_clear Heql.
  rewrite H2 in H0.
  discriminate.
  rewrite H2 in H0.
  inversion H0.
  enough (l1 = []).
  enough (l2 = []).
  rewrite H3.
  rewrite H6.
  rewrite H.
  rewrite H1.
  rewrite minus_one_digit_nil.
  simpl. auto.
  destruct l2; auto.
  destruct l1; discriminate.
  destruct l1; auto.
  discriminate.

  + (*3/4*)
  destruct b.
  *
  simpl.
  simpl in Heql1.
  simpl in Heql.
  rewrite Heql in Heql0.
  simpl in Heql0.
  discriminate.

  *
  remember (b::b1).
  rename b into bb.
  rename l1 into b.
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  symmetry in Heql1.
  apply firstn_nil in Heql1.
  inversion_clear Heql1.
  enough (length l - S n = 0).
  rewrite H0 in Heql0.
  simpl in Heql0.
  rewrite H0 in Heql3.
  simpl in Heql3.
  discriminate.
  enough (b = incr1 l).
  enough (length l <= length b).
  lia.
  rewrite H0.
  apply incr1_length.
  rewrite Heql.
  rewrite incr1_decr1.
  auto.
  rewrite Heql2.
  simpl. lia.
  rewrite Heql2 in H.
  discriminate.

  + (*4/4*)
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  assert ((b0::l0)++l2 = l).
  rewrite Heql0.
  rewrite Heql2.
  apply firstn_skipn.
  assert ((b1::l1)++l3 = b).
  rewrite Heql1.
  rewrite Heql3.
  apply firstn_skipn.

  rewrite <- H in Heql.
  rewrite <- H0 in Heql.
  remember (IHn b E1).
  clear Heqe.

  rewrite <- H0 in e.
  (* simpl app in Heql. *)
  destruct n.
  *
  rewrite <- Heql in e.
  Opaque decr1 app.
  simpl in e.
  Transparent app.

  enough (length l2 = 1).
  enough (length l3 = 1).

  destruct l2; destruct l3.
  simpl in H1. lia.
  simpl in H1. lia.
  simpl in H2. lia.
  destruct l2; destruct l3.
  destruct b2; destruct b3.

  **
  rewrite ?decr1_E1_snoc in e.
  rewrite ?decr1_E2_snoc in e.
  apply snoc_eq in e.
  inversion_clear e.
  discriminate.
  simpl. lia.
  simpl. lia.
  **
  rewrite ?decr1_E1_snoc in e.
  rewrite ?decr1_E2_snoc in e.
  rewrite ?decr1_E1_snoc in e.
  apply snoc_eq in e.
  inversion e.
  rewrite decr1_E2_snoc.
  rewrite H3.
  auto.
  simpl. lia.
  simpl. lia.
  **
  rewrite ?decr1_E1_snoc in e.
  rewrite ?decr1_E2_snoc in e.
  apply snoc_eq in e.
  inversion e.
  rewrite decr1_E1_snoc.
  rewrite H3.
  auto.
  rewrite <- H3.
  simpl. lia.
  simpl. lia.
  **
  rewrite ?decr1_E2_snoc in e.
  rewrite ?decr1_E1_snoc in e.
  apply snoc_eq in e.
  inversion e.
  discriminate.
  simpl. lia.
  **
  simpl in H2. discriminate.
  **
  simpl in H1. discriminate.
  **
  simpl in H1. discriminate.
  **
  rewrite Heql3.
  rewrite skipn_length.
  enough (length b >= 1 ).
  lia.
  rewrite <- H0.
  simpl. lia.
  **
  rewrite Heql2.
  rewrite skipn_length.
  enough (length l >= 1 ).
  lia.
  rewrite <- H.
  simpl. lia.
  *
  rewrite <- Heql in e.
  simpl in e. 
  assert (length (l0 ++ l2) - n = length l - S n).
  rewrite <- H.
  simpl app.
  rewrite ?app_length.
  simpl.
  rewrite ?app_length.
  lia.
  assert (length (l1 ++ l3) - n = length b - S n).
  rewrite <- H0.
  simpl app.
  rewrite ?app_length.
  simpl.
  rewrite ?app_length.
  lia.
  rewrite H1 in e.
  rewrite H2 in e.

  simpl in H.
  simpl in H0.
  rewrite H in e.
  rewrite H0 in e.

  remember (firstn (length l - S n) l).
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  remember (firstn (length b - S n) b).

  assert (l4 ++ l5 = l).
  rewrite Heql4. rewrite Heql5.
  apply firstn_skipn.
  assert (l7 ++ l6 = b).
  rewrite Heql6. rewrite Heql7.
  apply firstn_skipn.
  assert (length l2 = S (S n)).
  rewrite Heql2.
  rewrite skipn_length.
  enough (length l >= S (S n)).
  lia.
  assert (length l < S (S n) \/ length l >= S (S n)) by lia.
  inversion_clear H5; auto.
  replace (length l - S (S n)) with 0 in Heql0 by lia.
  simpl in Heql0.
  discriminate.
  rewrite <- minus_one_digit_iter_decr_helper with (n:= S (S n)); auto.
  rewrite  Heql.
  rewrite minus_one_digit_E12.
  rewrite IHn.
  rewrite <- minus_one_digit_E12.
  enough (length l3 = S (S n)).
  rewrite minus_one_digit_iter_decr_helper; auto.
  rewrite Heql3.
  rewrite skipn_length.
  enough (length b >= S (S n)).
  lia.
  assert (length b < S (S n) \/ length b >= S (S n)) by lia.
  inversion_clear H6; auto.
  replace (length b - S (S n)) with 0 in Heql1 by lia.
  simpl in Heql1. discriminate.


  -
  remember (firstn (length l - S n) l).
  remember (firstn (length b - S n) b).

  destruct l0; destruct l1; auto.

  + (*1/3*)
  remember (skipn (length b - S n) b).
  symmetry in Heql0.
  apply firstn_nil in Heql0.
  inversion_clear Heql0.
  *
  enough (length b - S n = 0 \/ length b - S n = 1).
  inversion_clear H0.
  **
  rewrite H1 in Heql1.
  simpl in Heql1.
  discriminate.
  **
  assert (length l < length b) by lia.
  rewrite Heql in H0.
  enough (Forall (eq E1) b).
  rewrite H1 in Heql1.
  simpl in Heql1.
  destruct b. discriminate.
  inversion Heql1.
  destruct b.
  assert (length l0 = S n).
  rewrite Heql2.
  rewrite skipn_length.
  lia.
  enough (Forall (eq E1) l0).
  rewrite <- IHn.
  enough (length (decr1 l0) = n).
  rewrite H1 in Heql2.
  simpl in Heql2.
  rewrite <- minus_one_digit_E12.
  symmetry.
  apply minus_one_digit_ltn.
  lia.
  enough (length l0 = S (length (decr1 l0))).
  lia.
  remember (decr1 l0).
  replace l0 with (incr1 l2) in H6.
  rewrite Heql0 in H6.
  rewrite <- Heql0 in H6.
  apply incr1_cons1_inv in H6.
  replace l0 with (incr1 l2).
  symmetry.
  apply incr1_length_plus.
  lia.
  rewrite Heql0.
  apply incr1_decr1.
  lia.
  rewrite Heql0.
  apply incr1_decr1.
  lia.
  rewrite Heql2.
  apply Forall_skipn.
  auto.
  Transparent decr1.
  simpl decr1.
  rewrite H1 in Heql2.
  simpl in Heql2.
  inversion_clear H2.
  discriminate.
  enough (b = incr1 l).
  rewrite H2.
  apply incr1_cons1.
  rewrite <- Heql in H0.
  rewrite H2 in H0.
  lia.
  rewrite  Heql.
  symmetry.
  apply incr1_decr1.
  lia.
  **
  enough (length l = length b \/ length b = S (length l)).
  lia.
  enough (length l = length b \/ length l < length b).
  inversion_clear H0; auto.
  enough (b = incr1 l).
  rewrite H0 in H1.
  rewrite H0.
  apply incr1_length_plus in H1.
  auto.
  rewrite Heql.
  symmetry.
  apply incr1_decr1.
  lia.
  enough (length l <= length b).
  lia.
  enough (b = incr1 l).
  rewrite H0.
  apply incr1_length.
  rewrite Heql.
  symmetry.
  apply incr1_decr1.
  destruct b.
  simpl in Heql1.
  discriminate.
  simpl. lia.
  *
  rewrite H in Heql.
  symmetry in Heql.
  apply decr1_nil in Heql.
  inversion_clear Heql.
  **
  rewrite H0 in Heql1.
  simpl in Heql1.
  discriminate.
  **
  rewrite H0 in Heql1.
  simpl in Heql1.
  discriminate.
  + (*2/3*)
  remember (skipn (length l - S n) l).
  symmetry in Heql1.
  apply firstn_nil in Heql1.
  inversion_clear Heql1.
  *
  destruct b0.
  **
  destruct l0.
  ***
  simpl.
  assert (length l1 = S n).
  rewrite Heql2.
  rewrite skipn_length.
  enough (length l > S n).
  lia.
  assert (length l <= S n \/ length l > S n) by lia.
  inversion_clear H0; auto.
  replace (length l - S n) with 0 in Heql0 by lia.
  simpl in Heql0.
  discriminate.
  rewrite <- minus_one_digit_E12.
  assert ([E1]++l1 = l).
  rewrite Heql0.
  rewrite Heql2.
  apply firstn_skipn.
  exfalso.
  enough (length l1 < S n).
  lia.
  enough (length l1 < length l).
  enough (length l <= S n).
  lia.
  enough (length l <= length b).
  lia.
  rewrite Heql.
  apply decr1_length.
  rewrite <- H1.
  rewrite app_length.
  simpl.
  lia.
  ***
  exfalso.
  enough (length l - S n = 0).
  rewrite H0 in Heql0.
  discriminate.
  enough (length l <= length b).
  lia.
  rewrite Heql.
  apply decr1_length.
  **
  exfalso.
  enough (length l - S n = 0).
  rewrite H0 in Heql0.
  discriminate.
  enough (length l <= length b).
  lia.
  rewrite Heql.
  apply decr1_length.
  *
  exfalso.
  rewrite H in Heql.
  simpl in Heql.
  rewrite Heql in Heql0.
  simpl in Heql0.
  discriminate.
  + (*3/3*)
  remember (skipn (length l - S n) l).
  remember (skipn (length b - S n) b).
  assert ((b0::l0)++l2 = l).
  rewrite Heql0.
  rewrite Heql2.
  apply firstn_skipn.
  assert ((b1 :: l1)++l3 = b).
  rewrite Heql1.
  rewrite Heql3.
  apply firstn_skipn.
  destruct b0; destruct b1; destruct l0; destruct l1.
  * (*1/16*)
  enough (l2 = decr1 l3).
  rewrite H1.
  apply IHn.
  apply decr1_in_tail with (l:=[E1]).
  rewrite H. rewrite H0.
  auto.
  * (*2/16*)
  exfalso.
  assert (length l < length b).
  rewrite <- H.
  rewrite <- H0.
  simpl.
  rewrite app_length.
  enough  (length l2 = length l3).
  lia.
  rewrite Heql2.
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length l >=  S n).
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.
  rewrite Heql in H1.
  apply decr1_cons2 in H1.
  rewrite <- Heql in H1.
  rewrite <- H in H1.
  simpl in H1.
  inversion H1.
  discriminate.
  * (*3/16*)
  exfalso.
  assert (length l > length b).
  rewrite <- H.
  rewrite <- H0.
  simpl.
  rewrite app_length.
  enough  (length l2 = length l3).
  lia.
  rewrite Heql2.
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length l >=  S n).
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.
  assert (length l <= length b).
  rewrite Heql.
  apply decr1_length.
  lia.
  * (*4/16*)
  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >=  S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.
  assert (length l2 = length l3) by lia.
  clear IHn Heql0 Heql1 Heql2 Heql3 H1 H2.

  remember E1.
  rewrite Heqb2 at 2.
  rewrite Heqb2 in H0.
  clear Heqb2.
  remember E1.
  clear Heqb3.

  eapply minus_one_digit_decr1_helper.
  apply Heql.
  auto.
  auto.
  auto.

  * (*5/16*)
  simpl.
  rewrite <- H in Heql.
  rewrite <- H0 in Heql.
  simpl  in Heql.
  destruct l3.
  inversion Heql.
  rewrite minus_one_digit_nil.
  auto.
  remember (length (decr1 (b0 :: l3)) =? length (b0 :: l3)).
  destruct b1.
  inversion Heql.
  assert (l2 = E2 :: decr1 (b0 :: l3)).
  inversion Heql.
  auto.
  rewrite H1.
  remember (decr1 (b0 :: l3)).
  assert (length l0 = n).

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  rewrite H1 in H2.
  simpl in H2.
  lia.

  apply minus_one_digit_iter_decr_helper3.
  auto.

  * (*6/16*)

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  assert (l1 = []).
  destruct l1; auto.
  exfalso.
  enough (length l = length b \/ S (length l) = length b).

  rewrite <- H in H3.
  rewrite <- H0 in H3.
  simpl in H3.
  rewrite ?app_length in H3.
  inversion H3; lia.
  
  enough (length l = length b \/ length l < length b).
  inversion H3; auto.
  right.
  rewrite Heql.
  apply decr1_length_plus.
  rewrite Heql in H4.
  auto.
  enough (length l <= length b).
  lia.
  rewrite Heql.
  apply decr1_length.

  rewrite H3 in *.
  exfalso.
  enough (length (decr1 b) < length b).
  apply decr1_cons1 in H4.
  rewrite <- H0 in H4.
  inversion H4.
  discriminate.

  rewrite <- Heql.
  rewrite <- H.
  rewrite <- H0.
  simpl.
  lia.

  * (*7/16*)

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  remember (decr1 (decr1 [E2])).
  simpl in Heql4.
  subst l1.
  Opaque decr1.
  simpl app.
  Transparent decr1.

  exfalso.
  assert (length b < length l).
  rewrite <- H0.
  rewrite <- H.

  simpl.
  rewrite app_length.
  lia.

  assert (length l <= length b).
  rewrite Heql.
  apply decr1_length.
  lia.

  * (*8/16*)

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  eapply minus_one_digit_decr1_helper.
  apply Heql.
  apply H.
  apply H0.
  lia.

  * (*9/16*)
  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  assert (length l2 = length l3)  by lia.
  simpl.
  exfalso.
  eapply binary_lt_not.
  apply H3.
  setoid_rewrite H.
  setoid_rewrite H0.
  rewrite Heql.
  apply lt_decr1.
  rewrite <- H0.
  rewrite app_length.
  lia.

  * (*10/16*)
  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  remember (decr1 (decr1 [E2])).
  simpl in Heql4.
  subst l0.

  Opaque decr1.
  simpl.
  Transparent decr1.

  enough (Forall (eq E1) b).
  enough (Forall (eq E2) l).
  enough (l1=[]).
  rewrite <- H0 in H3.
  inversion H3.
  inversion H9.
  rewrite H5 in *.
  simpl in * |- .
  rewrite <- H12.

  remember (decr1 (decr1 [E1; E1])).
  simpl in Heql5.
  subst l5.

  apply decr1_special3.
  lia.
  rewrite <- H in H4.
  inversion H4; auto.
  auto.

  destruct l1; auto.

  exfalso.
  enough (length l = length b \/ S (length l) = length b).

  rewrite <- H in H5.
  rewrite <- H0 in H5.
  simpl in H5.
  rewrite ?app_length in H5.
  inversion H5; lia.
  
  enough (length l = length b \/ length l < length b).
  inversion H5; auto.
  right.
  rewrite Heql.
  apply decr1_length_plus.
  rewrite Heql in H6.
  auto.
  enough (length l <= length b).
  lia.
  rewrite Heql.
  apply decr1_length.

  rewrite Heql.
  apply decr1_cons2.
  rewrite <- Heql.
  rewrite <- H0.
  rewrite <- H.
  simpl.
  rewrite app_length.
  lia.

  apply decr1_cons1.
  rewrite <- Heql.
  rewrite <- H0.
  rewrite <- H.
  simpl.
  rewrite app_length.
  lia.

  * (*11/16*)  

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  exfalso.
  assert (length b < length l).
  rewrite <- H,  <- H0.
  simpl. 
  rewrite app_length.

  lia.
  assert (length l <= length b).
  rewrite Heql.
  apply decr1_length.
  lia.

  * (*12/16*)   

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  eapply minus_one_digit_decr1_helper.
  apply Heql.
  apply H.
  apply H0.
  lia.

  * (*13/16*)     
  simpl.

  rewrite <- H in Heql.
  rewrite <- H0 in Heql.

  eapply decr1_in_tail.
  apply Heql.

  * (*14/16*)   

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  exfalso.
  enough (Forall (eq E1) b).
  rewrite <- H0 in H3.
  inversion H3.
  discriminate.
  
  apply decr1_cons1.
  rewrite <- Heql, <- H, <- H0.
  simpl.
  rewrite app_length.
  lia.

  * (*15/16*)   
  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  exfalso.

  assert (length b < length l).
  rewrite <- H0, <- H.
  simpl.
  rewrite app_length.
  lia.
  assert (length l <= length b).
  rewrite Heql.
  apply decr1_length.
  lia.

  * (*16/16*)   

  assert (length l2 = S n).
  rewrite Heql2.
  rewrite? skipn_length.
  enough (length l >=  S n).
  lia.
  assert (length l < S n \/ length l >= S n) by lia.
  inversion_clear H1; try lia.
  replace (length l - S n) with 0 in Heql0 by lia.
  discriminate.

  assert (length l3 = S n).
  rewrite Heql3.
  rewrite? skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H2; try lia.
  replace (length b - S n) with 0 in Heql1 by lia.
  discriminate.

  eapply minus_one_digit_decr1_helper.
  apply Heql.
  apply H.
  apply H0.
  lia.
Qed.

Transparent decr1.

Lemma minus0_0: forall b, minus'' [] b = [].
Proof.
  intros.
  induction b.
  simpl. auto.
  simpl.
  rewrite IHb.
  rewrite minus_one_digit_nil.
  auto.
Qed.


Lemma minus''_decr1: forall a b, minus'' (decr1 a) b = decr1 (minus'' a b).
Proof.
  intros.
  generalize dependent a.
  induction b; intros.
  simpl. auto.

  simpl.
  rewrite IHb.
  rewrite minus_one_digit_decr1.
  auto.
Qed.
  
Lemma iter_decr_minus''_commute: forall n a b,
minus'' (iter n decr1 a) b = iter n decr1 (minus'' a b).
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction n ; intros.
  simpl. auto.
  simpl.
  rewrite IHn.
  rewrite minus''_decr1.
  auto.
Qed.


Lemma minus_one_digit_iter_decr: forall n b,
iter (2 ^ n) decr1 b = minus_one_digit' b n E1 /\
iter (2 ^ n + 2 ^ n) decr1 b = minus_one_digit' b n E2.
Proof.
  intros.
  generalize dependent b.
  induction n; intros.
  split.
  simpl. auto.
  simpl. auto.

  split.
  -
  simpl.
  replace (2 ^ n + 0) with (2^n) by lia.
  remember (firstn (length b - S n) b).
  remember ((skipn (length b - S n) b)).
  destruct l.
  +
  assert ([]++l0=b).
  rewrite Heql.
  rewrite Heql0.
  apply firstn_skipn.
  simpl in H.
  rewrite H.
  apply IHn.
  +
  assert ((b0::l)++l0=b).
  rewrite Heql.
  rewrite Heql0.
  apply firstn_skipn.
  remember (IHn b).
  inversion_clear a.
  rewrite H1.
  rewrite <- H.
  assert (length l0  = S n).
  rewrite Heql0.
  rewrite skipn_length.
  enough (length b >=  S n).
  lia.
  assert (length b >= S n \/ length b < S n) by lia.
  inversion_clear H2. auto.
  replace (length b - S n) with 0 in Heql by lia.
  simpl in Heql. discriminate.
  rewrite <- minus_one_digit_E12.
  apply minus_one_digit_iter_decr_helper.
  auto.
  -
  simpl.
  replace (2 ^ n + 0) with (2^n) by lia.
  rewrite iter_plus.
  remember (IHn b).
  inversion_clear a.
  rewrite H0.
  clear a Heqa H H0.
  remember (IHn (minus_one_digit' b n E2)).
  inversion_clear a.
  rewrite H0.
  clear a Heqa H H0.
  remember (firstn (length b - S n) b).
  remember ((skipn (length b - S n) b)).
  destruct l.
  +
  symmetry in Heql.
  apply firstn_nil in Heql.
  inversion_clear Heql.
  rewrite <- ?minus_one_digit_E12.
  apply minus_one_digit_ltn.
  apply minus_one_digit_ltn2.
  lia.
  rewrite H. 
  rewrite minus_one_digit_nil.
  rewrite minus_one_digit_nil.
  auto.
  +
  rewrite <- ?minus_one_digit_E12.
  assert ((b0::l)++l0 = b).
  rewrite Heql.
  rewrite Heql0.
  apply firstn_skipn.
  assert (length l0 = S n).
  rewrite Heql0.
  rewrite skipn_length.
  enough (length b >= S n).
  lia.
  assert (length b < S n \/ length b >= S n) by lia.
  inversion_clear H0; auto.
  replace (length b - S n) with 0 in Heql by lia.
  simpl in Heql.
  discriminate.
  destruct b0.
  *
  destruct l.
  **
  rewrite <- H.
  rewrite minus_one_digit_iter_decr_helper.
  auto.
  auto.
  **
  rewrite <- H.
  rewrite minus_one_digit_iter_decr_helper.
  remember (decr1 (E1 :: b0 :: l)).
  assert ( 0 < length l1).
  rewrite Heql1.
  apply decr1_ge2digit.
  destruct l1.
  simpl in H1. lia.
  rewrite minus_one_digit_iter_decr_helper.
  auto.
  auto.
  auto.
  *
  rewrite <- H.
  rewrite minus_one_digit_iter_decr_helper.
  remember (decr1 (E2 :: l)).
  enough ( 0 < length l1).
  destruct l1.
  simpl in H1. lia.
  rewrite minus_one_digit_iter_decr_helper.
  auto.
  auto.
  2: auto.
  rewrite Heql1.
  generalize l.
  intros.
  destruct l2; auto.
  apply decr1_ge2digit.
Qed.


Lemma minus_minus': forall a b, minus a b = minus'' a b.
Proof.
  intros.
  generalize dependent a.
  induction b; intros.
  simpl. auto.
  simpl.
  remember (length b).
  destruct a.
  all: replace (2 ^ n + 0) with (2^n) by lia.
  -
  rewrite IHb.
  rewrite iter_decr_minus''_commute.
  remember (minus'' a0 b).
  apply minus_one_digit_iter_decr.
  -
  rewrite IHb.
  rewrite iter_decr_minus''_commute.
  remember (minus'' a0 b).
  apply minus_one_digit_iter_decr.
Qed.
  

Example check_min: minus [E2] [E1] = [E1].
Proof.
  reflexivity.
Qed.

Example check_min1: minus [E2;E1] [E1] = [E1;E2].
Proof.
  reflexivity.
Qed.

Example check_min2: minus [E1;E2] [E1] = [E1;E1].
Proof.
  reflexivity.
Qed.

Example check_min3: minus [E2] [E1;E1] = [].
Proof.
  reflexivity.
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

Lemma minus_decr: forall a b,
  decr1 (minus a b) = minus (decr1 a) b.
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length.
 
  auto.
  destruct b.
  auto.
  destruct b.
  simpl.
  intros. 
  rewrite H.
  rewrite decr_iter_comm.
  auto. 
  auto.
  intros.
  simpl.
  rewrite H.
  rewrite decr_iter_comm.
  auto.
  auto.
Qed.

Lemma zero_minus: forall b,
  minus [] b = [].
Proof.
  induction b.
  auto.
  simpl.
  destruct a.
  rewrite iter_decr1_nil.
  assumption.
  rewrite iter_decr1_nil.
  assumption.
Qed.

Lemma minus_incr_decr_helper: forall a b0,
false = (length (incr1 b0) =? length b0) -> 
minus (iter (2 ^ length b0 + 2 ^ length b0) decr1 a) (tl (incr1 b0)) =
minus (iter (2 ^ length b0) decr1 a) (incr1 b0).
Proof.
  intros.
  generalize dependent a.
  induction b0 using list_ind_length.
  simpl. auto.
  destruct b0.
  auto.
  destruct b.
  simpl.
  remember (E1_head_incr).
  rewrite e in H.
  inversion H.
  simpl.
  remember (length (incr1 b0) =? length b0).
  destruct b.
  simpl in H.
  rewrite <- Heqb in H.
  simpl in H.
  rewrite <- H in Heqb.
  inversion Heqb.
  simpl.
  rewrite Nat.add_0_r.
   symmetry in Heqb.
   apply length_eq_incr_S in Heqb.
   rewrite Heqb.
   simpl.
   intros.
   rewrite <- iter_plus.
   rewrite Nat.add_0_r.
   auto.
Qed.

Lemma minus_incr_decr: forall a b,
  minus a (incr1 b) = decr1 (minus a b).
Proof.
  intros.
  generalize dependent a.
  induction b using list_ind_length.
  auto.
  destruct b.
  auto.
  destruct b.
  simpl.
  remember (length (incr1 b0) =? length b0).
  intros.
  destruct b.
  simpl.
  rewrite H.
  symmetry in Heqb.
  Search (_ =? _ = true).
  apply Nat.eqb_eq in Heqb.
  rewrite Heqb.
  auto.
  auto.
  simpl.
  rewrite <- H.
  Search (length (tl (incr1 _)) = length _).
  rewrite length_incr_tl.

  Search (_ + 0 = _).
  rewrite Nat.add_0_r.
  apply minus_incr_decr_helper.
  assumption.
  symmetry in Heqb.
  apply length_eq_incr_S in Heqb.
  lia.
  auto.


  simpl.
  remember (length (incr1 b0) =? length b0).
  intros.
  destruct b.
  simpl.
  symmetry in Heqb.
  apply Nat.eqb_eq in Heqb.
  rewrite Heqb.
  rewrite H.
  auto.
  auto.
  simpl.
  rewrite H.
  symmetry in Heqb.
  apply length_eq_incr_S in Heqb.
  rewrite Heqb.
  simpl.
  auto.
  auto.
Qed.
  

Lemma minus_plus: forall a b : bilist,
  minus (plus a b) b = a.
Proof.
  induction b using bilist_incr_ind.
  simpl.
  rewrite plus_comm.
  auto.
  rewrite minus_incr_decr.
  rewrite minus_decr.
  Search (incr1 (plus _ _) = plus _ (incr1 _)).
  rewrite plus_incr1_right.
  rewrite decr1_incr1.
  assumption.
Qed.



Inductive biZ := biNat : bilist -> biZ | biNeg : bilist -> biZ.

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


