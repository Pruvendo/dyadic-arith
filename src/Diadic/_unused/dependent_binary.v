(* From Coq Require Import List. *)
From Coq Require Import Vectors.Vector.
Import VectorNotations.
Local Open Scope vector_scope.
Require Import Nat.
Require Import Coq.Init.Datatypes.
Local Open Scope nat_scope.
From Coq Require Import Vectors.Fin.
Locate ">?" .
Require Import Psatz.
Require Import ZArith.
Check ( 5 <? 5)%nat.

Require Import Coq.Program.Equality.


Print sig.
(* Inductive sig (A : Type) (P : A -> Prop) : Type :=
	exist : forall x : A, P x -> {x : A | P x} *)

Check {x: nat | ltb x 6 = true}.

(* {x: bilist | lenght x <= n}. *)

Program Definition foo (a: {x: nat | ltb x 6 = true}) :  {x: nat | ltb x 7 = true} := S a.


Abort.



(* Compute proj1_sig (foo (exist (fun x => ltb x 6 = true) 4 eq_refl)).


l {a: Z} -> process (UML) -> l {a = b : Z}

a: Z32 -> b: Z32

good a -> good b *)


Inductive binary : Type :=
  | E1
  | E2.

(*
1 = 1 = 1 +
2 = 2 = 10
3 = 11 = 11 +
4 = 12 = 100
5 = 21 = 101
6 = 22 = 110
7 = 111 = 111 +
8 = 112 = 1000
9 = 121 = 1001
10 = 122 = 1010
11 = 211 = 1011
12 = 212 = 1100
13 = 221 = 1101
14 = 222 = 1110
15 = 1111 = 1111 +
*)  

Inductive weakvector (X : Type) : nat -> nat -> Type :=
  | nil : forall m, weakvector X 0 m
  | cons {n m} (x : X) : weakvector X n m -> n <? m = true -> weakvector X (S n) m.
Arguments cons {X n m}.

Example foo: (0 <? 1) = true.
auto.
Defined.
Print  foo. 

Check @nil binary 1.
Check cons E1 (@nil binary 1) eq_refl.
Check cons E2 (@nil binary 1) eq_refl.

Definition biwector : nat -> nat -> Type := weakvector binary. 
Definition bivector : nat -> Type := Vector.t binary. 



(* Fixpoint incr (b : bilist) : bilist :=
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

Check tl. *)
Inductive t : nat -> Set :=
|F1 : forall {n}, t (n)
|FS : forall {n}, t n -> t (S n).

Print t.
Check (t 5).


Definition allE1 {n} (b: bivector n) := Forall (eq E1) b.
Definition allE2 {n} (b: bivector n) := Forall (eq E2) b.

Fixpoint ballE1 {n m} (b: biwector n m) : bool :=
  match b with
  | @nil _ _ => true
  | cons E1 t _ => ballE1 t
  | cons E2 _ _ => false
  end.

Fixpoint ballE2 {n m} (b: biwector n m) : bool :=
  match b with
  | @nil _ _ => true
  | cons E1 _ _ => false
  | cons E2 t _ => ballE2 t
  end.

Require Import Coq.Program.Equality.
(*
Lemma allE1_in_bool: forall n (b: bivector n), allE1 b <-> ballE1 b = true.
Proof.
  intros.
  split. intros.
  induction b.
  simpl. auto.
  simpl. 
  dependent destruction H.
  apply IHb.
  apply H0.
  intros.
  induction b.
  simpl. constructor.
  simpl in H.
  destruct h.
  constructor. auto.
  apply IHb.
  apply H.
  discriminate.
Qed.
  

Lemma allE2_in_bool: forall n (b: bivector n), allE2 b <-> ballE2 b = true.
Proof.
  intros.
  split. intros.
  induction b.
  simpl. auto.
  simpl. 
  dependent destruction H.
  apply IHb.
  apply H0.
  intros.
  induction b.
  constructor.
  simpl in H.
  destruct h.
  discriminate.
  constructor. auto.
  apply IHb.
  apply H.
Qed.


Program Definition incr1 {n} (b : bivector n) : bivector (if (ballE2 b) then (S n) else n).
induction b.
simpl.
refine ([E1]).
simpl.
destruct h.
-
destruct (ballE2 b).
refine (E2::tl IHb).
refine (E1::IHb).
-
destruct (ballE2 b).
refine (E1::IHb).
refine (E2::IHb).
Defined.
*)

Check cons.

Definition tl {n m} (b : biwector (S n) (S m)) : biwector n (S m).
dependent induction b.
exact b.
Defined.

Definition length {n m} (b : biwector n m) : nat.
dependent induction b.
exact 0.
exact (S IHb).
Defined.

Lemma length_correct: forall n m (b : biwector n m), length b = n.
Proof.
  intros.
  dependent induction b.
  simpl. auto.
  simpl.
  rewrite IHb.
  auto.
Qed.

Lemma length_le: forall n m (b : biwector n m), n <= m.
Proof.
  intros.
  dependent induction b.
  lia.
  apply Nat.ltb_lt in e.
  apply lt_le_S.
  apply e.
Qed.



(*
Definition length {n} (b : biwector (n)) : nat.
Proof.
  induction b.
  exact 0.
  exact (1 + IHb).
Defined. 
*)

(* Fixpoint length {n} (b : biwector n) : nat := 
  match b with
  | @nil _ _ => 0
  | cons _ t => S (length t)
  end. *)

Lemma leb_help : forall n, n <=? S n = true.
Proof.
  intros.
  induction n. reflexivity.
  simpl. apply IHn.
Defined.

Lemma ltb_not_eqb: forall n m, (n <? m) = true -> (n =? m) = false.
Proof.
  intros.
  generalize dependent m.
  induction n; intros.
  induction m. unfold ltb in H.
  simpl in H. discriminate.
  simpl. reflexivity.
  destruct m.
  simpl. reflexivity.
  simpl. apply IHn.
  unfold ltb in H.
  unfold ltb.
  remember (S n).
  simpl in H.
  simpl.
  apply H.
Defined.

Lemma lebS_leb: forall n m, (S n <=? m) = true -> (n <=? m) = true.
Proof.
  intros.
  generalize dependent m.
  induction n;intros.
  simpl. reflexivity.
  simpl.
  destruct m.
  simpl in H. 
  discriminate.
  apply IHn.
  remember (S n).
  simpl in H.
  apply H.
Defined.


Definition embed_wector {n m} (b: biwector n m): biwector n (S m).
Proof.
  dependent induction b.
  exact (@nil binary (S m)).
  apply (cons x IHb).
  unfold ltb in e.
  unfold ltb.
  simpl.
  apply lebS_leb.
  apply e.
Defined.

Lemma ltb_noteqS_ltbS: forall n m, (n <? m) = true -> false = (S n =? m) -> (S n <? m) = true.
Proof.
  intros.
  generalize dependent m.
  induction n; intros.
  induction m.
  unfold ltb in H. simpl in H.
  discriminate.
  destruct m.
  simpl in H0. discriminate.
  unfold ltb.
  simpl. reflexivity.
  destruct m.
  unfold ltb in H.
  simpl in H.
  discriminate.
  apply IHn.
  apply H.
  apply H0.
Defined.


Definition incr {n m} (b : biwector n m) : biwector 
(if (ballE2 b) then (S n) else n) 
(if andb (ballE2 b) (n =? m) then (S m) else m).
Proof.
  generalize dependent m.
  dependent induction b; intros.
  +
  simpl.
  destruct m.
  exact (cons E1 (nil binary 1) eq_refl).
  exact (cons E1 (nil binary (S m)) eq_refl).
  +
  remember (ballE2 (cons x b e)).
  remember (S n =? m).
  rewrite ltb_not_eqb in IHb; [| apply e].
  replace ((ballE2 b && false)%bool) with false in IHb.
  remember x.
  destruct b0; destruct b1; simpl; simpl in Heqb0;
  destruct b2; try discriminate.
  -
  rewrite <- Heqb0 in IHb.
  apply (cons E1 (embed_wector IHb)).
  unfold ltb in e.
  unfold ltb.
  remember (S n).
  simpl.
  apply e.
  -
  rewrite <- Heqb0 in IHb.
  apply cons. exact E1. exact IHb.
  apply ltb_noteqS_ltbS.
  apply e.
  apply Heqb1.
  -






Definition embed_wector {n m} (H: n <=? m = true) (b: biwector n): biwector m.
Proof.
  generalize dependent m.
  dependent induction b.
  intros.
  exact (@nil binary m).
  intros.
  destruct m.
  simpl in H.
  discriminate.
  simpl in H.
  apply IHb in H.
  exact (cons x H).
Defined.

Compute embed_wector (leb_help 3) (cons E1 (@nil binary 2)).

Fixpoint incr' {n} (b : biwector n) : biwector n :=



Definition incr {n} (b : biwector n) : (biwector (if andb (ballE2 b) (length b =? n) then (S n) else n)).
Proof.
  dependent induction b.
  simpl.
  destruct n.
  exact (cons E1 (@nil binary 0)).
  exact (cons E1 (@nil binary n)). 
  simpl.
  case_eq x; intros.
  simpl.
  case_eq (ballE2 b); intros; rewrite H0 in IHb;
  case_eq (length b =? n); intros; rewrite H1 in IHb; simpl in IHb.
  exact (cons E2 (tl IHb)).
  destruct n.
  exact (@nil binary 1).
  exact (embed_wector (leb_help (S n)) (cons E2 (tl IHb))).
  exact (cons E1 IHb).
  exact (cons E1 IHb).
  case_eq (ballE2 b); intros; rewrite H0 in IHb;
  case_eq (length b =? n); intros; rewrite H1 in IHb; simpl in IHb; simpl.
  exact (cons E1 (cons E2 (tl IHb))).
  destruct n.
  exact (@nil binary 1).
  exact (cons E1 (IHb)).
  exact (cons E2 IHb).
  exact (cons E2 IHb).
Defined.

Compute incr (cons E1 (@nil binary 2)) : biwector 3.
Compute incr (cons E2 (@nil binary 2)) : biwector 3.
Compute incr (cons E2 (cons E2 (@nil binary 2))) : biwector 4.

Definition incr1 {n} (b : biwector n) : option (biwector n) :=
Proof.
  remember (incr b).
  clear Heqb0.
  case_eq (ballE2 b);
  case_eq (length b =? n); intros.
  rewrite H in b0; rewrite H0 in b0; simpl in b0.
  exact None.
  exact (Some b0).
  exact (Some b0).
  exact (Some b0).
Defined.

Compute incr1 (cons E1 (@nil binary 5)).
Compute incr1 ((@nil binary 0)).

Lemma ballE2_None : forall n (b : biwector n) ,
  ballE2 b = true -> length b = n -> incr1 b = None.
Proof.
  intros.
  unfold incr1.
  rewrite H.
  dependent induction b.
  simpl in H0.
  rewrite <- H0.
  cbn.
  reflexivity.
  unfold incr1.
  simpl.
  destruct x.
  simpl in H.
  inversion H.
  replace (ballE2 b) with true.
  replace (length b =? n) with true.
  enough ((length b =? n) = true).
  setoid_rewrite H1.
  rewrite H0.

Check option

Definition unit {n} (b : bivector n) : option (bivector n) := 
    if n <? 3 then Some b else None.

Compute unit [E1;E1].




Compute incr1 [E1;E2]: bivector 2. 
Compute incr1 [E1;E2;E2]: bivector 3.
Compute incr1 [E2;E2;E2]: bivector 4. 

Compute incr1 (incr1 [E2]). 

Program Definition incr2 {n} (b : bivector n) : bivector (if ((ballE2 b)||(n=?1))%bool then (S n) else n).
induction b.
simpl. refine ([E2]).

simpl.
destruct h.
-
remember (ballE2 b).
destruct b0.
remember (n=?0). destruct b0.
simpl in IHb. simpl.
replace n with 0.
refine ([E1; E1]).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb1.
apply PeanoNat.Nat.eqb_sym.
simpl in IHb. simpl.
refine (E2::tl IHb).

remember (n=?1). remember (n=?0).
destruct b0; destruct b1; simpl in IHb; simpl.
exfalso.
assert (n=0).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb2. reflexivity.
rewrite H in Heqb1. simpl in Heqb1.
discriminate.
replace n with 1 in *.
refine (E2 :: tl IHb).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb1. apply PeanoNat.Nat.eqb_sym.
replace n with 0 in *.
refine ([E1; E1]).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb2. apply PeanoNat.Nat.eqb_sym.
refine (E1::IHb).
-
remember (ballE2 b).
destruct b0.
remember (n=?0). destruct b0.
simpl in IHb. simpl.
replace n with 0.
refine ([E1; E2]).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb1.
apply PeanoNat.Nat.eqb_sym.
simpl in IHb. simpl.
refine (E1:: IHb).

remember (n=?1). remember (n=?0).
destruct b0; destruct b1; simpl in IHb; simpl.
exfalso.
assert (n=0).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb2. reflexivity.
rewrite H in Heqb1. simpl in Heqb1.
discriminate.
replace n with 1 in *.
refine (E2 :: tl IHb).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb1. apply PeanoNat.Nat.eqb_sym.
replace n with 0 in *.
refine ([E1; E2]).
apply PeanoNat.Nat.eqb_eq.
rewrite Heqb2. apply PeanoNat.Nat.eqb_sym.
refine (E2::IHb).
Defined.

(* Fixpoint incr2 (b : bilist) : bilist :=
match b with
  | [] => [E2]
  | [E1] => [E1; E1]
  | [E2] => [E1; E2]
  | E1 :: t => let b' := incr2 t in
               if (length b' =? length t) then E1::b' else E2 :: (tl b')
  | E2 :: t => let b' := incr2 t in
               if (length b' =? length t) then E2::b' else E1::b'
end. *)

Definition length {n} (b: bivector n) := n.

Require Import Psatz.

Lemma incr1_length: forall n (b: bivector n), 
      length b <= length (incr1 b).
Proof.
  intros.
  unfold length.
  destruct (ballE2 b); lia.
Qed.  

Lemma incr1_length_plus: forall n (b: bivector n), length b < length (incr1 b) ->
                                   S (length b) = length (incr1 b).
Proof.
  unfold length.
  intros.
  destruct (ballE2 b). auto.
  lia.
Qed.

Lemma incr2_length: forall n (b: bivector n), length b <= length (incr2 b).
Proof.
  unfold length.
  intros.
  destruct (ballE2 b). simpl. lia.
  destruct (n =? 1). simpl. lia.
  simpl. lia.
Qed.  

Lemma incr2_length_plus: forall n (b: bivector n), length b < length (incr2 b) ->
                                   S (length b) =  length (incr2 b).
Proof.
  unfold length.
  intros.
  destruct (ballE2 b). simpl. auto.
  destruct (n =? 1). simpl. auto.
  simpl. simpl in H. lia.
Qed.
  
Lemma incr2_incr1_length: forall n (b: bivector n), length (incr1 b) <= length (incr2 b).
Proof.
  unfold length.
  intros.
  destruct (ballE2 b). simpl. auto.
  destruct (n =? 1). simpl. auto.
  simpl. auto.
Qed.  

Lemma incr1_cons2: forall n (b: bivector n), length b < length (incr1 b) ->
                    Forall (eq E2) b.
Proof.
  unfold length.
  intros.
  apply allE2_in_bool.
  destruct (ballE2 b). auto. lia.
Qed.

Require Import FinProof.Lib.CPDT.


Print JMeq.


Lemma incr1_cons1: forall n (b: bivector n), length b < length (incr1 b) ->
                    Forall (eq E1) (incr1 b) .
Proof.
  intros.
  unfold length in H.
  apply allE1_in_bool.
  generalize dependent n.
  dependent induction b; intros.
  simpl in H.
  simpl. auto.
  simpl.
  destruct h.
  simpl in H. lia.
  simpl in H.
  remember (incr1 b).
  clear Heqb0.
  dep_destruct (ballE2 b).
  simpl. apply IHb. lia. lia.
Qed.

Lemma incr1_E1: forall n (b: bivector (S n)), Forall (eq E1) b -> 
   length b = length (incr1 b).
Proof.
  unfold length.
  intros.
  remember (ballE2 b).
  destruct b0; auto.
  symmetry in Heqb0.
  apply allE2_in_bool in Heqb0.
  exfalso.
  generalize dependent n.
  dependent induction b; intros.
  inversion H.
  inversion Heqb0.
  rewrite <- H8 in H3.
  discriminate.
Qed.

Definition tl_incr1 {n} (b: bivector (S (S n))) (H: ballE1 b = true) : bivector (S n) .
remember (incr1 b). clear Heqb0.
remember (ballE2 b).
destruct b1.
exfalso.
dependent induction b.
symmetry in Heqb1. simpl in H. 
simpl in Heqb1. destruct h. discriminate.
discriminate.
refine (tl b0).
Defined.


Definition incr1_tl {n} (b: bivector (S (S n))) (H: ballE1 b = true) : bivector (S n).
remember (ballE2 b).
destruct b0.
exfalso.
dependent induction b.
simpl in H. simpl in Heqb0.
destruct h. discriminate. discriminate.

remember (tl b).
(* clear Heqt. *)
simpl in t.
remember (incr1 t).
(* clear Heqt. *) clear Heqb1.
dependent destruction b.
simpl in Heqt.
dependent destruction b.
rewrite Heqt in b0.
simpl in b0.
simpl in H.
simpl in Heqb0.
destruct h0. refine b0.
destruct h. discriminate.
rewrite <- Heqb0 in b0. refine b0.
Defined.


Lemma incr1_tl_comm_E1: forall n (b: bivector (S (S n))) (H: ballE1 b = true),   
   incr1 (tl b) ~= tl (incr1 b).
Proof.
  intros.
  unfold incr1_tl.   
