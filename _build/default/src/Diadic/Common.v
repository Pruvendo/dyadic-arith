From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Local Open Scope nat_scope.

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

Lemma empty_tl: forall {X} (b : list X),
  [] = tl b -> length b <= 1.
Proof.
  intros.
  induction b.
  auto.
  simpl in H.
  simpl. rewrite <- H.
  simpl. auto. Qed.

Lemma length_ge_zero: forall {X} (b : list X),
  0 < length b -> length b = S (length (tl b)).
Proof.
  intros.
  induction b.
  inversion H.
  auto.
Qed.

Lemma eq_E1_head: forall {X} (b b' : list X) (h : X),
  b = b' -> h :: b = h ::b'.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma length_eq_head: forall {X} (b b' : list X) (h : X), 
    length b = length b' -> length (h :: b) = length (h :: b').
Proof.
    intros.
    simpl.
    auto.
Qed.

Lemma tl_greater: forall {X} (b : list X),
  0 < length b -> length (tl  b) =? length b = false.
Proof.
  intros.
  destruct b.
  inversion H.
  simpl.
  induction (length b).
  auto.
  auto.
Qed.

Inductive iter_relation {X} (R: X -> X -> Prop): nat -> X -> X -> Prop :=
| iter_relation0 : forall x y, R x y -> iter_relation R 0 x y
| iter_relationS : forall x y' y n, R y' y -> iter_relation R n x y' -> iter_relation R (S n) x y.


Definition bilist_reducible_prop {X} (R: X -> X -> Prop) : Prop := 
    forall y, exists n, forall x, (iter_relation R n x y -> False).
  
  
Lemma iter_relation_S: forall {X} R n (x y: X),  
iter_relation R (S n) x y ->
        exists y', iter_relation R n y' y.
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

Lemma iter_relation_S2: forall {X} R n (x y: X),  
iter_relation R (S n) x y ->
        exists y', iter_relation R n y' y /\ R x y'.
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

Lemma iter_relation_plus: forall {X} R n m (x y: X),  
iter_relation R (n + m) x y ->
        exists y', iter_relation R m y' y.
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

Lemma iter_relation_S_inv: forall {X} R n (x y x': X),  
iter_relation R n x' y ->
R x x' ->
iter_relation R (S n) x y.
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


Lemma iter_relation_trans: forall {X} R n m (x y z: X),  
iter_relation R (n + m) x z ->
(forall x0 : X, iter_relation R m x0 z -> R x0 y ) ->
iter_relation R n x y.
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

Lemma iterS: forall X f (x:X) n, iter (S n) f x = f (iter n f x).
Proof.
  intros.
  generalize dependent x.
  induction n; intros.
  simpl. auto.
  simpl.
  rewrite <-IHn. simpl. auto.  
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


Fixpoint del_h {X} (b b': list X) : list X :=
  match b' with
  | [] => []
  | h :: t => if (length b =? length t + 1) then h :: t else del_h b t 
end.

Compute del_h [] [1].
Compute del_h [1; 1] [1].
Compute del_h [1; 2] [1; 1; 1].


Fixpoint del_t {X} (b b' : list X) : list X:=
  match b' with
  | [] => []
  | h :: t => if length (del_h b b') =? length t then [h] else h :: del_t b t
end.

Compute firstn 1 [].
Compute firstn 2 [1;2].
Compute skipn 1 [].
Compute skipn 1 [1; 2].
Compute skipn 2 [1; 2].

Definition split {X} (n: nat) (t : list X) : list X * list X :=
  (firstn n t, skipn n t).

Compute split 1 [1].

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