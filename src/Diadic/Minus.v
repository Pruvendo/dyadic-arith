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

Fixpoint minus_one_digit' (b : bilist) (n: nat) (d: binary) {struct n}:  bilist := 
  match n with
  | O => match d with
         | E1 => decr1 b
         | E2 => decr1 (decr1 b)
         end
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


Lemma minus_one_digit0: forall n a, 
       minus_one_digit' [] n a = [].
Proof.
  intros.
  generalize dependent a.
  induction n; intros.
  simpl. destruct a; auto.
  simpl. rewrite IHn. destruct a; auto.
Qed.

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

Lemma minus_one_digit_iter_decr_helper4: forall l0 n,
length l0 = n ->
minus_one_digit' (E1::l0) n E1 = l0.
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


Lemma minus_minus'': forall a b, minus a b = minus'' a b.
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
  apply Nat.eqb_eq in Heqb.
  rewrite Heqb.
  auto.
  auto.
  simpl.
  rewrite <- H.
  rewrite length_incr_tl.

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

Lemma minus_one_digit_iter_decr_E1: forall n b,
iter (2 ^ n) decr1 b = minus_one_digit' b n E1 .
Proof.
  apply minus_one_digit_iter_decr.
Qed.  


Lemma minus_one_digit_iter_decr_E2: forall n b,
iter (2 ^ n + 2 ^ n) decr1 b = minus_one_digit' b n E2.
Proof.
  apply minus_one_digit_iter_decr.
Qed. 

Lemma minus_n_n: forall n, minus n n = [].
Proof.
  induction n using bilist_lt_ind.
  auto.
  destruct n.
  auto.
  simpl.
  destruct b.
  -
  rewrite minus_one_digit_iter_decr_E1.
  rewrite minus_one_digit_iter_decr_helper4.
  apply H.
  apply lt_less_length.
  simpl. lia.
  auto.
  -
  replace (2 ^ length n + (2 ^ length n + 0)) with (2 ^ length n + 2 ^ length n) by lia. 
  rewrite minus_one_digit_iter_decr_E2.
  rewrite minus_one_digit_iter_decr_helper3.
  apply H.
  apply lt_less_length.
  simpl. lia.
  auto.
Qed.

Lemma minus_Sn_n: forall n, minus (incr1 n) n = [E1].
Proof.
  induction n using bilist_lt_ind.
  auto.
  destruct n.
  auto.
  simpl.
  destruct b.
  -
  remember (length (incr1 n) =? length n).
  destruct b.
  +
  rewrite minus_one_digit_iter_decr_E1.
  rewrite minus_one_digit_iter_decr_helper4.
  apply H.
  apply lt_less_length.
  simpl. lia.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  +
  rewrite minus_one_digit_iter_decr_E1.
  remember (tl (incr1 n)).
  enough (length l = length n).
  rewrite <- H0.
  replace (E2::l) with (E2::[]++l) by auto.
  setoid_rewrite minus_one_digit_iter_decr_helper; auto.
  simpl.
  enough (E1 :: l = incr1 n).
  rewrite H1.
  apply H.
  apply binary_lt_cons.
  lia.
  symmetry in Heqb.
  apply length_eq_incr_S in Heqb.
  assert (length n  < length (incr1 n)) by lia.
  apply incr1_cons1 in H1.
  eapply Forall_eq.
  simpl. lia.
  constructor.
  reflexivity.
  rewrite Heql.
  remember (incr1 n).
  destruct b.
  auto.
  simpl.
  inversion H1; auto.
  auto.
  rewrite Heql.
  symmetry in Heqb.
  apply length_eq_incr_S in Heqb.
  remember (incr1 n).
  destruct b.
  simpl in Heqb.
  lia.
  simpl in Heqb.
  simpl.
  lia.
  -
  remember (length (incr1 n) =? length n).
  destruct b.
  +
  replace  (2 ^ length n + (2 ^ length n + 0)) with  (2 ^ length n + 2 ^ length n ) by lia.
  rewrite minus_one_digit_iter_decr_E2.
  rewrite minus_one_digit_iter_decr_helper3.
  apply H.
  apply lt_less_length.
  simpl. lia.
  apply PeanoNat.Nat.eqb_eq.
  auto.
  +
  replace  (2 ^ length n + (2 ^ length n + 0)) with  (2 ^ length n + 2 ^ length n ) by lia.
  rewrite minus_one_digit_iter_decr_E2.
  rewrite <- minus_one_digit_E12.
  rewrite minus_one_digit_iter_decr_helper4.
  apply H.
  apply binary_lt_cons. lia.
  apply length_eq_incr_S.
  auto.
Qed.

Lemma minus_incr_hom: forall a b,
minus (incr1 a) (incr1 b) = minus a b.
Proof.
  intros.
  generalize dependent a.
  induction b using bilist_incr_ind; intros.
  simpl.
  apply decr1_incr1.
  rewrite minus_incr_decr.
  rewrite IHb.
  rewrite minus_incr_decr.
  auto.
Qed.

