From Coq Require Export List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Nat.
Require Import Psatz.
Require Import ZArith.

Require Import Common.
Require Import Basic.

Import Common.

Local Open Scope nat_scope.


Inductive biZ := biNat : bilist -> biZ | biNeg : bilist -> biZ.

