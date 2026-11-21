(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma xtnl_locked : { f : nat -> Z -> Z | f = xtn }. Proof. exists xtn. reflexivity. Qed.
Definition xtnl : nat -> Z -> Z := proj1_sig xtnl_locked.

(* [comment removed for export] *)
Ltac xor_ac :=
  apply Z.bits_inj'; intros ?n ?Hn; rewrite !Z.lxor_spec;
  repeat match goal with |- context [Z.testbit ?x ?m] => generalize (Z.testbit x m); intro end;
  btauto.

(* [comment removed for export] *)
Definition comb5 (x0 x1 x2 x3 x4 : Z) : Z :=
  Z.lxor (xtnl 160 x0) (Z.lxor (xtnl 128 x1) (Z.lxor (xtnl 96 x2) (Z.lxor (xtnl 64 x3) (xtnl 32 x4)))).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lane_step (l w : Z) : Z := xtnl 160 (Z.lxor l w).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition combine (l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 : Z) : Z :=
  xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor l0 w0)) (Z.lxor l1 w1))) (Z.lxor l2 w2))) (Z.lxor l3 w3))) (Z.lxor l4 w4)).

(* [comment removed for export] *)
Definition binv (l0 l1 l2 l3 l4 q : Z) : Prop := comb5 l0 l1 l2 l3 l4 = xtnl 160 q.

(* [comment removed for export] *)

