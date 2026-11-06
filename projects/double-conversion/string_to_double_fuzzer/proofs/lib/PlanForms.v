(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP
     AsanMainLib AsanShape AsanMainDefs AsanMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section Forms.
  Variable HS_asan : nat -> option acs.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Variable TTm : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

  Definition segb (ch : acs) (C : class) (HT : list (nat * (nat * acs))) (L : nat) (p : plan) : bool :=
    match seg_check KCm BFUELm FUELm ITm TTm ch C HT p with
    | COk s => class_seg_ok (lv_of HT) L C s
    | CErr _ _ _ => false
    end.
  Definition payb (ch : acs) (C : class) (L : nat) (p : plan) : bool :=
    match pay_check KCm BFUELm FUELm ITm TTm ch C p with
    | COk s => class_pay_ok L C s
    | CErr _ _ _ => false
    end.
  Definition preb (h : nat) (C : class) (HT : list (nat * (nat * acs))) (L : nat) (p : plan) : bool :=
    match pre_check HS_asan KCm BFUELm FUELm ITm TTm h C HT p with
    | COk s => class_seg_ok (lv_of HT) L C s
    | CErr _ _ _ => false
    end.

  (* [comment removed for export] *)
  Lemma segb_tree : forall lo hi ch C L p HT PT,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    segb ch C HT L p = true ->
    mcover HT PT = true -> mforest_ok KCm BFUELm FUELm ITm TTm L HT C PT = true ->
    mtree_ok KCm BFUELm FUELm ITm TTm lo hi ch C (MPre L p HT PT) = true.
  Proof.
    intros lo hi ch C L p HT PT HL H HC HF. unfold segb in H.
    destruct (seg_check KCm BFUELm FUELm ITm TTm ch C HT p) as [s|] eqn:E; [|discriminate H].
    exact (mtree_ok_segP KCm BFUELm FUELm ITm TTm lo hi ch C L p HT PT s HL E H HC HF).
  Qed.
  Lemma payb_leaf : forall lo hi ch C L p,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    payb ch C L p = true ->
    mtree_ok KCm BFUELm FUELm ITm TTm lo hi ch C (MLeaf L p) = true.
  Proof.
    intros lo hi ch C L p HL H. unfold payb in H.
    destruct (pay_check KCm BFUELm FUELm ITm TTm ch C p) as [s|] eqn:E; [|discriminate H].
    exact (mtree_ok_leafP KCm BFUELm FUELm ITm TTm lo hi ch C L p s HL E H).
  Qed.
  Lemma preb_tree : forall hi h C L p HT PT,
    Nat.leb L hi = true ->
    preb h C HT L p = true ->
    mcover HT PT = true -> mforest_ok KCm BFUELm FUELm ITm TTm L HT C PT = true ->
    mtree_ok KCm BFUELm FUELm ITm TTm 0 hi (HSA HS_asan h) C (MPre L p HT PT) = true.
  Proof.
    intros hi h C L p HT PT HL H HC HF. unfold preb in H.
    destruct (pre_check HS_asan KCm BFUELm FUELm ITm TTm h C HT p) as [s|] eqn:E; [|discriminate H].
    exact (mtree_ok_pre0 HS_asan KCm BFUELm FUELm ITm TTm hi h C L p HT PT s HL E H HC HF).
  Qed.
  (* [comment removed for export] *)
End Forms.
