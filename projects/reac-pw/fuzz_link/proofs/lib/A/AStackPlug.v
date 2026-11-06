(** * reac-pw/fuzz_link (asan, image A): the side-stack premises of lib/A/AStackApi.v, discharged.

    [AStackApi.link_stack_malloc_sized] and [AStackApi.link_stack_free_called] take the size-premised contracts of
    classes 8 and 9 ([SM8], [SM9]) and the release contracts of classes 8 and 9 ([SF8], [SF9]) as premises. This file
    gives each from the walks' instances (lib/A/Rt/StackSideInst.v), for every [B] with [PcapSyms B] and every
    [FPState]:
    - [sm8_of_inst], [sf8_of_inst]: [link_stack_malloc_8] / [link_stack_free_8], whose types name the constants
      [PC_STACK_MALLOC_8] = 0x3df90, [PC_STACK_FREE_8] = 0x3e10c, [CID8] = 8 (Rt/StackMalloc8Tbl.v, Rt/StackFree8Tbl.v);
    - [sm9_of_inst], [sf9_of_inst]: [link_stack_malloc_9] / [link_stack_free_9], whose types are the definitions
      [stack_malloc_9_contract B] / [stack_free_9_contract B] (Rt/StackSide9.v) over [PC_STACK_MALLOC_9] = 0x3e15c,
      [PC_STACK_FREE_9] = 0x3e2d4, [CID9] = 9.
    Each is closed by [exact] on the instance: the match is up to unfolding those named constants and definitions
    (delta conversion only; [link_side_consts] checks each constant's value by [eq_refl]). [link_sized_plugged] and
    [link_free_plugged] are AStackApi's two lemmas with the four premises supplied. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AsStackSz StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0l AStackApi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackMalloc8Tbl StackFree8Tbl StackSide9 StackSideInst.
Import ListNotations.
Local Open Scope Z_scope.

(** The constants the instances name, and the class-9 definitions, by their values. *)
Lemma link_side_consts :
  PC_STACK_MALLOC_8 = 0x3df90 /\ PC_STACK_FREE_8 = 0x3e10c /\ CID8 = 8 /\
  PC_STACK_MALLOC_9 = 0x3e15c /\ PC_STACK_FREE_9 = 0x3e2d4 /\ CID9 = 9.
Proof. repeat split; reflexivity. Qed.

Lemma sm9_def : forall (fq : YK11.FPState) (rc : YM05.RunCeil) B,
  stack_malloc_9_contract (fx := fq) B = astack_malloc_sz_realizes (fx := fq) tfibsegs B 0x3e15c 9.
Proof. reflexivity. Qed.

Lemma sf9_def : forall (fq : YK11.FPState) (rc : YM05.RunCeil) B,
  stack_free_9_contract (fx := fq) B = astack_free_realizes (fx := fq) tfibsegs B 0x3e2d4 9.
Proof. reflexivity. Qed.

Section p.
Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma sm8_of_inst : forall fq : YK11.FPState, astack_malloc_sz_realizes (fx := fq) tfibsegs B 0x3df90 8.
Proof. intros fq. exact (link_stack_malloc_8 (fx := fq) B TB). Qed.

Lemma sm9_of_inst : forall fq : YK11.FPState, astack_malloc_sz_realizes (fx := fq) tfibsegs B 0x3e15c 9.
Proof. intros fq. exact (link_stack_malloc_9 (fx := fq) B TB). Qed.

Lemma sf8_of_inst : forall fq : YK11.FPState, astack_free_realizes (fx := fq) tfibsegs B 0x3e10c 8.
Proof. intros fq. exact (link_stack_free_8 (fx := fq) B TB). Qed.

Lemma sf9_of_inst : forall fq : YK11.FPState, astack_free_realizes (fx := fq) tfibsegs B 0x3e2d4 9.
Proof. intros fq. exact (link_stack_free_9 (fx := fq) B TB). Qed.

(** AStackApi's lemmas with the four premises supplied. *)
Lemma link_sized_plugged : forall (fq : YK11.FPState) cid pc, In (cid, pc) link_fs_sized ->
  astack_malloc_sz_realizes (fx := fq) tfibsegs B pc cid.
Proof. exact (link_stack_malloc_sized tfibsegs B sm8_of_inst sm9_of_inst). Qed.

Lemma link_free_plugged : forall (fq : YK11.FPState) cid pc, In (cid, pc) link_fs_free ->
  astack_free_realizes (fx := fq) tfibsegs B pc cid.
Proof. exact (link_stack_free_called tfibsegs B sf8_of_inst sf9_of_inst). Qed.

End p.
