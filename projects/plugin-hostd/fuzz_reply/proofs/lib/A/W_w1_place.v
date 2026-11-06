(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the placement hypotheses of lane W1's walks, discharged at the pinned placement
   PB_fr (W_img.v) in the form of W_img.v fr_relro_img: W_check_bounded.v CBAP (cb_objs_apart), W_next_line.v NLAP
   (nl_objs_apart) and HCROM (musl memchr's masks at 0x10350 .. 0x10370 lie in a read-only segment). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_kit W_img W_contract W_check_bounded W_next_line.
Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

(* Replace each object address the goal names at PB_fr by its value. *)
Ltac w1_vals := repeat match goal with |- context [@pa_val ?T ?L PB_fr ?n] =>
  let v := eval vm_compute in (@pa_val T L PB_fr n) in change (@pa_val T L PB_fr n) with v end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma cb_objs_apart_fr : cb_objs_apart (PI := PB_fr).
Proof. unfold cb_objs_apart. cbv zeta. w1_vals. lia. Qed.

Lemma nl_objs_apart_fr : nl_objs_apart (PI := PB_fr).
Proof. unfold nl_objs_apart. cbv zeta. w1_vals. lia. Qed.
Lemma nl_crom_fr : forall a, 0x10350 <= a < 0x10370 -> in_rom (@pa_segs _ fr_prog_listing PB_fr) a.
Proof.
intros a Ha. exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
End a.
