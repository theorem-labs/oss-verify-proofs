(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the cf BRIDGE of YGcallPx.v. h-rw-man-5's poison / unpoison contracts over the second
   allocator instance (YGcfHp.v:128-154, relaxed to `cf_head <= req_size n`) ARE the generic texts of YGcallPx.v at
     ARx := fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md,  hd := cf_head,
     pc  := cf_pc_poison (poison) / cf_pc_unpoison (unpoison), the per-image CfImg fields.
   Both directions are below (the cf -> x ones by conversion), so a walk takes the cf text itself as its callee
   hypothesis (APOISON : apoison_realizes_cf pa_segs B) and passes apoison_realizes_cf_x / _cf_xs of it where
   YGcallPx's rules (aj_poison_x / aj_poison_at_x / aj_unpoison_x / aj_unpoison_at_x) ask for the generic one.
   The walks' relation is ARcf /\ xs_placed_cf (YGcallcf.v, S1KitAlloc); apoison_realizes_x_xs /
   aunpoison_realizes_x_xs lift a text at plain ARcf to it, apoison_realizes_cf_xs / aunpoison_realizes_cf_xs
   go from the cf text to it in one step, and the rules' LAWS is YGcallcf.v's AR_laws_x_xs.
   Uses the shared cf instance classes CfImg / CfParams only; no preset name, no address, no ledger, no numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface YGcallPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

Lemma apoison_realizes_x_cf :
apoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head cf_pc_poison ->
apoison_realizes_cf segs B.
Proof.
intros H ly S Hp W regs mem md p n Hpre Ha0 Ha1 H8 Hin Hn.
exact (H ly S Hp W regs mem md p n Hpre Ha0 Ha1 H8 Hin ltac:(lia)).
Qed.

Lemma aunpoison_realizes_x_cf :
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head cf_pc_unpoison ->
aunpoison_realizes_cf segs B.
Proof.
intros H ly S Hp W regs mem md p n Hpre Ha0 Ha1 H8 Hhp Hin Hn.
exact (H ly S Hp W regs mem md p n Hpre Ha0 Ha1 H8 Hhp Hin ltac:(lia)).
Qed.

Lemma apoison_realizes_cf_x :
apoison_realizes_cf segs B ->
apoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head cf_pc_poison.
Proof. intros H. exact H. Qed.

Lemma aunpoison_realizes_cf_x :
aunpoison_realizes_cf segs B ->
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head cf_pc_unpoison.
Proof. intros H. exact H. Qed.

(* The walks' relation is ARcf /\ xs_placed_cf (YGcallcf.v, S1KitAlloc): a text at plain ARcf lifts to it, since
   poison and unpoison keep ly and S (YGcallPx.v apoison_realizes_x_conj / aunpoison_realizes_x_conj). *)
Lemma apoison_realizes_x_xs : forall pc,
apoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head pc ->
apoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) cf_head pc.
Proof. intros pc H. exact (apoison_realizes_x_conj segs B _ cf_head xs_placed_cf pc H). Qed.

Lemma aunpoison_realizes_x_xs : forall pc,
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head pc ->
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) cf_head pc.
Proof. intros pc H. exact (aunpoison_realizes_x_conj segs B _ cf_head xs_placed_cf pc H). Qed.

Lemma apoison_realizes_cf_xs :
apoison_realizes_cf segs B ->
apoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) cf_head cf_pc_poison.
Proof. intros H. exact (apoison_realizes_x_xs cf_pc_poison (apoison_realizes_cf_x H)). Qed.

Lemma aunpoison_realizes_cf_xs :
aunpoison_realizes_cf segs B ->
aunpoison_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) cf_head cf_pc_unpoison.
Proof. intros H. exact (aunpoison_realizes_x_xs cf_pc_unpoison (aunpoison_realizes_cf_x H)). Qed.

End J.
End G.
