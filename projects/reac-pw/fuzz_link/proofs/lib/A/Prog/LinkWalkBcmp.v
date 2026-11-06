(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ImgBaseAG.v, with its module paths and module names changed; 66 of its 81 lines of code are new or changed and 92 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the bcmp wrapper (wrapper_bcmp, 0x4305c) on the caller's journal, for the walks of
   link's own functions that call it (check_requests +0xe8).

   aj_gx_bcmp_at: Reusable/YG0d.v `abcmp_realizes segs B pc` (proved on the image by lib/A/AE2s.v
   `bcmp_icpt_contract` at 0x4305c, from AR_laws and PcapSyms) lifted onto ajournal_gx with LinkWalk.v
   aj_gx_art_sm_at (window 2 * ESTACK), keeping `same_but_materialized` for apost's descriptors and file system.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma aj_gx_bcmp_at : forall pc, abcmp_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, y <= a < y + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (getr regs2 10 = w64 0 <->
          forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hy Hn Hn0 Hx0 Hxn Hy0 Hyn Hsx Hsy Hwx Hwy Hax Hay Hrx Hhx Hry Hhy.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre SK segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT
  HJX ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & Hrow & Hwin).
eapply SRr_mono.
{ apply (aj_gx_art_sm_at SK segs B LAWS segs_low (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP
    ly S W0 mem md own lyc Sc mdc k raw
    (fun regs' _ => getr regs' 10 = w64 0 <->
       forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i))
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - eapply SRr_mono; [exact (HC lyc Sc W regsT memT mdc x y n HPRE Hrow Hwin Hx Hy Hn Hn0 Hx0 Hxn Hy0 Hyn Hsx Hsy
      Hwx Hwy Hax Hay Hrx Hhx Hry Hhy)|].
    cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & v & -> & HAR' & HP & Hsm & Hv & Hiff & Hfr & Hpres).
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
    split; [exact HAR'|]. split; [exact HP|]. split; [exact Hsm|]. split; [rewrite Hv; exact Hiff|].
    split; [intros a Ha Hw _; exact (Hfr a Ha Hw)|]. split; [exact Hpres|].
    intros a Ha. apply Hpres. apply Hwin. exact Ha. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hsm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H))|]. split; [exact Hpres2 | exact Hsm].
Qed.
End a.
