(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ImgBaseAG.v, with its module paths and module names changed; 102 of its 119 lines of code are new or changed and 90 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the journal lifts of the strnlen and strlen wrappers that KEEP the model relation
   `same_but_materialized mdc md2` of the runtime contract in their post. link_ajkit.v's aj_gx_strnlen_at and
   aj_gx_strlen_at drop it, and a walk that calls the wrapper before its `ret` needs it for apost's
   `m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc`. The strncmp and strcmp lifts that keep it are in
   lib/A/Prog/LinkWalk.v (aj_gx_strncmp_sm_at, aj_gx_strcmp_at, over aj_gx_art_sm_at).

   - aj_gx_strnlen_atS: wrapper_strnlen over lib/Rt/StrnlenDef.v astrnlen_whole_realizesM (window 2 * ESTACK);
     proved on link by lib/A/Rt/RtClosed.v link_strnlenM_closed (0x43048, consts 0x10360 .. 0x10380).
   - aj_gx_strlen_atS: wrapper_strlen over lib/A/Rt/RtString.v astrlen_realizes (window ESTACK); proved on link by
     lib/A/Rt/RtClosed.v cmd_strlen_closed (0x43044).
   Each is generic in the segments (no address of link).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument, as in link_amem.v, link_ajkit.v and LinkWalk.v. *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* wrapper_strnlen over lib/Rt/StrnlenDef.v astrnlen_whole_realizesM: link_ajkit.v aj_gx_strnlen_at, with the
   contract's `same_but_materialized` of the model kept in the post. *)
Lemma aj_gx_strnlen_atS : forall lo hi pc, astrnlen_whole_realizesM segs B lo hi pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  src_ok segs W regsT memT x n -> (forall a, x <= a < x + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range x n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  consts_view segs lo hi W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (exists j, first_byte segs W memT x n 0 j /\ getr regs2 10 = w64 j) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros lo hi pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hn Hnr Hx0 Hxn Hsrc Hwin Hamr Hrad Hhull Hcv.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (aj_gx_ecall_pre SK segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & Hlo2 & Hwin2).
eapply SRr_mono.
{ apply (aj_gx_call_at SK segs B LAWS segs_low (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' mem' md' => AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
       same_but_materialized mdc md' /\
       (exists j, first_byte segs W memT x n 0 j /\ getr regs' 10 = w64 j) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - intros regs' mem' md' (HAR' & _ & Hs & _ & Hf & Hp).
    split; [exact HAR'|]. split; [exact Hs|]. split; [|exact Hp].
    intros a Ha Hw _. exact (Hf a Ha Hw).
  - exact (HC lyc Sc W regsT memT mdc x n HPRE Hlo2 Hwin2 Hx Hn Hnr Hx0 Hxn Hsrc Hwin Hamr Hrad Hhull Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & Hs & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hs].
Qed.

(* wrapper_strlen over lib/A/Rt/RtString.v astrlen_realizes (window ESTACK): link_ajkit.v aj_gx_strlen_at, through
   LinkWalk.v aj_gx_art_sm_at, with `same_but_materialized` of the model kept in the post. *)
Lemma aj_gx_strlen_atS : forall pc, RtString.astrlen_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> 0 < x ->
  astr_at segs W memT x s ->
  aread_ok segs ESTACK W regsT memT x (astr_len s + 1) ->
  atail_vis segs W memT (x + astr_len s) ->
  rt_rom_view segs B W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (astr_len s) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hx0 Hstr Hrd Htail Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre SK segs B ESTACK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_gx_art_sm_at SK segs B LAWS segs_low ESTACK (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S W0
    mem md own lyc Sc mdc k raw (fun regs' _ => getr regs' 10 = w64 (astr_len s)) HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - exact (HC lyc Sc W regsT memT mdc x s HPRE Hx Hx0 Hstr Hrd Htail Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hsm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H))|]. split; [exact Hpres2 | exact Hsm].
Qed.
End w.
End a.
