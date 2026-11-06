(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ImgBaseAG.v, with its module paths and module names changed; 66 of its 81 lines of code are new or changed and 92 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkBcmp.v, with its module paths and module names changed; 67 of its 96 lines of code are new or changed and 52 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the printf-family calls on link's memory FILE as steps of the caller's program-global
   journal `ajournal_gx G XO OUT` (lib/A/W_journalG.v), for the walks of link's own functions that print on g_say
   (reac_code_emit 0x89d00 fprintf / 0x89d1c vfprintf, reac_served_mark 0x89aec / 0x89b5c fprintf).

   The two contracts are lib/A/Rt/LinkVfDefs.v `afprintf_mf_realizes` / `avfprintf_mf_realizes`:
   a call at pc with ecall_pre, a stack window of K bytes, the FILE at f with k bytes pending,
   returning to ra at SOME FP state fx' (f registers but f10 kept, rounding mode 0), AR at the call's ly S W, every
   byte outside the window and the FILE block kept, presence kept, and the FILE as `apf_file_post` says. A caller
   applies the contract at its own state (ly := lyc, S := Sc, the premises are the caller's facts) and gets an SRr from
   `cfg_at segs pc regsT memT mdc`; `aj_gx_printf_mf_at` lifts that SRr onto the caller's journal (link_ajkit.v
   `aj_gx_call_atF` with the written cells Eb := the FILE block, which the caller's write set grants through `ajw`),
   and turns the post's FP facts into `BoxBase.fxr fx fx'` (link_amem.v `fxr_of_frm0`), the relation `apostF`
   carries. `aj_gx_printf_pre` gives the call's ecall_pre, the window's room and presence from the journal (link_ajkit.v
   `aj_gx_ecall_pre` at w := K).

   The two posts have the same shape, so one lift serves both contracts.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.
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
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* The call's pre-state on the journal: ecall_pre at the journal's current state, the K bytes below sp are the
   journal's (room above ly_stk_lo, present). *)
Lemma aj_gx_printf_pre : forall K G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  ESTACK <= K -> spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - K -> spZ regsT <= sp0 ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  ecall_pre segs B lyc Sc W regsT memT mdc /\ ly_stk_lo lyc + K <= spZ regsT /\
  (forall a, spZ regsT - K <= a < spZ regsT -> apresent (w_H W) memT a).
Proof.
intros K G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX HK H16 Hlo Hhi Hra Hgp Htp.
exact (aj_gx_ecall_pre SK segs B K G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT
  HJX HK H16 Hlo Hhi Hra Hgp Htp).
Qed.

(* THE STEP: a printf-family contract's conclusion at the caller's state (the SRr from cfg_at that
   afprintf_mf_realizes / avfprintf_mf_realizes give at ly := lyc, S := Sc, MS := link_amf), lifted onto the caller's
   journal. The FILE block's bytes are bytes the journal lets a callee write (the caller's write set, apre's ajw). *)
Lemma aj_gx_printf_mf_at : forall K pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
    (f kp : Z) (pb T : list Z) (fl om wend pos len : Z),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= K -> sp0 - STK <= spZ regsT - K -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, f <= a < f + AMF_BLOCK -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  SRr segs W (cfg_at segs pc regsT memT mdc)
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs (raZ regsT) regs' mem' md' /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
       Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
       AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\ same_but_materialized mdc md' /\
       getr regs' 10 = w64 (Z.of_nat (length T)) /\
       apf_file_post segs link_amf (rdW W mem') f kp pb T fl om wend pos len /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
          ~ (spZ regsT - K <= a < spZ regsT) -> aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a)) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
       @BoxBase.fxr fx fx' /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = w64 (Z.of_nat (length T)) /\
       apf_file_post segs link_amf (rdW W mem2) f kp pb T fl om wend pos len /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
          ~ (spZ regsT - K <= a < spZ regsT) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros K pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw f kp pb T fl om wend pos len
  HG HJX HK Hlo Hhi Hraw HF HC.
eapply SRr_mono.
{ apply (aj_gx_call_atF SK segs B LAWS segs_low K (fun a => f <= a < f + AMF_BLOCK) pc G XO OUT W regsT memT STK
    sp0 FP ly S W0 mem md own lyc Sc mdc k raw
    (fun fx' regs' mem' md' =>
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
       Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
       AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\ same_but_materialized mdc md' /\
       getr regs' 10 = w64 (Z.of_nat (length T)) /\
       apf_file_post segs link_amf (rdW W mem') f kp pb T fl om wend pos len /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
          ~ (spZ regsT - K <= a < spZ regsT) -> aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))
    HG HJX HK Hlo Hhi Hraw).
  - intros a Ha. exact (HF a Ha).
  - intros fx' regs' mem' md' (_ & _ & HAR & _ & Hsame & _ & _ & Hkept & Hpres).
    split; [exact HAR|]. split; [exact Hsame|]. split; [|exact Hpres].
    intros a Ha Hw Hf. exact (Hkept a Ha Hf Hw).
  - exact HC. }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HJ2 & HR & HZ & _ & HP & Hsm & H10 & Hfp & Hkept & Hpres).
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [reflexivity|].
split; [exact (fxr_of_frm0 fx fx' HR HZ)|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hsm|]. split; [exact H10|]. split; [exact Hfp|].
split; [exact Hkept | exact Hpres].
Qed.

End a.
