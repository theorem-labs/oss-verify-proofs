(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: the snprintf row SNP_x of image A's top (W_LLVMFuzzerTestOneInput_top_x.v Section topx,
     Hypothesis SNP_x : asnprintf_realizes_x TfibB ARX (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD)
   at top_x's relation after QMm W1, ARX = ARcf /\ Hp = [] /\ arodata_ok_cf (TopX_RT.ARX_rtW, the same body), from
   TopX_SNP.topx_SNP_x at the relation before W1 (FMgxaSeamARX.ARX_seam = ARcf /\ Hp = []), as top_x lifts lock /
   unlock / strlen (topx_ALOCK_W / topx_AUNLOCK_W / topx_ASTRLEN_x_W):
   - the pre at ARX_rtW gives the pre at the old relation and arodata_ok_cf at the call memory (TopX_RT.ecall_pre_rtW);
   - the old post gives ARcf and Hp = [] at the return memory, and arodata_ok_cf survives the call by
     TopX_RT.aro_keep_view: the two exceptions of snprintf's view frame are its output buffer [d, d + n), which starts
     at or above PF_GLOBALS_TOP = 0x5fb000, so it holds no image byte (W_img.fr_img_range) and so no kept byte
     (YCbqG.kept_x_off_img), and its scratch stack window, which lies above the image (TopX_RT.stk_above_img).
   proves no function (kind: segment lemma of the reply top composition). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require TopX_RT TopX_SNP.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section snp_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma topx_SNP_x_W : asnprintf_realizes_x AD2l.TfibB TopX_RT.ARX_rtW (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf)
  W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
Proof.
intros ly S Hp W regs mem md d n f fmt ps args T HG HPRE Ha0 Ha1 Ha2 Hn Hd0 Hf0 HSTR HPS Eps Hflo Hfhi HSA Hdlo
  HT HTl HRD HTV HARGS HWR HAM7 HROM.
destruct HPRE as (HPRE0 & Hstk & Hscr).
destruct (TopX_RT.ecall_pre_rtW _ _ _ _ _ _ _ HPRE0) as (HPRE1 & HQ).
pose proof HPRE1 as (HA & _).
pose proof (TopX_RT.stk_above_img _ _ _ _ _ _ HA) as HI.
eapply YA0n.SRr_mono;
  [exact (TopX_SNP.topx_SNP_x ly S Hp W regs mem md d n f fmt ps args T HG (conj HPRE1 (conj Hstk Hscr)) Ha0 Ha1 Ha2
            Hn Hd0 Hf0 HSTR HPS Eps Hflo Hfhi HSA Hdlo HT HTl HRD HTV HARGS HWR HAM7 HROM)|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HQ' & HV & Hpr & Hsp).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HQ' (conj HV (conj Hpr Hsp)))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TopX_RT.aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n) (ascratch_stk (3 * ESTACK) regs) HA).
- (* the output buffer is off the image: d >= PF_GLOBALS_TOP = 0x5fb000, and every image byte is below 0x5fb000 *)
  intros a Ha. apply kept_x_off_img. intros Hi. pose proof (W_img.fr_img_range a Hi) as Hr.
  unfold W_sites.PF_GLOBALS_TOP in Hdlo. lia.
- (* the scratch window is above the image: ly_stk_lo ly + 3 * ESTACK <= sp and kImgEnd + 2 ^ 40 <= ly_stk_lo ly *)
  intros a Ha. unfold ascratch_stk in Ha. unfold ESTACK in *. lia.
- intros a Hb HnX HnY. exact (HV a Hb HnY HnX).
- exact HQ.
Qed.
End snp_w.
