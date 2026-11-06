(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the B top's SNP row.  lib/B/W_LLVMFuzzerTestOneInput_top_x.v's Section hypothesis SNP_x
     Hypothesis SNP_x : asnprintf_realizes_x TfibB ARX (pa_sigma WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
   (top_x.v:851 on a working branch 5f9367924bc) at the B top's instance, closed: topx_SNP_x below states that type
   with top_x's ARX written as its body (top_x.v:164-165, `fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs
   TfibB ly S Hp W mem md /\ Hp = []`), as lib/B/TopxDrainLitB.v and RT_pf_snp_srr.v snp_xn_ARX do, so this file does
   not Require top_x and the plug of SNP_x is `exact topx_SNP_x` up to unfolding ARX.
   - The proof is RT_pf_snp_srr.v snp_xn_ARX (snprintf at __wrap_snprintf proved on image B), whose two hypotheses close
     here: W_H8 by the world field w_H8 (Reusable/YA0n.v), REALVSN by topx_REALVSN.
   - snp_xn_ARX concludes RT_pf_snp_srr.v's asnprintf_realizes_xn; W_sites_x.v's asnprintf_realizes_x carries the same
     four narrowing premises (narrowed in place, the previous commits), so the two texts are equal up to the name of
     the image top (W_sites.v's PF_GLOBALS_TOP, RT_pf_Tbl.v's, both 0x5fc000: SnpNarrowSites.v PF_GLOBALS_TOP_tbl), and
     the step is conversion.
   - topx_REALVSN: REAL(vsnprintf) = musl vsnprintf in every ARX state, from the allocator laws' const-cell field
     (YCbqG.alx_const_cells at FMgxaSeamARX.ARX_seam_laws, whose relation is ARX's body), YF0m.ts_const at
     YD2l.TfibB_syms, and the window's const row z8 (ANum 0x9fcf0) 0x963b4 (YF0m Tfib_const; a vm_compute lookup),
     read as a word by YF0x.val_mem_rdword.  SnpLand's discharge probe on image B (PfChainRevive.SnpLand, throwaway
     ZZSnpLandProbe.v, 2026-10-30), committed here.
   No file on this tree instantiates B top_x's fr_contract_top_x with its topx_* rows (lib/B/ReplyDriverCfB.v's fit
   check passes only the four head rules and is Aborted), so this row is the plug of record for SNP_x.
   proves no function (kind: instance discharge). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites W_journal_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require VfprintfCall G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RT_IImgA RT_gxa_calls RT_gxa_calls_mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FMgxaSeamCall RT_pf_stmt RT_pf_stmt_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Exec Mem Frame Cells Step MState Arr ITree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0x RT_pf_kit RT_pf_bz FMgxa_bridge FMgxaSeamBase
FMgxaSeamCells FMgxaSeamFam FMgxaSeamPost FMgxaSeamShadow FMgxaSeamNorm FMgxaSeamNormG FMgxaSeamNormX FMgxaSeamPostX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FMgxaSeamReadyX FMgxaSeamGuard FMgxaSeamShadowX
RT_pf_snp_pcom RT_pf_chain_k FMgxaSeamARX YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require ImageA Mem Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require R_m2s I_pcrr I_pchead I_pck I_qck I_pcxgram
I_pcxlist F_achk Shadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Printf_model Printf_text G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RStep.
(* the B top's instance (snp_xn_ARX below): its start-up B (TfibB, TfibB_syms), the cf live state at the one
   parameter record of both images, and the two side laws proved at it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FMgxaSeamARX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_snp_srr.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.W_img.
Module TRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.TopX_RT_lock.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section topx_snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* snp_xn_ARX's REALVSN at the B top's ARX *)
Lemma topx_REALVSN : forall ly S Hp (W : world tfibsegs) mem md,
  (ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) ->
  rdword (aview tfibsegs (w_H W) mem) PF_REAL_VSNPRINTF = Some PF_MUSL_VSNPRINTF.
Proof.
intros ly S Hp W mem md HAR.
apply YF0x.val_mem_rdword; [unfold PF_MUSL_VSNPRINTF; lia|].
pose proof (YF0x.cell_holds_val_mem TfibB ly (w_H W) mem (ANum PF_REAL_VSNPRINTF) 8 (ANum PF_MUSL_VSNPRINTF))
  as HV.
cbn [YG0f.aeval] in HV. apply HV.
apply (proj1 (Forall_forall (cell_holds TfibB ly (aview tfibsegs (w_H W) mem)) (as_const TfibB ly))
         (alx_const_cells _ _ _ FMgxaSeamARX.ARX_seam_laws ly S Hp W mem md HAR)).
rewrite (ts_const TfibB TfibB_syms ly).
apply (YF0x.cell_lookup_In _ (ANum PF_REAL_VSNPRINTF)). vm_compute. reflexivity.
Qed.

(* the row: top_x's SNP_x type, ARX unfolded *)
Lemma topx_SNP_x :
  asnprintf_realizes_x TfibB
    (fun ly S Hp (W : world segs) mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [])
    (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
Proof. exact (snp_xn_ARX (fun W a H => w_H8 W a H) topx_REALVSN). Qed.
End topx_snp.

(* ---- QMm W1 (a Theorem Labs lane's B W1 rows, 2026-10-31): the SNP row at the B top's W1 ARX, TopX_RT_lock.ARX_rtW (top_x's
   ARX: ARcf /\ Hp = [] /\ arodata_ok_cf). topx_SNP_x above stays; top_x cites topx_SNP_W. The lift is TopX_RT_lock's
   rule: split the pre (ecall_pre_rtW), run topx_SNP_x at ARX_rt, and keep arodata_ok_cf across the call's view frame
   (aro_keep_view). Its write set is the buffer [d, d + n): PF_GLOBALS_TOP = 0x5fc000 <= d and every image byte lies
   below 0x5fc000 (W_img.fr_img_range), so it holds no kept byte (YCbqG.kept_x_off_img); its stack window
   (ascratch_stk (3 * ESTACK)) lies above the image (TopX_RT_lock.stk_above_img and the pre's stack bound). ---- *)
Section topx_snp_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Lemma topx_SNP_W :
  asnprintf_realizes_x TfibB TRL.ARX_rtW (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf) W_sites.FR_GOT_GUARD
    W_sites.FR_GUARD.
Proof.
intros ly S Hp W regs mem md d n f fmt ps args T Hg (HPRE & Hlo & Hsc).
destruct (TRL.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
pose proof (TRL.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
intros H10 H11 H12 Hn Hd Hf Hfmt Hps Hpsl Hf1 Hf2 Hs Hgl.
lazymatch type of Hgl with ?g <= _ => let v := eval vm_compute in g in change g with v in Hgl end.
intros.
eapply SRr_mono; [eapply (topx_SNP_x ly S Hp W regs mem md d n f fmt ps args T Hg (conj HPRE0 (conj Hlo Hsc)));
  eassumption|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HQ' & HV & Hpr & Hsc').
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
split; [|exact (conj Hrp (conj Hsm (conj HQ' (conj HV (conj Hpr Hsc')))))].
split; [exact HA'|]. split; [exact HH'|].
apply (TRL.aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n)
  (fun a => spZ regs - 3 * ESTACK <= a < spZ regs) (proj1 HPRE0)).
- intros a Ha. apply kept_x_off_img. intros Hi. pose proof (W_img.fr_img_range a Hi). cbv beta in Ha. lia.
- intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
- intros a Ha HnX HnY. exact (HV a Ha HnY HnX).
- exact HQ.
Qed.
End topx_snp_w.
