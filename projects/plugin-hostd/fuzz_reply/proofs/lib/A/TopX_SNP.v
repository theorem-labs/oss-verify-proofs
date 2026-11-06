(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/TopX_SNP.v, with its module paths and module names changed; 9 of its 67 lines of code are new or changed and 46 lines of the source are left out. *)
(* The top_x row SNP_x (TOPX-OWNERS.md (sha256 bb821fae800d; internal record), group RT; TOPX-PLUGS.md (sha256 e0a351b05fe4; internal record), "SNP narrowing"),
   PROVED at the instance.  A's top_x (W_LLVMFuzzerTestOneInput_top_x.v:921) states
     SNP_x : asnprintf_realizes_x TfibB ARX (SIGMA WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD
   and topx_SNP_x below states it at FMgxaSeamARX.v's ARX_seam, top_x.v:162-163's ARX verbatim, as TopX_RT.v states
   its rows at ARX_rt: the plug at the top (ReplyATopX.v's SNP_x) is `exact` up to unfolding.  This file does not
   Require top_x.
   - The proof is RT_pf_snp_srr.v's snp_xn_ARX: W_sites_x.v's asnprintf_realizes_x is narrowed in place to the text
     of RT_pf_snp_srr.v's asnprintf_realizes_xn, so the two are the same proposition up to unfolding (their
     PF_GLOBALS_TOP are W_sites.v's and RT_pf_Tbl.v's, the same number 0x5fb000).
   - Its two premises are closed here: W_H8 by the world field w_H8; REALVSN (REAL(vsnprintf) = musl vsnprintf in
     every ARx state) by topx_REALVSN, from the allocator laws' alx_const_cells at ARX_seam_laws and the start-up
     table's const row z8 (ANum 0x9f770) 0x95e34 (ts_const at TfibB_syms; the row found by vm_compute, read by
     AF0x.val_mem_rdword).
   No premise is left: every lemma here is closed.
   proves no function (kind: composition). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites W_journal_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require VfprintfCall G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RT_IImgA RT_gxa_calls RT_gxa_calls_mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FMgxaSeamCall RT_pf_stmt RT_pf_stmt_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pf_Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Exec Mem Frame Cells Step MState Arr ITree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0x RT_pf_kit RT_pf_bz FMgxa_bridge FMgxaSeamBase
FMgxaSeamCells FMgxaSeamFam FMgxaSeamPost FMgxaSeamShadow FMgxaSeamNorm FMgxaSeamNormG FMgxaSeamNormX FMgxaSeamPostX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FMgxaSeamReadyX FMgxaSeamGuard FMgxaSeamShadowX
RT_pf_snp_pcom RT_pf_chain_k FMgxaSeamARX AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require ImageA Mem Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require R_m2s I_pcrr I_pchead I_pck I_qck I_pcxgram
I_pcxlist F_achk Shadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Printf_model Printf_text G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RT_pf_snp_srr.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section topx_snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* REALVSN of RT_pf_snp_srr.v's snp_xn_ARX: the cell 0x9f770 holds musl vsnprintf's address in every ARX state *)
Lemma topx_REALVSN : forall ly S Hp (W : world tfibsegs) mem md, FMgxaSeamARX.ARX_seam ly S Hp W mem md ->
  rdword (aview tfibsegs (w_H W) mem) PF_REAL_VSNPRINTF = Some PF_MUSL_VSNPRINTF.
Proof.
intros ly S Hp W mem md HAR.
apply AF0x.val_mem_rdword; [unfold PF_MUSL_VSNPRINTF; lia|].
pose proof (AF0x.cell_holds_val_mem AD2l.TfibB ly (w_H W) mem (ANum PF_REAL_VSNPRINTF) 8 (ANum PF_MUSL_VSNPRINTF))
  as HV.
cbn [YG0f.aeval] in HV. apply HV.
apply (proj1 (Forall_forall (cell_holds AD2l.TfibB ly (aview tfibsegs (w_H W) mem)) (as_const AD2l.TfibB ly))
         (alx_const_cells _ _ _ FMgxaSeamARX.ARX_seam_laws ly S Hp W mem md HAR)).
rewrite (ts_const AD2l.TfibB AD2l.TfibB_syms ly).
apply (AF0x.cell_lookup_In _ (ANum PF_REAL_VSNPRINTF)). vm_compute. reflexivity.
Qed.

(* SNP_x (top_x.v:816) at ARX_seam *)
Lemma topx_SNP_x :
  asnprintf_realizes_x AD2l.TfibB FMgxaSeamARX.ARX_seam (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf)
    W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
Proof. exact (RT_pf_snp_srr.snp_xn_ARX (fun W a H => w_H8 W a H) topx_REALVSN). Qed.

End topx_snp.
