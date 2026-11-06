(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_012.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_cLN0 F0A_hbN_cert F0A_cLN1.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_blind l0 F0A_cN0 F0A_cN1.

(* [comment removed for export] *)
Module F0A_hbLN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbLN0"; "AM_LN0_0L"; "AM_LN0_0M"; "AU_LN0_0L"; "AU_LN0_0M"; "C5_LN0_0L"; "C5_LN0_0M"; "DUo_LN0_0L"; "DUo_LN0_0M"; "E5_LN0_0L"; "E5_LN0_0M"; "EM_LN0_0L"; "EM_LN0_0M"; "EMd_LN0_0L"; "EMd_LN0_0M"; "EMx_LN0_0L"; "EMx_LN0_0M"; "EU_LN0_0L"; "EU_LN0_0M"; "EUd_LN0_0L"; "EUd_LN0_0M"; "EUs_LN0_0L"; "EUs_LN0_0M"; "EUx_LN0_0L"; "EUx_LN0_0M"; "LA_LN0_0"; "LR_LN0_0L"; "LR_LN0_0M"; "PT_LN0_0L"; "PT_LN0_0M"; "R5_LN0_0L"; "R5_LN0_0M"; "S0_LN0_0"; "SC_LN0_0"; "SX_LN0_0L"; "SX_LN0_0M"; "T5_LN0_0L"; "T5_LN0_0M"; "T5f_LN0_0L"; "T5f_LN0_0M"; "XF_LN0_0L"; "XF_LN0_0M"; "lPA_LN0_0"; "lPB_LN0_0L"; "lPB_LN0_0M"; "lPC_LN0_0L"; "lPC_LN0_0M"; "lPD_LN0_0L"; "lPD_LN0_0M"; "lPE_LN0_0L"; "lPE_LN0_0M"; "lPL_LN0_0"; "lPT_LN0_0L"; "lPT_LN0_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN0 : axst := Eval vm_compute in Erc_LN0.
Lemma FRESH_LN0 : hb_fresh E_LN0 = true. Proof. vmr. Qed.

Definition S0_LN0_0 : axst := Eval vm_compute in (S0_hb E_LN0 0).
Definition lPA_LN0_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN0_0).
Definition LA_LN0_0 : axst := Eval vm_compute in (leaf 0 lPA_LN0_0).
Definition SC_LN0_0 : axst := Eval vm_compute in (SC_hb LA_LN0_0).
Definition lPL_LN0_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN0_0).
Definition FAM_LN0_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN0_0_ok : hbfam_ok Erc_LN0 0 FAM_LN0_0.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_LN0_0L : axst := Eval vm_compute in (SX_hb SC_LN0_0 0 true).
Definition lPB_LN0_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN0_0L).
Definition E5_LN0_0L : axst := Eval vm_compute in (leaf 0 lPB_LN0_0L).
Definition C5_LN0_0L : axst := Eval vm_compute in (C5_hb E5_LN0_0L).
Definition R5_LN0_0L : list sobj := Eval vm_compute in (R5_hb C5_LN0_0L).
Definition T5_LN0_0L : axst := Eval vm_compute in (T5_hb C5_LN0_0L).
Definition T5f_LN0_0L : axst := Eval vm_compute in (T5f_hb C5_LN0_0L).
Definition lPC_LN0_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN0_0L).
Definition EUs_LN0_0L : axst := Eval vm_compute in (leaf 0 lPC_LN0_0L).
Definition EM_LN0_0L : axst := Eval vm_compute in (leaf 1 lPC_LN0_0L).
Definition EMx_LN0_0L : axst := Eval vm_compute in (selX EM_LN0_0L [O_csh vH vMS]).
Definition EMd_LN0_0L : axst := Eval vm_compute in (EMd_hb EM_LN0_0L).
Definition AM_LN0_0L : axst := Eval vm_compute in (A_after EMd_LN0_0L (SLit 0)).
Definition lPD_LN0_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN0_0L).
Definition EU_LN0_0L : axst := Eval vm_compute in (leaf 0 lPD_LN0_0L).
Definition EUx_LN0_0L : axst := Eval vm_compute in (selX EU_LN0_0L (D_U_hb true)).
Definition EUd_LN0_0L : axst := Eval vm_compute in (EUd_hb EU_LN0_0L true).
Definition DUo_LN0_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN0_0L))) (ss_objs (ax_S EUx_LN0_0L))).
Definition AU_LN0_0L : axst := Eval vm_compute in (A_after EUd_LN0_0L (SLit 0)).
Definition lPE_LN0_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN0_0L).
Definition LR_LN0_0L : axst := Eval vm_compute in (leaf 0 lPE_LN0_0L).
Definition PT_LN0_0L : axst := Eval vm_compute in (PT_hb LR_LN0_0L).
Definition lPT_LN0_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN0_0L).
Definition XF_LN0_0L : axst := Eval vm_compute in (leaf 0 lPT_LN0_0L).
Definition VAR_LN0_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN0_0L_ok : hbvar_ok SC_LN0_0 0 true VAR_LN0_0L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_LN0_0M : axst := Eval vm_compute in (SX_hb SC_LN0_0 0 false).
Definition lPB_LN0_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN0_0M).
Definition E5_LN0_0M : axst := Eval vm_compute in (leaf 0 lPB_LN0_0M).
Definition C5_LN0_0M : axst := Eval vm_compute in (C5_hb E5_LN0_0M).
Definition R5_LN0_0M : list sobj := Eval vm_compute in (R5_hb C5_LN0_0M).
Definition T5_LN0_0M : axst := Eval vm_compute in (T5_hb C5_LN0_0M).
Definition T5f_LN0_0M : axst := Eval vm_compute in (T5f_hb C5_LN0_0M).
Definition lPC_LN0_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN0_0M).
Definition EUs_LN0_0M : axst := Eval vm_compute in (leaf 0 lPC_LN0_0M).
Definition EM_LN0_0M : axst := Eval vm_compute in (leaf 1 lPC_LN0_0M).
Definition EMx_LN0_0M : axst := Eval vm_compute in (selX EM_LN0_0M [O_csh vH vMS]).
Definition EMd_LN0_0M : axst := Eval vm_compute in (EMd_hb EM_LN0_0M).
Definition AM_LN0_0M : axst := Eval vm_compute in (A_after EMd_LN0_0M (SLit 0)).
Definition lPD_LN0_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN0_0M).
Definition EU_LN0_0M : axst := Eval vm_compute in (leaf 0 lPD_LN0_0M).
Definition EUx_LN0_0M : axst := Eval vm_compute in (selX EU_LN0_0M (D_U_hb false)).
Definition EUd_LN0_0M : axst := Eval vm_compute in (EUd_hb EU_LN0_0M false).
Definition DUo_LN0_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN0_0M))) (ss_objs (ax_S EUx_LN0_0M))).
Definition AU_LN0_0M : axst := Eval vm_compute in (A_after EUd_LN0_0M (SLit 0)).
Definition lPE_LN0_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN0_0M).
Definition LR_LN0_0M : axst := Eval vm_compute in (leaf 0 lPE_LN0_0M).
Definition PT_LN0_0M : axst := Eval vm_compute in (PT_hb LR_LN0_0M).
Definition lPT_LN0_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN0_0M).
Definition XF_LN0_0M : axst := Eval vm_compute in (leaf 0 lPT_LN0_0M).
Definition VAR_LN0_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN0_0M_ok : hbvar_ok SC_LN0_0 0 false VAR_LN0_0M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbLN0.

(* [comment removed for export] *)
Module F0A_hbLN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbLN1"; "AM_LN1_0L"; "AM_LN1_0M"; "AU_LN1_0L"; "AU_LN1_0M"; "C5_LN1_0L"; "C5_LN1_0M"; "DUo_LN1_0L"; "DUo_LN1_0M"; "E5_LN1_0L"; "E5_LN1_0M"; "EM_LN1_0L"; "EM_LN1_0M"; "EMd_LN1_0L"; "EMd_LN1_0M"; "EMx_LN1_0L"; "EMx_LN1_0M"; "EU_LN1_0L"; "EU_LN1_0M"; "EUd_LN1_0L"; "EUd_LN1_0M"; "EUs_LN1_0L"; "EUs_LN1_0M"; "EUx_LN1_0L"; "EUx_LN1_0M"; "LA_LN1_0"; "LR_LN1_0L"; "LR_LN1_0M"; "PT_LN1_0L"; "PT_LN1_0M"; "R5_LN1_0L"; "R5_LN1_0M"; "S0_LN1_0"; "SC_LN1_0"; "SX_LN1_0L"; "SX_LN1_0M"; "T5_LN1_0L"; "T5_LN1_0M"; "T5f_LN1_0L"; "T5f_LN1_0M"; "XF_LN1_0L"; "XF_LN1_0M"; "lPA_LN1_0"; "lPB_LN1_0L"; "lPB_LN1_0M"; "lPC_LN1_0L"; "lPC_LN1_0M"; "lPD_LN1_0L"; "lPD_LN1_0M"; "lPE_LN1_0L"; "lPE_LN1_0M"; "lPL_LN1_0"; "lPT_LN1_0L"; "lPT_LN1_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN1 : axst := Eval vm_compute in Erc_LN1.
Lemma FRESH_LN1 : hb_fresh E_LN1 = true. Proof. vmr. Qed.

Definition S0_LN1_0 : axst := Eval vm_compute in (S0_hb E_LN1 0).
Definition lPA_LN1_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN1_0).
Definition LA_LN1_0 : axst := Eval vm_compute in (leaf 0 lPA_LN1_0).
Definition SC_LN1_0 : axst := Eval vm_compute in (SC_hb LA_LN1_0).
Definition lPL_LN1_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN1_0).
Definition FAM_LN1_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN1_0_ok : hbfam_ok Erc_LN1 0 FAM_LN1_0.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_LN1_0L : axst := Eval vm_compute in (SX_hb SC_LN1_0 0 true).
Definition lPB_LN1_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN1_0L).
Definition E5_LN1_0L : axst := Eval vm_compute in (leaf 0 lPB_LN1_0L).
Definition C5_LN1_0L : axst := Eval vm_compute in (C5_hb E5_LN1_0L).
Definition R5_LN1_0L : list sobj := Eval vm_compute in (R5_hb C5_LN1_0L).
Definition T5_LN1_0L : axst := Eval vm_compute in (T5_hb C5_LN1_0L).
Definition T5f_LN1_0L : axst := Eval vm_compute in (T5f_hb C5_LN1_0L).
Definition lPC_LN1_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN1_0L).
Definition EUs_LN1_0L : axst := Eval vm_compute in (leaf 0 lPC_LN1_0L).
Definition EM_LN1_0L : axst := Eval vm_compute in (leaf 1 lPC_LN1_0L).
Definition EMx_LN1_0L : axst := Eval vm_compute in (selX EM_LN1_0L [O_csh vH vMS]).
Definition EMd_LN1_0L : axst := Eval vm_compute in (EMd_hb EM_LN1_0L).
Definition AM_LN1_0L : axst := Eval vm_compute in (A_after EMd_LN1_0L (SLit 0)).
Definition lPD_LN1_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN1_0L).
Definition EU_LN1_0L : axst := Eval vm_compute in (leaf 0 lPD_LN1_0L).
Definition EUx_LN1_0L : axst := Eval vm_compute in (selX EU_LN1_0L (D_U_hb true)).
Definition EUd_LN1_0L : axst := Eval vm_compute in (EUd_hb EU_LN1_0L true).
Definition DUo_LN1_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN1_0L))) (ss_objs (ax_S EUx_LN1_0L))).
Definition AU_LN1_0L : axst := Eval vm_compute in (A_after EUd_LN1_0L (SLit 0)).
Definition lPE_LN1_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN1_0L).
Definition LR_LN1_0L : axst := Eval vm_compute in (leaf 0 lPE_LN1_0L).
Definition PT_LN1_0L : axst := Eval vm_compute in (PT_hb LR_LN1_0L).
Definition lPT_LN1_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN1_0L).
Definition XF_LN1_0L : axst := Eval vm_compute in (leaf 0 lPT_LN1_0L).
Definition VAR_LN1_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN1_0L_ok : hbvar_ok SC_LN1_0 0 true VAR_LN1_0L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_LN1_0M : axst := Eval vm_compute in (SX_hb SC_LN1_0 0 false).
Definition lPB_LN1_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN1_0M).
Definition E5_LN1_0M : axst := Eval vm_compute in (leaf 0 lPB_LN1_0M).
Definition C5_LN1_0M : axst := Eval vm_compute in (C5_hb E5_LN1_0M).
Definition R5_LN1_0M : list sobj := Eval vm_compute in (R5_hb C5_LN1_0M).
Definition T5_LN1_0M : axst := Eval vm_compute in (T5_hb C5_LN1_0M).
Definition T5f_LN1_0M : axst := Eval vm_compute in (T5f_hb C5_LN1_0M).
Definition lPC_LN1_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN1_0M).
Definition EUs_LN1_0M : axst := Eval vm_compute in (leaf 0 lPC_LN1_0M).
Definition EM_LN1_0M : axst := Eval vm_compute in (leaf 1 lPC_LN1_0M).
Definition EMx_LN1_0M : axst := Eval vm_compute in (selX EM_LN1_0M [O_csh vH vMS]).
Definition EMd_LN1_0M : axst := Eval vm_compute in (EMd_hb EM_LN1_0M).
Definition AM_LN1_0M : axst := Eval vm_compute in (A_after EMd_LN1_0M (SLit 0)).
Definition lPD_LN1_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN1_0M).
Definition EU_LN1_0M : axst := Eval vm_compute in (leaf 0 lPD_LN1_0M).
Definition EUx_LN1_0M : axst := Eval vm_compute in (selX EU_LN1_0M (D_U_hb false)).
Definition EUd_LN1_0M : axst := Eval vm_compute in (EUd_hb EU_LN1_0M false).
Definition DUo_LN1_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN1_0M))) (ss_objs (ax_S EUx_LN1_0M))).
Definition AU_LN1_0M : axst := Eval vm_compute in (A_after EUd_LN1_0M (SLit 0)).
Definition lPE_LN1_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN1_0M).
Definition LR_LN1_0M : axst := Eval vm_compute in (leaf 0 lPE_LN1_0M).
Definition PT_LN1_0M : axst := Eval vm_compute in (PT_hb LR_LN1_0M).
Definition lPT_LN1_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN1_0M).
Definition XF_LN1_0M : axst := Eval vm_compute in (leaf 0 lPT_LN1_0M).
Definition VAR_LN1_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN1_0M_ok : hbvar_ok SC_LN1_0 0 false VAR_LN1_0M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbLN1.

(* [comment removed for export] *)
Module F0T_hbNT.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0T_hbNT"; "AM_N0_1L"; "AM_N0_1M"; "AM_N0_2L"; "AM_N0_2M"; "AU_N0_1L"; "AU_N0_1M"; "AU_N0_2L"; "AU_N0_2M"; "C5_N0_1L"; "C5_N0_1M"; "C5_N0_2L"; "C5_N0_2M"; "DUo_N0_1L"; "DUo_N0_1M"; "DUo_N0_2L"; "DUo_N0_2M"; "E5_N0_1L"; "E5_N0_1M"; "E5_N0_2L"; "E5_N0_2M"; "EM_N0_1L"; "EM_N0_1M"; "EM_N0_2L"; "EM_N0_2M"; "EMd_N0_1L"; "EMd_N0_1M"; "EMd_N0_2L"; "EMd_N0_2M"; "EMx_N0_1L"; "EMx_N0_1M"; "EMx_N0_2L"; "EMx_N0_2M"; "EU_N0_1L"; "EU_N0_1M"; "EU_N0_2L"; "EU_N0_2M"; "EUd_N0_1L"; "EUd_N0_1M"; "EUd_N0_2L"; "EUd_N0_2M"; "EUs_N0_1L"; "EUs_N0_1M"; "EUs_N0_2L"; "EUs_N0_2M"; "EUx_N0_1L"; "EUx_N0_1M"; "EUx_N0_2L"; "EUx_N0_2M"; "LA_N0_1"; "LA_N0_2"; "LR_N0_1L"; "LR_N0_1M"; "LR_N0_2L"; "LR_N0_2M"; "PT_N0_1L"; "PT_N0_1M"; "PT_N0_2L"; "PT_N0_2M"; "R5_N0_1L"; "R5_N0_1M"; "R5_N0_2L"; "R5_N0_2M"; "S0_N0_1"; "S0_N0_2"; "SC_N0_1"; "SC_N0_2"; "SX_N0_1L"; "SX_N0_1M"; "SX_N0_2L"; "SX_N0_2M"; "T5_N0_1L"; "T5_N0_1M"; "T5_N0_2L"; "T5_N0_2M"; "T5f_N0_1L"; "T5f_N0_1M"; "T5f_N0_2L"; "T5f_N0_2M"; "XF_N0_1L"; "XF_N0_1M"; "XF_N0_2L"; "XF_N0_2M"; "lPA_N0_1"; "lPA_N0_2"; "lPB_N0_1L"; "lPB_N0_1M"; "lPB_N0_2L"; "lPB_N0_2M"; "lPC_N0_1L"; "lPC_N0_1M"; "lPC_N0_2L"; "lPC_N0_2M"; "lPD_N0_1L"; "lPD_N0_1M"; "lPD_N0_2L"; "lPD_N0_2M"; "lPE_N0_1L"; "lPE_N0_1M"; "lPE_N0_2L"; "lPE_N0_2M"; "lPL_N0_1"; "lPL_N0_2"; "lPT_N0_1L"; "lPT_N0_1M"; "lPT_N0_2L"; "lPT_N0_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_NT : axst := Eval vm_compute in Erc_NT.
Lemma FRESH_NT : hb_fresh E_NT = true. Proof. vmr. Qed.

Definition S0_N0_1 : axst := Eval vm_compute in (S0_hb E_NT 1).
Definition lPA_N0_1 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N0_1).
Definition LA_N0_1 : axst := Eval vm_compute in (leaf 0 lPA_N0_1).
Definition SC_N0_1 : axst := Eval vm_compute in (SC_hb LA_N0_1).
Definition lPL_N0_1 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N0_1).
Definition FAM_N0_1 : hbfam := ltac2:(tb__ "0|0|
S1S40S54S32S42S66A5").
Lemma FAM_N0_1_ok : hbfam_ok Erc_NT 1 FAM_N0_1.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N0_1L : axst := Eval vm_compute in (SX_hb SC_N0_1 1 true).
Definition lPB_N0_1L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_1L).
Definition E5_N0_1L : axst := Eval vm_compute in (leaf 0 lPB_N0_1L).
Definition C5_N0_1L : axst := Eval vm_compute in (C5_hb E5_N0_1L).
Definition R5_N0_1L : list sobj := Eval vm_compute in (R5_hb C5_N0_1L).
Definition T5_N0_1L : axst := Eval vm_compute in (T5_hb C5_N0_1L).
Definition T5f_N0_1L : axst := Eval vm_compute in (T5f_hb C5_N0_1L).
Definition lPC_N0_1L : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_1L).
Definition EUs_N0_1L : axst := Eval vm_compute in (leaf 0 lPC_N0_1L).
Definition EM_N0_1L : axst := Eval vm_compute in (leaf 1 lPC_N0_1L).
Definition EMx_N0_1L : axst := Eval vm_compute in (selX EM_N0_1L [O_csh vH vMS]).
Definition EMd_N0_1L : axst := Eval vm_compute in (EMd_hb EM_N0_1L).
Definition AM_N0_1L : axst := Eval vm_compute in (A_after EMd_N0_1L (SLit 0)).
Definition lPD_N0_1L : list leafA := Eval vm_compute in (runA 900 [] AM_N0_1L).
Definition EU_N0_1L : axst := Eval vm_compute in (leaf 0 lPD_N0_1L).
Definition EUx_N0_1L : axst := Eval vm_compute in (selX EU_N0_1L (D_U_hb true)).
Definition EUd_N0_1L : axst := Eval vm_compute in (EUd_hb EU_N0_1L true).
Definition DUo_N0_1L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_1L))) (ss_objs (ax_S EUx_N0_1L))).
Definition AU_N0_1L : axst := Eval vm_compute in (A_after EUd_N0_1L (SLit 0)).
Definition lPE_N0_1L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_1L).
Definition LR_N0_1L : axst := Eval vm_compute in (leaf 0 lPE_N0_1L).
Definition PT_N0_1L : axst := Eval vm_compute in (PT_hb LR_N0_1L).
Definition lPT_N0_1L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_1L).
Definition XF_N0_1L : axst := Eval vm_compute in (leaf 0 lPT_N0_1L).
Definition VAR_N0_1L : hbvar := ltac2:(tb__ "0|0|
S0S44S56S12SaS3cS48S4cS5aS2aS16S1eS1aS2S5eS22S2eS26SeS6S62S34S38S68S50A18").
Lemma VAR_N0_1L_ok : hbvar_ok SC_N0_1 1 true VAR_N0_1L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N0_1M : axst := Eval vm_compute in (SX_hb SC_N0_1 1 false).
Definition lPB_N0_1M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_1M).
Definition E5_N0_1M : axst := Eval vm_compute in (leaf 0 lPB_N0_1M).
Definition C5_N0_1M : axst := Eval vm_compute in (C5_hb E5_N0_1M).
Definition R5_N0_1M : list sobj := Eval vm_compute in (R5_hb C5_N0_1M).
Definition T5_N0_1M : axst := Eval vm_compute in (T5_hb C5_N0_1M).
Definition T5f_N0_1M : axst := Eval vm_compute in (T5f_hb C5_N0_1M).
Definition lPC_N0_1M : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_1M).
Definition EUs_N0_1M : axst := Eval vm_compute in (leaf 0 lPC_N0_1M).
Definition EM_N0_1M : axst := Eval vm_compute in (leaf 1 lPC_N0_1M).
Definition EMx_N0_1M : axst := Eval vm_compute in (selX EM_N0_1M [O_csh vH vMS]).
Definition EMd_N0_1M : axst := Eval vm_compute in (EMd_hb EM_N0_1M).
Definition AM_N0_1M : axst := Eval vm_compute in (A_after EMd_N0_1M (SLit 0)).
Definition lPD_N0_1M : list leafA := Eval vm_compute in (runA 900 [] AM_N0_1M).
Definition EU_N0_1M : axst := Eval vm_compute in (leaf 0 lPD_N0_1M).
Definition EUx_N0_1M : axst := Eval vm_compute in (selX EU_N0_1M (D_U_hb false)).
Definition EUd_N0_1M : axst := Eval vm_compute in (EUd_hb EU_N0_1M false).
Definition DUo_N0_1M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_1M))) (ss_objs (ax_S EUx_N0_1M))).
Definition AU_N0_1M : axst := Eval vm_compute in (A_after EUd_N0_1M (SLit 0)).
Definition lPE_N0_1M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_1M).
Definition LR_N0_1M : axst := Eval vm_compute in (leaf 0 lPE_N0_1M).
Definition PT_N0_1M : axst := Eval vm_compute in (PT_hb LR_N0_1M).
Definition lPT_N0_1M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_1M).
Definition XF_N0_1M : axst := Eval vm_compute in (leaf 0 lPT_N0_1M).
Definition VAR_N0_1M : hbvar := ltac2:(tb__ "0|0|
S0S45S57S13SbS3dS49S4dS5bS2bS17S1fS1bS3S5fS23S2fS27SfS7S63S35S39S69S51A18").
Lemma VAR_N0_1M_ok : hbvar_ok SC_N0_1 1 false VAR_N0_1M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition S0_N0_2 : axst := Eval vm_compute in (S0_hb E_NT 2).
Definition lPA_N0_2 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N0_2).
Definition LA_N0_2 : axst := Eval vm_compute in (leaf 0 lPA_N0_2).
Definition SC_N0_2 : axst := Eval vm_compute in (SC_hb LA_N0_2).
Definition lPL_N0_2 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N0_2).
Definition FAM_N0_2 : hbfam := ltac2:(tb__ "0|0|
S1S41S55S33S43S67A5").
Lemma FAM_N0_2_ok : hbfam_ok Erc_NT 2 FAM_N0_2.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N0_2L : axst := Eval vm_compute in (SX_hb SC_N0_2 2 true).
Definition lPB_N0_2L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_2L).
Definition E5_N0_2L : axst := Eval vm_compute in (leaf 0 lPB_N0_2L).
Definition C5_N0_2L : axst := Eval vm_compute in (C5_hb E5_N0_2L).
Definition R5_N0_2L : list sobj := Eval vm_compute in (R5_hb C5_N0_2L).
Definition T5_N0_2L : axst := Eval vm_compute in (T5_hb C5_N0_2L).
Definition T5f_N0_2L : axst := Eval vm_compute in (T5f_hb C5_N0_2L).
Definition lPC_N0_2L : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_2L).
Definition EUs_N0_2L : axst := Eval vm_compute in (leaf 0 lPC_N0_2L).
Definition EM_N0_2L : axst := Eval vm_compute in (leaf 1 lPC_N0_2L).
Definition EMx_N0_2L : axst := Eval vm_compute in (selX EM_N0_2L [O_csh vH vMS]).
Definition EMd_N0_2L : axst := Eval vm_compute in (EMd_hb EM_N0_2L).
Definition AM_N0_2L : axst := Eval vm_compute in (A_after EMd_N0_2L (SLit 0)).
Definition lPD_N0_2L : list leafA := Eval vm_compute in (runA 900 [] AM_N0_2L).
Definition EU_N0_2L : axst := Eval vm_compute in (leaf 0 lPD_N0_2L).
Definition EUx_N0_2L : axst := Eval vm_compute in (selX EU_N0_2L (D_U_hb true)).
Definition EUd_N0_2L : axst := Eval vm_compute in (EUd_hb EU_N0_2L true).
Definition DUo_N0_2L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_2L))) (ss_objs (ax_S EUx_N0_2L))).
Definition AU_N0_2L : axst := Eval vm_compute in (A_after EUd_N0_2L (SLit 0)).
Definition lPE_N0_2L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_2L).
Definition LR_N0_2L : axst := Eval vm_compute in (leaf 0 lPE_N0_2L).
Definition PT_N0_2L : axst := Eval vm_compute in (PT_hb LR_N0_2L).
Definition lPT_N0_2L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_2L).
Definition XF_N0_2L : axst := Eval vm_compute in (leaf 0 lPT_N0_2L).
Definition VAR_N0_2L : hbvar := ltac2:(tb__ "0|0|
S0S46S58S14ScS3eS4aS4eS5cS2cS18S20S1cS4S60S24S30S28S10S8S64S36S3aS6aS52A18").
Lemma VAR_N0_2L_ok : hbvar_ok SC_N0_2 2 true VAR_N0_2L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N0_2M : axst := Eval vm_compute in (SX_hb SC_N0_2 2 false).
Definition lPB_N0_2M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_2M).
Definition E5_N0_2M : axst := Eval vm_compute in (leaf 0 lPB_N0_2M).
Definition C5_N0_2M : axst := Eval vm_compute in (C5_hb E5_N0_2M).
Definition R5_N0_2M : list sobj := Eval vm_compute in (R5_hb C5_N0_2M).
Definition T5_N0_2M : axst := Eval vm_compute in (T5_hb C5_N0_2M).
Definition T5f_N0_2M : axst := Eval vm_compute in (T5f_hb C5_N0_2M).
Definition lPC_N0_2M : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_2M).
Definition EUs_N0_2M : axst := Eval vm_compute in (leaf 0 lPC_N0_2M).
Definition EM_N0_2M : axst := Eval vm_compute in (leaf 1 lPC_N0_2M).
Definition EMx_N0_2M : axst := Eval vm_compute in (selX EM_N0_2M [O_csh vH vMS]).
Definition EMd_N0_2M : axst := Eval vm_compute in (EMd_hb EM_N0_2M).
Definition AM_N0_2M : axst := Eval vm_compute in (A_after EMd_N0_2M (SLit 0)).
Definition lPD_N0_2M : list leafA := Eval vm_compute in (runA 900 [] AM_N0_2M).
Definition EU_N0_2M : axst := Eval vm_compute in (leaf 0 lPD_N0_2M).
Definition EUx_N0_2M : axst := Eval vm_compute in (selX EU_N0_2M (D_U_hb false)).
Definition EUd_N0_2M : axst := Eval vm_compute in (EUd_hb EU_N0_2M false).
Definition DUo_N0_2M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_2M))) (ss_objs (ax_S EUx_N0_2M))).
Definition AU_N0_2M : axst := Eval vm_compute in (A_after EUd_N0_2M (SLit 0)).
Definition lPE_N0_2M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_2M).
Definition LR_N0_2M : axst := Eval vm_compute in (leaf 0 lPE_N0_2M).
Definition PT_N0_2M : axst := Eval vm_compute in (PT_hb LR_N0_2M).
Definition lPT_N0_2M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_2M).
Definition XF_N0_2M : axst := Eval vm_compute in (leaf 0 lPT_N0_2M).
Definition VAR_N0_2M : hbvar := ltac2:(tb__ "0|0|
S0S47S59S15SdS3fS4bS4fS5dS2dS19S21S1dS5S61S25S31S29S11S9S65S37S3bS6bS53A18").
Lemma VAR_N0_2M_ok : hbvar_ok SC_N0_2 2 false VAR_N0_2M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0T_hbNT.

(* [comment removed for export] *)
Module F0A_hbN_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "eval"; "sobj"; "agree_below"; "obj_range"; "ranges_disjoint"; "rm"; "ss_next"; "ss_objs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbN_skel.Skel"; "JH1"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "true"; "bool"; "prod"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbN_skel"; "KEEPXh"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "modulo"; "pow"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "VSXh"; "hv_C5"; "hv_EMd"; "hv_EUd"; "VS0h"; "hbfam_ok"; "hbvar_ok"; "hf_LA"; "hf_S0"; "hf_SC"; "hv_E5"; "hv_EMx"; "hv_EUs"; "hv_EUx"; "hv_LR"; "hv_PT"; "hv_SX"; "hv_XF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "TASK_SIZE"; "event"; "map_has"; "map_remove"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "keepsM"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vMS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "ELEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11.
Import ListNotations.
Open Scope Z_scope.

Definition KEEPXh (rS r : valuation) : Prop := ltac2:(tb__ "0|0|
S1eS27S1eR1S28A3ScS13Q40A1S1Vr;R2A2S1VrS;R2A2A3F_;Fv;").

Section Skel.
Context {Q : assn} (X : trk Q).
Variable nW : nat.
Variables (A' : AA) (Kc : KcA) (rho1' : valuation).
Variables (ch : sec_chunk) (f : nat) (l : bool).
Variable TZ : Z -> Prop.
Variables (E : axst) (cf : hbfam) (cv : hbvar).
Hypothesis FOK : ltac2:(tb__ "0|0|
S2dVE;Vf;Vcf;A3").
Hypothesis VOK : ltac2:(tb__ "0|0|
S2eS31Vcf;A1Vf;Vl;Vcv;A4").
Definition JH1 : jpredA := ltac2:(tb__ "0|0|
S56S10S5bVch;A1VTZ;S57VnW;S58S1bVA';VKc;Vrho1';A6A4").
Variables (JP JH2 : jpredA).
Hypothesis HJ1 : JOK X JH1.
Hypothesis HJP : JOK X JP.
Hypothesis HJ2 : JOK X JH2.
Variables (ENV0 ENVX : valuation -> Prop).
Hypothesis ENV0_keep : ltac2:(tb__ "0|0|
S0S0VENV0;R2A1S49S48S2cA1R3R2A3VENV0;R3A1F_;F_;Fr';Fr;").
Hypothesis ENVX_keep : ltac2:(tb__ "0|0|
S0S0VENVX;R2A1S21R3R2A2VENVX;R3A1F_;F_;Fr';Fr;").
Variables (nlitM nlitU : Z).
Variables (rhoE : valuation) (tpE : list word).

Hypothesis G_entry : ltac2:(tb__ "0|0|
S20S11S10S12VE;VrhoE;VtpE;R1A6SdS0S0SbS11S10S12S30Vcf;A1R1VtpE;R3A6VENV0;R1A1A2Lr2;A2F_;Fw;").
Hypothesis G_scan : ltac2:(tb__ "0|0|
S16S13Q40A1A1S0VENVX;R1A1S3aVQ;VX;S11S10S12S38Vcv;A1R2R3A5A3F_;Fr4;S0VENV0;R1A1S3aVQ;VX;S11S10S12S2fVcf;A1R2R4A5A3F_;Fr;F_;Ftp;").
Hypothesis G_c5 : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10S12S32Vcv;A1R4R3R2A6S11S10S12S29Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Hypothesis G_eus : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10S12S34Vcv;A1R4R3R2A6SeF_;F_;Fw;Ftp;Fr;").
Hypothesis G_shd : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1S20VENVX;R3A1S11S10S12S33Vcv;A1R4R3R2A6SdS0S0SbS11S10S12S2aVcv;A1R1R5R4A6S1eScG0S1R2R1A2S1R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Hypothesis G_madv_num : ltac2:(tb__ "0|1|
S0VENVX;R1A1SbScS1fS14Q40S3R2S5aA2A2VnlitM;A3SbScS1fS25VnlitM;Z1000A2Z0M0A3SbS22G0VnlitM;A2S22VnlitM;S26Z2Z3eA2A2A2A2A2F_;Fr;").
Hypothesis G_madv_pre : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1VENVX;R2A1S53S10S12S12S2aVcv;A1R3R2G0S18L_;VnlitM;A8F_;Ftp;Fr;").
Hypothesis G_du : ltac2:(tb__ "0|1|
S0S16S13Q40A1M0A1S20VENVX;R3A1S11S10S12S35Vcv;A1R4R3R2A6SdS0S0SbS11S10VJP;S2bVcv;A1R1R5R4A6S1eScG0S1R2R1A2S1R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Hypothesis G_mun_num : ltac2:(tb__ "0|2|
S0VENVX;R1A1SbScS13Q40M0A1S3R2S59A2S15G0VnlitU;A2A3SbScS1fS25VnlitU;Z1000A2Z0M1A3SbS22G1VnlitU;A2S22VnlitU;S26Z2Z3eA2A2A2A2A2F_;Fr;").
Hypothesis G_mun_pre : ltac2:(tb__ "0|d|
S0S16S13Q40M0A1M1A1VENVX;R2A1S16S3fA1M2S4cS3dS55S10R6R5S2bVcv;A1M3S17G2S4eR3S4fR2R1A2A4A5VJP;R7R6R4R2A4S4dR4U0A2G1SbScS1fS25S14G0R1A2M4S42A2Z0A3SbS24S23G4VnlitU;A2M5S3eA2SbScS19S40S3cS3bR4A1A1M6R1S15G0VnlitU;A2M7A3S18A3SbG1S27S1aG1G1A2S17G1G1R2R1A4S3cS3bR5A1A1A3ScG1R2G7A3F_;Fs;SbScS19S43S41G6R1A2R1G7A3S18A3SbS4S27S4R1SaS44G3A1A1A3S7S6RbR2A2S17S1fS1fS14G0R3A2M8S23G8VnlitU;A2A4A2F_;Fo;SbS1aS2S2A2M9S1fS27G9R2S45G3A1A3SbS24S14G0S3RcS1cS2S2R3A3A2A2MaR2A2S22R2S23GaS14G0S3RcS1dS2S2R3A3A2A2A2A2A2SfSbS24S14G0R5A2MbS14G0S47S14G0S3RdS46G3A1A2A2R3A2A2McA2S22GcS23GbVnlitU;A2A2A2A1F_;F_;Fy;Frr;VJH2;S52R9S51S8R9A1R1G7A3A2S54G4G5R8A3R6S50R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;Ftp;Fr;").
Hypothesis G_qsz : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10VJH2;S36Vcv;A1R4R3R2A6S11S10VJH2;S37Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Hypothesis G_exit : ltac2:(tb__ "0|0|
S0S16S13Q40A1A1S20VENVX;R3A1S11S10VJH2;S39Vcv;A1R4R3R2A6VQ;R3A1F_;F_;Fw;Ftp;Fr;").

Lemma KEEPXh_refl : ltac2:(tb__ "0|0|
S0S21R1R1A2Fr;"). Proof. intros r v _. reflexivity. Qed.
Lemma KEEPXh_trans : ltac2:(tb__ "0|1|
S0S0S0S21R3R2A2M0G0S21R5R3A2F_;F_;Fr3;Fr2;Fr1;"). Proof. intros r1 r2 r3 H1 H2 v Hv. rewrite (H2 v Hv). exact (H1 v Hv). Qed.
Lemma KEEPXh_keepsM : ltac2:(tb__ "0|0|
S0S0S49S48S28A1R2R1A3S21R3R2A2F_;Fr';Fr;").
Proof. intros r r' [_ HM] v Hv. apply (HM v (SVar v)). unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. Qed.
Lemma VSXh_lt : ltac2:(tb__ "0|0|
S1eS27S1eR1S28A3S4bR2PcfA2F_;Fv;").
Proof. intros v Hv. unfold VSXh, VS0h in Hv. cbn in Hv. repeat (destruct Hv as [<-|Hv]; [reflexivity|]). destruct Hv. Qed.
Lemma KEEPXh_agree : ltac2:(tb__ "0|0|
S1eS0S0S5R3R2R1A3S4aPcfR4A2S21R4R3A2F_;F_;Fr';Fr;Fk;").
Proof. intros k r r' (Hw & _) Hk v Hv. symmetry. apply Hw. pose proof (VSXh_lt v Hv). lia. Qed.
Lemma KEEPXh_same : ltac2:(tb__ "0|0|
S0S0S1eScS13Q40A1S1R2R1A2S1R3R1A2A3Fv;S21R3R2A2F_;Fr';Fr;"). Proof. intros r r' H v _. apply H. Qed.
Hypothesis C5_next207 : ltac2:(tb__ "0|0|
S4aPcfS9S44S29Vcv;A1A1A1A2").

Theorem hb_skeleton : ltac2:(tb__ "0|0|
S3aVQ;VX;S11S10S12VE;VrhoE;VtpE;A5A3").
Proof.
  apply (tr_glue X _ JH1 (hf_S0 cf) tpE ENV0 G_entry). intros r2 EN2.
  apply (seg_PA X E f cf FOK JH1 r2 tpE HJ1). intros r3 K3.
  apply (G_scan tpE); [|exact (ENV0_keep r2 r3 EN2 K3)]. intros rS ENS.

  apply (seg_PB X _ f l cv VOK JH1 rS tpE HJ1). intros r1 K1. pose proof (ENVX_keep _ _ ENS (KEEPXh_keepsM _ _ K1)) as EN1.
  apply (tr_conseq X _ (SPA segsA JH1 (hv_C5 cv) r1 tpE)); [intros w Hw; exact (G_c5 r1 tpE w EN1 Hw)|].
  apply (seg_memset X _ f l cv VOK JH1 r1 tpE HJ1). intros r2' Hag. pose proof (ENVX_keep _ _ EN1 (KEEPXh_agree _ _ _ Hag C5_next207)) as EN2'.
  apply (seg_PC X _ f l cv VOK JH1 r2' tpE HJ1).
  { intros r3' K3'. apply (tr_pure X _ False); [|intros []]. intros w Hw. exact (G_eus r3' tpE w (ENVX_keep _ _ EN2' (KEEPXh_keepsM _ _ K3')) Hw). }
  intros r3' K3'. pose proof (ENVX_keep _ _ EN2' (KEEPXh_keepsM _ _ K3')) as EN3'.

  apply (tr_conseq X _ (SPA segsA JH1 (hv_EMx cv) r3' tpE)); [intros w Hw; exact (SPA_axforms segsA JH1 _ r3' _ _ tpE w (v_EMx _ f l cv VOK) Hw)|].
  apply (tr_glue X _ JH1 (hv_EMd cv) tpE ENVX).
  { intros w Hw. destruct (G_shd r3' tpE w EN3' Hw) as (r4 & H4 & RW4). exists r4. split; [exact H4 | exact (ENVX_keep _ _ EN3' (KEEPXh_same _ _ RW4))]. }
  intros r4 EN4. destruct (G_madv_num r4 EN4) as (NM1 & NM2 & NM3).
  pose proof (v_EMdnode _ f l cv VOK) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). apply Pos.leb_le in N7.
  apply (tr_madvise X JH1 JH1 (hv_EMd cv) r4 tpE (fun _ => true) EBEG ELEN nlitM HJ1 N7 N1 N2 N3 N4 NM1 NM2 NM3 N5 (G_madv_pre r4 tpE EN4)).
  unfold madvise_post. rewrite (v_AM _ f l cv VOK). set (r5 := set_rm r4 _). set (tp5 := tp_dontneed _ _ _ tpE).
  assert (EN5 : ENVX r5) by (apply (ENVX_keep _ _ EN4); apply KEEPXh_same; intros v; reflexivity).
  apply (seg_PD X _ f l cv VOK JH1 r5 tp5 HJ1). intros r6 K6. pose proof (ENVX_keep _ _ EN5 (KEEPXh_keepsM _ _ K6)) as EN6.

  apply (tr_conseq X _ (SPA segsA JH1 (hv_EUx cv) r6 tp5)); [intros w Hw; exact (SPA_axforms segsA JH1 _ r6 _ _ tp5 w (v_EUx _ f l cv VOK) Hw)|].
  apply (tr_glue X _ JP (hv_EUd cv) tp5 ENVX).
  { intros w Hw. destruct (G_du r6 tp5 w EN6 Hw) as (r7 & H7 & RW7). exists r7. split; [exact H7 | exact (ENVX_keep _ _ EN6 (KEEPXh_same _ _ RW7))]. }
  intros r7 EN7. destruct (G_mun_num r7 EN7) as (NU1 & NU2 & NU3).
  pose proof (v_EUdnode _ f l cv VOK) as (U1 & U2 & U3 & U4 & U5 & U6). apply Pos.leb_le in U6.
  apply (tr_munmap X JP JH2 (hv_EUd cv) r7 tp5 vH vMS nlitU HJP U6 U1 U2 U3 U4 NU1 NU2 NU3 (G_mun_pre r7 tp5 EN7)).
  rewrite (v_AU _ f l cv VOK). set (r8 := set_rm r7 _). set (tp8 := tp_forget _ _ tp5).
  assert (EN8 : ENVX r8) by (apply (ENVX_keep _ _ EN7); apply KEEPXh_same; intros v; reflexivity).

  apply (seg_PE X _ f l cv VOK JH2 r8 tp8 HJ2). intros r9 K9. pose proof (ENVX_keep _ _ EN8 (KEEPXh_keepsM _ _ K9)) as EN9.
  apply (tr_conseq X _ (SPA segsA JH2 (hv_PT cv) r9 tp8)); [intros w Hw; exact (G_qsz r9 tp8 w EN9 Hw)|].
  apply (seg_PT X _ f l cv VOK JH2 r9 tp8 HJ2). intros r10 K10.
  apply (tr_done X). intros w Hw. exact (G_exit r10 tp8 w (ENVX_keep _ _ EN9 (KEEPXh_keepsM _ _ K10)) Hw).
Qed.
End Skel.
End F0A_hbN_skel.

(* [comment removed for export] *)
Module F0A_hbN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbN0"; "AM_N0_1L"; "AM_N0_1M"; "AM_N0_2L"; "AM_N0_2M"; "AU_N0_1L"; "AU_N0_1M"; "AU_N0_2L"; "AU_N0_2M"; "C5_N0_1L"; "C5_N0_1M"; "C5_N0_2L"; "C5_N0_2M"; "DUo_N0_1L"; "DUo_N0_1M"; "DUo_N0_2L"; "DUo_N0_2M"; "E5_N0_1L"; "E5_N0_1M"; "E5_N0_2L"; "E5_N0_2M"; "EM_N0_1L"; "EM_N0_1M"; "EM_N0_2L"; "EM_N0_2M"; "EMd_N0_1L"; "EMd_N0_1M"; "EMd_N0_2L"; "EMd_N0_2M"; "EMx_N0_1L"; "EMx_N0_1M"; "EMx_N0_2L"; "EMx_N0_2M"; "EU_N0_1L"; "EU_N0_1M"; "EU_N0_2L"; "EU_N0_2M"; "EUd_N0_1L"; "EUd_N0_1M"; "EUd_N0_2L"; "EUd_N0_2M"; "EUs_N0_1L"; "EUs_N0_1M"; "EUs_N0_2L"; "EUs_N0_2M"; "EUx_N0_1L"; "EUx_N0_1M"; "EUx_N0_2L"; "EUx_N0_2M"; "LA_N0_1"; "LA_N0_2"; "LR_N0_1L"; "LR_N0_1M"; "LR_N0_2L"; "LR_N0_2M"; "PT_N0_1L"; "PT_N0_1M"; "PT_N0_2L"; "PT_N0_2M"; "R5_N0_1L"; "R5_N0_1M"; "R5_N0_2L"; "R5_N0_2M"; "S0_N0_1"; "S0_N0_2"; "SC_N0_1"; "SC_N0_2"; "SX_N0_1L"; "SX_N0_1M"; "SX_N0_2L"; "SX_N0_2M"; "T5_N0_1L"; "T5_N0_1M"; "T5_N0_2L"; "T5_N0_2M"; "T5f_N0_1L"; "T5f_N0_1M"; "T5f_N0_2L"; "T5f_N0_2M"; "XF_N0_1L"; "XF_N0_1M"; "XF_N0_2L"; "XF_N0_2M"; "lPA_N0_1"; "lPA_N0_2"; "lPB_N0_1L"; "lPB_N0_1M"; "lPB_N0_2L"; "lPB_N0_2M"; "lPC_N0_1L"; "lPC_N0_1M"; "lPC_N0_2L"; "lPC_N0_2M"; "lPD_N0_1L"; "lPD_N0_1M"; "lPD_N0_2L"; "lPD_N0_2M"; "lPE_N0_1L"; "lPE_N0_1M"; "lPE_N0_2L"; "lPE_N0_2M"; "lPL_N0_1"; "lPL_N0_2"; "lPT_N0_1L"; "lPT_N0_1M"; "lPT_N0_2L"; "lPT_N0_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_N0 : axst := Eval vm_compute in Erc_N0.
Lemma FRESH_N0 : hb_fresh E_N0 = true. Proof. vmr. Qed.

Definition S0_N0_1 : axst := Eval vm_compute in (S0_hb E_N0 1).
Definition lPA_N0_1 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N0_1).
Definition LA_N0_1 : axst := Eval vm_compute in (leaf 0 lPA_N0_1).
Definition SC_N0_1 : axst := Eval vm_compute in (SC_hb LA_N0_1).
Definition lPL_N0_1 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N0_1).
Definition FAM_N0_1 : hbfam := ltac2:(tb__ "0|0|
S1S40S54S32S42S66A5").
Lemma FAM_N0_1_ok : hbfam_ok Erc_N0 1 FAM_N0_1.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N0_1L : axst := Eval vm_compute in (SX_hb SC_N0_1 1 true).
Definition lPB_N0_1L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_1L).
Definition E5_N0_1L : axst := Eval vm_compute in (leaf 0 lPB_N0_1L).
Definition C5_N0_1L : axst := Eval vm_compute in (C5_hb E5_N0_1L).
Definition R5_N0_1L : list sobj := Eval vm_compute in (R5_hb C5_N0_1L).
Definition T5_N0_1L : axst := Eval vm_compute in (T5_hb C5_N0_1L).
Definition T5f_N0_1L : axst := Eval vm_compute in (T5f_hb C5_N0_1L).
Definition lPC_N0_1L : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_1L).
Definition EUs_N0_1L : axst := Eval vm_compute in (leaf 0 lPC_N0_1L).
Definition EM_N0_1L : axst := Eval vm_compute in (leaf 1 lPC_N0_1L).
Definition EMx_N0_1L : axst := Eval vm_compute in (selX EM_N0_1L [O_csh vH vMS]).
Definition EMd_N0_1L : axst := Eval vm_compute in (EMd_hb EM_N0_1L).
Definition AM_N0_1L : axst := Eval vm_compute in (A_after EMd_N0_1L (SLit 0)).
Definition lPD_N0_1L : list leafA := Eval vm_compute in (runA 900 [] AM_N0_1L).
Definition EU_N0_1L : axst := Eval vm_compute in (leaf 0 lPD_N0_1L).
Definition EUx_N0_1L : axst := Eval vm_compute in (selX EU_N0_1L (D_U_hb true)).
Definition EUd_N0_1L : axst := Eval vm_compute in (EUd_hb EU_N0_1L true).
Definition DUo_N0_1L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_1L))) (ss_objs (ax_S EUx_N0_1L))).
Definition AU_N0_1L : axst := Eval vm_compute in (A_after EUd_N0_1L (SLit 0)).
Definition lPE_N0_1L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_1L).
Definition LR_N0_1L : axst := Eval vm_compute in (leaf 0 lPE_N0_1L).
Definition PT_N0_1L : axst := Eval vm_compute in (PT_hb LR_N0_1L).
Definition lPT_N0_1L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_1L).
Definition XF_N0_1L : axst := Eval vm_compute in (leaf 0 lPT_N0_1L).
Definition VAR_N0_1L : hbvar := ltac2:(tb__ "0|0|
S0S44S56S12SaS3cS48S4cS5aS2aS16S1eS1aS2S5eS22S2eS26SeS6S62S34S38S68S50A18").
Lemma VAR_N0_1L_ok : hbvar_ok SC_N0_1 1 true VAR_N0_1L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N0_1M : axst := Eval vm_compute in (SX_hb SC_N0_1 1 false).
Definition lPB_N0_1M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_1M).
Definition E5_N0_1M : axst := Eval vm_compute in (leaf 0 lPB_N0_1M).
Definition C5_N0_1M : axst := Eval vm_compute in (C5_hb E5_N0_1M).
Definition R5_N0_1M : list sobj := Eval vm_compute in (R5_hb C5_N0_1M).
Definition T5_N0_1M : axst := Eval vm_compute in (T5_hb C5_N0_1M).
Definition T5f_N0_1M : axst := Eval vm_compute in (T5f_hb C5_N0_1M).
Definition lPC_N0_1M : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_1M).
Definition EUs_N0_1M : axst := Eval vm_compute in (leaf 0 lPC_N0_1M).
Definition EM_N0_1M : axst := Eval vm_compute in (leaf 1 lPC_N0_1M).
Definition EMx_N0_1M : axst := Eval vm_compute in (selX EM_N0_1M [O_csh vH vMS]).
Definition EMd_N0_1M : axst := Eval vm_compute in (EMd_hb EM_N0_1M).
Definition AM_N0_1M : axst := Eval vm_compute in (A_after EMd_N0_1M (SLit 0)).
Definition lPD_N0_1M : list leafA := Eval vm_compute in (runA 900 [] AM_N0_1M).
Definition EU_N0_1M : axst := Eval vm_compute in (leaf 0 lPD_N0_1M).
Definition EUx_N0_1M : axst := Eval vm_compute in (selX EU_N0_1M (D_U_hb false)).
Definition EUd_N0_1M : axst := Eval vm_compute in (EUd_hb EU_N0_1M false).
Definition DUo_N0_1M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_1M))) (ss_objs (ax_S EUx_N0_1M))).
Definition AU_N0_1M : axst := Eval vm_compute in (A_after EUd_N0_1M (SLit 0)).
Definition lPE_N0_1M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_1M).
Definition LR_N0_1M : axst := Eval vm_compute in (leaf 0 lPE_N0_1M).
Definition PT_N0_1M : axst := Eval vm_compute in (PT_hb LR_N0_1M).
Definition lPT_N0_1M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_1M).
Definition XF_N0_1M : axst := Eval vm_compute in (leaf 0 lPT_N0_1M).
Definition VAR_N0_1M : hbvar := ltac2:(tb__ "0|0|
S0S45S57S13SbS3dS49S4dS5bS2bS17S1fS1bS3S5fS23S2fS27SfS7S63S35S39S69S51A18").
Lemma VAR_N0_1M_ok : hbvar_ok SC_N0_1 1 false VAR_N0_1M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition S0_N0_2 : axst := Eval vm_compute in (S0_hb E_N0 2).
Definition lPA_N0_2 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N0_2).
Definition LA_N0_2 : axst := Eval vm_compute in (leaf 0 lPA_N0_2).
Definition SC_N0_2 : axst := Eval vm_compute in (SC_hb LA_N0_2).
Definition lPL_N0_2 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N0_2).
Definition FAM_N0_2 : hbfam := ltac2:(tb__ "0|0|
S1S41S55S33S43S67A5").
Lemma FAM_N0_2_ok : hbfam_ok Erc_N0 2 FAM_N0_2.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N0_2L : axst := Eval vm_compute in (SX_hb SC_N0_2 2 true).
Definition lPB_N0_2L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_2L).
Definition E5_N0_2L : axst := Eval vm_compute in (leaf 0 lPB_N0_2L).
Definition C5_N0_2L : axst := Eval vm_compute in (C5_hb E5_N0_2L).
Definition R5_N0_2L : list sobj := Eval vm_compute in (R5_hb C5_N0_2L).
Definition T5_N0_2L : axst := Eval vm_compute in (T5_hb C5_N0_2L).
Definition T5f_N0_2L : axst := Eval vm_compute in (T5f_hb C5_N0_2L).
Definition lPC_N0_2L : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_2L).
Definition EUs_N0_2L : axst := Eval vm_compute in (leaf 0 lPC_N0_2L).
Definition EM_N0_2L : axst := Eval vm_compute in (leaf 1 lPC_N0_2L).
Definition EMx_N0_2L : axst := Eval vm_compute in (selX EM_N0_2L [O_csh vH vMS]).
Definition EMd_N0_2L : axst := Eval vm_compute in (EMd_hb EM_N0_2L).
Definition AM_N0_2L : axst := Eval vm_compute in (A_after EMd_N0_2L (SLit 0)).
Definition lPD_N0_2L : list leafA := Eval vm_compute in (runA 900 [] AM_N0_2L).
Definition EU_N0_2L : axst := Eval vm_compute in (leaf 0 lPD_N0_2L).
Definition EUx_N0_2L : axst := Eval vm_compute in (selX EU_N0_2L (D_U_hb true)).
Definition EUd_N0_2L : axst := Eval vm_compute in (EUd_hb EU_N0_2L true).
Definition DUo_N0_2L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_2L))) (ss_objs (ax_S EUx_N0_2L))).
Definition AU_N0_2L : axst := Eval vm_compute in (A_after EUd_N0_2L (SLit 0)).
Definition lPE_N0_2L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_2L).
Definition LR_N0_2L : axst := Eval vm_compute in (leaf 0 lPE_N0_2L).
Definition PT_N0_2L : axst := Eval vm_compute in (PT_hb LR_N0_2L).
Definition lPT_N0_2L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_2L).
Definition XF_N0_2L : axst := Eval vm_compute in (leaf 0 lPT_N0_2L).
Definition VAR_N0_2L : hbvar := ltac2:(tb__ "0|0|
S0S46S58S14ScS3eS4aS4eS5cS2cS18S20S1cS4S60S24S30S28S10S8S64S36S3aS6aS52A18").
Lemma VAR_N0_2L_ok : hbvar_ok SC_N0_2 2 true VAR_N0_2L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N0_2M : axst := Eval vm_compute in (SX_hb SC_N0_2 2 false).
Definition lPB_N0_2M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N0_2M).
Definition E5_N0_2M : axst := Eval vm_compute in (leaf 0 lPB_N0_2M).
Definition C5_N0_2M : axst := Eval vm_compute in (C5_hb E5_N0_2M).
Definition R5_N0_2M : list sobj := Eval vm_compute in (R5_hb C5_N0_2M).
Definition T5_N0_2M : axst := Eval vm_compute in (T5_hb C5_N0_2M).
Definition T5f_N0_2M : axst := Eval vm_compute in (T5f_hb C5_N0_2M).
Definition lPC_N0_2M : list leafA := Eval vm_compute in (runA 900 [] T5f_N0_2M).
Definition EUs_N0_2M : axst := Eval vm_compute in (leaf 0 lPC_N0_2M).
Definition EM_N0_2M : axst := Eval vm_compute in (leaf 1 lPC_N0_2M).
Definition EMx_N0_2M : axst := Eval vm_compute in (selX EM_N0_2M [O_csh vH vMS]).
Definition EMd_N0_2M : axst := Eval vm_compute in (EMd_hb EM_N0_2M).
Definition AM_N0_2M : axst := Eval vm_compute in (A_after EMd_N0_2M (SLit 0)).
Definition lPD_N0_2M : list leafA := Eval vm_compute in (runA 900 [] AM_N0_2M).
Definition EU_N0_2M : axst := Eval vm_compute in (leaf 0 lPD_N0_2M).
Definition EUx_N0_2M : axst := Eval vm_compute in (selX EU_N0_2M (D_U_hb false)).
Definition EUd_N0_2M : axst := Eval vm_compute in (EUd_hb EU_N0_2M false).
Definition DUo_N0_2M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N0_2M))) (ss_objs (ax_S EUx_N0_2M))).
Definition AU_N0_2M : axst := Eval vm_compute in (A_after EUd_N0_2M (SLit 0)).
Definition lPE_N0_2M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N0_2M).
Definition LR_N0_2M : axst := Eval vm_compute in (leaf 0 lPE_N0_2M).
Definition PT_N0_2M : axst := Eval vm_compute in (PT_hb LR_N0_2M).
Definition lPT_N0_2M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N0_2M).
Definition XF_N0_2M : axst := Eval vm_compute in (leaf 0 lPT_N0_2M).
Definition VAR_N0_2M : hbvar := ltac2:(tb__ "0|0|
S0S47S59S15SdS3fS4bS4fS5dS2dS19S21S1dS5S61S25S31S29S11S9S65S37S3bS6bS53A18").
Lemma VAR_N0_2M_ok : hbvar_ok SC_N0_2 2 false VAR_N0_2M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbN0.

(* [comment removed for export] *)
Module F0A_hbN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0A_hbN1"; "AM_N1_1L"; "AM_N1_1M"; "AM_N1_2L"; "AM_N1_2M"; "AU_N1_1L"; "AU_N1_1M"; "AU_N1_2L"; "AU_N1_2M"; "C5_N1_1L"; "C5_N1_1M"; "C5_N1_2L"; "C5_N1_2M"; "DUo_N1_1L"; "DUo_N1_1M"; "DUo_N1_2L"; "DUo_N1_2M"; "E5_N1_1L"; "E5_N1_1M"; "E5_N1_2L"; "E5_N1_2M"; "EM_N1_1L"; "EM_N1_1M"; "EM_N1_2L"; "EM_N1_2M"; "EMd_N1_1L"; "EMd_N1_1M"; "EMd_N1_2L"; "EMd_N1_2M"; "EMx_N1_1L"; "EMx_N1_1M"; "EMx_N1_2L"; "EMx_N1_2M"; "EU_N1_1L"; "EU_N1_1M"; "EU_N1_2L"; "EU_N1_2M"; "EUd_N1_1L"; "EUd_N1_1M"; "EUd_N1_2L"; "EUd_N1_2M"; "EUs_N1_1L"; "EUs_N1_1M"; "EUs_N1_2L"; "EUs_N1_2M"; "EUx_N1_1L"; "EUx_N1_1M"; "EUx_N1_2L"; "EUx_N1_2M"; "LA_N1_1"; "LA_N1_2"; "LR_N1_1L"; "LR_N1_1M"; "LR_N1_2L"; "LR_N1_2M"; "PT_N1_1L"; "PT_N1_1M"; "PT_N1_2L"; "PT_N1_2M"; "R5_N1_1L"; "R5_N1_1M"; "R5_N1_2L"; "R5_N1_2M"; "S0_N1_1"; "S0_N1_2"; "SC_N1_1"; "SC_N1_2"; "SX_N1_1L"; "SX_N1_1M"; "SX_N1_2L"; "SX_N1_2M"; "T5_N1_1L"; "T5_N1_1M"; "T5_N1_2L"; "T5_N1_2M"; "T5f_N1_1L"; "T5f_N1_1M"; "T5f_N1_2L"; "T5f_N1_2M"; "XF_N1_1L"; "XF_N1_1M"; "XF_N1_2L"; "XF_N1_2M"; "lPA_N1_1"; "lPA_N1_2"; "lPB_N1_1L"; "lPB_N1_1M"; "lPB_N1_2L"; "lPB_N1_2M"; "lPC_N1_1L"; "lPC_N1_1M"; "lPC_N1_2L"; "lPC_N1_2M"; "lPD_N1_1L"; "lPD_N1_1M"; "lPD_N1_2L"; "lPD_N1_2M"; "lPE_N1_1L"; "lPE_N1_1M"; "lPE_N1_2L"; "lPE_N1_2M"; "lPL_N1_1"; "lPL_N1_2"; "lPT_N1_1L"; "lPT_N1_1M"; "lPT_N1_2L"; "lPT_N1_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_N1 : axst := Eval vm_compute in Erc_N1.
Lemma FRESH_N1 : hb_fresh E_N1 = true. Proof. vmr. Qed.

Definition S0_N1_1 : axst := Eval vm_compute in (S0_hb E_N1 1).
Definition lPA_N1_1 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N1_1).
Definition LA_N1_1 : axst := Eval vm_compute in (leaf 0 lPA_N1_1).
Definition SC_N1_1 : axst := Eval vm_compute in (SC_hb LA_N1_1).
Definition lPL_N1_1 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N1_1).
Definition FAM_N1_1 : hbfam := ltac2:(tb__ "0|0|
S1S40S54S32S42S66A5").
Lemma FAM_N1_1_ok : hbfam_ok Erc_N1 1 FAM_N1_1.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N1_1L : axst := Eval vm_compute in (SX_hb SC_N1_1 1 true).
Definition lPB_N1_1L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N1_1L).
Definition E5_N1_1L : axst := Eval vm_compute in (leaf 0 lPB_N1_1L).
Definition C5_N1_1L : axst := Eval vm_compute in (C5_hb E5_N1_1L).
Definition R5_N1_1L : list sobj := Eval vm_compute in (R5_hb C5_N1_1L).
Definition T5_N1_1L : axst := Eval vm_compute in (T5_hb C5_N1_1L).
Definition T5f_N1_1L : axst := Eval vm_compute in (T5f_hb C5_N1_1L).
Definition lPC_N1_1L : list leafA := Eval vm_compute in (runA 900 [] T5f_N1_1L).
Definition EUs_N1_1L : axst := Eval vm_compute in (leaf 0 lPC_N1_1L).
Definition EM_N1_1L : axst := Eval vm_compute in (leaf 1 lPC_N1_1L).
Definition EMx_N1_1L : axst := Eval vm_compute in (selX EM_N1_1L [O_csh vH vMS]).
Definition EMd_N1_1L : axst := Eval vm_compute in (EMd_hb EM_N1_1L).
Definition AM_N1_1L : axst := Eval vm_compute in (A_after EMd_N1_1L (SLit 0)).
Definition lPD_N1_1L : list leafA := Eval vm_compute in (runA 900 [] AM_N1_1L).
Definition EU_N1_1L : axst := Eval vm_compute in (leaf 0 lPD_N1_1L).
Definition EUx_N1_1L : axst := Eval vm_compute in (selX EU_N1_1L (D_U_hb true)).
Definition EUd_N1_1L : axst := Eval vm_compute in (EUd_hb EU_N1_1L true).
Definition DUo_N1_1L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N1_1L))) (ss_objs (ax_S EUx_N1_1L))).
Definition AU_N1_1L : axst := Eval vm_compute in (A_after EUd_N1_1L (SLit 0)).
Definition lPE_N1_1L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N1_1L).
Definition LR_N1_1L : axst := Eval vm_compute in (leaf 0 lPE_N1_1L).
Definition PT_N1_1L : axst := Eval vm_compute in (PT_hb LR_N1_1L).
Definition lPT_N1_1L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N1_1L).
Definition XF_N1_1L : axst := Eval vm_compute in (leaf 0 lPT_N1_1L).
Definition VAR_N1_1L : hbvar := ltac2:(tb__ "0|0|
S0S44S56S12SaS3cS48S4cS5aS2aS16S1eS1aS2S5eS22S2eS26SeS6S62S34S38S68S50A18").
Lemma VAR_N1_1L_ok : hbvar_ok SC_N1_1 1 true VAR_N1_1L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N1_1M : axst := Eval vm_compute in (SX_hb SC_N1_1 1 false).
Definition lPB_N1_1M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N1_1M).
Definition E5_N1_1M : axst := Eval vm_compute in (leaf 0 lPB_N1_1M).
Definition C5_N1_1M : axst := Eval vm_compute in (C5_hb E5_N1_1M).
Definition R5_N1_1M : list sobj := Eval vm_compute in (R5_hb C5_N1_1M).
Definition T5_N1_1M : axst := Eval vm_compute in (T5_hb C5_N1_1M).
Definition T5f_N1_1M : axst := Eval vm_compute in (T5f_hb C5_N1_1M).
Definition lPC_N1_1M : list leafA := Eval vm_compute in (runA 900 [] T5f_N1_1M).
Definition EUs_N1_1M : axst := Eval vm_compute in (leaf 0 lPC_N1_1M).
Definition EM_N1_1M : axst := Eval vm_compute in (leaf 1 lPC_N1_1M).
Definition EMx_N1_1M : axst := Eval vm_compute in (selX EM_N1_1M [O_csh vH vMS]).
Definition EMd_N1_1M : axst := Eval vm_compute in (EMd_hb EM_N1_1M).
Definition AM_N1_1M : axst := Eval vm_compute in (A_after EMd_N1_1M (SLit 0)).
Definition lPD_N1_1M : list leafA := Eval vm_compute in (runA 900 [] AM_N1_1M).
Definition EU_N1_1M : axst := Eval vm_compute in (leaf 0 lPD_N1_1M).
Definition EUx_N1_1M : axst := Eval vm_compute in (selX EU_N1_1M (D_U_hb false)).
Definition EUd_N1_1M : axst := Eval vm_compute in (EUd_hb EU_N1_1M false).
Definition DUo_N1_1M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N1_1M))) (ss_objs (ax_S EUx_N1_1M))).
Definition AU_N1_1M : axst := Eval vm_compute in (A_after EUd_N1_1M (SLit 0)).
Definition lPE_N1_1M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N1_1M).
Definition LR_N1_1M : axst := Eval vm_compute in (leaf 0 lPE_N1_1M).
Definition PT_N1_1M : axst := Eval vm_compute in (PT_hb LR_N1_1M).
Definition lPT_N1_1M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N1_1M).
Definition XF_N1_1M : axst := Eval vm_compute in (leaf 0 lPT_N1_1M).
Definition VAR_N1_1M : hbvar := ltac2:(tb__ "0|0|
S0S45S57S13SbS3dS49S4dS5bS2bS17S1fS1bS3S5fS23S2fS27SfS7S63S35S39S69S51A18").
Lemma VAR_N1_1M_ok : hbvar_ok SC_N1_1 1 false VAR_N1_1M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition S0_N1_2 : axst := Eval vm_compute in (S0_hb E_N1 2).
Definition lPA_N1_2 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N1_2).
Definition LA_N1_2 : axst := Eval vm_compute in (leaf 0 lPA_N1_2).
Definition SC_N1_2 : axst := Eval vm_compute in (SC_hb LA_N1_2).
Definition lPL_N1_2 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N1_2).
Definition FAM_N1_2 : hbfam := ltac2:(tb__ "0|0|
S1S41S55S33S43S67A5").
Lemma FAM_N1_2_ok : hbfam_ok Erc_N1 2 FAM_N1_2.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N1_2L : axst := Eval vm_compute in (SX_hb SC_N1_2 2 true).
Definition lPB_N1_2L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N1_2L).
Definition E5_N1_2L : axst := Eval vm_compute in (leaf 0 lPB_N1_2L).
Definition C5_N1_2L : axst := Eval vm_compute in (C5_hb E5_N1_2L).
Definition R5_N1_2L : list sobj := Eval vm_compute in (R5_hb C5_N1_2L).
Definition T5_N1_2L : axst := Eval vm_compute in (T5_hb C5_N1_2L).
Definition T5f_N1_2L : axst := Eval vm_compute in (T5f_hb C5_N1_2L).
Definition lPC_N1_2L : list leafA := Eval vm_compute in (runA 900 [] T5f_N1_2L).
Definition EUs_N1_2L : axst := Eval vm_compute in (leaf 0 lPC_N1_2L).
Definition EM_N1_2L : axst := Eval vm_compute in (leaf 1 lPC_N1_2L).
Definition EMx_N1_2L : axst := Eval vm_compute in (selX EM_N1_2L [O_csh vH vMS]).
Definition EMd_N1_2L : axst := Eval vm_compute in (EMd_hb EM_N1_2L).
Definition AM_N1_2L : axst := Eval vm_compute in (A_after EMd_N1_2L (SLit 0)).
Definition lPD_N1_2L : list leafA := Eval vm_compute in (runA 900 [] AM_N1_2L).
Definition EU_N1_2L : axst := Eval vm_compute in (leaf 0 lPD_N1_2L).
Definition EUx_N1_2L : axst := Eval vm_compute in (selX EU_N1_2L (D_U_hb true)).
Definition EUd_N1_2L : axst := Eval vm_compute in (EUd_hb EU_N1_2L true).
Definition DUo_N1_2L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N1_2L))) (ss_objs (ax_S EUx_N1_2L))).
Definition AU_N1_2L : axst := Eval vm_compute in (A_after EUd_N1_2L (SLit 0)).
Definition lPE_N1_2L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N1_2L).
Definition LR_N1_2L : axst := Eval vm_compute in (leaf 0 lPE_N1_2L).
Definition PT_N1_2L : axst := Eval vm_compute in (PT_hb LR_N1_2L).
Definition lPT_N1_2L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N1_2L).
Definition XF_N1_2L : axst := Eval vm_compute in (leaf 0 lPT_N1_2L).
Definition VAR_N1_2L : hbvar := ltac2:(tb__ "0|0|
S0S46S58S14ScS3eS4aS4eS5cS2cS18S20S1cS4S60S24S30S28S10S8S64S36S3aS6aS52A18").
Lemma VAR_N1_2L_ok : hbvar_ok SC_N1_2 2 true VAR_N1_2L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N1_2M : axst := Eval vm_compute in (SX_hb SC_N1_2 2 false).
Definition lPB_N1_2M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N1_2M).
Definition E5_N1_2M : axst := Eval vm_compute in (leaf 0 lPB_N1_2M).
Definition C5_N1_2M : axst := Eval vm_compute in (C5_hb E5_N1_2M).
Definition R5_N1_2M : list sobj := Eval vm_compute in (R5_hb C5_N1_2M).
Definition T5_N1_2M : axst := Eval vm_compute in (T5_hb C5_N1_2M).
Definition T5f_N1_2M : axst := Eval vm_compute in (T5f_hb C5_N1_2M).
Definition lPC_N1_2M : list leafA := Eval vm_compute in (runA 900 [] T5f_N1_2M).
Definition EUs_N1_2M : axst := Eval vm_compute in (leaf 0 lPC_N1_2M).
Definition EM_N1_2M : axst := Eval vm_compute in (leaf 1 lPC_N1_2M).
Definition EMx_N1_2M : axst := Eval vm_compute in (selX EM_N1_2M [O_csh vH vMS]).
Definition EMd_N1_2M : axst := Eval vm_compute in (EMd_hb EM_N1_2M).
Definition AM_N1_2M : axst := Eval vm_compute in (A_after EMd_N1_2M (SLit 0)).
Definition lPD_N1_2M : list leafA := Eval vm_compute in (runA 900 [] AM_N1_2M).
Definition EU_N1_2M : axst := Eval vm_compute in (leaf 0 lPD_N1_2M).
Definition EUx_N1_2M : axst := Eval vm_compute in (selX EU_N1_2M (D_U_hb false)).
Definition EUd_N1_2M : axst := Eval vm_compute in (EUd_hb EU_N1_2M false).
Definition DUo_N1_2M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N1_2M))) (ss_objs (ax_S EUx_N1_2M))).
Definition AU_N1_2M : axst := Eval vm_compute in (A_after EUd_N1_2M (SLit 0)).
Definition lPE_N1_2M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N1_2M).
Definition LR_N1_2M : axst := Eval vm_compute in (leaf 0 lPE_N1_2M).
Definition PT_N1_2M : axst := Eval vm_compute in (PT_hb LR_N1_2M).
Definition lPT_N1_2M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N1_2M).
Definition XF_N1_2M : axst := Eval vm_compute in (leaf 0 lPT_N1_2M).
Definition VAR_N1_2M : hbvar := ltac2:(tb__ "0|0|
S0S47S59S15SdS3fS4bS4fS5dS2dS19S21S1dS5S61S25S31S29S11S9S65S37S3bS6bS53A18").
Lemma VAR_N1_2M_ok : hbvar_ok SC_N1_2 2 false VAR_N1_2M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbN1.

