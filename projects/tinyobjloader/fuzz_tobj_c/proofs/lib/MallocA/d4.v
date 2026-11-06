(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_069.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cN0 F0A_hbN_cert F0A_cN1 F0A_cLN2 F0A_cN2.

(* [comment removed for export] *)
Module F0A_hbN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbN0"; "AM_N0_1L"; "AM_N0_1M"; "AM_N0_2L"; "AM_N0_2M"; "AU_N0_1L"; "AU_N0_1M"; "AU_N0_2L"; "AU_N0_2M"; "C5_N0_1L"; "C5_N0_1M"; "C5_N0_2L"; "C5_N0_2M"; "DUo_N0_1L"; "DUo_N0_1M"; "DUo_N0_2L"; "DUo_N0_2M"; "E5_N0_1L"; "E5_N0_1M"; "E5_N0_2L"; "E5_N0_2M"; "EM_N0_1L"; "EM_N0_1M"; "EM_N0_2L"; "EM_N0_2M"; "EMd_N0_1L"; "EMd_N0_1M"; "EMd_N0_2L"; "EMd_N0_2M"; "EMx_N0_1L"; "EMx_N0_1M"; "EMx_N0_2L"; "EMx_N0_2M"; "EU_N0_1L"; "EU_N0_1M"; "EU_N0_2L"; "EU_N0_2M"; "EUd_N0_1L"; "EUd_N0_1M"; "EUd_N0_2L"; "EUd_N0_2M"; "EUs_N0_1L"; "EUs_N0_1M"; "EUs_N0_2L"; "EUs_N0_2M"; "EUx_N0_1L"; "EUx_N0_1M"; "EUx_N0_2L"; "EUx_N0_2M"; "LA_N0_1"; "LA_N0_2"; "LR_N0_1L"; "LR_N0_1M"; "LR_N0_2L"; "LR_N0_2M"; "PT_N0_1L"; "PT_N0_1M"; "PT_N0_2L"; "PT_N0_2M"; "R5_N0_1L"; "R5_N0_1M"; "R5_N0_2L"; "R5_N0_2M"; "S0_N0_1"; "S0_N0_2"; "SC_N0_1"; "SC_N0_2"; "SX_N0_1L"; "SX_N0_1M"; "SX_N0_2L"; "SX_N0_2M"; "T5_N0_1L"; "T5_N0_1M"; "T5_N0_2L"; "T5_N0_2M"; "T5f_N0_1L"; "T5f_N0_1M"; "T5f_N0_2L"; "T5f_N0_2M"; "XF_N0_1L"; "XF_N0_1M"; "XF_N0_2L"; "XF_N0_2M"; "lPA_N0_1"; "lPA_N0_2"; "lPB_N0_1L"; "lPB_N0_1M"; "lPB_N0_2L"; "lPB_N0_2M"; "lPC_N0_1L"; "lPC_N0_1M"; "lPC_N0_2L"; "lPC_N0_2M"; "lPD_N0_1L"; "lPD_N0_1M"; "lPD_N0_2L"; "lPD_N0_2M"; "lPE_N0_1L"; "lPE_N0_1M"; "lPE_N0_2L"; "lPE_N0_2M"; "lPL_N0_1"; "lPL_N0_2"; "lPT_N0_1L"; "lPT_N0_1M"; "lPT_N0_2L"; "lPT_N0_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbN1"; "AM_N1_1L"; "AM_N1_1M"; "AM_N1_2L"; "AM_N1_2M"; "AU_N1_1L"; "AU_N1_1M"; "AU_N1_2L"; "AU_N1_2M"; "C5_N1_1L"; "C5_N1_1M"; "C5_N1_2L"; "C5_N1_2M"; "DUo_N1_1L"; "DUo_N1_1M"; "DUo_N1_2L"; "DUo_N1_2M"; "E5_N1_1L"; "E5_N1_1M"; "E5_N1_2L"; "E5_N1_2M"; "EM_N1_1L"; "EM_N1_1M"; "EM_N1_2L"; "EM_N1_2M"; "EMd_N1_1L"; "EMd_N1_1M"; "EMd_N1_2L"; "EMd_N1_2M"; "EMx_N1_1L"; "EMx_N1_1M"; "EMx_N1_2L"; "EMx_N1_2M"; "EU_N1_1L"; "EU_N1_1M"; "EU_N1_2L"; "EU_N1_2M"; "EUd_N1_1L"; "EUd_N1_1M"; "EUd_N1_2L"; "EUd_N1_2M"; "EUs_N1_1L"; "EUs_N1_1M"; "EUs_N1_2L"; "EUs_N1_2M"; "EUx_N1_1L"; "EUx_N1_1M"; "EUx_N1_2L"; "EUx_N1_2M"; "LA_N1_1"; "LA_N1_2"; "LR_N1_1L"; "LR_N1_1M"; "LR_N1_2L"; "LR_N1_2M"; "PT_N1_1L"; "PT_N1_1M"; "PT_N1_2L"; "PT_N1_2M"; "R5_N1_1L"; "R5_N1_1M"; "R5_N1_2L"; "R5_N1_2M"; "S0_N1_1"; "S0_N1_2"; "SC_N1_1"; "SC_N1_2"; "SX_N1_1L"; "SX_N1_1M"; "SX_N1_2L"; "SX_N1_2M"; "T5_N1_1L"; "T5_N1_1M"; "T5_N1_2L"; "T5_N1_2M"; "T5f_N1_1L"; "T5f_N1_1M"; "T5f_N1_2L"; "T5f_N1_2M"; "XF_N1_1L"; "XF_N1_1M"; "XF_N1_2L"; "XF_N1_2M"; "lPA_N1_1"; "lPA_N1_2"; "lPB_N1_1L"; "lPB_N1_1M"; "lPB_N1_2L"; "lPB_N1_2M"; "lPC_N1_1L"; "lPC_N1_1M"; "lPC_N1_2L"; "lPC_N1_2M"; "lPD_N1_1L"; "lPD_N1_1M"; "lPD_N1_2L"; "lPD_N1_2M"; "lPE_N1_1L"; "lPE_N1_1M"; "lPE_N1_2L"; "lPE_N1_2M"; "lPL_N1_1"; "lPL_N1_2"; "lPT_N1_1L"; "lPT_N1_1M"; "lPT_N1_2L"; "lPT_N1_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
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

(* [comment removed for export] *)
Module F0A_hbLN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbLN2"; "AM_LN2_0L"; "AM_LN2_0M"; "AU_LN2_0L"; "AU_LN2_0M"; "C5_LN2_0L"; "C5_LN2_0M"; "DUo_LN2_0L"; "DUo_LN2_0M"; "E5_LN2_0L"; "E5_LN2_0M"; "EM_LN2_0L"; "EM_LN2_0M"; "EMd_LN2_0L"; "EMd_LN2_0M"; "EMx_LN2_0L"; "EMx_LN2_0M"; "EU_LN2_0L"; "EU_LN2_0M"; "EUd_LN2_0L"; "EUd_LN2_0M"; "EUs_LN2_0L"; "EUs_LN2_0M"; "EUx_LN2_0L"; "EUx_LN2_0M"; "LA_LN2_0"; "LR_LN2_0L"; "LR_LN2_0M"; "PT_LN2_0L"; "PT_LN2_0M"; "R5_LN2_0L"; "R5_LN2_0M"; "S0_LN2_0"; "SC_LN2_0"; "SX_LN2_0L"; "SX_LN2_0M"; "T5_LN2_0L"; "T5_LN2_0M"; "T5f_LN2_0L"; "T5f_LN2_0M"; "XF_LN2_0L"; "XF_LN2_0M"; "lPA_LN2_0"; "lPB_LN2_0L"; "lPB_LN2_0M"; "lPC_LN2_0L"; "lPC_LN2_0M"; "lPD_LN2_0L"; "lPD_LN2_0M"; "lPE_LN2_0L"; "lPE_LN2_0M"; "lPL_LN2_0"; "lPT_LN2_0L"; "lPT_LN2_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cLN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN2 : axst := Eval vm_compute in Erc_LN2.
Lemma FRESH_LN2 : hb_fresh E_LN2 = true. Proof. vmr. Qed.

Definition S0_LN2_0 : axst := Eval vm_compute in (S0_hb E_LN2 0).
Definition lPA_LN2_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN2_0).
Definition LA_LN2_0 : axst := Eval vm_compute in (leaf 0 lPA_LN2_0).
Definition SC_LN2_0 : axst := Eval vm_compute in (SC_hb LA_LN2_0).
Definition lPL_LN2_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN2_0).
Definition FAM_LN2_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN2_0_ok : hbfam_ok Erc_LN2 0 FAM_LN2_0.
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

Definition SX_LN2_0L : axst := Eval vm_compute in (SX_hb SC_LN2_0 0 true).
Definition lPB_LN2_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN2_0L).
Definition E5_LN2_0L : axst := Eval vm_compute in (leaf 0 lPB_LN2_0L).
Definition C5_LN2_0L : axst := Eval vm_compute in (C5_hb E5_LN2_0L).
Definition R5_LN2_0L : list sobj := Eval vm_compute in (R5_hb C5_LN2_0L).
Definition T5_LN2_0L : axst := Eval vm_compute in (T5_hb C5_LN2_0L).
Definition T5f_LN2_0L : axst := Eval vm_compute in (T5f_hb C5_LN2_0L).
Definition lPC_LN2_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN2_0L).
Definition EUs_LN2_0L : axst := Eval vm_compute in (leaf 0 lPC_LN2_0L).
Definition EM_LN2_0L : axst := Eval vm_compute in (leaf 1 lPC_LN2_0L).
Definition EMx_LN2_0L : axst := Eval vm_compute in (selX EM_LN2_0L [O_csh vH vMS]).
Definition EMd_LN2_0L : axst := Eval vm_compute in (EMd_hb EM_LN2_0L).
Definition AM_LN2_0L : axst := Eval vm_compute in (A_after EMd_LN2_0L (SLit 0)).
Definition lPD_LN2_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN2_0L).
Definition EU_LN2_0L : axst := Eval vm_compute in (leaf 0 lPD_LN2_0L).
Definition EUx_LN2_0L : axst := Eval vm_compute in (selX EU_LN2_0L (D_U_hb true)).
Definition EUd_LN2_0L : axst := Eval vm_compute in (EUd_hb EU_LN2_0L true).
Definition DUo_LN2_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN2_0L))) (ss_objs (ax_S EUx_LN2_0L))).
Definition AU_LN2_0L : axst := Eval vm_compute in (A_after EUd_LN2_0L (SLit 0)).
Definition lPE_LN2_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN2_0L).
Definition LR_LN2_0L : axst := Eval vm_compute in (leaf 0 lPE_LN2_0L).
Definition PT_LN2_0L : axst := Eval vm_compute in (PT_hb LR_LN2_0L).
Definition lPT_LN2_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN2_0L).
Definition XF_LN2_0L : axst := Eval vm_compute in (leaf 0 lPT_LN2_0L).
Definition VAR_LN2_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN2_0L_ok : hbvar_ok SC_LN2_0 0 true VAR_LN2_0L.
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

Definition SX_LN2_0M : axst := Eval vm_compute in (SX_hb SC_LN2_0 0 false).
Definition lPB_LN2_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN2_0M).
Definition E5_LN2_0M : axst := Eval vm_compute in (leaf 0 lPB_LN2_0M).
Definition C5_LN2_0M : axst := Eval vm_compute in (C5_hb E5_LN2_0M).
Definition R5_LN2_0M : list sobj := Eval vm_compute in (R5_hb C5_LN2_0M).
Definition T5_LN2_0M : axst := Eval vm_compute in (T5_hb C5_LN2_0M).
Definition T5f_LN2_0M : axst := Eval vm_compute in (T5f_hb C5_LN2_0M).
Definition lPC_LN2_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN2_0M).
Definition EUs_LN2_0M : axst := Eval vm_compute in (leaf 0 lPC_LN2_0M).
Definition EM_LN2_0M : axst := Eval vm_compute in (leaf 1 lPC_LN2_0M).
Definition EMx_LN2_0M : axst := Eval vm_compute in (selX EM_LN2_0M [O_csh vH vMS]).
Definition EMd_LN2_0M : axst := Eval vm_compute in (EMd_hb EM_LN2_0M).
Definition AM_LN2_0M : axst := Eval vm_compute in (A_after EMd_LN2_0M (SLit 0)).
Definition lPD_LN2_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN2_0M).
Definition EU_LN2_0M : axst := Eval vm_compute in (leaf 0 lPD_LN2_0M).
Definition EUx_LN2_0M : axst := Eval vm_compute in (selX EU_LN2_0M (D_U_hb false)).
Definition EUd_LN2_0M : axst := Eval vm_compute in (EUd_hb EU_LN2_0M false).
Definition DUo_LN2_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN2_0M))) (ss_objs (ax_S EUx_LN2_0M))).
Definition AU_LN2_0M : axst := Eval vm_compute in (A_after EUd_LN2_0M (SLit 0)).
Definition lPE_LN2_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN2_0M).
Definition LR_LN2_0M : axst := Eval vm_compute in (leaf 0 lPE_LN2_0M).
Definition PT_LN2_0M : axst := Eval vm_compute in (PT_hb LR_LN2_0M).
Definition lPT_LN2_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN2_0M).
Definition XF_LN2_0M : axst := Eval vm_compute in (leaf 0 lPT_LN2_0M).
Definition VAR_LN2_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN2_0M_ok : hbvar_ok SC_LN2_0 0 false VAR_LN2_0M.
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
End F0A_hbLN2.

(* [comment removed for export] *)
Module F0A_hbN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbN2"; "AM_N2_1L"; "AM_N2_1M"; "AM_N2_2L"; "AM_N2_2M"; "AU_N2_1L"; "AU_N2_1M"; "AU_N2_2L"; "AU_N2_2M"; "C5_N2_1L"; "C5_N2_1M"; "C5_N2_2L"; "C5_N2_2M"; "DUo_N2_1L"; "DUo_N2_1M"; "DUo_N2_2L"; "DUo_N2_2M"; "E5_N2_1L"; "E5_N2_1M"; "E5_N2_2L"; "E5_N2_2M"; "EM_N2_1L"; "EM_N2_1M"; "EM_N2_2L"; "EM_N2_2M"; "EMd_N2_1L"; "EMd_N2_1M"; "EMd_N2_2L"; "EMd_N2_2M"; "EMx_N2_1L"; "EMx_N2_1M"; "EMx_N2_2L"; "EMx_N2_2M"; "EU_N2_1L"; "EU_N2_1M"; "EU_N2_2L"; "EU_N2_2M"; "EUd_N2_1L"; "EUd_N2_1M"; "EUd_N2_2L"; "EUd_N2_2M"; "EUs_N2_1L"; "EUs_N2_1M"; "EUs_N2_2L"; "EUs_N2_2M"; "EUx_N2_1L"; "EUx_N2_1M"; "EUx_N2_2L"; "EUx_N2_2M"; "LA_N2_1"; "LA_N2_2"; "LR_N2_1L"; "LR_N2_1M"; "LR_N2_2L"; "LR_N2_2M"; "PT_N2_1L"; "PT_N2_1M"; "PT_N2_2L"; "PT_N2_2M"; "R5_N2_1L"; "R5_N2_1M"; "R5_N2_2L"; "R5_N2_2M"; "S0_N2_1"; "S0_N2_2"; "SC_N2_1"; "SC_N2_2"; "SX_N2_1L"; "SX_N2_1M"; "SX_N2_2L"; "SX_N2_2M"; "T5_N2_1L"; "T5_N2_1M"; "T5_N2_2L"; "T5_N2_2M"; "T5f_N2_1L"; "T5f_N2_1M"; "T5f_N2_2L"; "T5f_N2_2M"; "XF_N2_1L"; "XF_N2_1M"; "XF_N2_2L"; "XF_N2_2M"; "lPA_N2_1"; "lPA_N2_2"; "lPB_N2_1L"; "lPB_N2_1M"; "lPB_N2_2L"; "lPB_N2_2M"; "lPC_N2_1L"; "lPC_N2_1M"; "lPC_N2_2L"; "lPC_N2_2M"; "lPD_N2_1L"; "lPD_N2_1M"; "lPD_N2_2L"; "lPD_N2_2M"; "lPE_N2_1L"; "lPE_N2_1M"; "lPE_N2_2L"; "lPE_N2_2M"; "lPL_N2_1"; "lPL_N2_2"; "lPT_N2_1L"; "lPT_N2_1M"; "lPT_N2_2L"; "lPT_N2_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_N2 : axst := Eval vm_compute in Erc_N2.
Lemma FRESH_N2 : hb_fresh E_N2 = true. Proof. vmr. Qed.

Definition S0_N2_1 : axst := Eval vm_compute in (S0_hb E_N2 1).
Definition lPA_N2_1 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N2_1).
Definition LA_N2_1 : axst := Eval vm_compute in (leaf 0 lPA_N2_1).
Definition SC_N2_1 : axst := Eval vm_compute in (SC_hb LA_N2_1).
Definition lPL_N2_1 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N2_1).
Definition FAM_N2_1 : hbfam := ltac2:(tb__ "0|0|
S1S40S54S32S42S66A5").
Lemma FAM_N2_1_ok : hbfam_ok Erc_N2 1 FAM_N2_1.
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

Definition SX_N2_1L : axst := Eval vm_compute in (SX_hb SC_N2_1 1 true).
Definition lPB_N2_1L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_1L).
Definition E5_N2_1L : axst := Eval vm_compute in (leaf 0 lPB_N2_1L).
Definition C5_N2_1L : axst := Eval vm_compute in (C5_hb E5_N2_1L).
Definition R5_N2_1L : list sobj := Eval vm_compute in (R5_hb C5_N2_1L).
Definition T5_N2_1L : axst := Eval vm_compute in (T5_hb C5_N2_1L).
Definition T5f_N2_1L : axst := Eval vm_compute in (T5f_hb C5_N2_1L).
Definition lPC_N2_1L : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_1L).
Definition EUs_N2_1L : axst := Eval vm_compute in (leaf 0 lPC_N2_1L).
Definition EM_N2_1L : axst := Eval vm_compute in (leaf 1 lPC_N2_1L).
Definition EMx_N2_1L : axst := Eval vm_compute in (selX EM_N2_1L [O_csh vH vMS]).
Definition EMd_N2_1L : axst := Eval vm_compute in (EMd_hb EM_N2_1L).
Definition AM_N2_1L : axst := Eval vm_compute in (A_after EMd_N2_1L (SLit 0)).
Definition lPD_N2_1L : list leafA := Eval vm_compute in (runA 900 [] AM_N2_1L).
Definition EU_N2_1L : axst := Eval vm_compute in (leaf 0 lPD_N2_1L).
Definition EUx_N2_1L : axst := Eval vm_compute in (selX EU_N2_1L (D_U_hb true)).
Definition EUd_N2_1L : axst := Eval vm_compute in (EUd_hb EU_N2_1L true).
Definition DUo_N2_1L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_1L))) (ss_objs (ax_S EUx_N2_1L))).
Definition AU_N2_1L : axst := Eval vm_compute in (A_after EUd_N2_1L (SLit 0)).
Definition lPE_N2_1L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_1L).
Definition LR_N2_1L : axst := Eval vm_compute in (leaf 0 lPE_N2_1L).
Definition PT_N2_1L : axst := Eval vm_compute in (PT_hb LR_N2_1L).
Definition lPT_N2_1L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_1L).
Definition XF_N2_1L : axst := Eval vm_compute in (leaf 0 lPT_N2_1L).
Definition VAR_N2_1L : hbvar := ltac2:(tb__ "0|0|
S0S44S56S12SaS3cS48S4cS5aS2aS16S1eS1aS2S5eS22S2eS26SeS6S62S34S38S68S50A18").
Lemma VAR_N2_1L_ok : hbvar_ok SC_N2_1 1 true VAR_N2_1L.
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

Definition SX_N2_1M : axst := Eval vm_compute in (SX_hb SC_N2_1 1 false).
Definition lPB_N2_1M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_1M).
Definition E5_N2_1M : axst := Eval vm_compute in (leaf 0 lPB_N2_1M).
Definition C5_N2_1M : axst := Eval vm_compute in (C5_hb E5_N2_1M).
Definition R5_N2_1M : list sobj := Eval vm_compute in (R5_hb C5_N2_1M).
Definition T5_N2_1M : axst := Eval vm_compute in (T5_hb C5_N2_1M).
Definition T5f_N2_1M : axst := Eval vm_compute in (T5f_hb C5_N2_1M).
Definition lPC_N2_1M : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_1M).
Definition EUs_N2_1M : axst := Eval vm_compute in (leaf 0 lPC_N2_1M).
Definition EM_N2_1M : axst := Eval vm_compute in (leaf 1 lPC_N2_1M).
Definition EMx_N2_1M : axst := Eval vm_compute in (selX EM_N2_1M [O_csh vH vMS]).
Definition EMd_N2_1M : axst := Eval vm_compute in (EMd_hb EM_N2_1M).
Definition AM_N2_1M : axst := Eval vm_compute in (A_after EMd_N2_1M (SLit 0)).
Definition lPD_N2_1M : list leafA := Eval vm_compute in (runA 900 [] AM_N2_1M).
Definition EU_N2_1M : axst := Eval vm_compute in (leaf 0 lPD_N2_1M).
Definition EUx_N2_1M : axst := Eval vm_compute in (selX EU_N2_1M (D_U_hb false)).
Definition EUd_N2_1M : axst := Eval vm_compute in (EUd_hb EU_N2_1M false).
Definition DUo_N2_1M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_1M))) (ss_objs (ax_S EUx_N2_1M))).
Definition AU_N2_1M : axst := Eval vm_compute in (A_after EUd_N2_1M (SLit 0)).
Definition lPE_N2_1M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_1M).
Definition LR_N2_1M : axst := Eval vm_compute in (leaf 0 lPE_N2_1M).
Definition PT_N2_1M : axst := Eval vm_compute in (PT_hb LR_N2_1M).
Definition lPT_N2_1M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_1M).
Definition XF_N2_1M : axst := Eval vm_compute in (leaf 0 lPT_N2_1M).
Definition VAR_N2_1M : hbvar := ltac2:(tb__ "0|0|
S0S45S57S13SbS3dS49S4dS5bS2bS17S1fS1bS3S5fS23S2fS27SfS7S63S35S39S69S51A18").
Lemma VAR_N2_1M_ok : hbvar_ok SC_N2_1 1 false VAR_N2_1M.
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

Definition S0_N2_2 : axst := Eval vm_compute in (S0_hb E_N2 2).
Definition lPA_N2_2 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N2_2).
Definition LA_N2_2 : axst := Eval vm_compute in (leaf 0 lPA_N2_2).
Definition SC_N2_2 : axst := Eval vm_compute in (SC_hb LA_N2_2).
Definition lPL_N2_2 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N2_2).
Definition FAM_N2_2 : hbfam := ltac2:(tb__ "0|0|
S1S41S55S33S43S67A5").
Lemma FAM_N2_2_ok : hbfam_ok Erc_N2 2 FAM_N2_2.
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

Definition SX_N2_2L : axst := Eval vm_compute in (SX_hb SC_N2_2 2 true).
Definition lPB_N2_2L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_2L).
Definition E5_N2_2L : axst := Eval vm_compute in (leaf 0 lPB_N2_2L).
Definition C5_N2_2L : axst := Eval vm_compute in (C5_hb E5_N2_2L).
Definition R5_N2_2L : list sobj := Eval vm_compute in (R5_hb C5_N2_2L).
Definition T5_N2_2L : axst := Eval vm_compute in (T5_hb C5_N2_2L).
Definition T5f_N2_2L : axst := Eval vm_compute in (T5f_hb C5_N2_2L).
Definition lPC_N2_2L : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_2L).
Definition EUs_N2_2L : axst := Eval vm_compute in (leaf 0 lPC_N2_2L).
Definition EM_N2_2L : axst := Eval vm_compute in (leaf 1 lPC_N2_2L).
Definition EMx_N2_2L : axst := Eval vm_compute in (selX EM_N2_2L [O_csh vH vMS]).
Definition EMd_N2_2L : axst := Eval vm_compute in (EMd_hb EM_N2_2L).
Definition AM_N2_2L : axst := Eval vm_compute in (A_after EMd_N2_2L (SLit 0)).
Definition lPD_N2_2L : list leafA := Eval vm_compute in (runA 900 [] AM_N2_2L).
Definition EU_N2_2L : axst := Eval vm_compute in (leaf 0 lPD_N2_2L).
Definition EUx_N2_2L : axst := Eval vm_compute in (selX EU_N2_2L (D_U_hb true)).
Definition EUd_N2_2L : axst := Eval vm_compute in (EUd_hb EU_N2_2L true).
Definition DUo_N2_2L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_2L))) (ss_objs (ax_S EUx_N2_2L))).
Definition AU_N2_2L : axst := Eval vm_compute in (A_after EUd_N2_2L (SLit 0)).
Definition lPE_N2_2L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_2L).
Definition LR_N2_2L : axst := Eval vm_compute in (leaf 0 lPE_N2_2L).
Definition PT_N2_2L : axst := Eval vm_compute in (PT_hb LR_N2_2L).
Definition lPT_N2_2L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_2L).
Definition XF_N2_2L : axst := Eval vm_compute in (leaf 0 lPT_N2_2L).
Definition VAR_N2_2L : hbvar := ltac2:(tb__ "0|0|
S0S46S58S14ScS3eS4aS4eS5cS2cS18S20S1cS4S60S24S30S28S10S8S64S36S3aS6aS52A18").
Lemma VAR_N2_2L_ok : hbvar_ok SC_N2_2 2 true VAR_N2_2L.
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

Definition SX_N2_2M : axst := Eval vm_compute in (SX_hb SC_N2_2 2 false).
Definition lPB_N2_2M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_2M).
Definition E5_N2_2M : axst := Eval vm_compute in (leaf 0 lPB_N2_2M).
Definition C5_N2_2M : axst := Eval vm_compute in (C5_hb E5_N2_2M).
Definition R5_N2_2M : list sobj := Eval vm_compute in (R5_hb C5_N2_2M).
Definition T5_N2_2M : axst := Eval vm_compute in (T5_hb C5_N2_2M).
Definition T5f_N2_2M : axst := Eval vm_compute in (T5f_hb C5_N2_2M).
Definition lPC_N2_2M : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_2M).
Definition EUs_N2_2M : axst := Eval vm_compute in (leaf 0 lPC_N2_2M).
Definition EM_N2_2M : axst := Eval vm_compute in (leaf 1 lPC_N2_2M).
Definition EMx_N2_2M : axst := Eval vm_compute in (selX EM_N2_2M [O_csh vH vMS]).
Definition EMd_N2_2M : axst := Eval vm_compute in (EMd_hb EM_N2_2M).
Definition AM_N2_2M : axst := Eval vm_compute in (A_after EMd_N2_2M (SLit 0)).
Definition lPD_N2_2M : list leafA := Eval vm_compute in (runA 900 [] AM_N2_2M).
Definition EU_N2_2M : axst := Eval vm_compute in (leaf 0 lPD_N2_2M).
Definition EUx_N2_2M : axst := Eval vm_compute in (selX EU_N2_2M (D_U_hb false)).
Definition EUd_N2_2M : axst := Eval vm_compute in (EUd_hb EU_N2_2M false).
Definition DUo_N2_2M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_2M))) (ss_objs (ax_S EUx_N2_2M))).
Definition AU_N2_2M : axst := Eval vm_compute in (A_after EUd_N2_2M (SLit 0)).
Definition lPE_N2_2M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_2M).
Definition LR_N2_2M : axst := Eval vm_compute in (leaf 0 lPE_N2_2M).
Definition PT_N2_2M : axst := Eval vm_compute in (PT_hb LR_N2_2M).
Definition lPT_N2_2M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_2M).
Definition XF_N2_2M : axst := Eval vm_compute in (leaf 0 lPT_N2_2M).
Definition VAR_N2_2M : hbvar := ltac2:(tb__ "0|0|
S0S47S59S15SdS3fS4bS4fS5dS2dS19S21S1dS5S61S25S31S29S11S9S65S37S3bS6bS53A18").
Lemma VAR_N2_2M_ok : hbvar_ok SC_N2_2 2 false VAR_N2_2M.
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
End F0A_hbN2.

