(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From Stdlib Require Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lu.

(* [comment removed for export] *)
Module F0T_hbLNT.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m2.F0T_hbLNT"; "AM_LN0_0L"; "AM_LN0_0M"; "AU_LN0_0L"; "AU_LN0_0M"; "C5_LN0_0L"; "C5_LN0_0M"; "DUo_LN0_0L"; "DUo_LN0_0M"; "E5_LN0_0L"; "E5_LN0_0M"; "EM_LN0_0L"; "EM_LN0_0M"; "EMd_LN0_0L"; "EMd_LN0_0M"; "EMx_LN0_0L"; "EMx_LN0_0M"; "EU_LN0_0L"; "EU_LN0_0M"; "EUd_LN0_0L"; "EUd_LN0_0M"; "EUs_LN0_0L"; "EUs_LN0_0M"; "EUx_LN0_0L"; "EUx_LN0_0M"; "LA_LN0_0"; "LR_LN0_0L"; "LR_LN0_0M"; "PT_LN0_0L"; "PT_LN0_0M"; "R5_LN0_0L"; "R5_LN0_0M"; "S0_LN0_0"; "SC_LN0_0"; "SX_LN0_0L"; "SX_LN0_0M"; "T5_LN0_0L"; "T5_LN0_0M"; "T5f_LN0_0L"; "T5f_LN0_0M"; "XF_LN0_0L"; "XF_LN0_0M"; "lPA_LN0_0"; "lPB_LN0_0L"; "lPB_LN0_0M"; "lPC_LN0_0L"; "lPC_LN0_0M"; "lPD_LN0_0L"; "lPD_LN0_0M"; "lPE_LN0_0L"; "lPE_LN0_0M"; "lPL_LN0_0"; "lPT_LN0_0L"; "lPT_LN0_0M"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LNT : axst := Eval vm_compute in Erc_LNT.
Lemma FRESH_LNT : hb_fresh E_LNT = true. Proof. vmr. Qed.

Definition S0_LN0_0 : axst := Eval vm_compute in (S0_hb E_LNT 0).
Definition lPA_LN0_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN0_0).
Definition LA_LN0_0 : axst := Eval vm_compute in (leaf 0 lPA_LN0_0).
Definition SC_LN0_0 : axst := Eval vm_compute in (SC_hb LA_LN0_0).
Definition lPL_LN0_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN0_0).
Definition FAM_LN0_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN0_0_ok : hbfam_ok Erc_LNT 0 FAM_LN0_0.
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
End F0T_hbLNT.

(* [comment removed for export] *)
Module F0T_hxLNT.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@Corelib.Init.Datatypes"; "false"; "list"; "prod"; "@Corelib.Init.Logic"; "False"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT"; "Erc_LNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln"; "HBIGNET_stmt"; "HBIGNT_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells Iface F0A_rebuild InvQ8 F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m2.F0T_hbLNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.F0A_hbN_qsz OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_du OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.F0T_hbN_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lu.F0T_hbN_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
Import ListNotations.
Open Scope Z_scope.
Ltac vmc := match goal with |- _ = ?b => vm_cast_no_check (eq_refl b) end.
Lemma E_LN0_eq : Erc_LNT = E_LNT. Proof. Time vmc. Qed.
Lemma CF_LN0_0 : hbcertF 0 0 E_LNT FAM_LN0_0.
Proof.
  constructor.
  - rewrite <- E_LN0_eq. exact FAM_LN0_0_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_LN0_0L : hbcertV 0 0 true FAM_LN0_0 VAR_LN0_0L.
Proof.
  constructor.
  - exact VAR_LN0_0L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_LN0_0M : hbcertV 0 0 false FAM_LN0_0 VAR_LN0_0M.
Proof.
  constructor.
  - exact VAR_LN0_0M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma TAG_LN0_ok : hbtag_ok 0 false E_LNT.
Proof. intros f FA. cbn [fam_allowed] in FA. subst f. exists FAM_LN0_0; split; [exact CF_LN0_0 | intros [|]; [exists VAR_LN0_0L; exact CV_LN0_0L | exists VAR_LN0_0M; exact CV_LN0_0M]]. Qed.
Theorem HBIGN_LNT : ltac2:(tb__ "0|1|
S5S6S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1SbR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S13R6R5S4ScA4F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_LN0_eq. exact (hb_tag CST XGL H1 H2 H3 H4 false E_LNT TAG_LN0_ok). Qed.
Theorem HBIGNE_LNT : ltac2:(tb__ "0|1|
S5S6S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1SbR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S12R6R5S4ScA4F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_LN0_eq. exact (hb_tagE CST XGL H1 H2 H3 H4 false E_LNT TAG_LN0_ok). Qed.
End F0T_hxLNT.

