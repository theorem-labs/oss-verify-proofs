(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From Stdlib Require Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_cont ln lq jr l4.

(* [comment removed for export] *)
Module SegQIF_m6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m6"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 6.

Definition S0_fa : axst := Eval vm_compute in (bumpM (S0M_of N false false) NXM).
Definition L1_fa : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fa)).
Definition XC_fa : list axform := Eval vm_compute in (XC_of false false L1_fa).
Definition C1_fa : axst := Eval vm_compute in (optA L1_fa (apply_axforms L1_fa XC_fa)).
Definition sF_fa : wsub := Eval vm_compute in (sF_of N false C1_fa).
Definition RF_fa : list sobj := Eval vm_compute in (optR (entails_frA C1_fa (PreD N false) sF_fa)).
Definition T1f_fa : axst := Eval vm_compute in (T1f_of N false C1_fa sF_fa RF_fa).
Definition XX_fa : list axform := Eval vm_compute in (XX_of N false false T1f_fa).
Definition Lx_fa : axst := Eval vm_compute in (optA T1f_fa (apply_axforms T1f_fa XX_fa)).
Definition D_fa : mdata := ltac2:(tb__ "0|0|
S2eS19SdS21S8S29S15S1dS25S11A9").
Lemma cert_fa : ltac2:(tb__ "0|0|
S2dS3S1S1S4A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_fb : axst := Eval vm_compute in (bumpM (S0M_of N false true) NXM).
Definition L1_fb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fb)).
Definition XC_fb : list axform := Eval vm_compute in (XC_of false true L1_fb).
Definition C1_fb : axst := Eval vm_compute in (optA L1_fb (apply_axforms L1_fb XC_fb)).
Definition sF_fb : wsub := Eval vm_compute in (sF_of N false C1_fb).
Definition RF_fb : list sobj := Eval vm_compute in (optR (entails_frA C1_fb (PreD N false) sF_fb)).
Definition T1f_fb : axst := Eval vm_compute in (T1f_of N false C1_fb sF_fb RF_fb).
Definition XX_fb : list axform := Eval vm_compute in (XX_of N false true T1f_fb).
Definition Lx_fb : axst := Eval vm_compute in (optA T1f_fb (apply_axforms T1f_fb XX_fb)).
Definition D_fb : mdata := ltac2:(tb__ "0|0|
S2eS1aSeS22S9S2aS16S1eS26S12A9").
Lemma cert_fb : ltac2:(tb__ "0|0|
S2dS3S1S2S5A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_ga : axst := Eval vm_compute in (bumpM (S0M_of N true false) NXM).
Definition L1_ga : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_ga)).
Definition XC_ga : list axform := Eval vm_compute in (XC_of true false L1_ga).
Definition C1_ga : axst := Eval vm_compute in (optA L1_ga (apply_axforms L1_ga XC_ga)).
Definition sF_ga : wsub := Eval vm_compute in (sF_of N true C1_ga).
Definition RF_ga : list sobj := Eval vm_compute in (optR (entails_frA C1_ga (PreD N true) sF_ga)).
Definition T1f_ga : axst := Eval vm_compute in (T1f_of N true C1_ga sF_ga RF_ga).
Definition XX_ga : list axform := Eval vm_compute in (XX_of N true false T1f_ga).
Definition Lx_ga : axst := Eval vm_compute in (optA T1f_ga (apply_axforms T1f_ga XX_ga)).
Definition D_ga : mdata := ltac2:(tb__ "0|0|
S2eS1bSfS23SaS2bS17S1fS27S13A9").
Lemma cert_ga : ltac2:(tb__ "0|0|
S2dS3S2S1S6A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_gb : axst := Eval vm_compute in (bumpM (S0M_of N true true) NXM).
Definition L1_gb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_gb)).
Definition XC_gb : list axform := Eval vm_compute in (XC_of true true L1_gb).
Definition C1_gb : axst := Eval vm_compute in (optA L1_gb (apply_axforms L1_gb XC_gb)).
Definition sF_gb : wsub := Eval vm_compute in (sF_of N true C1_gb).
Definition RF_gb : list sobj := Eval vm_compute in (optR (entails_frA C1_gb (PreD N true) sF_gb)).
Definition T1f_gb : axst := Eval vm_compute in (T1f_of N true C1_gb sF_gb RF_gb).
Definition XX_gb : list axform := Eval vm_compute in (XX_of N true true T1f_gb).
Definition Lx_gb : axst := Eval vm_compute in (optA T1f_gb (apply_axforms T1f_gb XX_gb)).
Definition D_gb : mdata := ltac2:(tb__ "0|0|
S2eS1cS10S24SbS2cS18S20S28S14A9").
Lemma cert_gb : ltac2:(tb__ "0|0|
S2dS3S2S2S7A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition D_of (g vb : bool) : mdata := ltac2:(tb__ "0|1|
S0S2fLg;Vg;S0S2fLvb;M0Vvb;S7S6X0x2G0Vvb;S5S4X0x2X0x2").
Lemma cert_of : ltac2:(tb__ "0|0|
S0S0S2dS3R2R1ScR2R1A2A4Fvb;Fg;").
Proof. intros [|] [|]; [exact cert_gb | exact cert_ga | exact cert_fb | exact cert_fa]. Qed.
End SegQIF_m6.

(* [comment removed for export] *)
Module SegQIF_m8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m8"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 8.

Definition S0_fa : axst := Eval vm_compute in (bumpM (S0M_of N false false) NXM).
Definition L1_fa : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fa)).
Definition XC_fa : list axform := Eval vm_compute in (XC_of false false L1_fa).
Definition C1_fa : axst := Eval vm_compute in (optA L1_fa (apply_axforms L1_fa XC_fa)).
Definition sF_fa : wsub := Eval vm_compute in (sF_of N false C1_fa).
Definition RF_fa : list sobj := Eval vm_compute in (optR (entails_frA C1_fa (PreD N false) sF_fa)).
Definition T1f_fa : axst := Eval vm_compute in (T1f_of N false C1_fa sF_fa RF_fa).
Definition XX_fa : list axform := Eval vm_compute in (XX_of N false false T1f_fa).
Definition Lx_fa : axst := Eval vm_compute in (optA T1f_fa (apply_axforms T1f_fa XX_fa)).
Definition D_fa : mdata := ltac2:(tb__ "0|0|
S2eS19SdS21S8S29S15S1dS25S11A9").
Lemma cert_fa : ltac2:(tb__ "0|0|
S2dS3S1S1S4A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_fb : axst := Eval vm_compute in (bumpM (S0M_of N false true) NXM).
Definition L1_fb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fb)).
Definition XC_fb : list axform := Eval vm_compute in (XC_of false true L1_fb).
Definition C1_fb : axst := Eval vm_compute in (optA L1_fb (apply_axforms L1_fb XC_fb)).
Definition sF_fb : wsub := Eval vm_compute in (sF_of N false C1_fb).
Definition RF_fb : list sobj := Eval vm_compute in (optR (entails_frA C1_fb (PreD N false) sF_fb)).
Definition T1f_fb : axst := Eval vm_compute in (T1f_of N false C1_fb sF_fb RF_fb).
Definition XX_fb : list axform := Eval vm_compute in (XX_of N false true T1f_fb).
Definition Lx_fb : axst := Eval vm_compute in (optA T1f_fb (apply_axforms T1f_fb XX_fb)).
Definition D_fb : mdata := ltac2:(tb__ "0|0|
S2eS1aSeS22S9S2aS16S1eS26S12A9").
Lemma cert_fb : ltac2:(tb__ "0|0|
S2dS3S1S2S5A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_ga : axst := Eval vm_compute in (bumpM (S0M_of N true false) NXM).
Definition L1_ga : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_ga)).
Definition XC_ga : list axform := Eval vm_compute in (XC_of true false L1_ga).
Definition C1_ga : axst := Eval vm_compute in (optA L1_ga (apply_axforms L1_ga XC_ga)).
Definition sF_ga : wsub := Eval vm_compute in (sF_of N true C1_ga).
Definition RF_ga : list sobj := Eval vm_compute in (optR (entails_frA C1_ga (PreD N true) sF_ga)).
Definition T1f_ga : axst := Eval vm_compute in (T1f_of N true C1_ga sF_ga RF_ga).
Definition XX_ga : list axform := Eval vm_compute in (XX_of N true false T1f_ga).
Definition Lx_ga : axst := Eval vm_compute in (optA T1f_ga (apply_axforms T1f_ga XX_ga)).
Definition D_ga : mdata := ltac2:(tb__ "0|0|
S2eS1bSfS23SaS2bS17S1fS27S13A9").
Lemma cert_ga : ltac2:(tb__ "0|0|
S2dS3S2S1S6A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_gb : axst := Eval vm_compute in (bumpM (S0M_of N true true) NXM).
Definition L1_gb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_gb)).
Definition XC_gb : list axform := Eval vm_compute in (XC_of true true L1_gb).
Definition C1_gb : axst := Eval vm_compute in (optA L1_gb (apply_axforms L1_gb XC_gb)).
Definition sF_gb : wsub := Eval vm_compute in (sF_of N true C1_gb).
Definition RF_gb : list sobj := Eval vm_compute in (optR (entails_frA C1_gb (PreD N true) sF_gb)).
Definition T1f_gb : axst := Eval vm_compute in (T1f_of N true C1_gb sF_gb RF_gb).
Definition XX_gb : list axform := Eval vm_compute in (XX_of N true true T1f_gb).
Definition Lx_gb : axst := Eval vm_compute in (optA T1f_gb (apply_axforms T1f_gb XX_gb)).
Definition D_gb : mdata := ltac2:(tb__ "0|0|
S2eS1cS10S24SbS2cS18S20S28S14A9").
Lemma cert_gb : ltac2:(tb__ "0|0|
S2dS3S2S2S7A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition D_of (g vb : bool) : mdata := ltac2:(tb__ "0|1|
S0S2fLg;Vg;S0S2fLvb;M0Vvb;S7S6X0x2G0Vvb;S5S4X0x2X0x2").
Lemma cert_of : ltac2:(tb__ "0|0|
S0S0S2dS3R2R1ScR2R1A2A4Fvb;Fg;").
Proof. intros [|] [|]; [exact cert_gb | exact cert_ga | exact cert_fb | exact cert_fa]. Qed.
End SegQIF_m8.

(* [comment removed for export] *)
Module SegQIF_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Corelib.Init.Datatypes"; "prod"; "nat"; "bool"; "cons"; "list"; "pair"; "true"; "app"; "nil"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sv"; "SExt"; "holds"; "sobj"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_cache_inited"; "cs_cache"; "aa_q_global"; "aa_q_thread"; "mkQB"; "aa_geom"; "ag_spacebeg"; "ageom"; "cs_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "RTC_A"; "cells_ok"; "rtc_cells"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "lt"; "add"; "mul"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QW"; "@Stdlib.Lists.List"; "In"; "Forall2"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env"; "qienvF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "VSM"; "ZUM"; "m_Ly"; "mcert"; "REFOBJ_KO"; "S7"; "XROs"; "ZD_KO"; "dst_cellsM"; "m_Lx"; "vCHq"; "zhiM"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "qienv"; "zloQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue"; "ENVM"; "zbMq"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "in_zone"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "QIV"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dspec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_cont"; "DZM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "ro_cond"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_cont.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.SegQCF_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m0.SegQIF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_cont.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma K0_id_boundM : ltac2:(tb__ "0|1|
S5dS1cS12SaS39Q40A1A1SaS5aA1S59S0S0S5eR8A1S3S2dZ1R3A2S2dR3Z1eA2A2S2S8S1dR9A1ScA3S3fRbRaR9R8R7R6A6S36S0R5SdS0S25S34RbR6A2M0A1S1eG0A1A3A3S3S2dZ0R6A2S2fR6S32Z2Z1cA2A2A2F_;F_;F_;F_;F_;Fx;Fc;Fmd;Ftr;Ftp;Fr;FA;FKc;").
Proof.
  intros Kc A r tp tr md c x HKc Hc HCI HK Hx. pose proof HK as (HA & _).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [_ _ _ _ _ _ HCLS _ _ _ _ _ _].
  pose proof (HCLS HCI c Hc) as CV. pose proof (cv_bounds _ _ _ _ _ CV) as (_ & B2 & B3 & _).
  pose proof HA as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD.entry_cls_pureQ _ A c Hc (PC c Hc) HQP) as (_ & _ & _ & _ & _ & _ & HIDS & _).
  destruct (HIDS x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X0 & _ & X2).
  pose proof (Size_facts c Hc) as (SZ & _). unfold cls_of in B2, B3. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in B3. lia.
Qed.

Lemma dst_cellsM_in : ltac2:(tb__ "0|1|
S0S7S58R1S33R2A1A2S36S6S6S0S7A2M0S15A2SbG0S15SbS0S7S31Z4S2eR2A1A2U4A4S16ScQ20S4bR2A1A3A4S49R3A1A3F_;Fi;Fn;").
Proof.
  intros n i Hi. unfold dst_cellsM. apply (proj1 (in_rev _ _)). apply in_map_iff. exists i. split; [reflexivity|]. unfold idxs. apply in_seq. lia.
Qed.

Section ExitM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S44Vn;Vg;Vvb;VD;A4").

Lemma qif_x1 : ltac2:(tb__ "0|8|
S1cS0S0S0S7S6S0S0A2M0SaG0A1SaS1bA1M1G1S12SaS39Q40A1M2A1S4fS2G1S20RcA1SeS1bA1A3S2S8S1dRdA1ScA3S3eVA0;ReA2S2G1S1fRfA1S9S1bS21ReS9G0RaR9A3RdA3SdS1bR8R7A3A3A3S3S2dZ1S11RbA1M3A2S2dG3Z1eA2A2S2S0S53S11RcA1A1Vn;A3S2S0S2eS10S0S1eS34R12S11RdA1M4A2A1A2A1S51G4A1A3S2S8S3cS11ReA1M5S34R13G5A2A2Vg;A3S56Vn;R14S11RfA1RbA4S3aS1aS3dS3fVKc;A1M6VA0;Vrho0;S3bR15S11R10A1A2R14R12R11S9G0R10RfA3ReRdAaS4aVD;A1RcRbRaA6S5S12S12S3S3aS1aS3dG6VA0;Vrho0;S3bR17S11R12A1A2R16R14R13S9G0R12R11A3R10RfAaS43VD;A1R1RdRcA6S3S1S2G2S14R2R1A2S14RfR1A2A3Fi;S0S4S3S2dS52S23S22R18A1A1S11R13A1A2M7R1A2S2fR1S30G7Z80A2A2A2A1S2SfS39Q8A1A1S26S1aS13R3A1R2A3S26S1aS13R10A1R2A3A3F_;Fz;A2A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp [tr [ms md]] HTH HCI HQP HGL C1 Hn HFULL HGR (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH) H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (c := it_cls it) in *. set (A1 := drainA A c) in *.
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG _ _ _ HLEN HCLS _ _ _ _ _ _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (Z.to_nat c < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI c C1) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_clsM A c HLA) in CV1.
  set (cs := cls_of A c) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  destruct (kchunks_facts c C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  assert (NF0 : 0 <= nf) by (unfold nf; lia). assert (HFL : length (cs_cache cs) = (Z.to_nat n + Z.to_nat n)%nat) by lia.
  assert (KEEP : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite Hn, HFL; lia).
  assert (EFA1 : cs_free_array (drain_cs c cs) = cs_free_array cs ++ skipn (Z.to_nat n) (cs_cache cs)) by (unfold drain_cs; cbn [cs_free_array]; rewrite KEEP; reflexivity).
  assert (LFA1 : Z.of_nat (length (cs_free_array (drain_cs c cs))) = nf + n) by (rewrite EFA1, length_app, length_skipn, HFL; unfold nf; lia).
  assert (EMF1 : cs_mapped_free_array (drain_cs c cs) = if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs).
  { unfold drain_cs. cbn [cs_mapped_free_array]. fold cs in HGR. rewrite HGR. unfold kFreeArrayMapSize. destruct g; reflexivity. }
  pose proof (cv_fa_bounds _ _ _ _ _ CV1) as (FC1 & FC2 & FC3). rewrite LFA1 in FC2. rewrite EMF1 in FC1, FC2, FC3. unfold kFreeArrayMapSize in FC1.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & _). fold SB in S1, S2.
  pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, kFreeArraySize in *. rewrite kSpaceSize_val in S2.
  assert (RIv : region_info SB c = SB + 2 ^ 37 + 128 * c) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (GIF : cs_mapped_free_array cs <= (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs) <= cs_mapped_free_array cs + 262144) by (case g; lia).
  assert (MF0 : 0 <= cs_mapped_free_array cs <= 536870912) by (clear - FC1 FC2 FC3 NF0 KC GIF; lia).
  assert (ERI : bv_unsigned (eval rho vRI) = SB + 2 ^ 37 + 128 * c) by (unfold vRI; cbn [eval]; rewrite E225; fold SB; rewrite RIv, u64_lit by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho dstM) = SB + c * 2 ^ 32 + 3758096384 + 4 * nf).
  { unfold dstM. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite E200, E155, E221. fold SB nf. rewrite !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
    unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }

  set (xi := fun i : nat => nth (Z.to_nat n + i) (cs_cache cs) 0).
  assert (XIN : forall i, (i < Z.to_nat n)%nat -> nth_error (cs_cache cs) (Z.to_nat n + i) = Some (xi i)) by (intros i Hi; unfold xi; apply nth_error_nth'; lia).
  assert (HXI : forall i, (i < Z.to_nat n)%nat -> 0 <= xi i < 2 ^ 28).
  { intros i Hi. apply (K0_id_boundM Kc A1 rho tp tr md c (xi i) HKc C1 HCI HK). unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite EFA1.
    apply in_or_app. left. apply in_or_app. right. apply (nth_error_In _ i). rewrite nth_error_skipn. exact (XIN i Hi). }
  pose proof (cv_ri_au _ _ _ _ _ CV1) as K_au. pose proof (cv_ri_mu _ _ _ _ _ CV1) as K_mu. pose proof (cv_bounds _ _ _ _ _ CV1) as (_ & BAU & BMU & _).
  assert (K_dst : forall i, (i < Z.to_nat n)%nat -> cell_ok (view segsA (rm rho)) (mkACell (free_array SB c + 4 * nf + 4 * Z.of_nat i) 4 (xi i))).
  { intros i Hi. pose proof (cv_fa_cells _ _ _ _ _ CV1 (length (cs_free_array cs) + i) (xi i)
                               ltac:(rewrite EFA1; rewrite nth_error_app2 by lia; replace (length (cs_free_array cs) + i - length (cs_free_array cs))%nat with i by lia; rewrite nth_error_skipn; exact (XIN i Hi))) as X0.
    fold SB in X0. rewrite Nat2Z.inj_add in X0. fold nf in X0. replace (free_array SB c + 4 * (nf + Z.of_nat i)) with (free_array SB c + 4 * nf + 4 * Z.of_nat i) in X0 by lia. exact X0. }
  fold SB in K_au, K_mu. rewrite FAv in K_dst. cbn [cs_allocated_user cs_mapped_user drain_cs] in BAU, BMU. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in BMU.

  set (R := map carve_obj [riOS n g; dstOS n]). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (keepN (m_Lx D) 2) R vRI 0 128 _ Hsm (c_Lxobjs n g vb D HC) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite ERI; lia) ltac:(rewrite ERI; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (keepN (m_Lx D) 2) R dstM 0 (4 * n) (dst_cellsM n) Hsm (c_Lxobjs n g vb D HC) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside, dst_cellsM; apply Forall_rev; apply Forall_map_in; intros i Hi; apply In_idxs in Hi; cbn; lia) ltac:(rewrite Edst; lia) ltac:(rewrite Edst; lia)) as [AV2 PR2].
  fold rho3 v3 in AV1, PR1, AV2, PR2. rewrite ERI in AV1, PR1. rewrite Edst in AV2, PR2.
  set (ri := SB + 2 ^ 37 + 128 * c) in *. set (da := SB + c * 2 ^ 32 + 3758096384 + 4 * nf) in *.
  assert (Enf1 : eval rho (SAlu ALU_ADD vNF (SLit n)) = Z_to_bv 64 (nf + n)) by (apply (ev_add_lit rho vNF nf n); [unfold vNF; cbn [eval]; exact E221 | lia | lia | lia]).
  assert (Emf1 : eval rho (if g then SAlu ALU_ADD vMFA (SLit 262144) else vMFA) = Z_to_bv 64 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs)).
  { case g; [apply (ev_add_lit rho vMFA (cs_mapped_free_array cs) 262144); [unfold vMFA; cbn [eval]; exact E222 | lia | lia | lia] | unfold vMFA; cbn [eval]; exact E222]. }
  assert (C0 : cell_ok v3 (mkACell (ri + 0) 8 0)) by exact (av_cell v3 ri 0 8 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C16 : cell_ok v3 (mkACell (ri + 16) 8 (nf + n))) by exact (av_cell v3 ri 16 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) Enf1).
  assert (C24 : cell_ok v3 (mkACell (ri + 24) 8 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs))) by exact (av_cell v3 ri 24 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) Emf1).
  assert (C32 : cell_ok v3 (mkACell (ri + 32) 8 (cs_allocated_user cs))) by exact (av_cell v3 ri 32 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) E223).
  assert (C40 : cell_ok v3 (mkACell (ri + 40) 8 0)) by exact (av_cell v3 ri 40 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) eq_refl).
  assert (C48 : cell_ok v3 (mkACell (ri + 48) 8 (cs_mapped_user cs))) by exact (av_cell v3 ri 48 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) E224).
  assert (C56 : cell_ok v3 (mkACell (ri + 56) 8 0)) by exact (av_cell v3 ri 56 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) eq_refl).
  assert (C68 : cell_ok v3 (mkACell (ri + 68) 1 0)) by exact (av_cell v3 ri 68 1 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) eq_refl).
  assert (Cd3 : forall i, (i < Z.to_nat n)%nat -> cell_ok v3 (mkACell (da + 4 * Z.of_nat i) 4 (xi i))).
  { intros i Hi. apply (av_cell v3 da (4 * Z.of_nat i) 4 (SExt true 32 (vCHq i)) (xi i) rho (fun j => AV2 _ _ _ j (dst_cellsM_in n i Hi))).
    unfold vCHq. cbn [eval]. rewrite (ECH i Hi). fold cs. fold (xi i). apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.sext32_small. pose proof (HXI i Hi). lia. }
  set (P := fun z : Z => (ri <= z < ri + 128) \/ (da <= z < da + 4 * n)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]]; unfold carve_obj, riOS, dstOS, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz; rewrite ?ERI, ?Edst in Hz; fold ri da in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (VD : forall z, da <= z < da + 4 * n -> v3 z = v z).
  { intros z Hz. set (i := Z.to_nat ((z - da) / 4)).
    pose proof (Z.div_pos (z - da) 4 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (z - da) 4 n ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_mod (z - da) 4 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (z - da) 4 ltac:(lia)) as MB.
    assert (Hi : (i < Z.to_nat n)%nat) by (unfold i; lia).
    apply (cell_ok_same v v3 _ (K_dst i Hi) (Cd3 i Hi)). cbn [c_addr c_w]. unfold i. rewrite Z2Nat.id by lia. lia. }
  assert (VO : forall z, ~ (ri <= z < ri + 128) -> v3 z = v z).
  { intros z Hz. destruct (Z_le_dec da z) as [L1|L1]; [destruct (Z_lt_dec z (da + 4 * n)) as [L2|L2]; [exact (VD z (conj L1 L2))|]|]; apply FR; unfold P; lia. }
  assert (HK3 : K0 Kc A1 rho3 tp tr md).
  { apply (K0_ri_blind Kc A1 rho rho3 tp tr md c HKc C1 HCI); try (intros; reflexivity); try exact HK.
    all: change (ag_spacebeg (aa_geom A1)) with SB; rewrite ?RIv; fold ri; fold v3 v.
    all: unfold A1; rewrite ?(drainA_clsM A c HLA); fold cs; rewrite ?LFA1, ?EMF1; cbn [cs_allocated_user cs_mapped_user drain_cs].
    all: unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    - exact VO.
    - intros z Hz. exact (PR1 z ltac:(lia)).
    - intros a0 Ha0. apply FRrm. unfold P, ri, da. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha0; lia). unfold IMG_LO, IMG_HI in Ha0. lia.
    - exact C0.
    - exact C16.
    - exact C24.
    - exact C32.
    - exact C40.
    - exact C48.
    - exact C56.
    - exact C68. }
  assert (PDZ : forall z, P z -> DZ A1 c z).
  { intros z Hz. unfold DZ. cbv zeta. change (aa_geom A1) with (aa_geom A). fold SB. rewrite RIv, FAv. unfold kRegionInfoStride, kFreeArraySize. unfold P, ri, da in Hz.
    destruct Hz as [Hz|Hz]; [right; left; lia | right; right; left; clear - Hz FC2 FC3 NF0 KC GIF; lia]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A1 a s (it :: its) tmp' rest c HTH HCI HGL C1 rho tp tr md v v3 n0 nd HK) as (HCB3 & HRM3); [ | | exact HCB | exact HRM | ].
  { intros z Hz. apply FR. intros HP. exact (Hz (PDZ z HP)). }
  { intros z HB Hd. rewrite FR; [exact Hd|]. unfold P, ri, da. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HB. lia. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. split; [exact (DZ_QFPM A1 A0 c z C1 EG (PDZ z Hz))|]. unfold P, ri, da in Hz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (m_Lx D) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (m_Lx D) (keepN (m_Lx D) 2) R tp tr ms md (c_Lxobjs n g vb D HC) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|split; [intros i; reflexivity|]].
  - split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HRM3 | exact HF3].
  - intros z Hz. apply VO. rewrite RIv in Hz. exact Hz.
Qed.
End ExitM.

Lemma cell_ok_tr : ltac2:(tb__ "0|0|
S27S27S0S7S0S0S3S2dR4R1A2S2fR1S30R4S2eR3A1A2A2A2S2SfS39Q8A1A1R6R2A1R7R2A1A3F_;Fz;S28R6S29R4R3R2A3A2S28R6S29R5R4R3A3A2F_;F_;Fv;Fk;Fa;Fm';Fm;").
Proof. intros m m' a k v HE H j Hj. cbn [c_addr c_w RtCells.c_val] in *. rewrite HE by lia. exact (H j Hj). Qed.

Lemma qienv_F : ltac2:(tb__ "0|0|
S1cS6S0S0A2S12S0S0S54R5R4R3R2R1A5S40R6R5R4R3R2A5F_;Fst;Ft;Fr;Fit;FA;").
Proof. intros A it r t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17]. constructor; try assumption. lia. Qed.

Lemma inz_KO : ltac2:(tb__ "0|0|
S1cS6S0S0A2S12S0S0S40R5R4R3R2R1A5S8S60R7R5A2S4dS19S17R6A1S5fS65A1A3S37S18S5cS5bR7S57R9R8A2S55S4cS42R3A1A5S45R3A1S48R3A1A5F_;F_;Fvb;F_;Fst;Ft;Fr;Fit;FA;").
Proof.
  intros A it r t st QE vb HTOP HFp.
  apply (in_zone_ext_list r (zbQ (ag_thread (aa_geom A)) (ag_ctx (aa_geom A)) (ag_spacebeg (aa_geom A)) (fst it) (it_ab it) (topG (aa_geom A))
                                 (ag_thread (aa_geom A) + 208 + 80 * it_cls it) (ag_thread (aa_geom A) + 208 + 80 * it_cls it) (Sh (fst it))) zloQ zhiQ (if vb then ALLZ else removelast ALLZ)).
  - unfold REFOBJ_KO, ZD_KO. apply Forall2_app; [|apply Forall2_app; [|apply Forall2_app]].
    + apply (inz_ishF A it r t st QE). destruct vb; cbn; tauto.
    + apply (inz_fixF A it r); [destruct vb; cbn; tauto | destruct vb; cbn; tauto | exact HTOP | exact HFp].
    + apply (inz_rtiF A it r t st QE); destruct vb; cbn; tauto.
    + pose proof (inz_itmF A it r t st QE vb (if vb then ALLZ else removelast ALLZ) ltac:(intros z Hz; destruct vb; cbn in Hz |- *; tauto) ltac:(intros ->; cbn; tauto)) as X.
      unfold N_itmF, ZD_itmF in X. cbn [map app] in X. apply Forall2_cons_iff in X as [_ X].
      unfold N_itmF. destruct vb; cbn [tl app map] in X |- *; exact X.
  - unfold ZD_KO, ZD_fix, ZD_rti. destruct vb; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [cbn; tauto | split; [reflexivity | split; reflexivity]]).
Qed.

Lemma inVSM : ltac2:(tb__ "0|0|
S1S2S8S38S1S68R1A1S41A3ScA3S36S1R2S41A3F_;Fv;").
Proof. intros v H. apply existsb_exists in H as (x & Hx & E). apply Pos.eqb_eq in E. subst x. exact Hx. Qed.
Lemma UZ57 : ltac2:(tb__ "0|0|
S8S7S36S7R1S9S7U5S9S7U7SeS7A1A3A3A3S36S7R2S42R3A1A3F_;Fz;Fvb;").
Proof. intros vb z Hz. destruct vb; cbn in Hz |- *; tauto. Qed.

Lemma ro_XRO : ltac2:(tb__ "0|5|
S1cS12S8S24S2bS26S1aS13R3A1A2S2cS2aR1A2A2S4dS64S67R5R4A2S4eS50S6S6S6S6S15S0A2M0S0A2M1SaS6S6S0S7A2S15A2A1M2A2M3S0A2M4S50G3G4Lk;R1G1G2G1G4Lp;R2G0S0G0G4Lp0;R2S15S0SbG3S0SbG1G2SbG0S0SbS15S0R2R1A4R3A4R5A4Z0A4Llo;Lb;X6x1Lhi;Lp0;X6x1Lcs;Lp;X6x1Lk;S47R3A1A4A3F_;FG;Fg;Frho;FA0;").
Proof.
  intros A0 rho g G HR. unfold XROs, pgbS, cfcS, cfbS. destruct g; cbn [map]; repeat apply Forall_cons; try apply Forall_nil; apply (ro_cond_intro A0 (mkSC 0 0 0));
    try (unfold PG; lia); try reflexivity; try (unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  all: try (intros z Hz; split; [right; right; unfold qrtc2_zone; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia]).
  all: repeat apply Forall_cons; try apply Forall_nil.
  all: cbv beta iota; eexists; (split; [reflexivity|]); rtc_cellx HR.
Qed.

Section OutM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S44Vn;Vg;Vvb;VD;A4").

Lemma qif_out : ltac2:(tb__ "0|8|
S1cS0S0S0S7S6S0S0A2M0SaG0A1SaS1bA1M1G1S12S12SaS39Q40A1M2A1S4fS0S0S2G1S20RfA1SeS1bA1A3S2S8S1dR10A1ScA3S0S35R12R1A2S35VA0;R2A2F_;Fz;S3eVA0;R12A2S2G1S1fR13A1S9S1bS21R12S9G0ReRdA3R11A3SdS1bRcRbA3A3A3S2S0S53S11RfA1A1Vn;A3S2S0S2eS10S0S1eS34R15S11R10A1M3A2A1A2A1S51G3A1A3S2S8S3cS11R11A1M4S34R16G4A2A2Vg;A3S2S8Vvb;S63R12A1A3S40R18R13ReRbRaA5S0S4S66R1aS11R15A1M5R1A3A1S2SfS39Q8A1A1S26S1aS13R12A1R2A3S26S1aS13R11A1R2A3A3F_;Fz;S56Vn;R1aG5R11A4S62R12R16S34R1bS11R16A1A2ReRdA5S3aS1aS3dS3fVKc;A1M6VA0;Vrho0;S3bR1cS11R17A1A2R1bR19R18S9G0R17R16A3R15R14AaS43VD;A1R13R11R10A6S5S12S12S3S3aS1aS3dG6VA0;Vrho0;S3bR1eS11R19A1A2M7R1dR1bR1aS9G0R19R18A3R17R16AaS46Vvb;A1R1R13R12A6S3S54G7R19R1R11R10A5S3S1S36S1R1S41A3S4S2S1R2PceA3A1S4S2S1R3PcfA3A1S2G2S14R5R4A2S14R19R4A2A3F_;F_;F_;Fv;S3S1S69R1S61A2S2G2S14R3R2A2S14R17R2A2A3F_;Fv;S2S27S26S1aS13R1A1A2S26S1aS13R15A1A2A3A2A2A2A2Lrho7;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fw;Ftp;FrhoB;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho rhoB tp [tr [ms md]] t st HTH HCI HQW HQP HGL Hn HFULL HGR EVB QEB HVW HENV HQV H0.
  pose proof HENV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH).
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL. set (c := it_cls it) in *. set (A1 := drainA A c) in *.
  set (J := JRI (K0 Kc) A0 rho0 A1 a n0 nd (it :: its) tmp' rest).
  pose proof (JRI_stable (K0 Kc) HL A0 rho0 A1 a n0 nd (it :: its) tmp' rest) as HSTB.
  destruct (proj2 H0) as (HK1 & HCB1 & HRM1 & HFRM1). cbn [w_tr w_cfg cfg_model fst snd] in HK1, HCB1, HRM1, HFRM1.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK1) as [HG HRIG HRTC _ HST HLEN HCLS _ _ _ _ HKTOP _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG, HRTC, HST.
  destruct HRIG as (E151 & E152 & E155 & E156).
  destruct (geoM_nums A it rhoB t st QEB) as (C1 & FAv & S1 & S14 & TG & UF & R1 & ABU). cbv zeta in FAv, S1, S14, UF, R1. fold c in C1, FAv, UF, R1.
  pose proof (qf_nums A it rhoB t st QEB) as (T0 & T1 & C0 & C1' & _ & _ & _). pose proof (qf_wins A it rhoB t st QEB) as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  pose proof (qf_Sh A it rhoB t st QEB) as (SH0 & SH1 & L0 & L1).
  destruct (kchunks_facts c C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  assert (HLA : (Z.to_nat c < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI c C1) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_clsM A c HLA) in CV1.
  set (cs := cls_of A c) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *. set (pce := T + 208 + 80 * c).
  assert (HFL : length (cs_cache cs) = (Z.to_nat n + Z.to_nat n)%nat) by lia.
  assert (KEEP : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite Hn, HFL; lia).
  assert (LCA1 : Z.of_nat (length (cs_cache (drain_cs c cs))) = n) by (unfold drain_cs; cbn [cs_cache]; rewrite KEEP, length_firstn, HFL; lia).
  pose proof (cv_max _ _ _ _ _ CV1) as C_max. pose proof (cv_size _ _ _ _ _ CV1) as C_sz. pose proof (cv_count _ _ _ _ _ CV1) as C_cnt. unfold pc_entry in C_max, C_sz, C_cnt.
  fold T pce in C_max, C_sz, C_cnt. rewrite <- KMX in C_max. rewrite LCA1 in C_cnt.

  pose proof QEB as [_ _ _ _ _ _ QCVB _ _ QTB QSTB _ _ _ _ QPR _]. fold c cs in QCVB.
  set (xi := fun i : nat => nth (Z.to_nat n + i) (cs_cache cs) 0).
  assert (XIN : forall i, (i < Z.to_nat n)%nat -> nth_error (cs_cache cs) (Z.to_nat n + i) = Some (xi i)) by (intros i Hi; unfold xi; apply nth_error_nth'; lia).
  assert (NDZ_T : forall z, pce + 4 <= z < T + 4096 -> ~ DZM A c z).
  { intros z Hz HZ. unfold DZM in HZ. cbv zeta in HZ. fold SB T in HZ. rewrite FAv in HZ.
    assert (SHL : 0x7fff8000 <= Sh (SB + c * 2 ^ 32 + 3758096384)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (SB + c * 2 ^ 32 + 3758096384) 8 ltac:(unfold HIGH_SHADOW_END in S1; lia) ltac:(lia)); lia).
    unfold SHADOW_BAND_HI, HIGH_SHADOW_END in *. fold SB T in WTS, WTB. unfold pce in Hz. clear - Hz HZ C1 S1 WTS WTB SHL. lia. }
  assert (C_chk : forall i, (i < Z.to_nat n)%nat -> cell_ok (view segsA (rm rho)) (mkACell (pce + 16 + 4 * (n + Z.of_nat i)) 4 (xi i))).
  { intros i Hi. pose proof (cv_chunks _ _ _ _ _ QCVB (Z.to_nat n + i)%nat (xi i) (XIN i Hi)) as X0. unfold pc_entry in X0. fold T pce in X0.
    replace (pce + 16 + 4 * Z.of_nat (Z.to_nat n + i)) with (pce + 16 + 4 * (n + Z.of_nat i)) in X0 by lia.
    apply (cell_ok_tr (view segsA (rm rhoB))); [|exact X0]. intros z Hz. apply HVW. apply NDZ_T. unfold pce in Hz. cbn [Z.of_nat] in Hz. lia. }
  assert (HT15 : view segsA (rm rho) (fst it - 15) = Some (Z_to_bv 8 t)).
  { rewrite HVW; [exact (proj2 QTB)|]. apply (floc_outM A it rhoB t st QEB). unfold FLM. right; right; right; right; right; left.
    pose proof QEB as [_ _ _ _ QGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in QGEO. destruct QGEO as (_ & _ & _ & RZ & _ & EU & _). lia. }
  assert (HSTC : cell_ok (view segsA (rm rho)) (mkACell (T + 2784) 8 st)).
  { apply (cell_ok_tr (view segsA (rm rhoB))); [|exact (proj2 QSTB)]. intros z Hz. apply HVW. apply NDZ_T. cbn [Z.of_nat] in Hz. lia. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  set (tO := T_out n g vb (m_Ly D)).
  assert (HT : SPA segsA TJ (s_C tO) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H0) | exact I]).
  set (dsD := DSO n g pce).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Eent : eval rho entQ = Z_to_bv 64 pce).
  { apply bv_eq. unfold entQ, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC. cbn [eval]. rewrite E200, !u64_lit by (unfold pce; lia). unfold M64v.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite Z.mod_small by lia. unfold pce. lia. }
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  assert (ZT : forall z, T + 208 <= z < T + 2768 -> QRD A0 z /\ ~ (SHADOW_BAND_LO <= z < SHADOW_BAND_HI)).
  { intros z Hz. split; [left; right; left; rewrite <- EG; fold T; lia|]. fold T in WTB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear - Hz WTB. lia. }
  assert (PCEB : 0 <= pce /\ pce + 4096 < 2 ^ 62) by (unfold pce; clear - T0 T1 TG C1; lia).
  assert (ROC : Forall (ro_cond A0 rho) dsD).
  { unfold dsD, DSO. apply Forall_app. split.
    - exact (ro_XRO A0 rho g (aa_geom A) HR).
    - cbn [map]. repeat apply Forall_cons; try apply Forall_nil.
      +
        unfold chkS, ro_cond. split; [exact Eent|]. split; [unfold pce; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold pce; lia|].
        split; [unfold cells_inside, chk_cells; apply Forall_map_in; intros i Hi; apply In_idxs in Hi; cbn; lia|].
        split; [intros z Hz; apply ZT; unfold pce in Hz; lia|].
        intros z Hz. set (i := Z.to_nat ((z - (pce + 16 + 4 * n)) / 4)).
        pose proof (Z.div_pos (z - (pce + 16 + 4 * n)) 4 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (z - (pce + 16 + 4 * n)) 4 n ltac:(lia) ltac:(lia)) as D1.
        pose proof (Z.div_mod (z - (pce + 16 + 4 * n)) 4 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (z - (pce + 16 + 4 * n)) 4 ltac:(lia)) as MB.
        assert (Hi : (i < Z.to_nat n)%nat) by (unfold i; lia).
        exists (16 + 4 * (n + Z.of_nat i)), 4%nat, (vCHq i), (xi i).
        split; [unfold chk_cells; apply in_map_iff; exists i; split; [reflexivity | unfold idxs; apply in_seq; lia]|].
        split; [unfold i; rewrite Z2Nat.id by lia; cbn [Z.of_nat]; lia|].
        split; [unfold vCHq; cbn [eval]; exact (ECH i Hi)|].
        replace (pce + (16 + 4 * (n + Z.of_nat i))) with (pce + 16 + 4 * (n + Z.of_nat i)) by lia. exact (C_chk i Hi).
      + unfold mcS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists (2 * n). split; [reflexivity | exact C_max].
      + unfold cntS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists n. split; [reflexivity|]. replace (pce + 0) with pce by lia. exact C_cnt.
      + unfold szMS. apply (ro_cond_intro A0 (mkSC 0 0 0)); [exact Eent | clear - PCEB; lia | clear; lia | clear; lia | clear; lia | clear - PCEB; lia | | | reflexivity | ].
        * unfold cells_inside. repeat apply Forall_cons; try apply Forall_nil. cbn. clear. lia.
        * intros z Hz. apply ZT. unfold pce in Hz. clear - Hz C1. lia.
        * repeat apply Forall_cons; try apply Forall_nil. exists (Size c). split; [cbn [eval]; exact E201 | exact C_sz]. }
  assert (HOBJ : ss_objs (ax_S (s_C tO)) = keepN (s_C tO) (s_k tO) ++ map dobj dsD) by exact (c_outobjs n g vb D HC pce).
  set (vals := [Z_to_bv 64 n; Z_to_bv 64 (2 * n)]).
  set (rho3 := rho_absorb rho (map dobj dsD) (vms md tp ms)) in *.
  set (rho4 := rho_sets rho3 (combine (s_bs tO) vals)).
  assert (OT : forall v, v <> 206%positive -> v <> 207%positive -> rw rho4 v = rw rho v).
  { intros v N6 N7. unfold rho4. rewrite rho_sets_other; [reflexivity|]. unfold tO, T_out, vals. cbn [s_bs combine map fst In]. intros [X0|[X0|[]]]; congruence. }
  assert (NDB : List.NoDup (map fst (combine (s_bs tO) vals))) by (unfold tO, T_out, vals; cbn [s_bs combine map fst]; repeat constructor; cbn [In]; intuition congruence).
  assert (G206 : rw rho4 206%positive = Z_to_bv 64 n) by (apply (rho_sets_get _ rho3 _ _ NDB); unfold tO, T_out, vals; cbn [s_bs combine In]; tauto).
  assert (G207 : rw rho4 207%positive = Z_to_bv 64 (2 * n)) by (apply (rho_sets_get _ rho3 _ _ NDB); unfold tO, T_out, vals; cbn [s_bs combine In]; tauto).
  destruct (s_step (K0 Kc) HL A0 rho0 (zbMq A it) zloQ zhiM (ZUM vb) (zsepMq A it rhoB t st QEB vb EVB) tO J dsD vals A1 rho tp tr ms md
              (c_out n g vb D HC) HSTB HQW HOBJ eq_refl HT HK1 HFRM1 ROC) as (rho5 & H5 & V5 & RM5 & AG5 & EV5).
  { intros HK3 HF3 EV3. fold rho3 in HK3, HF3, EV3. fold rho3. fold rho4.
    assert (HK4 : K0 Kc A1 rho4 tp tr md).
    { apply (kq_stable segsA (K0 Kc) HL A1 rho3 rho4 tp tr md md); [|apply mat_equiv_refl | exact HK3]. split; [|split].
      - intros v Hv. symmetry. unfold QNPRE in Hv. apply OT; lia.
      - intros l0. unfold rho4. rewrite (proj1 (rho_sets_rl_rm _ rho3)). reflexivity.
      - intros x. unfold rho4. rewrite (proj2 (rho_sets_rl_rm _ rho3)). reflexivity. }
    assert (ERM4 : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
    assert (HQV4 : QIV rho4 it (cls_of A1 c) t st).
    { unfold A1. rewrite (drainA_clsM A c HLA). fold cs. unfold QIV in HQV |- *. cbv zeta in HQV |- *. fold c cs in HQV |- *.
      destruct HQV as (V165 & V200 & V201 & V202 & V203 & V204 & V205 & _ & _ & V209 & V210).
      rewrite LCA1, <- KMX, G206, G207. rewrite (OT 165%positive), (OT 200%positive), (OT 201%positive), (OT 202%positive), (OT 203%positive), (OT 204%positive), (OT 205%positive), (OT 209%positive), (OT 210%positive) by discriminate.
      cbn [cs_mapped_user drain_cs]. repeat split; assumption. }
    assert (QE4 : qienv A1 it rho4 t st).
    { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip.qienv_of_K (K0 Kc) HL A1 a s n0 nd it its tmp' rest rho4 tp tr md t st HTH HCI HGL QPR); [| exact HK4 | rewrite ERM4, EV3; exact HCB1 | exact HQV4 | exact (proj1 QTB) | rewrite ERM4, EV3; exact HT15 | exact (proj1 QSTB) | rewrite ERM4, EV3; exact HSTC].
      fold c. unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite LCA1, <- KMX. lia. }
    pose proof (qienv_F A1 it rho4 t st QE4) as QF4.
    assert (HTOP4 : top_high A1 rho4) by (unfold top_high in *; rewrite !OT by (unfold V_DEPTH; lia); exact HKTOP).
    assert (HFpre1 : Forall (holds rho) (pre_facts DEPTH_R)).
    { pose proof (SPA_facts_hold segsA _ rho (m_Ly D) tp _ H0) as HFa. apply Forall_forall. intros f Hf.
      pose proof (proj1 (forallb_forall _ _) (c_Lypre n g vb D HC) f Hf) as X. apply existsb_exists in X as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'. exact (proj1 (Forall_forall _ _) HFa f Hf'). }
    assert (HFpre4 : Forall (holds rho4) (pre_facts DEPTH_R)).
    { apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho rho4 f0); [| exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFpre1 f0 Hf0)].
      split; [intros v Hv; symmetry; apply OT; unfold NPRE in *; lia | intros l0; unfold rho4; rewrite (proj1 (rho_sets_rl_rm _ rho3)); reflexivity]. }
    pose proof (qe_E A1 it rho4 t st QE4) as (_ & _ & _ & Erie & Eent4 & Eslot & _). change (aa_geom A1) with (aa_geom A) in Erie, Eent4, Eslot. fold c SB T in Erie, Eent4, Eslot. fold pce in Eent4, Eslot.
    unfold A1 in Eslot. rewrite (drainA_clsM A c HLA) in Eslot. fold cs in Eslot. rewrite LCA1 in Eslot.
    split; [split; [exact HK3 | split; [rewrite EV3; exact HCB1 | split; [rewrite EV3; exact HRM1 | exact HF3]]]|].
    split.
    { pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip.carve_itm A1 it rho4 t st QE4 vb ltac:(intros X0; rewrite EVB in X0; unfold vb_of in X0; apply negb_true_iff in X0; apply Z.eqb_neq in X0; exact X0)) as CI.
      unfold N_itm in CI. cbn [app] in CI. apply Forall_cons_iff in CI as [CI0 CI]. apply Forall_cons_iff in CI as [_ CI]. apply Forall_cons_iff in CI as [CI2 CI]. apply Forall_cons_iff in CI as [CI3 _].
      unfold tO, T_out, N_OUT. cbn [s_N]. repeat apply Forall_cons; try apply Forall_nil; [exact CI0 | exact CI2 | exact CI3]. }
    split.
    { unfold tO, T_out, N_OUT, ZD_OUT, rieS0, entG, slotG. cbn [s_N s_ZDn map carve_obj]. repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
      all: split; [apply UZ57; cbn; tauto|]. all: split; [cbn; lia|]. all: split; [cbn; lia|]. all: right.
      all: unfold carved; rewrite obj_range_mk by lia; unfold zbMq; cbn [fst snd zbM zbQ]; fold SB T c; fold pce; unfold UE in *; rewrite ?Erie, ?Eent4, ?Eslot; lia. }
    split.
    { exact (in_zone_same rho4 _ _ _ _ _ (REFOBJ_KO vb) (ZD_KO vb) (c_outK n g vb D HC) (inz_KO A1 it rho4 t st QF4 vb HTOP4 HFpre4)). }
    intros _. unfold tO, T_out, F_OUT. cbn [s_F]. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken eval]. rewrite G207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
    - cbn [holds eval]. rewrite G206, G207, !u64_lit by lia. lia.
    - cbn [holds eval]. rewrite G207, !u64_lit by lia. lia. }
  fold rho3 in RM5, EV5. fold rho4 in V5, AG5.
  assert (VV5 : forall v, In v VSM -> rw rho5 v = rw rho4 v).
  { intros v Hv. rewrite (V5 v (SVar v)); [reflexivity|]. unfold tO, T_out. cbn [s_M]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  assert (ERM5 : view segsA (rm rho5) = view segsA (rm rho)) by (rewrite RM5; exact EV5).
  exists rho5. split; [exact H5|]. split; [|split; [intros v Hv N6 N7; rewrite (VV5 v Hv); exact (OT v N6 N7) | split; [|exact ERM5]]].
  -
    destruct (proj2 H5) as (HK5 & HCB5 & _). cbn [w_tr w_cfg cfg_model fst snd] in HK5, HCB5.
    assert (HQV5 : QIV rho5 it (cls_of A1 c) t st).
    { unfold A1. rewrite (drainA_clsM A c HLA). fold cs. unfold QIV in HQV |- *. cbv zeta in HQV |- *. fold c cs in HQV |- *.
      destruct HQV as (V165 & V200 & V201 & V202 & V203 & V204 & V205 & _ & _ & V209 & V210).
      rewrite (VV5 165%positive (inVSM 165%positive eq_refl)), (VV5 200%positive (inVSM 200%positive eq_refl)), (VV5 201%positive (inVSM 201%positive eq_refl)), (VV5 202%positive (inVSM 202%positive eq_refl)), (VV5 203%positive (inVSM 203%positive eq_refl)),
              (VV5 204%positive (inVSM 204%positive eq_refl)), (VV5 205%positive (inVSM 205%positive eq_refl)), (VV5 206%positive (inVSM 206%positive eq_refl)), (VV5 207%positive (inVSM 207%positive eq_refl)), (VV5 209%positive (inVSM 209%positive eq_refl)), (VV5 210%positive (inVSM 210%positive eq_refl)).
      rewrite LCA1, <- KMX, G206, G207. rewrite (OT 165%positive), (OT 200%positive), (OT 201%positive), (OT 202%positive), (OT 203%positive), (OT 204%positive), (OT 205%positive), (OT 209%positive), (OT 210%positive) by discriminate.
      cbn [cs_mapped_user drain_cs]. repeat split; assumption. }
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip.qienv_of_K (K0 Kc) HL A1 a s n0 nd it its tmp' rest rho5 tp tr md t st HTH HCI HGL QPR); [| exact HK5 | exact HCB5 | exact HQV5 | exact (proj1 QTB) | rewrite ERM5; exact HT15 | exact (proj1 QSTB) | rewrite ERM5; exact HSTC].
    fold c. unfold A1. rewrite (drainA_clsM A c HLA). fold cs. rewrite LCA1, <- KMX. lia.
  - intros v Hv. rewrite <- (proj1 AG5 v Hv). apply OT; unfold NPRE in Hv; lia.
Qed.
End OutM.
End SegQIF_exit.

(* [comment removed for export] *)
Module SegQIF_mid.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "prod"; "true"; "nil"; "nat"; "app"; "length"; "pair"; "snd"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "budget_bound"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "cs_cache"; "mkQB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env"; "qienvF"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "HVI"; "HVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "TRP"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "is_primary"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "qienv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue"; "ENVM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "PostD"; "PreD"; "S7"; "m_S0"; "mcert"; "mdata"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_mid.MidT"; "MID_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_mid"; "QEV"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_cont.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.SegQCF_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m0.SegQIF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_cont OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QEV : list positive := ltac2:(tb__ "0|0|
S2S1P97S2S1P98S2S1P9bS2S1P9cS2S1Pa5S2S1Pc8S2S1Pc9S2S1PcaS2S1PcbS2S1PccS2S1PcdS2S1PceS2S1PcfS2S1Pd1S2S1Pd2S7S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma qienvF_agreeL : ltac2:(tb__ "0|0|
S15S5S0S0A2S10S10S0S0S1fR6R5R4R2R1A5S1S33S1R1S46A3SdS20Q40A1S12R6R2A2S12R7R2A2A3F_;Fi;SdS2aS29SeS11R5A1A2S29SeS11R6A1A2A3S1fR9R8R6R5R4A5F_;F_;F_;Fst;Ft;Fr';Fr;Fit;FA;").
Proof.
  intros A it r r' t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17] HRW HRM.
  constructor; rewrite ?HRM; try assumption.
  - destruct Q4 as (E151 & E152 & E155 & E156). repeat split; rewrite HRW by (unfold QEV; cbn; tauto); assumption.
  - unfold QIV in *. cbv zeta in *. destruct Q6 as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
    repeat split; rewrite HRW by (unfold QEV; cbn; tauto); assumption.
Qed.

Section MidT.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJI : ltac2:(tb__ "0|1|
S15S0S0S8S4S5S0S0A2A1S4S14A1M0G0S31VQ;VX;S1dS28VKc;A1VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.

Hypothesis HDC : ltac2:(tb__ "0|2|
S0S3S15S0S10S4S20Q40A1A1S33S0R6S36A3SdS3R6S6A3S34S16R6A1S25A2F_;S32VQ;VX;S1cSeS37R8R7R6VKc;R5A5S40R8R7A2M0R4R3A5S24SeS13S22G0A1A1R4R3S2S5S21S23A2M1SbS21S23S3fR8R7A2S38R6VKc;R5A3A4S7G1A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;").

Definition MID_stmt (n : Z) (g vb : bool) (D : mdata) : Prop := ltac2:(tb__ "0|6|
S15S0S0S0S8S5S0S0A2M0S4G0A1S4S14A1M1S10S4S20Q40A1A1M2S0S0SdG1S19RcA1S7S14A1A3SdS3S17RdA1S6A3S0S2eRfR1A2S2eVA0;R2A2F_;Fz;S1eVA0;RfA2SdG1S18R10A1S2S14S1bRfS2G0RbRaA3ReA3S9S14R9Vrest;A3A3A3SdS3S39ScS0S0RcA3A1S6A3SdS0S3bSfRdA1A1Vn;A3SdS0S35SaS0S1aS2fR13SfReA1M3A2A1A2A1S3aG3A1A3SdS3S27SfRfA1M4S2fR14G4A2A2Vg;A3SdS3Vvb;S3cR10A1A3SdS3Vg;S6A3S34S16R17A1S25A2F_;S3eVn;R17SfR12A1RfA4S1fR18R13R10ReRdA5S2dR11R12A2S2bR12R19R17R16R15A5S2cR13R1aR17R16A4S10G2S3dS26R1eSfR19A1A2R19R2R14R13A5S2dR3R18A2S2bR4R1fR1dR1cR1bA5S2cR5R20R1dR1cA4S30VQ;VX;S1cSeS1dS28VKc;A1M5VA0;Vrho0;S26R22SfR1dA1A2R21R1fR1eS2G0R1dR1cA3R1bVrest;AaS41Vvb;A1R6R5A5A3F_;F_;F_;F_;FtpL;Frho7;S30VQ;VX;S1cSeS1dG5VA0;Vrho0;R1dR1cR1aR19S2G0R18R17A3R16Vrest;AaS42VD;A1R15R14A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").

Theorem mid : ltac2:(tb__ "0|0|
S0S3S3S44S43R4R3R2R1A4S45R5R4R3R2A4F_;FD;Fvb;Fg;Fn;").
Proof.
  intros n g vb D HC A a s n0 nd it its tmp' rho tp t st HTH HCI HQW HQP HGL HPR Hn HFULL HGR EVB HB HENV QE HVx HVi HVs HCt.
  set (c := it_cls it) in *. set (J := JRI (K0 Kc) A0 rho0 A a n0 nd (it :: its) tmp' rest). set (A1 := drainA A c) in *.
  set (J1 := JRI (K0 Kc) A0 rho0 A1 a n0 nd (it :: its) tmp' rest).
  pose proof QE as [_ _ _ _ QGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in QGEO. destruct QGEO as (C1 & _). fold c in C1.
  assert (HNS : In n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.DRAIN_NS) by (rewrite <- Hn; exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.kchunks_cases c C1)).
  destruct (kchunks_facts c C1) as (KC & _). rewrite Hn in KC.

  apply (seg_M1 n g vb D HC X J rho tp (HJI _ _ _ _ _ _ _)). intros rho1 HKp1.
  assert (K1 : forall v, In v VSM -> rw rho1 v = rw rho v) by (intros v Hv; exact (keepsM_id VSM rho rho1 v HKp1 Hv)).
  assert (L1 : forall v, (v < NPRE)%positive -> rw rho1 v = rw rho v) by (intros v Hv; symmetry; exact (proj1 (proj1 HKp1) v Hv)).
  assert (RM1 : rm rho1 = rm rho) by exact (keeps_rm _ rho rho1 HKp1).
  assert (KQ1 : forall i, In i (QEV ++ [162; 163; 164; 166; 184; 185; 186; 187; 208]%positive) -> rw rho1 i = rw rho i).
  { intros i Hi. destruct (Pos.ltb_spec i NPRE) as [L|L]; [exact (L1 i L)|]. apply K1. unfold VSM, QEV, NPRE in *. cbn in Hi |- *. first [ revert Hi; clear - L; intros Hi; intuition (subst; try lia; tauto) | intuition (subst; try lia; tauto) ].     }
  assert (QE1 : qienvF A it rho1 t st) by (apply (qienvF_agreeL A it rho rho1 t st QE); [intros i Hi; apply KQ1; apply in_or_app; left; exact Hi | rewrite RM1; reflexivity]).
  assert (HENV1 : ENVM n A c rho1).
  { destruct HENV as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH). unfold ENVM. cbv zeta.
    rewrite !K1 by (unfold VSM; cbn; tauto). split; [exact E200|]. split; [exact E201|]. split; [exact E221|]. split; [exact E222|]. split; [exact E223|]. split; [exact E224|]. split; [exact E225|].
    intros i Hi. rewrite K1; [exact (ECH i Hi)|]. assert (Ei : (i <= 7)%nat) by lia. unfold VSM. do 8 (destruct i as [|i]; [first [ repeat match goal with H : _ |- _ => clear H end; cbn; tauto | cbn; tauto ] |]).     lia. }
  assert (E208 : rw rho1 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite K1 by (unfold VSM; cbn; tauto); exact (proj2 (proj2 (proj2 (proj2 HVx))))).

  apply (qif_call Kc HKc A0 rho0 X n g vb D HC (fun A' c' r1 t1 HB' => HDC n g A' c' r1 t1 HNS HB') A a s n0 nd it its tmp' rest rho1 tp t st HTH HCI HQP HGL Hn HFULL HGR EVB HB HENV1 QE1 E208).
  intros rho5 tpL AG5 VO5 VB5. fold c A1 J1 in VO5 |- *.
  assert (R5 : forall v, (v < NXM)%positive -> rw rho5 v = rw rho1 v) by (intros v Hv; symmetry; apply (proj1 AG5); rewrite (proj2 (proj2 (proj2 (proj2 (c_XF0 n g vb D HC))))); exact Hv).

  apply (tr_conseq X _ (SPA segsA J1 (m_Lx D) rho5 tpL)); [intros w Hw; exact (SPA_axforms segsA J1 _ rho5 _ _ tpL w (c_Lx n g vb D HC) Hw)|].
  assert (HENV5 : ENVM n A c rho5).
  { destruct HENV1 as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH). unfold ENVM. cbv zeta.
    rewrite !R5 by (unfold NXM; lia). split; [exact E200|]. split; [exact E201|]. split; [exact E221|]. split; [exact E222|]. split; [exact E223|]. split; [exact E224|]. split; [exact E225|].
    intros i Hi. rewrite R5; [exact (ECH i Hi)|]. unfold NXM. lia. }
  apply (tr_glue X _ J1 (m_Ly D) tpL (fun r => (forall i, rw r i = rw rho5 i)
            /\ (forall z, ~ (region_info (ag_spacebeg (aa_geom A)) c <= z < region_info (ag_spacebeg (aa_geom A)) c + 128) -> view segsA (rm r) z = view segsA (rm rho5) z))).
  { intros w Hw. destruct (qif_x1 Kc HKc A0 rho0 n g vb D HC A a s n0 nd it its tmp' rest rho5 tpL w HTH HCI HQP HGL C1 Hn HFULL HGR HENV5 Hw) as (rho6 & H6 & RW6 & V6).
    exists rho6. split; [exact H6|]. split; [exact RW6 | exact V6]. }
  intros rho6 (RW6 & V6).

  assert (HVW6 : forall z, ~ DZM A c z -> view segsA (rm rho6) z = view segsA (rm rho1) z).
  { intros z Hz. rewrite V6; [apply VO5; intros HZ; exact (Hz (dzone_M A it rho1 t st QE1 z HZ))|].
    intros HR. apply Hz. unfold DZM. cbv zeta. right; left.
    destruct (geoM_nums A it rho1 t st QE1) as (_ & FAv & _). cbv zeta in FAv. fold c in FAv. rewrite FAv.
    unfold region_info, kRegionInfoStride in HR. rewrite kSpaceSize_val in HR. clear - HR C1. lia. }
  assert (HENV6 : ENVM n A c rho6).
  { destruct HENV5 as (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH). unfold ENVM. cbv zeta.
    rewrite !RW6. split; [exact E200|]. split; [exact E201|]. split; [exact E221|]. split; [exact E222|]. split; [exact E223|]. split; [exact E224|]. split; [exact E225|].
    intros i Hi. rewrite RW6. exact (ECH i Hi). }
  assert (HQV6 : QIV rho6 it (cls_of A c) t st).
  { pose proof (qf_hv A it rho1 t st QE1) as HQV. unfold QIV in HQV |- *. cbv zeta in HQV |- *. rewrite !RW6, !R5 by (unfold NXM; lia). exact HQV. }
  apply (tr_glue X _ J1 (S7 vb) tpL (fun r => qienv A1 it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (qif_out Kc HKc A0 rho0 n g vb D HC A a s n0 nd it its tmp' rest rho6 rho1 tpL w t st HTH HCI HQW HQP HGL Hn HFULL HGR EVB QE1 HVW6 HENV6 HQV6 Hw) as (rho7 & H7 & QE7 & KV7 & KL7 & EV7).
    exists rho7. split; [exact H7|]. split; [exact QE7|].
    assert (K7 : forall i, In i [162; 163; 164; 165; 166; 184; 185; 186; 187; 208]%positive -> rw rho7 i = rw rho i).
    { intros i Hi. rewrite KV7; [| unfold VSM; cbn in Hi |- *; intuition (subst; tauto) | cbn in Hi; intuition (subst; lia) | cbn in Hi; intuition (subst; lia)].
      rewrite RW6, R5 by (unfold NXM; cbn in Hi; intuition (subst; lia)). apply KQ1. unfold QEV. cbn in Hi |- *. first [ revert Hi; repeat match goal with H : _ |- _ => clear H end; intros Hi; intuition (subst; tauto) | intuition (subst; tauto) ]. }
    destruct HVx as (E184 & E185 & E186 & E187 & E208'). destruct HVi as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !K7 by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !K7 by (cbn; tauto); tauto|].
    destruct w as [tr7 [ms7 md7]]. destruct (proj2 H7) as (_ & HCB7 & _). cbn [w_tr w_cfg cfg_model fst snd] in HCB7. destruct HCB7 as (_ & _ & _ & _ & HITM).
    destruct (HITM 0%nat it eq_refl) as [X0 _]. unfold HVS. replace (a + 24 + 8 * (Z.of_nat nd + Z.of_nat 0)) with (a + 24 + 8 * Z.of_nat nd) in X0 by lia. exact X0. }
  intros rho7 (QE7 & HV7 & HI7 & HS7). exact (HCt rho7 tpL QE7 HV7 HI7 HS7).
Qed.
End MidT.
End SegQIF_mid.

(* [comment removed for export] *)
Module SegQIF_top.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "prod"; "nil"; "nat"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "budget_bound"; "class_fresh"; "qbatch"; "@Corelib.Init.Logic"; "eq"; "True"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "QP"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs"; "SIDEQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "qienv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "mdata"; "PostD"; "PreD"; "mcert"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis"; "QI_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_mid"; "QEV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "JOK"; "TRP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_mid OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma SIDEQ_vars : ltac2:(tb__ "0|0|
S3SaSaS0S19S0R1S2S0PdS2S0P9bS2S0P9eS2S0P94S2S0P8aS2S0P8bS2S0P8dS2S0P91S2S0P92S6S0A1A3A3A3A3A3A3A3A3A3A3S12S18Q40A1SbR3R2A2SbR4R2A2A3F_;Fv;S24R4R3A2S24R5R3A2F_;F_;Fr';Fr;Fvb;").
Proof.
  intros vb r r' HE (x & d & H). exists x, d. unfold QI_side in *.
  assert (E : forall i, In i [13; 155; 158; 148; 138; 139; 141; 145; 146]%positive -> bv_unsigned (rw r' i) = bv_unsigned (rw r i)) by (intros i Hi; rewrite (HE i Hi); reflexivity).
  assert (EB : bv_unsigned (eval r' (bgv vb)) = bv_unsigned (eval r (bgv vb))) by (destruct vb; cbn [bgv eval]; unfold vAB; cbn [eval]; apply E; cbn; tauto).
  cbv zeta in *. unfold V_CLS, V_SIZE in *. rewrite !E by (cbn; tauto). rewrite EB. exact H.
Qed.
Lemma QP_drainM : ltac2:(tb__ "0|0|
SeSeS1S22R3R2A2S16S10R4R2A2A1S22R5S2dR4R3A2A2F_;F_;Fc;FA;FA0;").
Proof.
  intros A0 A c (E & EL & EF) NF. split; [|split].
  - unfold same_but_qcs in *. rewrite E. unfold drainA. cbn. reflexivity.
  - unfold drainA. cbn [aa_cls]. rewrite length_list_upd. exact EL.
  - intros c' Hc'. unfold drainA. cbn [aa_cls]. rewrite nth_list_upd_other; [exact (EF c' Hc')|].
    intros X0. apply NF. unfold class_fresh in *. apply Nat2Z.inj in X0 || idtac. congruence.
Qed.

Lemma qienv_agreeL : ltac2:(tb__ "0|0|
SeS5S1S1A2SaSaS1S1S25R6R5R4R2R1A5S0S19S0R1S32A3S12S18Q40A1SbR6R2A2SbR7R2A2A3F_;Fi;S12S21S20S17ScR5A1A2S20S17ScR6A1A2A3S25R9R8R6R5R4A5F_;F_;F_;Fst;Ft;Fr';Fr;Fit;FA;").
Proof.
  intros A it r r' t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17] HRW HRM.
  constructor; rewrite ?HRM; try assumption.
  - destruct Q4 as (E151 & E152 & E155 & E156). repeat split; rewrite HRW by (cbn; tauto); assumption.
  - unfold QIV in *. cbv zeta in *. destruct Q6 as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
    repeat split; rewrite HRW by (cbn; tauto); assumption.
Qed.

Section QIFTop.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJI : ltac2:(tb__ "0|1|
SeS1S1S7S4S5S1S1A2A1S4S11A1M0G0S33VQ;VX;S23S1fVKc;A1VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Hypothesis HBUD : budget_bound A0 <= LIMIT.

Hypothesis HDC : ltac2:(tb__ "0|2|
S1S3SeS1SaS4S18Q40A1A1S19S1R6S2cA3S12S3R6S9A3S1aSfR6A1S2bA2F_;S34VQ;VX;S2aS17S2eR8R7R6VKc;R5A5S28R8R7A2M0R4R3A5S1eS17SdS1cG0A1A1R4R3S2S5S1bS1dA2M1S8S1bS1dS27R8R7A2S2fR6VKc;R5A3A4S6G1A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;").

Lemma cert_ex : ltac2:(tb__ "0|0|
S1S3S3S14S1aZ1R3A2S1aR3Z1eA2A2S15S26S26S29S30R5A1R4R3R1A4LD;A2F_;Fvb;Fg;Fc;").
Proof.
  intros c g vb Hc. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.kchunks_cases c Hc) as HN. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.DRAIN_NS in HN. cbn [In] in HN.
  destruct HN as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E.
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m1.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m1.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m2.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m2.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m3.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m3.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m4.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m4.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m5.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_m5.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m6.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m6.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m8.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_m8.cert_of g vb).
Qed.

Theorem qi_full_step : ltac2:(tb__ "0|0|
S31S1fVKc;A1VA0;Vrho0;VQ;VX;Vrest;S4S18Q40A1A1S13L_;A7").
Proof.
  intros A a n0 nd it its tmp' rho tp _ HI HVx HVi HVs EPR HFL HC.
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6). pose proof (K0_laws Kc HKc) as HL.
  set (c := it_cls it). set (J := JRI (K0 Kc) A0 rho0 A a n0 nd (it :: its) tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 c /\ Z.of_nat (length (cs_cache (cls_of A c))) = max_count c /\ 1 <= c <= 30)).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK.
    split; [exact (cls_item_not_fresh (K0 Kc) HL A0 A a s it its (tmp' ++ rest) rho tp tr md I1 I2 I4 HK I5 EPR)|].
    destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG _ _ _ _ _ HCLS _ _ _ _ _ _].
    pose proof (benv_of_K (K0 Kc) HL A I2 rho tp tr md HK) as BE. destruct BE as [_ _ HQP HAU _ _ _].
    assert (HIN : In it (qitems (qall A))) by (rewrite (qall_A1 A I1), I5; unfold qitems; cbn [flat_map qb_items app]; left; reflexivity).
    pose proof (item_slot A HQP HAU HG it HIN EPR) as IS. cbv zeta in IS. destruct IS as (C1 & _). fold c in C1.
    pose proof (cv_len _ _ _ _ _ (HCLS I2 c C1)) as KL. fold c in HFL. split; [lia | exact C1]. }
  intros (NFR & HFULL & C1). set (n := kchunks c). set (g := drain_grows c (cls_of A c)). set (vb := vb_of it).
  destruct (cert_ex c g vb C1) as (D & HCm). fold n in HCm.
  assert (HBG : g = true -> budget_bound A <= LIMIT).
  { intros _. destruct I4 as (ESB & _). unfold same_but_qcs in ESB. unfold budget_bound. rewrite ESB. cbn [aa_V aa_Km aa_Kf]. exact HBUD. }
  assert (NB : forall i, (i < 200)%positive \/ i = 208%positive -> ~ In i BLQ) by (intros i Hi Y; unfold BLQ in Y; cbn in Y; lia).

  apply (tr_glue X _ J (CqiP vb) tp (fun r => exists t st, qienvF A it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (qip_pre (K0 Kc) HL A0 rho0 A a s n0 nd it its tmp' rest rho tp w I1 I2 I3 I5 EPR ltac:(fold c; lia) Hw HVi HVs) as (rho2 & t & st & Hs & QE & OTH & EV).
    exists rho2. split; [exact Hs|]. exists t, st. split; [exact QE|].
    destruct HVx as (E184 & E185 & E186 & E187 & E208). destruct HVi as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !OTH by (apply NB; lia); tauto|]. split; [unfold HVI; rewrite !OTH by (apply NB; lia); tauto|].
    unfold HVS. rewrite EV. exact HVs. }
  intros rhoE (t & st & QE & HVe & HIe & HSe).

  apply (qip_call X vb J rhoE tp (HJI _ _ _ _ _ _ _)).
  { pose proof QE as [HG _ _ HRIG HGEO HV _ _ _ [Ht1 _] _ _ HQP HAU HIN HPR HMU].
    apply (SIDEQ_vars vb (rho_sub rhoE (sQ vb))); [|eapply (qi_side A); eassumption].
    intros v Hv. cbn [rw rho_sub]. rewrite (sP_sQ vb v Hv). reflexivity. }
  intros rho' Hag.
  assert (AGV : forall i, (i < 216)%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  assert (ERM : rm rho' = rm rhoE) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  pose proof (qienvF_agree A it rhoE rho' t st QE AGV ERM) as QE'.
  assert (HV' : HVX rho' tmp') by (destruct HVe as (E184 & E185 & E186 & E187 & E208); unfold HVX; rewrite !AGV by lia; tauto).
  assert (HI' : HVI rho' a n0 nd it) by (destruct HIe as (E162 & E163 & E164 & E165 & E166); unfold HVI; rewrite !AGV by lia; tauto).
  assert (HS' : HVS rho' a nd it) by (unfold HVS; rewrite ERM; exact HSe).

  apply (tr_glue X _ J (m_S0 D) tp (fun r => ENVM n A c r /\ qienvF A it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (qif_in Kc HKc A0 rho0 n g vb D HCm A a s n0 nd it its tmp' rest rho' tp w t st I1 I2 I3 I4 I5 eq_refl HFULL eq_refl eq_refl Hw QE') as (rho2 & H2 & HE & KV & KL & EV2).
    exists rho2. split; [exact H2|]. split; [exact HE|].
    assert (KQ : forall i, In i (QEV ++ [162; 163; 164; 166; 184; 185; 186; 187; 208]%positive) -> rw rho2 i = rw rho' i).
    { intros i Hi. destruct (Pos.ltb_spec i NPRE) as [L|L]; [exact (KL i L)|]. apply KV.
      - unfold VSM. unfold QEV, NPRE in *. cbn in Hi |- *. first [ revert Hi; clear - L; intros Hi; intuition (subst; try lia; tauto) | intuition (subst; try lia; tauto) ].
      - intros X0. destruct (BSM_range n i ltac:(destruct (kchunks_facts c C1); fold n; lia) X0) as [[Y _]|[Y _]]; unfold QEV in Hi; cbn in Hi; intuition (subst; lia). }
    split; [apply (qienvF_agreeL A it rho' rho2 t st QE'); [intros i Hi; apply KQ; apply in_or_app; left; exact Hi | exact EV2]|].
    destruct HV' as (E184 & E185 & E186 & E187 & E208). destruct HI' as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !KQ by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !KQ by (cbn; tauto); tauto|].
    unfold HVS. rewrite EV2. exact HS'. }
  intros r2 (HE2 & QE2 & HV2 & HI2 & HS2).

  apply (mid Kc HKc A0 rho0 X HJI rest HDC n g vb D HCm A a s n0 nd it its tmp' r2 tp t st I1 I2 I3 I4 I5 EPR eq_refl HFULL eq_refl eq_refl HBG HE2 QE2 HV2 HI2 HS2).
  intros rho7 tpL QE7 HV7 HI7 HS7. fold c in QE7 |- *.
  set (A1 := drainA A c) in *. set (J1 := JRI (K0 Kc) A0 rho0 A1 a n0 nd (it :: its) tmp' rest).

  apply (seg_T8 X vb J1 rho7 tpL (HJI _ _ _ _ _ _ _)). intros Tx M rho8 HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  assert (K8 : forall i, In i (QEV ++ [162; 163; 164; 166; 184; 185; 186; 187; 208]%positive) -> rw rho8 i = rw rho7 i).
  { intros i Hi. destruct (Pos.ltb_spec i NPRE) as [L|L]; [symmetry; exact (proj1 (proj1 HKp) i L)|]. apply (keepsM_id VK7 rho7 rho8 i HKp).
    unfold VK7, QEV, NPRE in *. cbn in Hi |- *. first [ revert Hi; clear - L; intros Hi; intuition (subst; try lia; tauto) | intuition (subst; try lia; tauto) ].     }
  assert (QE8 : qienv A1 it rho8 t st) by (apply (qienv_agreeL A1 it rho7 rho8 t st QE7); [intros i Hi; apply K8; apply in_or_app; left; exact Hi | rewrite (keeps_rm _ rho7 rho8 HKp); reflexivity]).
  pose proof (HVX_keep VK7 rho7 rho8 tmp' HKp ltac:(unfold VK7; cbn; tauto) HV7) as HV8.
  assert (HI8 : HVI rho8 a n0 nd it) by (destruct HI7 as (E162 & E163 & E164 & E165 & E166); unfold HVI; rewrite !K8 by (cbn; tauto); tauto).
  pose proof (HVS_keep _ rho7 rho8 a nd it HKp HS7) as HS8.
  apply (tr_glue X _ J1 (TQIf vb) tpL (fun r => qienv A1 it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (entM_SPA J1 (E8 vb) (TQIf vb) (idm VK7) rho8 tpL w (E8_ent vb) (tr_stable X _ (HJI _ _ _ _ _ _ _)) Hw) as (H9 & AG9 & V9 & RM9).
    eexists. split; [exact H9|].
    assert (K9 : forall i, In i (QEV ++ [162; 163; 164; 166; 184; 185; 186; 187; 208]%positive) -> rw (rho_sub rho8 (infer_sub NPRE (ax_S (E8 vb)) (ax_S (TQIf vb)))) i = rw rho8 i).
    { intros i Hi. destruct (Pos.ltb_spec i NPRE) as [L|L]; [symmetry; exact (proj1 AG9 i L)|]. rewrite (V9 i (SVar i)); [reflexivity|].
      unfold idm. apply in_map_iff. exists i. split; [reflexivity|]. unfold VK7, QEV, NPRE in *. cbn in Hi |- *. first [ revert Hi; clear - L; intros Hi; intuition (subst; try lia; tauto) | intuition (subst; try lia; tauto) ].     }
    split; [apply (qienv_agreeL A1 it rho8 _ t st QE8); [intros i Hi; apply K9; apply in_or_app; left; exact Hi | rewrite RM9; reflexivity]|].
    destruct HV8 as (E184 & E185 & E186 & E187 & E208). destruct HI8 as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !K9 by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !K9 by (cbn; tauto); tauto|].
    unfold HVS. rewrite RM9. exact HS8. }
  intros rho9 (QE9 & HV9 & HI9 & HS9).

  assert (I4' : QP A0 A1) by exact (QP_drainM A0 A c I4 NFR).
  set (A' := push_cache (set_q A1 [] (mkQB a its s :: tmp' ++ rest)) c (it_id (aa_geom A1) it)).
  apply (tr_glue X _ (JRI (K0 Kc) A0 rho0 A' a n0 (S nd) its tmp' rest) RIr tpL (fun r => HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. exact (qi_post (K0 Kc) HL (K0_secband Kc) A0 rho0 A1 it a s n0 nd its tmp' rest rho9 tpL w t st I1 I2 I3 I4' I5 Hw QE9 HV9 HI9 HS9). }
  intros rho10 (HV10 & HI10 & HS10). apply (seg_D_RrM X _ rho10 tpL (HJI _ _ _ _ _ _ _)). intros Tx M rho11 HIN HKp11. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' rho11 tpL I); [| exact (HVX_keep _ rho10 rho11 tmp' HKp11 ltac:(cbn; tauto) HV10) | exact (HVI_keep rho10 rho11 a n0 nd it HKp11 HI10) | exact (HVS_keep _ rho10 rho11 a nd it HKp11 HS10)].
  split; [reflexivity|]. split; [exact I2|]. split; [|split; [|split; [exists s; reflexivity|]]].
  - intros z Hz. apply I3. exact (QW_push_item A1 a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
  - pose proof QE9 as [_ _ _ _ HGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in HGEO. destruct HGEO as (C1' & _). apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv.QP_push; [exact I4' | fold c in C1'; lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_item A1 a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
Qed.
End QIFTop.
End SegQIF_top.

(* [comment removed for export] *)
Module SegQ3_close.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "list"; "nil"; "pair"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "PostD"; "PreD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TRP"; "trC"; "trS"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQ3M_sum"; "q3_arms3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQ3_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lm.SegQ3D_rec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.SegQ3D_top OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3M_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3M_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQ3M_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l4.
Import ListNotations.
Open Scope Z_scope.

Section Close.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.

Lemma HDC_S : ltac2:(tb__ "0|3|
S10OF_;S11SaS0R2S9VKc;A1M0A3S12S0R3G0A3S1S2S1cS1S15S4S25Q40A1A1S23S1R6S17A3S13S2R6S8A3S24S1dR6A1S16A2F_;S20RbS22RcRbA2SbS0S18R8R7R6VKc;R5A5S1fR8R7A2M1R4R3A5SfS0S14SdG1A1A1R4R3S3S7ScSeA2M2S6ScSeS1eR8R7A2S19R6VKc;R5A3A4S5G2A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;F_;F_;FQ;Fok;").
Proof.
  intros ok Q Hok Hokp n g A c rho1 tp1 Hn HB. rewrite trS_TRP. destruct g.
  - exact (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l4.DrainCG.drain_contract_g_all n Hn) ok A Kc c rho1 tp1 HKc Hok Hokp (HB eq_refl)).
  - exact (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.drain_contract_f_all n Hn) ok A Kc c rho1 tp1 HKc Hok Hokp).
Qed.
Lemma HDC_C : ltac2:(tb__ "0|2|
S11S1S2S1cS1S15S4S25Q40A1A1S23S1R6S17A3S13S2R6S8A3S24S1dR6A1S16A2F_;S20R9S21R9A1SbS0S18R8R7R6VKc;R5A5S1fR8R7A2M0R4R3A5SfS0S14SdG0A1A1R4R3S3S7ScSeA2M1S6ScSeS1eR8R7A2S19R6VKc;R5A3A4S5G1A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;FQ;").
Proof.
  intros Q n g A c rho1 tp1 Hn HB. rewrite trC_TRP. destruct g.
  - exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l4.DrainCG.drain_contract_g_all n Hn) A Kc c rho1 tp1 HKc (HB eq_refl)).
  - exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kc.DrainC.drain_contract_f_all n Hn) A Kc c rho1 tp1 HKc).
Qed.

Theorem q3_arms3_all : ltac2:(tb__ "0|1|
S10OF_;SaS0R1S9VKc;A1M0A3S12S0R2G0A3S28R3VKc;A2F_;F_;Fok;").
Proof.
  intros ok Hok Hokp A rho tp HT HCI HQB HBD. cbv zeta.
  pose proof (K0_laws Kc HKc) as HL. pose proof (fun A0 => K0_ok_frame ok Kc A0 Hok) as HOKK.
  set (X := trS ok (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))).
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; split; [apply JRD_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRD_stable; exact HL]]).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; split; [apply JRI_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JRI_stable; exact HL]]).
  assert (HJP : forall A1 it i ch a n0 nd its tmp' rest l lst rp, JOK X (JPU (K0 Kc) A rho A1 it i ch a n0 nd its tmp' rest l lst rp))
    by (intros; split; [apply JPU_okf; exact HOKK | split; [apply (okp_via ok Kc _ Hokp); intros r0 t0 tr0 md0 HJ0; exact (proj1 (proj2 (proj1 HJ0))) | apply JPU_stable; exact HL]]).
  split; [|split].
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SegQS_top.qi_sec_step (K0 Kc) HL (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10.K0_sec Kc HKc) A rho X HJI HJP rest).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_top.qi_full_step Kc HKc A rho X HJI rest HBD (HDC_S ok _ Hok Hokp)).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQCF_top.qc_full_step Kc HKc A rho X HJD HJI rest (fun g A1 r1 t1 HB => HDC_S ok _ Hok Hokp 1 g A1 24 r1 t1 (or_introl eq_refl) HB) HBD).
Qed.
Theorem q3_arms3E_all : q3_arms3E Kc.
Proof.
  intros A rho tp HT HCI HQB HBD. cbv zeta.
  pose proof (K0_laws Kc HKc) as HL.
  set (X := trC (LQPA segsA NPRE rho tp (PostsQ3 (K0 Kc) A))).
  assert (HJD : forall A1 tmp rest, JOK X (JRD (K0 Kc) A rho A1 tmp rest)) by (intros; apply JRD_stable; exact HL).
  assert (HJI : forall A1 a n0 nd its tmp rest, JOK X (JRI (K0 Kc) A rho A1 a n0 nd its tmp rest)) by (intros; apply JRI_stable; exact HL).
  assert (HJP : forall A1 it i ch a n0 nd its tmp' rest l lst rp, JOK X (JPU (K0 Kc) A rho A1 it i ch a n0 nd its tmp' rest l lst rp)) by (intros; apply JPU_stable; exact HL).
  split; [|split].
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SegQS_top.qi_sec_step (K0 Kc) HL (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10.K0_sec Kc HKc) A rho X HJI HJP rest).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQIF_top.qi_full_step Kc HKc A rho X HJI rest HBD (HDC_C _)).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQCF_top.qc_full_step Kc HKc A rho X HJD HJI rest (fun g A1 r1 t1 HB => HDC_C _ 1 g A1 24 r1 t1 (or_introl eq_refl) HB) HBD).
Qed.
End Close.

Theorem drain_sum_all : ltac2:(tb__ "0|0|
S10OF_;S1aS1bR1A1SaS0R3S9R2A1A3S12S0R4S9R3A1A3S26R5R4A2F_;F_;F_;FKc;Fok;").
Proof. intros ok Kc HKc Hok Hokp. exact (drain_sum_of_arms3 ok Kc HKc Hok Hokp (q3_arms3_all Kc HKc ok Hok Hokp)). Qed.
Theorem drain_sumE_all : ltac2:(tb__ "0|0|
S1aS1bR1A1S27R2A1F_;FKc;").
Proof. intros Kc HKc. exact (drain_sumE_of_arms3 Kc HKc (q3_arms3E_all Kc HKc)). Qed.
End SegQ3_close.

