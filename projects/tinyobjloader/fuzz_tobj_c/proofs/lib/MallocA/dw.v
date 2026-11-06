(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_072.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From Stdlib Require Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dn dc dk cx.

(* [comment removed for export] *)
Module SegQIF_m4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m4"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 4.

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
End SegQIF_m4.

(* [comment removed for export] *)
Module SegQIF_m6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m6"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m8"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
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
Module SegQIF_mid.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "prod"; "true"; "nil"; "nat"; "app"; "length"; "pair"; "snd"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "budget_bound"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "cs_cache"; "mkQB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env"; "qienvF"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "TRP"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "is_primary"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "qienv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue"; "ENVM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "PostD"; "PreD"; "S7"; "m_S0"; "mcert"; "mdata"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_mid.MidT"; "MID_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_mid"; "QEV"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dq.SegQCF_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dv.SegQIF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SegQIF_cont OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.SegQIF_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ce.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
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
  assert (HNS : In n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.DRAIN_NS) by (rewrite <- Hn; exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.kchunks_cases c C1)).
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "prod"; "nil"; "nat"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound"; "class_fresh"; "qbatch"; "@Corelib.Init.Logic"; "eq"; "True"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "QP"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "SIDEQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "qienv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mdata"; "PostD"; "PreD"; "mcert"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis"; "QI_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_mid"; "QEV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "JOK"; "TRP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ce.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_mid OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_m5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m8.
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
  intros c g vb Hc. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.kchunks_cases c Hc) as HN. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.DRAIN_NS in HN. cbn [In] in HN.
  destruct HN as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E.
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m1.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m1.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m2.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m2.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m3.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m3.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m4.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m4.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_m5.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_m5.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m6.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m6.cert_of g vb).
  - exists (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m8.D_of g vb). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_m8.cert_of g vb).
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
  - pose proof QE9 as [_ _ _ _ HGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in HGEO. destruct HGEO as (C1' & _). apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv.QP_push; [exact I4' | fold c in C1'; lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_item A1 a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
Qed.
End QIFTop.
End SegQIF_top.

(* [comment removed for export] *)
Module SegQ3_close.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "list"; "nil"; "pair"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC"; "DRAIN_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "PostD"; "PreD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TRP"; "trC"; "trS"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQ3M_sum"; "q3_arms3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQ3_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.SegQ3D_rec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SegQ3D_qis OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.SegQ3D_top OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3M_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3M_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQ3M_sum OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ce.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cx.
Import ListNotations.
Open Scope Z_scope.

Section Close.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.

Lemma HDC_S : ltac2:(tb__ "0|3|
S10OF_;S11SaS0R2S9VKc;A1M0A3S12S0R3G0A3S1S2S1cS1S15S4S25Q40A1A1S23S1R6S17A3S13S2R6S8A3S24S1dR6A1S16A2F_;S20RbS22RcRbA2SbS0S18R8R7R6VKc;R5A5S1fR8R7A2M1R4R3A5SfS0S14SdG1A1A1R4R3S3S7ScSeA2M2S6ScSeS1eR8R7A2S19R6VKc;R5A3A4S5G2A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;F_;F_;FQ;Fok;").
Proof.
  intros ok Q Hok Hokp n g A c rho1 tp1 Hn HB. rewrite trS_TRP. destruct g.
  - exact (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainCG.drain_contract_g_all n Hn) ok A Kc c rho1 tp1 HKc Hok Hokp (HB eq_refl)).
  - exact (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.drain_contract_f_all n Hn) ok A Kc c rho1 tp1 HKc Hok Hokp).
Qed.
Lemma HDC_C : ltac2:(tb__ "0|2|
S11S1S2S1cS1S15S4S25Q40A1A1S23S1R6S17A3S13S2R6S8A3S24S1dR6A1S16A2F_;S20R9S21R9A1SbS0S18R8R7R6VKc;R5A5S1fR8R7A2M0R4R3A5SfS0S14SdG0A1A1R4R3S3S7ScSeA2M1S6ScSeS1eR8R7A2S19R6VKc;R5A3A4S5G1A1A3A5A4F_;F_;Ftp1;Frho1;Fc;FA;Fg;Fn;FQ;").
Proof.
  intros Q n g A c rho1 tp1 Hn HB. rewrite trC_TRP. destruct g.
  - exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cx.DrainCG.drain_contract_g_all n Hn) A Kc c rho1 tp1 HKc (HB eq_refl)).
  - exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ce.DrainC.drain_contract_f_all n Hn) A Kc c rho1 tp1 HKc).
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
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SegQS_top.qi_sec_step (K0 Kc) HL (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10.K0_sec Kc HKc) A rho X HJI HJP rest).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_top.qi_full_step Kc HKc A rho X HJI rest HBD (HDC_S ok _ Hok Hokp)).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQCF_top.qc_full_step Kc HKc A rho X HJD HJI rest (fun g A1 r1 t1 HB => HDC_S ok _ Hok Hokp 1 g A1 24 r1 t1 (or_introl eq_refl) HB) HBD).
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
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SegQS_top.qi_sec_step (K0 Kc) HL (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10.K0_sec Kc HKc) A rho X HJI HJP rest).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQIF_top.qi_full_step Kc HKc A rho X HJI rest HBD (HDC_C _)).
  - intros rest. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQCF_top.qc_full_step Kc HKc A rho X HJD HJI rest (fun g A1 r1 t1 HB => HDC_C _ 1 g A1 24 r1 t1 (or_introl eq_refl) HB) HBD).
Qed.
End Close.

Theorem drain_sum_all : ltac2:(tb__ "0|0|
S10OF_;S1aS1bR1A1SaS0R3S9R2A1A3S12S0R4S9R3A1A3S26R5R4A2F_;F_;F_;FKc;Fok;").
Proof. intros ok Kc HKc Hok Hokp. exact (drain_sum_of_arms3 ok Kc HKc Hok Hokp (q3_arms3_all Kc HKc ok Hok Hokp)). Qed.
Theorem drain_sumE_all : ltac2:(tb__ "0|0|
S1aS1bR1A1S27R2A1F_;FKc;").
Proof. intros Kc HKc. exact (drain_sumE_of_arms3 Kc HKc (q3_arms3E_all Kc HKc)). Qed.
End SegQ3_close.

