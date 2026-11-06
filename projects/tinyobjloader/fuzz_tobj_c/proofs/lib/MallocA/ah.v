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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.

(* [comment removed for export] *)
Module F0A_cL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be"; "C4_L1Be"; "EQ_L1Be"; "q_L1Be"; "C2_L1Be_1"; "C2_L1Be_2"; "C2_L1Be_3"; "C3_L1Be"; "CD_L1Be"; "P0_L1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "Ems_L1Be"; "Eps_L1Be"; "S1c_L1Be_1"; "S1c_L1Be_2"; "S1c_L1Be_3"; "TM_L1Be"; "TQ_L1Be"; "run3_L1Be"; "run6_L1Be"; "RM_L1Be"; "RQ_L1Be"; "TM0_L1Be"; "TQ0_L1Be"; "run1_L1Be"; "run2_L1Be_1"; "run2_L1Be_2"; "run2_L1Be_3"; "run4_L1Be"; "run5_L1Be"; "EfD_L1Be_1"; "EfD_L1Be_2"; "EfD_L1Be_3"; "Eq_L1Be"; "RD_L1Be_1"; "RD_L1Be_2"; "RD_L1Be_3"; "TDr_L1Be_1"; "TDr_L1Be_2"; "TDr_L1Be_3"; "exits1_L1Be"; "Ebg_L1Be"; "Edr_L1Be"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "W_L1Be"; "Xf_L1Be"; "st_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L1Be : list ulink := Wcan 1.
Definition st_L1Be : ustop := UStopLe.
Definition q_L1Be : qvar := QBe.
Definition P0_L1Be : axst := ltac2:(tb__ "0|0|
S7eS11S66S68S39A4").

Definition run1_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_L1Be_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_L1Be_1 : axst := C2_of S1c_L1Be_1.
Definition run2_L1Be_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L1Be_1 : axst := leaf 0 run2_L1Be_1.
Definition ED_L1Be_1 : axst := ED_of EfD_L1Be_1.
Definition RD_L1Be_1 : list sobj := RD_of ED_L1Be_1 1.
Definition TD_L1Be_1 : axst := TD_of ED_L1Be_1 1.
Definition TDr_L1Be_1 : axst := TDr_of TD_L1Be_1.
Definition S1c_L1Be_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_L1Be_2 : axst := C2_of S1c_L1Be_2.
Definition run2_L1Be_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L1Be_2 : axst := leaf 0 run2_L1Be_2.
Definition ED_L1Be_2 : axst := ED_of EfD_L1Be_2.
Definition RD_L1Be_2 : list sobj := RD_of ED_L1Be_2 2.
Definition TD_L1Be_2 : axst := TD_of ED_L1Be_2 2.
Definition TDr_L1Be_2 : axst := TDr_of TD_L1Be_2.
Definition S1c_L1Be_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_L1Be_3 : axst := C2_of S1c_L1Be_3.
Definition run2_L1Be_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L1Be_3 : axst := leaf 0 run2_L1Be_3.
Definition ED_L1Be_3 : axst := ED_of EfD_L1Be_3.
Definition RD_L1Be_3 : list sobj := RD_of ED_L1Be_3 3.
Definition TD_L1Be_3 : axst := TD_of ED_L1Be_3 3.
Definition TDr_L1Be_3 : axst := TDr_of TD_L1Be_3.
Definition exits1_L1Be : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_L1Be : axst := CD_of TDr_L1Be_1.
Definition run3_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_L1Be : axst := leaf 0 run3_L1Be.
Definition Ebg_L1Be : axst := leaf 1 run3_L1Be.
Definition C3_L1Be : axst := C3_of Eps_L1Be.
Definition run4_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_L1Be : axst := leaf 0 run4_L1Be.
Definition C4_L1Be : axst := C4_of Ems_L1Be.
Definition RM_L1Be : list sobj := RM_of C4_L1Be.
Definition TM0_L1Be : axst := TM0_of C4_L1Be.
Definition TM_L1Be : axst := TM_of C4_L1Be.
Definition run5_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_L1Be : axst := leaf 0 run5_L1Be.
Definition EQ_L1Be : axst := EQ_of Eq_L1Be.
Definition RQ_L1Be : list sobj := RQ_of EQ_L1Be q_L1Be.
Definition TQ0_L1Be : axst := TQ0_of EQ_L1Be q_L1Be.
Definition TQ_L1Be : axst := TQ_of EQ_L1Be q_L1Be.
Definition run6_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_L1Be : axst := leaf 0 run6_L1Be.
Definition Xf_L1Be : axst := leaf 1 run6_L1Be.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L1Be : ltac2:(tb__ "0|0|
S0S9S79S6aS1cSaS2S21SbS2A1A3S69SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L1Be exits1_L1Be run1_L1Be); [unfold run1_L1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L1Be : ltac2:(tb__ "0|2|
S0S9S7aS6aS1cSaS2S21SbS2A1A3S69SaS77S78S3fZ1S1bZ0M0A1M1A3SbS77A1A3S7cS4S77S4S78R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L1Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1Be) run1_L1Be); [unfold run1_L1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L1Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_1 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_L1Be_1; reflexivity. Qed.
Lemma L2_L1Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_1; reflexivity]). Qed.
Lemma AXD_L1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S40S6dZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_1 : ltac2:(tb__ "0|1|
S0S9S71S40S6dZ1M0A1S1fS40G0A2S5aSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_1 : ltac2:(tb__ "0|0|
S0S9S7bS5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_2 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_L1Be_2; reflexivity. Qed.
Lemma L2_L1Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_2; reflexivity]). Qed.
Lemma AXD_L1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S41S6dZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_2 : ltac2:(tb__ "0|1|
S0S9S71S41S6dZ2M0A1S1fS41G0A2S5bSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_2 : ltac2:(tb__ "0|0|
S0S9S7bS5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_3 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_L1Be_3; reflexivity. Qed.
Lemma L2_L1Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_3; reflexivity]). Qed.
Lemma AXD_L1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S42S6dZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_3 : ltac2:(tb__ "0|1|
S0S9S71S42S6dZ3M0A1S1fS42G0A2S5cSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_3 : ltac2:(tb__ "0|0|
S0S9S7bS5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_L1Be; reflexivity. Qed.
Lemma L3_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L1Be | unfold Ebg_L1Be]; reflexivity]). Qed.
Lemma NX3_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L1Be : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_L1Be : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_L1Be; reflexivity. Qed.
Lemma L4_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_L1Be; reflexivity]). Qed.
Lemma D4_L1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L1Be : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S37S75S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L1Be : ltac2:(tb__ "0|0|
S0S9S72S37S75S2dS37A1S4cS7cS6S4S8S76A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L1Be : ltac2:(tb__ "0|0|
S0S4S73S2dS37A1S75S31S37S4cA5S4eA3"). Proof. unfold TM0_L1Be, TM0_of, RM_L1Be; reflexivity. Qed.
Lemma FBM_L1Be : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L1Be : ltac2:(tb__ "0|0|
S0S4S7dS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_L1Be; reflexivity. Qed.
Lemma L5_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_L1Be; reflexivity]). Qed.
Lemma AXQ_L1Be : ltac2:(tb__ "0|0|
S0SfS4A1S6cS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L1Be : ltac2:(tb__ "0|0|
S0S9S72S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L1Be : ltac2:(tb__ "0|0|
S0S4S73S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_L1Be, TQ0_of, RQ_L1Be; reflexivity. Qed.
Lemma FBQ_L1Be : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L1Be : ltac2:(tb__ "0|0|
S0S4S7dS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_L1Be; reflexivity. Qed.
Lemma L6_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S67A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L1Be | unfold Xf_L1Be]; reflexivity]). Qed.

End F0A_cL1Be.

(* [comment removed for export] *)
Module F0A_cL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf"; "C4_L1Bf"; "EQ_L1Bf"; "q_L1Bf"; "C2_L1Bf_1"; "C2_L1Bf_2"; "C2_L1Bf_3"; "C3_L1Bf"; "CD_L1Bf"; "P0_L1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "Ems_L1Bf"; "Eps_L1Bf"; "S1c_L1Bf_1"; "S1c_L1Bf_2"; "S1c_L1Bf_3"; "TM_L1Bf"; "TQ_L1Bf"; "run3_L1Bf"; "run6_L1Bf"; "RM_L1Bf"; "RQ_L1Bf"; "TM0_L1Bf"; "TQ0_L1Bf"; "run1_L1Bf"; "run2_L1Bf_1"; "run2_L1Bf_2"; "run2_L1Bf_3"; "run4_L1Bf"; "run5_L1Bf"; "EfD_L1Bf_1"; "EfD_L1Bf_2"; "EfD_L1Bf_3"; "Eq_L1Bf"; "RD_L1Bf_1"; "RD_L1Bf_2"; "RD_L1Bf_3"; "TDr_L1Bf_1"; "TDr_L1Bf_2"; "TDr_L1Bf_3"; "exits1_L1Bf"; "Ebg_L1Bf"; "Edr_L1Bf"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "W_L1Bf"; "Xf_L1Bf"; "st_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L1Bf : list ulink := Wcan 1.
Definition st_L1Bf : ustop := UStopLe.
Definition q_L1Bf : qvar := QBf.
Definition P0_L1Bf : axst := ltac2:(tb__ "0|0|
S7eS11S66S68S39A4").

Definition run1_L1Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_L1Bf_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_L1Bf_1 : axst := C2_of S1c_L1Bf_1.
Definition run2_L1Bf_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L1Bf_1 : axst := leaf 0 run2_L1Bf_1.
Definition ED_L1Bf_1 : axst := ED_of EfD_L1Bf_1.
Definition RD_L1Bf_1 : list sobj := RD_of ED_L1Bf_1 1.
Definition TD_L1Bf_1 : axst := TD_of ED_L1Bf_1 1.
Definition TDr_L1Bf_1 : axst := TDr_of TD_L1Bf_1.
Definition S1c_L1Bf_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_L1Bf_2 : axst := C2_of S1c_L1Bf_2.
Definition run2_L1Bf_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L1Bf_2 : axst := leaf 0 run2_L1Bf_2.
Definition ED_L1Bf_2 : axst := ED_of EfD_L1Bf_2.
Definition RD_L1Bf_2 : list sobj := RD_of ED_L1Bf_2 2.
Definition TD_L1Bf_2 : axst := TD_of ED_L1Bf_2 2.
Definition TDr_L1Bf_2 : axst := TDr_of TD_L1Bf_2.
Definition S1c_L1Bf_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_L1Bf_3 : axst := C2_of S1c_L1Bf_3.
Definition run2_L1Bf_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L1Bf_3 : axst := leaf 0 run2_L1Bf_3.
Definition ED_L1Bf_3 : axst := ED_of EfD_L1Bf_3.
Definition RD_L1Bf_3 : list sobj := RD_of ED_L1Bf_3 3.
Definition TD_L1Bf_3 : axst := TD_of ED_L1Bf_3 3.
Definition TDr_L1Bf_3 : axst := TDr_of TD_L1Bf_3.
Definition exits1_L1Bf : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_L1Bf : axst := CD_of TDr_L1Bf_1.
Definition run3_L1Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_L1Bf : axst := leaf 0 run3_L1Bf.
Definition Ebg_L1Bf : axst := leaf 1 run3_L1Bf.
Definition C3_L1Bf : axst := C3_of Eps_L1Bf.
Definition run4_L1Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_L1Bf : axst := leaf 0 run4_L1Bf.
Definition C4_L1Bf : axst := C4_of Ems_L1Bf.
Definition RM_L1Bf : list sobj := RM_of C4_L1Bf.
Definition TM0_L1Bf : axst := TM0_of C4_L1Bf.
Definition TM_L1Bf : axst := TM_of C4_L1Bf.
Definition run5_L1Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_L1Bf : axst := leaf 0 run5_L1Bf.
Definition EQ_L1Bf : axst := EQ_of Eq_L1Bf.
Definition RQ_L1Bf : list sobj := RQ_of EQ_L1Bf q_L1Bf.
Definition TQ0_L1Bf : axst := TQ0_of EQ_L1Bf q_L1Bf.
Definition TQ_L1Bf : axst := TQ_of EQ_L1Bf q_L1Bf.
Definition run6_L1Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_L1Bf : axst := leaf 0 run6_L1Bf.
Definition Xf_L1Bf : axst := leaf 1 run6_L1Bf.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L1Bf : ltac2:(tb__ "0|0|
S0S9S79S6aS1cSaS2S21SbS2A1A3S69SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L1Bf exits1_L1Bf run1_L1Bf); [unfold run1_L1Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L1Bf : ltac2:(tb__ "0|2|
S0S9S7aS6aS1cSaS2S21SbS2A1A3S69SaS77S78S3fZ1S1bZ0M0A1M1A3SbS77A1A3S7cS4S77S4S78R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L1Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1Bf) run1_L1Bf); [unfold run1_L1Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L1Bf_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Bf_1 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L1Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_L1Bf_1; reflexivity. Qed.
Lemma L2_L1Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Bf_1; reflexivity]). Qed.
Lemma AXD_L1Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S40S6dZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Bf_1 : ltac2:(tb__ "0|1|
S0S9S71S40S6dZ1M0A1S1fS40G0A2S5aSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Bf_1 : ltac2:(tb__ "0|0|
S0S9S7bS5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Bf_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Bf_2 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L1Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_L1Bf_2; reflexivity. Qed.
Lemma L2_L1Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Bf_2; reflexivity]). Qed.
Lemma AXD_L1Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S41S6dZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Bf_2 : ltac2:(tb__ "0|1|
S0S9S71S41S6dZ2M0A1S1fS41G0A2S5bSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Bf_2 : ltac2:(tb__ "0|0|
S0S9S7bS5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Bf_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Bf_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Bf_3 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Bf_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L1Bf_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_L1Bf_3; reflexivity. Qed.
Lemma L2_L1Bf_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Bf_3; reflexivity]). Qed.
Lemma AXD_L1Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Bf_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S42S6dZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Bf_3 : ltac2:(tb__ "0|1|
S0S9S71S42S6dZ3M0A1S1fS42G0A2S5cSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Bf_3 : ltac2:(tb__ "0|0|
S0S9S7bS5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_L1Bf; reflexivity. Qed.
Lemma L3_L1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L1Bf | unfold Ebg_L1Bf]; reflexivity]). Qed.
Lemma NX3_L1Bf : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L1Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L1Bf : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_L1Bf : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L1Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_L1Bf; reflexivity. Qed.
Lemma L4_L1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_L1Bf; reflexivity]). Qed.
Lemma D4_L1Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L1Bf : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L1Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L1Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S37S75S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L1Bf : ltac2:(tb__ "0|0|
S0S9S72S37S75S2dS37A1S4cS7cS6S4S8S76A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L1Bf : ltac2:(tb__ "0|0|
S0S4S73S2dS37A1S75S31S37S4cA5S4eA3"). Proof. unfold TM0_L1Bf, TM0_of, RM_L1Bf; reflexivity. Qed.
Lemma FBM_L1Bf : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L1Bf : ltac2:(tb__ "0|0|
S0S4S7dS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_L1Bf : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_L1Bf; reflexivity. Qed.
Lemma L5_L1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_L1Bf; reflexivity]). Qed.
Lemma AXQ_L1Bf : ltac2:(tb__ "0|0|
S0SfS4A1S6cS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L1Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L1Bf : ltac2:(tb__ "0|0|
S0S9S72S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L1Bf : ltac2:(tb__ "0|0|
S0S4S73S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_L1Bf, TQ0_of, RQ_L1Bf; reflexivity. Qed.
Lemma FBQ_L1Bf : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L1Bf : ltac2:(tb__ "0|0|
S0S4S7dS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_L1Bf : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_L1Bf; reflexivity. Qed.
Lemma L6_L1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S67A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L1Bf | unfold Xf_L1Bf]; reflexivity]). Qed.

End F0A_cL1Bf.

(* [comment removed for export] *)
Module F0A_cL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A"; "C4_L2A"; "EQ_L2A"; "q_L2A"; "C2_L2A_1"; "C2_L2A_2"; "C2_L2A_3"; "C2_L2A_4"; "C3_L2A"; "CD_L2A"; "P0_L2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "Ems_L2A"; "Eps_L2A"; "S1c_L2A_1"; "S1c_L2A_2"; "S1c_L2A_3"; "S1c_L2A_4"; "TM_L2A"; "TQ_L2A"; "run1_L2A"; "run3_L2A"; "run6_L2A"; "RM_L2A"; "RQ_L2A"; "TM0_L2A"; "TQ0_L2A"; "run2_L2A_1"; "run2_L2A_2"; "run2_L2A_3"; "run2_L2A_4"; "run4_L2A"; "run5_L2A"; "EfD_L2A_1"; "EfD_L2A_2"; "EfD_L2A_3"; "EfD_L2A_4"; "Eq_L2A"; "RD_L2A_1"; "RD_L2A_2"; "RD_L2A_3"; "RD_L2A_4"; "TDr_L2A_1"; "TDr_L2A_2"; "TDr_L2A_3"; "TDr_L2A_4"; "exits1_L2A"; "Ebg_L2A"; "Edr_L2A"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "W_L2A"; "Xf_L2A"; "st_L2A"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L2A : list ulink := Wcan 2.
Definition st_L2A : ustop := UStopLe.
Definition q_L2A : qvar := QA.
Definition P0_L2A : axst := ltac2:(tb__ "0|0|
S86S11S70S72S3bA4").

Definition run1_L2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S27SbS2A1A3S42A3").

Definition S1c_L2A_1 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z1A3").
Definition C2_L2A_1 : axst := C2_of S1c_L2A_1.
Definition run2_L2A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L2A_1 : axst := leaf 0 run2_L2A_1.
Definition ED_L2A_1 : axst := ED_of EfD_L2A_1.
Definition RD_L2A_1 : list sobj := RD_of ED_L2A_1 1.
Definition TD_L2A_1 : axst := TD_of ED_L2A_1 1.
Definition TDr_L2A_1 : axst := TDr_of TD_L2A_1.
Definition S1c_L2A_2 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z2A3").
Definition C2_L2A_2 : axst := C2_of S1c_L2A_2.
Definition run2_L2A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_L2A_2 : axst := leaf 0 run2_L2A_2.
Definition ED_L2A_2 : axst := ED_of EfD_L2A_2.
Definition RD_L2A_2 : list sobj := RD_of ED_L2A_2 2.
Definition TD_L2A_2 : axst := TD_of ED_L2A_2 2.
Definition TDr_L2A_2 : axst := TDr_of TD_L2A_2.
Definition S1c_L2A_3 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z3A3").
Definition C2_L2A_3 : axst := C2_of S1c_L2A_3.
Definition run2_L2A_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_L2A_3 : axst := leaf 0 run2_L2A_3.
Definition ED_L2A_3 : axst := ED_of EfD_L2A_3.
Definition RD_L2A_3 : list sobj := RD_of ED_L2A_3 3.
Definition TD_L2A_3 : axst := TD_of ED_L2A_3 3.
Definition TDr_L2A_3 : axst := TDr_of TD_L2A_3.
Definition S1c_L2A_4 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z4A3").
Definition C2_L2A_4 : axst := C2_of S1c_L2A_4.
Definition run2_L2A_4 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_L2A_4 : axst := leaf 0 run2_L2A_4.
Definition ED_L2A_4 : axst := ED_of EfD_L2A_4.
Definition RD_L2A_4 : list sobj := RD_of ED_L2A_4 4.
Definition TD_L2A_4 : axst := TD_of ED_L2A_4 4.
Definition TDr_L2A_4 : axst := TDr_of TD_L2A_4.
Definition exits1_L2A : list axst := ltac2:(tb__ "0|0|
SaS4S49SaS4S4aSaS4S4bSaS4S4cSbS4A1A3A3A3A3").

Definition CD_L2A : axst := CD_of TDr_L2A_1.
Definition run3_L2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3").
Definition Eps_L2A : axst := leaf 0 run3_L2A.
Definition Ebg_L2A : axst := leaf 1 run3_L2A.
Definition C3_L2A : axst := C3_of Eps_L2A.
Definition run4_L2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2aSbS2A1A3S40A3").
Definition Ems_L2A : axst := leaf 0 run4_L2A.
Definition C4_L2A : axst := C4_of Ems_L2A.
Definition RM_L2A : list sobj := RM_of C4_L2A.
Definition TM0_L2A : axst := TM0_of C4_L2A.
Definition TM_L2A : axst := TM_of C4_L2A.
Definition run5_L2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S29SbS2A1A3S4dA3").
Definition Eq_L2A : axst := leaf 0 run5_L2A.
Definition EQ_L2A : axst := EQ_of Eq_L2A.
Definition RQ_L2A : list sobj := RQ_of EQ_L2A q_L2A.
Definition TQ0_L2A : axst := TQ0_of EQ_L2A q_L2A.
Definition TQ_L2A : axst := TQ_of EQ_L2A q_L2A.
Definition run6_L2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3").
Definition Edr_L2A : axst := leaf 0 run6_L2A.
Definition Xf_L2A : axst := leaf 1 run6_L2A.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L2A : ltac2:(tb__ "0|0|
S0S9S82S38S1cSaS2S27SbS2A1A3S37SaS4S42SbS4A1A3S69A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L2A exits1_L2A run1_L2A); [unfold run1_L2A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L2A : ltac2:(tb__ "0|2|
S0S9S83S38S1cSaS2S27SbS2A1A3S37SaS80S81S42Z1S1bZ0M0A1M1A3SbS80A1A3S84S4S80S4S81R1G0G1A3LE;S69A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L2A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2A) run1_L2A); [unfold run1_L2A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L2A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S49A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2A_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2A_1 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2A_1 : ltac2:(tb__ "0|0|
S0S4S7S49S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L2A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S56A3"). Proof. unfold run2_L2A_1; reflexivity. Qed.
Lemma L2_L2A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S56A2S5cA3A2"). Proof. Time (split; [vmr | unfold EfD_L2A_1; reflexivity]). Qed.
Lemma AXD_L2A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5cS22A2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S43S75Z1M1A1S1fS43G1A2A3SeG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2A_1 : ltac2:(tb__ "0|1|
S0S9S79S43S75Z1M0A1S1fS43G0A2S61SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6cS23A2SeS4S65A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2A_1 : ltac2:(tb__ "0|0|
S0S9S7cS65S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4aA1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2A_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2A_2 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2A_2 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_L2A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_L2A_2; reflexivity. Qed.
Lemma L2_L2A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_L2A_2; reflexivity]). Qed.
Lemma AXD_L2A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S44S75Z2M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2A_2 : ltac2:(tb__ "0|1|
S0S9S79S44S75Z2M0A1S1fS44G0A2S62SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2A_2 : ltac2:(tb__ "0|0|
S0S9S7cS66S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2A_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4bA1S5S3eA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2A_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2A_3 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2A_3 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_L2A_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_L2A_3; reflexivity. Qed.
Lemma L2_L2A_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_L2A_3; reflexivity]). Qed.
Lemma AXD_L2A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2A_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S45S75Z3M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2A_3 : ltac2:(tb__ "0|1|
S0S9S79S45S75Z3M0A1S1fS45G0A2S63SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2A_3 : ltac2:(tb__ "0|0|
S0S9S7cS67S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2A_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4cA1S5S3fA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2A_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2A_4 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2A_4 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_L2A_4 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_L2A_4; reflexivity. Qed.
Lemma L2_L2A_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_L2A_4; reflexivity]). Qed.
Lemma AXD_L2A_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2A_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S46S75Z4M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2A_4 : ltac2:(tb__ "0|1|
S0S9S79S46S75Z4M0A1S1fS46G0A2S64SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2A_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2A_4 : ltac2:(tb__ "0|0|
S0S9S7cS68S41A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3S50A3"). Proof. unfold run3_L2A; reflexivity. Qed.
Lemma L3_L2A : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S36U0S50A2S48A3S0S4S36U1S50A2S6aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L2A | unfold Ebg_L2A]; reflexivity]). Qed.
Lemma NX3_L2A : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S41A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L2A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S48A1S5S40A1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L2A : ltac2:(tb__ "0|0|
S0S4S7S48S5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma NX3b_L2A : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L2A : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2aSbS2A1A3S40A3S5aA3"). Proof. unfold run4_L2A; reflexivity. Qed.
Lemma L4_L2A : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S2aSbS2A1A3A2ScA3S0S4S36U0S5aA2S47A3A2"). Proof. Time (split; [vmr | unfold Ems_L2A; reflexivity]). Qed.
Lemma D4_L2A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S47A1S5S39A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L2A : ltac2:(tb__ "0|0|
S0S4S7S47S5S39A1A2S39A3"). Proof. vmr. Qed.
Lemma W4_L2A : ltac2:(tb__ "0|1|
S1S0S9S19S5S39A1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L2A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S39S7eS2eS39A1A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L2A : ltac2:(tb__ "0|0|
S0S9S7aS39S7eS2eS39A1S52S84S6S4S8S7fA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L2A : ltac2:(tb__ "0|0|
S0S4S7bS2eS39A1S7eS31S39S52A5S54A3"). Proof. unfold TM0_L2A, TM0_of, RM_L2A; reflexivity. Qed.
Lemma FBM_L2A : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S54A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L2A : ltac2:(tb__ "0|0|
S0S4S85S54S17S5S39A1A1A2S4dA3"). Proof. vmr. Qed.
Lemma NX5_L2A : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4dA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S29SbS2A1A3S4dA3S5bA3"). Proof. unfold run5_L2A; reflexivity. Qed.
Lemma L5_L2A : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S29SbS2A1A3A2ScA3S0S4S36U0S5bA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_L2A; reflexivity]). Qed.
Lemma AXQ_L2A : ltac2:(tb__ "0|0|
S0SfS4A1S74S60S32A2SeS4S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L2A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S3aS2cS3bA1S2fS3aS3bA2A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L2A : ltac2:(tb__ "0|0|
S0S9S7aS3aS2cS3bA1S2fS3aS3bA2S53SaS4S30S3bA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L2A : ltac2:(tb__ "0|0|
S0S4S7bS2fS3aS3bA2S2cS3bA1S30S3bA1S3aS53A5S55A3"). Proof. unfold TQ0_L2A, TQ0_of, RQ_L2A; reflexivity. Qed.
Lemma FBQ_L2A : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L2A : ltac2:(tb__ "0|0|
S0S4S85S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX6_L2A : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3S51A3"). Proof. unfold run6_L2A; reflexivity. Qed.
Lemma L6_L2A : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S36U0S51A2S6bA3S0S4S36U1S51A2S71A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L2A | unfold Xf_L2A]; reflexivity]). Qed.

End F0A_cL2A.

(* [comment removed for export] *)
Module F0A_cL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be"; "C4_L2Be"; "EQ_L2Be"; "q_L2Be"; "C2_L2Be_1"; "C2_L2Be_2"; "C2_L2Be_3"; "C2_L2Be_4"; "C3_L2Be"; "CD_L2Be"; "P0_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "Ems_L2Be"; "Eps_L2Be"; "S1c_L2Be_1"; "S1c_L2Be_2"; "S1c_L2Be_3"; "S1c_L2Be_4"; "TM_L2Be"; "TQ_L2Be"; "run1_L2Be"; "run3_L2Be"; "run6_L2Be"; "RM_L2Be"; "RQ_L2Be"; "TM0_L2Be"; "TQ0_L2Be"; "run2_L2Be_1"; "run2_L2Be_2"; "run2_L2Be_3"; "run2_L2Be_4"; "run4_L2Be"; "run5_L2Be"; "EfD_L2Be_1"; "EfD_L2Be_2"; "EfD_L2Be_3"; "EfD_L2Be_4"; "Eq_L2Be"; "RD_L2Be_1"; "RD_L2Be_2"; "RD_L2Be_3"; "RD_L2Be_4"; "TDr_L2Be_1"; "TDr_L2Be_2"; "TDr_L2Be_3"; "TDr_L2Be_4"; "exits1_L2Be"; "Ebg_L2Be"; "Edr_L2Be"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "W_L2Be"; "Xf_L2Be"; "st_L2Be"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L2Be : list ulink := Wcan 2.
Definition st_L2Be : ustop := UStopLe.
Definition q_L2Be : qvar := QBe.
Definition P0_L2Be : axst := ltac2:(tb__ "0|0|
S86S11S70S72S3bA4").

Definition run1_L2Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S27SbS2A1A3S42A3").

Definition S1c_L2Be_1 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z1A3").
Definition C2_L2Be_1 : axst := C2_of S1c_L2Be_1.
Definition run2_L2Be_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L2Be_1 : axst := leaf 0 run2_L2Be_1.
Definition ED_L2Be_1 : axst := ED_of EfD_L2Be_1.
Definition RD_L2Be_1 : list sobj := RD_of ED_L2Be_1 1.
Definition TD_L2Be_1 : axst := TD_of ED_L2Be_1 1.
Definition TDr_L2Be_1 : axst := TDr_of TD_L2Be_1.
Definition S1c_L2Be_2 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z2A3").
Definition C2_L2Be_2 : axst := C2_of S1c_L2Be_2.
Definition run2_L2Be_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_L2Be_2 : axst := leaf 0 run2_L2Be_2.
Definition ED_L2Be_2 : axst := ED_of EfD_L2Be_2.
Definition RD_L2Be_2 : list sobj := RD_of ED_L2Be_2 2.
Definition TD_L2Be_2 : axst := TD_of ED_L2Be_2 2.
Definition TDr_L2Be_2 : axst := TDr_of TD_L2Be_2.
Definition S1c_L2Be_3 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z3A3").
Definition C2_L2Be_3 : axst := C2_of S1c_L2Be_3.
Definition run2_L2Be_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_L2Be_3 : axst := leaf 0 run2_L2Be_3.
Definition ED_L2Be_3 : axst := ED_of EfD_L2Be_3.
Definition RD_L2Be_3 : list sobj := RD_of ED_L2Be_3 3.
Definition TD_L2Be_3 : axst := TD_of ED_L2Be_3 3.
Definition TDr_L2Be_3 : axst := TDr_of TD_L2Be_3.
Definition S1c_L2Be_4 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z4A3").
Definition C2_L2Be_4 : axst := C2_of S1c_L2Be_4.
Definition run2_L2Be_4 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_L2Be_4 : axst := leaf 0 run2_L2Be_4.
Definition ED_L2Be_4 : axst := ED_of EfD_L2Be_4.
Definition RD_L2Be_4 : list sobj := RD_of ED_L2Be_4 4.
Definition TD_L2Be_4 : axst := TD_of ED_L2Be_4 4.
Definition TDr_L2Be_4 : axst := TDr_of TD_L2Be_4.
Definition exits1_L2Be : list axst := ltac2:(tb__ "0|0|
SaS4S49SaS4S4aSaS4S4bSaS4S4cSbS4A1A3A3A3A3").

Definition CD_L2Be : axst := CD_of TDr_L2Be_1.
Definition run3_L2Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3").
Definition Eps_L2Be : axst := leaf 0 run3_L2Be.
Definition Ebg_L2Be : axst := leaf 1 run3_L2Be.
Definition C3_L2Be : axst := C3_of Eps_L2Be.
Definition run4_L2Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2aSbS2A1A3S40A3").
Definition Ems_L2Be : axst := leaf 0 run4_L2Be.
Definition C4_L2Be : axst := C4_of Ems_L2Be.
Definition RM_L2Be : list sobj := RM_of C4_L2Be.
Definition TM0_L2Be : axst := TM0_of C4_L2Be.
Definition TM_L2Be : axst := TM_of C4_L2Be.
Definition run5_L2Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S29SbS2A1A3S4dA3").
Definition Eq_L2Be : axst := leaf 0 run5_L2Be.
Definition EQ_L2Be : axst := EQ_of Eq_L2Be.
Definition RQ_L2Be : list sobj := RQ_of EQ_L2Be q_L2Be.
Definition TQ0_L2Be : axst := TQ0_of EQ_L2Be q_L2Be.
Definition TQ_L2Be : axst := TQ_of EQ_L2Be q_L2Be.
Definition run6_L2Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3").
Definition Edr_L2Be : axst := leaf 0 run6_L2Be.
Definition Xf_L2Be : axst := leaf 1 run6_L2Be.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L2Be : ltac2:(tb__ "0|0|
S0S9S82S38S1cSaS2S27SbS2A1A3S37SaS4S42SbS4A1A3S69A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L2Be exits1_L2Be run1_L2Be); [unfold run1_L2Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L2Be : ltac2:(tb__ "0|2|
S0S9S83S38S1cSaS2S27SbS2A1A3S37SaS80S81S42Z1S1bZ0M0A1M1A3SbS80A1A3S84S4S80S4S81R1G0G1A3LE;S69A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L2Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2Be) run1_L2Be); [unfold run1_L2Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L2Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S49A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Be_1 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Be_1 : ltac2:(tb__ "0|0|
S0S4S7S49S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L2Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S56A3"). Proof. unfold run2_L2Be_1; reflexivity. Qed.
Lemma L2_L2Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S56A2S5cA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Be_1; reflexivity]). Qed.
Lemma AXD_L2Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5cS22A2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S43S75Z1M1A1S1fS43G1A2A3SeG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Be_1 : ltac2:(tb__ "0|1|
S0S9S79S43S75Z1M0A1S1fS43G0A2S61SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6cS23A2SeS4S65A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Be_1 : ltac2:(tb__ "0|0|
S0S9S7cS65S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4aA1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Be_2 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Be_2 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_L2Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_L2Be_2; reflexivity. Qed.
Lemma L2_L2Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Be_2; reflexivity]). Qed.
Lemma AXD_L2Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S44S75Z2M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Be_2 : ltac2:(tb__ "0|1|
S0S9S79S44S75Z2M0A1S1fS44G0A2S62SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Be_2 : ltac2:(tb__ "0|0|
S0S9S7cS66S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4bA1S5S3eA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Be_3 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Be_3 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_L2Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_L2Be_3; reflexivity. Qed.
Lemma L2_L2Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Be_3; reflexivity]). Qed.
Lemma AXD_L2Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S45S75Z3M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Be_3 : ltac2:(tb__ "0|1|
S0S9S79S45S75Z3M0A1S1fS45G0A2S63SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Be_3 : ltac2:(tb__ "0|0|
S0S9S7cS67S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Be_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4cA1S5S3fA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Be_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Be_4 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Be_4 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_L2Be_4 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_L2Be_4; reflexivity. Qed.
Lemma L2_L2Be_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Be_4; reflexivity]). Qed.
Lemma AXD_L2Be_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Be_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S46S75Z4M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Be_4 : ltac2:(tb__ "0|1|
S0S9S79S46S75Z4M0A1S1fS46G0A2S64SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Be_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Be_4 : ltac2:(tb__ "0|0|
S0S9S7cS68S41A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L2Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3S50A3"). Proof. unfold run3_L2Be; reflexivity. Qed.
Lemma L3_L2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S36U0S50A2S48A3S0S4S36U1S50A2S6aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L2Be | unfold Ebg_L2Be]; reflexivity]). Qed.
Lemma NX3_L2Be : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S41A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L2Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S48A1S5S40A1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L2Be : ltac2:(tb__ "0|0|
S0S4S7S48S5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma NX3b_L2Be : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L2Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L2Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2aSbS2A1A3S40A3S5aA3"). Proof. unfold run4_L2Be; reflexivity. Qed.
Lemma L4_L2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S2aSbS2A1A3A2ScA3S0S4S36U0S5aA2S47A3A2"). Proof. Time (split; [vmr | unfold Ems_L2Be; reflexivity]). Qed.
Lemma D4_L2Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S47A1S5S39A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L2Be : ltac2:(tb__ "0|0|
S0S4S7S47S5S39A1A2S39A3"). Proof. vmr. Qed.
Lemma W4_L2Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S39A1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L2Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S39S7eS2eS39A1A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L2Be : ltac2:(tb__ "0|0|
S0S9S7aS39S7eS2eS39A1S52S84S6S4S8S7fA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L2Be : ltac2:(tb__ "0|0|
S0S4S7bS2eS39A1S7eS31S39S52A5S54A3"). Proof. unfold TM0_L2Be, TM0_of, RM_L2Be; reflexivity. Qed.
Lemma FBM_L2Be : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S54A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L2Be : ltac2:(tb__ "0|0|
S0S4S85S54S17S5S39A1A1A2S4dA3"). Proof. vmr. Qed.
Lemma NX5_L2Be : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4dA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L2Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S29SbS2A1A3S4dA3S5bA3"). Proof. unfold run5_L2Be; reflexivity. Qed.
Lemma L5_L2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S29SbS2A1A3A2ScA3S0S4S36U0S5bA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_L2Be; reflexivity]). Qed.
Lemma AXQ_L2Be : ltac2:(tb__ "0|0|
S0SfS4A1S74S60S32A2SeS4S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L2Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S3aS2cS3bA1S2fS3aS3bA2A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L2Be : ltac2:(tb__ "0|0|
S0S9S7aS3aS2cS3bA1S2fS3aS3bA2S53SaS4S30S3bA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L2Be : ltac2:(tb__ "0|0|
S0S4S7bS2fS3aS3bA2S2cS3bA1S30S3bA1S3aS53A5S55A3"). Proof. unfold TQ0_L2Be, TQ0_of, RQ_L2Be; reflexivity. Qed.
Lemma FBQ_L2Be : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L2Be : ltac2:(tb__ "0|0|
S0S4S85S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX6_L2Be : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L2Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3S51A3"). Proof. unfold run6_L2Be; reflexivity. Qed.
Lemma L6_L2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S36U0S51A2S6bA3S0S4S36U1S51A2S71A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L2Be | unfold Xf_L2Be]; reflexivity]). Qed.

End F0A_cL2Be.

(* [comment removed for export] *)
Module F0A_cL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf"; "C4_L2Bf"; "EQ_L2Bf"; "q_L2Bf"; "C2_L2Bf_1"; "C2_L2Bf_2"; "C2_L2Bf_3"; "C2_L2Bf_4"; "C3_L2Bf"; "CD_L2Bf"; "P0_L2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "Ems_L2Bf"; "Eps_L2Bf"; "S1c_L2Bf_1"; "S1c_L2Bf_2"; "S1c_L2Bf_3"; "S1c_L2Bf_4"; "TM_L2Bf"; "TQ_L2Bf"; "run1_L2Bf"; "run3_L2Bf"; "run6_L2Bf"; "RM_L2Bf"; "RQ_L2Bf"; "TM0_L2Bf"; "TQ0_L2Bf"; "run2_L2Bf_1"; "run2_L2Bf_2"; "run2_L2Bf_3"; "run2_L2Bf_4"; "run4_L2Bf"; "run5_L2Bf"; "EfD_L2Bf_1"; "EfD_L2Bf_2"; "EfD_L2Bf_3"; "EfD_L2Bf_4"; "Eq_L2Bf"; "RD_L2Bf_1"; "RD_L2Bf_2"; "RD_L2Bf_3"; "RD_L2Bf_4"; "TDr_L2Bf_1"; "TDr_L2Bf_2"; "TDr_L2Bf_3"; "TDr_L2Bf_4"; "exits1_L2Bf"; "Ebg_L2Bf"; "Edr_L2Bf"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "W_L2Bf"; "Xf_L2Bf"; "st_L2Bf"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L2Bf : list ulink := Wcan 2.
Definition st_L2Bf : ustop := UStopLe.
Definition q_L2Bf : qvar := QBf.
Definition P0_L2Bf : axst := ltac2:(tb__ "0|0|
S86S11S70S72S3bA4").

Definition run1_L2Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S27SbS2A1A3S42A3").

Definition S1c_L2Bf_1 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z1A3").
Definition C2_L2Bf_1 : axst := C2_of S1c_L2Bf_1.
Definition run2_L2Bf_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L2Bf_1 : axst := leaf 0 run2_L2Bf_1.
Definition ED_L2Bf_1 : axst := ED_of EfD_L2Bf_1.
Definition RD_L2Bf_1 : list sobj := RD_of ED_L2Bf_1 1.
Definition TD_L2Bf_1 : axst := TD_of ED_L2Bf_1 1.
Definition TDr_L2Bf_1 : axst := TDr_of TD_L2Bf_1.
Definition S1c_L2Bf_2 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z2A3").
Definition C2_L2Bf_2 : axst := C2_of S1c_L2Bf_2.
Definition run2_L2Bf_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_L2Bf_2 : axst := leaf 0 run2_L2Bf_2.
Definition ED_L2Bf_2 : axst := ED_of EfD_L2Bf_2.
Definition RD_L2Bf_2 : list sobj := RD_of ED_L2Bf_2 2.
Definition TD_L2Bf_2 : axst := TD_of ED_L2Bf_2 2.
Definition TDr_L2Bf_2 : axst := TDr_of TD_L2Bf_2.
Definition S1c_L2Bf_3 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z3A3").
Definition C2_L2Bf_3 : axst := C2_of S1c_L2Bf_3.
Definition run2_L2Bf_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_L2Bf_3 : axst := leaf 0 run2_L2Bf_3.
Definition ED_L2Bf_3 : axst := ED_of EfD_L2Bf_3.
Definition RD_L2Bf_3 : list sobj := RD_of ED_L2Bf_3 3.
Definition TD_L2Bf_3 : axst := TD_of ED_L2Bf_3 3.
Definition TDr_L2Bf_3 : axst := TDr_of TD_L2Bf_3.
Definition S1c_L2Bf_4 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z4A3").
Definition C2_L2Bf_4 : axst := C2_of S1c_L2Bf_4.
Definition run2_L2Bf_4 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_L2Bf_4 : axst := leaf 0 run2_L2Bf_4.
Definition ED_L2Bf_4 : axst := ED_of EfD_L2Bf_4.
Definition RD_L2Bf_4 : list sobj := RD_of ED_L2Bf_4 4.
Definition TD_L2Bf_4 : axst := TD_of ED_L2Bf_4 4.
Definition TDr_L2Bf_4 : axst := TDr_of TD_L2Bf_4.
Definition exits1_L2Bf : list axst := ltac2:(tb__ "0|0|
SaS4S49SaS4S4aSaS4S4bSaS4S4cSbS4A1A3A3A3A3").

Definition CD_L2Bf : axst := CD_of TDr_L2Bf_1.
Definition run3_L2Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3").
Definition Eps_L2Bf : axst := leaf 0 run3_L2Bf.
Definition Ebg_L2Bf : axst := leaf 1 run3_L2Bf.
Definition C3_L2Bf : axst := C3_of Eps_L2Bf.
Definition run4_L2Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2aSbS2A1A3S40A3").
Definition Ems_L2Bf : axst := leaf 0 run4_L2Bf.
Definition C4_L2Bf : axst := C4_of Ems_L2Bf.
Definition RM_L2Bf : list sobj := RM_of C4_L2Bf.
Definition TM0_L2Bf : axst := TM0_of C4_L2Bf.
Definition TM_L2Bf : axst := TM_of C4_L2Bf.
Definition run5_L2Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S29SbS2A1A3S4dA3").
Definition Eq_L2Bf : axst := leaf 0 run5_L2Bf.
Definition EQ_L2Bf : axst := EQ_of Eq_L2Bf.
Definition RQ_L2Bf : list sobj := RQ_of EQ_L2Bf q_L2Bf.
Definition TQ0_L2Bf : axst := TQ0_of EQ_L2Bf q_L2Bf.
Definition TQ_L2Bf : axst := TQ_of EQ_L2Bf q_L2Bf.
Definition run6_L2Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3").
Definition Edr_L2Bf : axst := leaf 0 run6_L2Bf.
Definition Xf_L2Bf : axst := leaf 1 run6_L2Bf.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L2Bf : ltac2:(tb__ "0|0|
S0S9S82S38S1cSaS2S27SbS2A1A3S37SaS4S42SbS4A1A3S69A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L2Bf exits1_L2Bf run1_L2Bf); [unfold run1_L2Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L2Bf : ltac2:(tb__ "0|2|
S0S9S83S38S1cSaS2S27SbS2A1A3S37SaS80S81S42Z1S1bZ0M0A1M1A3SbS80A1A3S84S4S80S4S81R1G0G1A3LE;S69A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L2Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L2Bf) run1_L2Bf); [unfold run1_L2Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L2Bf_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S49A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Bf_1 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S49S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L2Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S56A3"). Proof. unfold run2_L2Bf_1; reflexivity. Qed.
Lemma L2_L2Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S56A2S5cA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Bf_1; reflexivity]). Qed.
Lemma AXD_L2Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5cS22A2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S43S75Z1M1A1S1fS43G1A2A3SeG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Bf_1 : ltac2:(tb__ "0|1|
S0S9S79S43S75Z1M0A1S1fS43G0A2S61SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6cS23A2SeS4S65A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Bf_1 : ltac2:(tb__ "0|0|
S0S9S7cS65S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Bf_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4aA1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Bf_2 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_L2Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_L2Bf_2; reflexivity. Qed.
Lemma L2_L2Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Bf_2; reflexivity]). Qed.
Lemma AXD_L2Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S44S75Z2M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Bf_2 : ltac2:(tb__ "0|1|
S0S9S79S44S75Z2M0A1S1fS44G0A2S62SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Bf_2 : ltac2:(tb__ "0|0|
S0S9S7cS66S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Bf_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4bA1S5S3eA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Bf_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Bf_3 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Bf_3 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_L2Bf_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_L2Bf_3; reflexivity. Qed.
Lemma L2_L2Bf_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Bf_3; reflexivity]). Qed.
Lemma AXD_L2Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Bf_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S45S75Z3M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Bf_3 : ltac2:(tb__ "0|1|
S0S9S79S45S75Z3M0A1S1fS45G0A2S63SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Bf_3 : ltac2:(tb__ "0|0|
S0S9S7cS67S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L2Bf_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S77S5S4cA1S5S3fA1A2SeG3S12G1G2SaG0S12S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L2Bf_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L2Bf_4 : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L2Bf_4 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_L2Bf_4 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_L2Bf_4; reflexivity. Qed.
Lemma L2_L2Bf_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_L2Bf_4; reflexivity]). Qed.
Lemma AXD_L2Bf_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L2Bf_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S78S46S75Z4M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L2Bf_4 : ltac2:(tb__ "0|1|
S0S9S79S46S75Z4M0A1S1fS46G0A2S64SaS4S76G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L2Bf_4 : ltac2:(tb__ "0|0|
S0SfS4A1S74S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L2Bf_4 : ltac2:(tb__ "0|0|
S0S9S7cS68S41A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3S50A3"). Proof. unfold run3_L2Bf; reflexivity. Qed.
Lemma L3_L2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S36U0S50A2S48A3S0S4S36U1S50A2S6aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L2Bf | unfold Ebg_L2Bf]; reflexivity]). Qed.
Lemma NX3_L2Bf : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S41A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L2Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S48A1S5S40A1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L2Bf : ltac2:(tb__ "0|0|
S0S4S7S48S5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma NX3b_L2Bf : ltac2:(tb__ "0|0|
S0S9S73S37S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L2Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2aSbS2A1A3S40A3S5aA3"). Proof. unfold run4_L2Bf; reflexivity. Qed.
Lemma L4_L2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S2aSbS2A1A3A2ScA3S0S4S36U0S5aA2S47A3A2"). Proof. Time (split; [vmr | unfold Ems_L2Bf; reflexivity]). Qed.
Lemma D4_L2Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S77S5S47A1S5S39A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L2Bf : ltac2:(tb__ "0|0|
S0S4S7S47S5S39A1A2S39A3"). Proof. vmr. Qed.
Lemma W4_L2Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S39A1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L2Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S39S7eS2eS39A1A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L2Bf : ltac2:(tb__ "0|0|
S0S9S7aS39S7eS2eS39A1S52S84S6S4S8S7fA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L2Bf : ltac2:(tb__ "0|0|
S0S4S7bS2eS39A1S7eS31S39S52A5S54A3"). Proof. unfold TM0_L2Bf, TM0_of, RM_L2Bf; reflexivity. Qed.
Lemma FBM_L2Bf : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S54A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L2Bf : ltac2:(tb__ "0|0|
S0S4S85S54S17S5S39A1A1A2S4dA3"). Proof. vmr. Qed.
Lemma NX5_L2Bf : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4dA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S29SbS2A1A3S4dA3S5bA3"). Proof. unfold run5_L2Bf; reflexivity. Qed.
Lemma L5_L2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S29SbS2A1A3A2ScA3S0S4S36U0S5bA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_L2Bf; reflexivity]). Qed.
Lemma AXQ_L2Bf : ltac2:(tb__ "0|0|
S0SfS4A1S74S60S32A2SeS4S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L2Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S78S3aS2cS3bA1S2fS3aS3bA2A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L2Bf : ltac2:(tb__ "0|0|
S0S9S7aS3aS2cS3bA1S2fS3aS3bA2S53SaS4S30S3bA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L2Bf : ltac2:(tb__ "0|0|
S0S4S7bS2fS3aS3bA2S2cS3bA1S30S3bA1S3aS53A5S55A3"). Proof. unfold TQ0_L2Bf, TQ0_of, RQ_L2Bf; reflexivity. Qed.
Lemma FBQ_L2Bf : ltac2:(tb__ "0|3|
S1S0S9S7dS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7dS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S73S37G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L2Bf : ltac2:(tb__ "0|0|
S0S4S85S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX6_L2Bf : ltac2:(tb__ "0|1|
S1S0S9S73S37S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3S51A3"). Proof. unfold run6_L2Bf; reflexivity. Qed.
Lemma L6_L2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S36U0S51A2S6bA3S0S4S36U1S51A2S71A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L2Bf | unfold Xf_L2Bf]; reflexivity]). Qed.

End F0A_cL2Bf.

