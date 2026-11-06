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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From Stdlib Require Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_main.

(* [comment removed for export] *)
Module F0A_c1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf"; "C4_1Bf"; "EQ_1Bf"; "q_1Bf"; "C2_1Bf_1"; "C2_1Bf_2"; "C2_1Bf_3"; "C3_1Bf"; "CD_1Bf"; "P0_1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "Ems_1Bf"; "Eps_1Bf"; "S1c_1Bf_1"; "S1c_1Bf_2"; "S1c_1Bf_3"; "TM_1Bf"; "TQ_1Bf"; "run3_1Bf"; "run6_1Bf"; "RM_1Bf"; "RQ_1Bf"; "TM0_1Bf"; "TQ0_1Bf"; "run1_1Bf"; "run2_1Bf_1"; "run2_1Bf_2"; "run2_1Bf_3"; "run4_1Bf"; "run5_1Bf"; "EfD_1Bf_1"; "EfD_1Bf_2"; "EfD_1Bf_3"; "Eq_1Bf"; "RD_1Bf_1"; "RD_1Bf_2"; "RD_1Bf_3"; "TDr_1Bf_1"; "TDr_1Bf_2"; "TDr_1Bf_3"; "exits1_1Bf"; "Ebg_1Bf"; "Edr_1Bf"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "W_1Bf"; "Xf_1Bf"; "st_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_1Bf : list ulink := Wcan 1.
Definition st_1Bf : ustop := UStopLe.
Definition q_1Bf : qvar := QBf.
Definition P0_1Bf : axst := ltac2:(tb__ "0|0|
S31S67S69S3aA3").

Definition run1_1Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_1Bf_1 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z1A3").
Definition C2_1Bf_1 : axst := C2_of S1c_1Bf_1.
Definition run2_1Bf_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_1Bf_1 : axst := leaf 0 run2_1Bf_1.
Definition ED_1Bf_1 : axst := ED_of EfD_1Bf_1.
Definition RD_1Bf_1 : list sobj := RD_of ED_1Bf_1 1.
Definition TD_1Bf_1 : axst := TD_of ED_1Bf_1 1.
Definition TDr_1Bf_1 : axst := TDr_of TD_1Bf_1.
Definition S1c_1Bf_2 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z2A3").
Definition C2_1Bf_2 : axst := C2_of S1c_1Bf_2.
Definition run2_1Bf_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_1Bf_2 : axst := leaf 0 run2_1Bf_2.
Definition ED_1Bf_2 : axst := ED_of EfD_1Bf_2.
Definition RD_1Bf_2 : list sobj := RD_of ED_1Bf_2 2.
Definition TD_1Bf_2 : axst := TD_of ED_1Bf_2 2.
Definition TDr_1Bf_2 : axst := TDr_of TD_1Bf_2.
Definition S1c_1Bf_3 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z3A3").
Definition C2_1Bf_3 : axst := C2_of S1c_1Bf_3.
Definition run2_1Bf_3 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_1Bf_3 : axst := leaf 0 run2_1Bf_3.
Definition ED_1Bf_3 : axst := ED_of EfD_1Bf_3.
Definition RD_1Bf_3 : list sobj := RD_of ED_1Bf_3 3.
Definition TD_1Bf_3 : axst := TD_of ED_1Bf_3 3.
Definition TDr_1Bf_3 : axst := TDr_of TD_1Bf_3.
Definition exits1_1Bf : list axst := ltac2:(tb__ "0|0|
SaS4S46SaS4S47SaS4S48SbS4A1A3A3A3").

Definition CD_1Bf : axst := CD_of TDr_1Bf_1.
Definition run3_1Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3").
Definition Eps_1Bf : axst := leaf 0 run3_1Bf.
Definition Ebg_1Bf : axst := leaf 1 run3_1Bf.
Definition C3_1Bf : axst := C3_of Eps_1Bf.
Definition run4_1Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S25SbS2A1A3S3eA3").
Definition Ems_1Bf : axst := leaf 0 run4_1Bf.
Definition C4_1Bf : axst := C4_of Ems_1Bf.
Definition RM_1Bf : list sobj := RM_of C4_1Bf.
Definition TM0_1Bf : axst := TM0_of C4_1Bf.
Definition TM_1Bf : axst := TM_of C4_1Bf.
Definition run5_1Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S23SbS2A1A3S49A3").
Definition Eq_1Bf : axst := leaf 0 run5_1Bf.
Definition EQ_1Bf : axst := EQ_of Eq_1Bf.
Definition RQ_1Bf : list sobj := RQ_of EQ_1Bf q_1Bf.
Definition TQ0_1Bf : axst := TQ0_of EQ_1Bf q_1Bf.
Definition TQ_1Bf : axst := TQ_of EQ_1Bf q_1Bf.
Definition run6_1Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3").
Definition Edr_1Bf : axst := leaf 0 run6_1Bf.
Definition Xf_1Bf : axst := leaf 1 run6_1Bf.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_1Bf : ltac2:(tb__ "0|0|
S0S9S7aS6bS1cSaS2S21SbS2A1A3S6aSaS4S40SbS4A1A3S61A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_1Bf exits1_1Bf run1_1Bf); [unfold run1_1Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_1Bf : ltac2:(tb__ "0|2|
S0S9S7bS6bS1cSaS2S21SbS2A1A3S6aSaS78S79S40Z1S1bZ0M0A1M1A3SbS78A1A3S7dS4S78S4S79R1G0G1A3LE;S61A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_1Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_1Bf) run1_1Bf); [unfold run1_1Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_1Bf_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Bf_1 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_1Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_1Bf_1; reflexivity. Qed.
Lemma L2_1Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_1Bf_1; reflexivity]). Qed.
Lemma AXD_1Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S41S6eZ1M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Bf_1 : ltac2:(tb__ "0|1|
S0S9S72S41S6eZ1M0A1S1fS41G0A2S5bSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Bf_1 : ltac2:(tb__ "0|0|
S0S9S7cS5eS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Bf_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Bf_2 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_1Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_1Bf_2; reflexivity. Qed.
Lemma L2_1Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_1Bf_2; reflexivity]). Qed.
Lemma AXD_1Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S42S6eZ2M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Bf_2 : ltac2:(tb__ "0|1|
S0S9S72S42S6eZ2M0A1S1fS42G0A2S5cSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Bf_2 : ltac2:(tb__ "0|0|
S0S9S7cS5fS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Bf_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S48A1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Bf_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Bf_3 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Bf_3 : ltac2:(tb__ "0|0|
S0S4S7S48S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_1Bf_3 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3dA3S54A3"). Proof. unfold run2_1Bf_3; reflexivity. Qed.
Lemma L2_1Bf_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S54A2S59A3A2"). Proof. Time (split; [vmr | unfold EfD_1Bf_3; reflexivity]). Qed.
Lemma AXD_1Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS59S2aA2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Bf_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S43S6eZ3M1A1S1fS43G1A2A3SeG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Bf_3 : ltac2:(tb__ "0|1|
S0S9S72S43S6eZ3M0A1S1fS43G0A2S5dSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS66S2bA2SeS4S60A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Bf_3 : ltac2:(tb__ "0|0|
S0S9S7cS60S3fA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3S4bA3"). Proof. unfold run3_1Bf; reflexivity. Qed.
Lemma L3_1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S37U0S4bA2S45A3S0S4S37U1S4bA2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_1Bf | unfold Ebg_1Bf]; reflexivity]). Qed.
Lemma NX3_1Bf : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S3fA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_1Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S45A1S5S3eA1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_1Bf : ltac2:(tb__ "0|0|
S0S4S7S45S5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma NX3b_1Bf : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_1Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S25SbS2A1A3S3eA3S55A3"). Proof. unfold run4_1Bf; reflexivity. Qed.
Lemma L4_1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S25SbS2A1A3A2ScA3S0S4S37U0S55A2S44A3A2"). Proof. Time (split; [vmr | unfold Ems_1Bf; reflexivity]). Qed.
Lemma D4_1Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S44A1S5S38A1A2SeG2S12G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_1Bf : ltac2:(tb__ "0|0|
S0S4S7S44S5S38A1A2S38A3"). Proof. vmr. Qed.
Lemma W4_1Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S38A1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_1Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S38S76S2dS38A1A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_1Bf : ltac2:(tb__ "0|0|
S0S9S73S38S76S2dS38A1S4dS7dS6S4S8S77A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_1Bf : ltac2:(tb__ "0|0|
S0S4S74S2dS38A1S76S32S38S4dA5S4fA3"). Proof. unfold TM0_1Bf, TM0_of, RM_1Bf; reflexivity. Qed.
Lemma FBM_1Bf : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_1Bf : ltac2:(tb__ "0|0|
S0S4S7eS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX5_1Bf : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S23SbS2A1A3S49A3S56A3"). Proof. unfold run5_1Bf; reflexivity. Qed.
Lemma L5_1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S23SbS2A1A3A2ScA3S0S4S37U0S56A2S5aA3A2"). Proof. Time (split; [vmr | unfold Eq_1Bf; reflexivity]). Qed.
Lemma AXQ_1Bf : ltac2:(tb__ "0|0|
S0SfS4A1S6dS5aS33A2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_1Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S39S27S3aA1S2eS39S3aA2A3SeG0S4eA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_1Bf : ltac2:(tb__ "0|0|
S0S9S73S39S27S3aA1S2eS39S3aA2S4eSaS4S30S3aA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_1Bf : ltac2:(tb__ "0|0|
S0S4S74S2eS39S3aA2S27S3aA1S30S3aA1S39S4eA5S50A3"). Proof. unfold TQ0_1Bf, TQ0_of, RQ_1Bf; reflexivity. Qed.
Lemma FBQ_1Bf : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S50A1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_1Bf : ltac2:(tb__ "0|0|
S0S4S7eS50S17S5S39A1A1A2S4aA3"). Proof. vmr. Qed.
Lemma NX6_1Bf : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S4aA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_1Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3S4cA3"). Proof. unfold run6_1Bf; reflexivity. Qed.
Lemma L6_1Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS4cSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S37U0S4cA2S63A3S0S4S37U1S4cA2S68A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_1Bf | unfold Xf_1Bf]; reflexivity]). Qed.

End F0A_c1Bf.

(* [comment removed for export] *)
Module F0A_c2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "C4_2A"; "EQ_2A"; "q_2A"; "C2_2A_1"; "C2_2A_2"; "C2_2A_3"; "C2_2A_4"; "C3_2A"; "CD_2A"; "P0_2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "Ems_2A"; "Eps_2A"; "S1c_2A_1"; "S1c_2A_2"; "S1c_2A_3"; "S1c_2A_4"; "TM_2A"; "TQ_2A"; "run1_2A"; "run3_2A"; "run6_2A"; "RM_2A"; "RQ_2A"; "TM0_2A"; "TQ0_2A"; "run2_2A_1"; "run2_2A_2"; "run2_2A_3"; "run2_2A_4"; "run4_2A"; "run5_2A"; "EfD_2A_1"; "EfD_2A_2"; "EfD_2A_3"; "EfD_2A_4"; "Eq_2A"; "RD_2A_1"; "RD_2A_2"; "RD_2A_3"; "RD_2A_4"; "TDr_2A_1"; "TDr_2A_2"; "TDr_2A_3"; "TDr_2A_4"; "exits1_2A"; "Ebg_2A"; "Edr_2A"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "Xf_2A"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_2A : list ulink := Wcan 2.
Definition st_2A : ustop := UStopLe.
Definition q_2A : qvar := QA.
Definition P0_2A : axst := P0_f W_2A st_2A q_2A.

Definition run1_2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S27SbS2A1A3S42A3").

Definition S1c_2A_1 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z1A3").
Definition C2_2A_1 : axst := C2_of S1c_2A_1.
Definition run2_2A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_2A_1 : axst := leaf 0 run2_2A_1.
Definition ED_2A_1 : axst := ED_of EfD_2A_1.
Definition RD_2A_1 : list sobj := RD_of ED_2A_1 1.
Definition TD_2A_1 : axst := TD_of ED_2A_1 1.
Definition TDr_2A_1 : axst := TDr_of TD_2A_1.
Definition S1c_2A_2 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z2A3").
Definition C2_2A_2 : axst := C2_of S1c_2A_2.
Definition run2_2A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_2A_2 : axst := leaf 0 run2_2A_2.
Definition ED_2A_2 : axst := ED_of EfD_2A_2.
Definition RD_2A_2 : list sobj := RD_of ED_2A_2 2.
Definition TD_2A_2 : axst := TD_of ED_2A_2 2.
Definition TDr_2A_2 : axst := TDr_of TD_2A_2.
Definition S1c_2A_3 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z3A3").
Definition C2_2A_3 : axst := C2_of S1c_2A_3.
Definition run2_2A_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_2A_3 : axst := leaf 0 run2_2A_3.
Definition ED_2A_3 : axst := ED_of EfD_2A_3.
Definition RD_2A_3 : list sobj := RD_of ED_2A_3 3.
Definition TD_2A_3 : axst := TD_of ED_2A_3 3.
Definition TDr_2A_3 : axst := TDr_of TD_2A_3.
Definition S1c_2A_4 : axst := ltac2:(tb__ "0|0|
S21S36U0S4fA2S17S5S42A1A1Z4A3").
Definition C2_2A_4 : axst := C2_of S1c_2A_4.
Definition run2_2A_4 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_2A_4 : axst := leaf 0 run2_2A_4.
Definition ED_2A_4 : axst := ED_of EfD_2A_4.
Definition RD_2A_4 : list sobj := RD_of ED_2A_4 4.
Definition TD_2A_4 : axst := TD_of ED_2A_4 4.
Definition TDr_2A_4 : axst := TDr_of TD_2A_4.
Definition exits1_2A : list axst := ltac2:(tb__ "0|0|
SaS4S49SaS4S4aSaS4S4bSaS4S4cSbS4A1A3A3A3A3").

Definition CD_2A : axst := CD_of TDr_2A_1.
Definition run3_2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3").
Definition Eps_2A : axst := leaf 0 run3_2A.
Definition Ebg_2A : axst := leaf 1 run3_2A.
Definition C3_2A : axst := C3_of Eps_2A.
Definition run4_2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S2aSbS2A1A3S40A3").
Definition Ems_2A : axst := leaf 0 run4_2A.
Definition C4_2A : axst := C4_of Ems_2A.
Definition RM_2A : list sobj := RM_of C4_2A.
Definition TM0_2A : axst := TM0_of C4_2A.
Definition TM_2A : axst := TM_of C4_2A.
Definition run5_2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S29SbS2A1A3S4dA3").
Definition Eq_2A : axst := leaf 0 run5_2A.
Definition EQ_2A : axst := EQ_of Eq_2A.
Definition RQ_2A : list sobj := RQ_of EQ_2A q_2A.
Definition TQ0_2A : axst := TQ0_of EQ_2A q_2A.
Definition TQ_2A : axst := TQ_of EQ_2A q_2A.
Definition run6_2A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3").
Definition Edr_2A : axst := leaf 0 run6_2A.
Definition Xf_2A : axst := leaf 1 run6_2A.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_2A : ltac2:(tb__ "0|0|
S0S9S80S38S1cSaS2S27SbS2A1A3S37SaS4S42SbS4A1A3S69A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_2A exits1_2A run1_2A); [unfold run1_2A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_2A : ltac2:(tb__ "0|2|
S0S9S81S38S1cSaS2S27SbS2A1A3S37SaS7eS7fS42Z1S1bZ0M0A1M1A3SbS7eA1A3S82S4S7eS4S7fR1G0G1A3LE;S69A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_2A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_2A) run1_2A); [unfold run1_2A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_2A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S75S5S49A1S5S3cA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2A_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2A_1 : ltac2:(tb__ "0|0|
S0S9S71S37S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2A_1 : ltac2:(tb__ "0|0|
S0S4S7S49S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_2A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S56A3"). Proof. unfold run2_2A_1; reflexivity. Qed.
Lemma L2_2A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S56A2S5cA3A2"). Proof. Time (split; [vmr | unfold EfD_2A_1; reflexivity]). Qed.
Lemma AXD_2A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S72S5cS22A2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S76S43S73Z1M1A1S1fS43G1A2A3SeG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2A_1 : ltac2:(tb__ "0|1|
S0S9S77S43S73Z1M0A1S1fS43G0A2S61SaS4S74G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S72S6cS23A2SeS4S65A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2A_1 : ltac2:(tb__ "0|0|
S0S9S7aS65S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S75S5S4aA1S5S3dA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2A_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2A_2 : ltac2:(tb__ "0|0|
S0S9S71S37S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2A_2 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_2A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_2A_2; reflexivity. Qed.
Lemma L2_2A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_2A_2; reflexivity]). Qed.
Lemma AXD_2A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S72S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S76S44S73Z2M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2A_2 : ltac2:(tb__ "0|1|
S0S9S77S44S73Z2M0A1S1fS44G0A2S62SaS4S74G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S72S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2A_2 : ltac2:(tb__ "0|0|
S0S9S7aS66S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2A_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S75S5S4bA1S5S3eA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2A_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2A_3 : ltac2:(tb__ "0|0|
S0S9S71S37S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2A_3 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_2A_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_2A_3; reflexivity. Qed.
Lemma L2_2A_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_2A_3; reflexivity]). Qed.
Lemma AXD_2A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S72S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2A_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S76S45S73Z3M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2A_3 : ltac2:(tb__ "0|1|
S0S9S77S45S73Z3M0A1S1fS45G0A2S63SaS4S74G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S72S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2A_3 : ltac2:(tb__ "0|0|
S0S9S7aS67S41A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2A_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S75S5S4cA1S5S3fA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2A_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2A_4 : ltac2:(tb__ "0|0|
S0S9S71S37S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2A_4 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_2A_4 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_2A_4; reflexivity. Qed.
Lemma L2_2A_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_2A_4; reflexivity]). Qed.
Lemma AXD_2A_4 : ltac2:(tb__ "0|0|
S0SfS4A1S72S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2A_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S76S46S73Z4M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2A_4 : ltac2:(tb__ "0|1|
S0S9S77S46S73Z4M0A1S1fS46G0A2S64SaS4S74G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2A_4 : ltac2:(tb__ "0|0|
S0SfS4A1S72S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2A_4 : ltac2:(tb__ "0|0|
S0S9S7aS68S41A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2bSaS2S26SbS2A1A3A3S41A3S50A3"). Proof. unfold run3_2A; reflexivity. Qed.
Lemma L3_2A : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S36U0S50A2S48A3S0S4S36U1S50A2S6aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_2A | unfold Ebg_2A]; reflexivity]). Qed.
Lemma NX3_2A : ltac2:(tb__ "0|1|
S1S0S9S71S37S13S5S41A1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_2A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S75S5S48A1S5S40A1A2SeG2S11G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_2A : ltac2:(tb__ "0|0|
S0S4S7S48S5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma NX3b_2A : ltac2:(tb__ "0|0|
S0S9S71S37S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_2A : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S2aSbS2A1A3S40A3S5aA3"). Proof. unfold run4_2A; reflexivity. Qed.
Lemma L4_2A : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S2aSbS2A1A3A2ScA3S0S4S36U0S5aA2S47A3A2"). Proof. Time (split; [vmr | unfold Ems_2A; reflexivity]). Qed.
Lemma D4_2A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S75S5S47A1S5S39A1A2SeG2S11G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_2A : ltac2:(tb__ "0|0|
S0S4S7S47S5S39A1A2S39A3"). Proof. vmr. Qed.
Lemma W4_2A : ltac2:(tb__ "0|1|
S1S0S9S19S5S39A1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_2A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S76S39S7cS2eS39A1A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_2A : ltac2:(tb__ "0|0|
S0S9S78S39S7cS2eS39A1S52S82S6S4S8S7dA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_2A : ltac2:(tb__ "0|0|
S0S4S79S2eS39A1S7cS31S39S52A5S54A3"). Proof. unfold TM0_2A, TM0_of, RM_2A; reflexivity. Qed.
Lemma FBM_2A : ltac2:(tb__ "0|3|
S1S0S9S7bS15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7bS15S1aS13S5S54A1A1A1G2A3ScA3S0S9S71S37G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_2A : ltac2:(tb__ "0|0|
S0S4S83S54S17S5S39A1A1A2S4dA3"). Proof. vmr. Qed.
Lemma NX5_2A : ltac2:(tb__ "0|1|
S1S0S9S71S37S13S5S4dA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S29SbS2A1A3S4dA3S5bA3"). Proof. unfold run5_2A; reflexivity. Qed.
Lemma L5_2A : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S29SbS2A1A3A2ScA3S0S4S36U0S5bA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_2A; reflexivity]). Qed.
Lemma AXQ_2A : ltac2:(tb__ "0|0|
S0SfS4A1S72S60S32A2SeS4S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_2A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S76S3aS2cS3bA1S2fS3aS3bA2A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_2A : ltac2:(tb__ "0|0|
S0S9S78S3aS2cS3bA1S2fS3aS3bA2S53SaS4S30S3bA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_2A : ltac2:(tb__ "0|0|
S0S4S79S2fS3aS3bA2S2cS3bA1S30S3bA1S3aS53A5S55A3"). Proof. unfold TQ0_2A, TQ0_of, RQ_2A; reflexivity. Qed.
Lemma FBQ_2A : ltac2:(tb__ "0|3|
S1S0S9S7bS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7bS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S71S37G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_2A : ltac2:(tb__ "0|0|
S0S4S83S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX6_2A : ltac2:(tb__ "0|1|
S1S0S9S71S37S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_2A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S28SaS2S2dSbS2A1A3A3S4eA3S51A3"). Proof. unfold run6_2A; reflexivity. Qed.
Lemma L6_2A : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S36U0S51A2S6bA3S0S4S36U1S51A2S70A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_2A | unfold Xf_2A]; reflexivity]). Qed.

End F0A_c2A.

(* [comment removed for export] *)
Module F0A_c2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be"; "C4_2Be"; "EQ_2Be"; "q_2Be"; "C2_2Be_1"; "C2_2Be_2"; "C2_2Be_3"; "C2_2Be_4"; "C3_2Be"; "CD_2Be"; "P0_2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "Ems_2Be"; "Eps_2Be"; "S1c_2Be_1"; "S1c_2Be_2"; "S1c_2Be_3"; "S1c_2Be_4"; "TM_2Be"; "TQ_2Be"; "run1_2Be"; "run3_2Be"; "run6_2Be"; "RM_2Be"; "RQ_2Be"; "TM0_2Be"; "TQ0_2Be"; "run2_2Be_1"; "run2_2Be_2"; "run2_2Be_3"; "run2_2Be_4"; "run4_2Be"; "run5_2Be"; "EfD_2Be_1"; "EfD_2Be_2"; "EfD_2Be_3"; "EfD_2Be_4"; "Eq_2Be"; "RD_2Be_1"; "RD_2Be_2"; "RD_2Be_3"; "RD_2Be_4"; "TDr_2Be_1"; "TDr_2Be_2"; "TDr_2Be_3"; "TDr_2Be_4"; "exits1_2Be"; "Ebg_2Be"; "Edr_2Be"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "W_2Be"; "Xf_2Be"; "st_2Be"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_2Be : list ulink := Wcan 2.
Definition st_2Be : ustop := UStopLe.
Definition q_2Be : qvar := QBe.
Definition P0_2Be : axst := ltac2:(tb__ "0|0|
S31S71S73S3cA3").

Definition run1_2Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S27SbS2A1A3S43A3").

Definition S1c_2Be_1 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z1A3").
Definition C2_2Be_1 : axst := C2_of S1c_2Be_1.
Definition run2_2Be_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_2Be_1 : axst := leaf 0 run2_2Be_1.
Definition ED_2Be_1 : axst := ED_of EfD_2Be_1.
Definition RD_2Be_1 : list sobj := RD_of ED_2Be_1 1.
Definition TD_2Be_1 : axst := TD_of ED_2Be_1 1.
Definition TDr_2Be_1 : axst := TDr_of TD_2Be_1.
Definition S1c_2Be_2 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z2A3").
Definition C2_2Be_2 : axst := C2_of S1c_2Be_2.
Definition run2_2Be_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_2Be_2 : axst := leaf 0 run2_2Be_2.
Definition ED_2Be_2 : axst := ED_of EfD_2Be_2.
Definition RD_2Be_2 : list sobj := RD_of ED_2Be_2 2.
Definition TD_2Be_2 : axst := TD_of ED_2Be_2 2.
Definition TDr_2Be_2 : axst := TDr_of TD_2Be_2.
Definition S1c_2Be_3 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z3A3").
Definition C2_2Be_3 : axst := C2_of S1c_2Be_3.
Definition run2_2Be_3 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_2Be_3 : axst := leaf 0 run2_2Be_3.
Definition ED_2Be_3 : axst := ED_of EfD_2Be_3.
Definition RD_2Be_3 : list sobj := RD_of ED_2Be_3 3.
Definition TD_2Be_3 : axst := TD_of ED_2Be_3 3.
Definition TDr_2Be_3 : axst := TDr_of TD_2Be_3.
Definition S1c_2Be_4 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z4A3").
Definition C2_2Be_4 : axst := C2_of S1c_2Be_4.
Definition run2_2Be_4 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S40A3").
Definition EfD_2Be_4 : axst := leaf 0 run2_2Be_4.
Definition ED_2Be_4 : axst := ED_of EfD_2Be_4.
Definition RD_2Be_4 : list sobj := RD_of ED_2Be_4 4.
Definition TD_2Be_4 : axst := TD_of ED_2Be_4 4.
Definition TDr_2Be_4 : axst := TDr_of TD_2Be_4.
Definition exits1_2Be : list axst := ltac2:(tb__ "0|0|
SaS4S4aSaS4S4bSaS4S4cSaS4S4dSbS4A1A3A3A3A3").

Definition CD_2Be : axst := CD_of TDr_2Be_1.
Definition run3_2Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S2bSaS2S26SbS2A1A3A3S42A3").
Definition Eps_2Be : axst := leaf 0 run3_2Be.
Definition Ebg_2Be : axst := leaf 1 run3_2Be.
Definition C3_2Be : axst := C3_of Eps_2Be.
Definition run4_2Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S2aSbS2A1A3S41A3").
Definition Ems_2Be : axst := leaf 0 run4_2Be.
Definition C4_2Be : axst := C4_of Ems_2Be.
Definition RM_2Be : list sobj := RM_of C4_2Be.
Definition TM0_2Be : axst := TM0_of C4_2Be.
Definition TM_2Be : axst := TM_of C4_2Be.
Definition run5_2Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S29SbS2A1A3S4eA3").
Definition Eq_2Be : axst := leaf 0 run5_2Be.
Definition EQ_2Be : axst := EQ_of Eq_2Be.
Definition RQ_2Be : list sobj := RQ_of EQ_2Be q_2Be.
Definition TQ0_2Be : axst := TQ0_of EQ_2Be q_2Be.
Definition TQ_2Be : axst := TQ_of EQ_2Be q_2Be.
Definition run6_2Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S28SaS2S2dSbS2A1A3A3S4fA3").
Definition Edr_2Be : axst := leaf 0 run6_2Be.
Definition Xf_2Be : axst := leaf 1 run6_2Be.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_2Be : ltac2:(tb__ "0|0|
S0S9S83S39S1cSaS2S27SbS2A1A3S38SaS4S43SbS4A1A3S6aA6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_2Be exits1_2Be run1_2Be); [unfold run1_2Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_2Be : ltac2:(tb__ "0|2|
S0S9S84S39S1cSaS2S27SbS2A1A3S38SaS81S82S43Z1S1bZ0M0A1M1A3SbS81A1A3S85S4S81S4S82R1G0G1A3LE;S6aA4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_2Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_2Be) run1_2Be); [unfold run1_2Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_2Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4aA1S5S3dA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Be_1 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Be_1 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_2Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_2Be_1; reflexivity. Qed.
Lemma L2_2Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_2Be_1; reflexivity]). Qed.
Lemma AXD_2Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S44S76Z1M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Be_1 : ltac2:(tb__ "0|1|
S0S9S7aS44S76Z1M0A1S1fS44G0A2S62SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Be_1 : ltac2:(tb__ "0|0|
S0S9S7dS66S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4bA1S5S3eA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Be_2 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Be_2 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_2Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_2Be_2; reflexivity. Qed.
Lemma L2_2Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_2Be_2; reflexivity]). Qed.
Lemma AXD_2Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S45S76Z2M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Be_2 : ltac2:(tb__ "0|1|
S0S9S7aS45S76Z2M0A1S1fS45G0A2S63SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Be_2 : ltac2:(tb__ "0|0|
S0S9S7dS67S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4cA1S5S3fA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Be_3 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Be_3 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_2Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_2Be_3; reflexivity. Qed.
Lemma L2_2Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_2Be_3; reflexivity]). Qed.
Lemma AXD_2Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S46S76Z3M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Be_3 : ltac2:(tb__ "0|1|
S0S9S7aS46S76Z3M0A1S1fS46G0A2S64SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Be_3 : ltac2:(tb__ "0|0|
S0S9S7dS68S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Be_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4dA1S5S40A1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Be_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S4dA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Be_4 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Be_4 : ltac2:(tb__ "0|0|
S0S4S7S4dS5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma RUN2_2Be_4 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S40A3S5aA3"). Proof. unfold run2_2Be_4; reflexivity. Qed.
Lemma L2_2Be_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S5aA2S60A3A2"). Proof. Time (split; [vmr | unfold EfD_2Be_4; reflexivity]). Qed.
Lemma AXD_2Be_4 : ltac2:(tb__ "0|0|
S0SfS4A1S75S60S22A2SeS4S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Be_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S47S76Z4M1A1S1fS47G1A2A3SeG0S65A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Be_4 : ltac2:(tb__ "0|1|
S0S9S7aS47S76Z4M0A1S1fS47G0A2S65SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Be_4 : ltac2:(tb__ "0|0|
S0SfS4A1S75S70S23A2SeS4S69A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Be_4 : ltac2:(tb__ "0|0|
S0S9S7dS69S42A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_2Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S2bSaS2S26SbS2A1A3A3S42A3S51A3"). Proof. unfold run3_2Be; reflexivity. Qed.
Lemma L3_2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S37U0S51A2S49A3S0S4S37U1S51A2S6bA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_2Be | unfold Ebg_2Be]; reflexivity]). Qed.
Lemma NX3_2Be : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S42A1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_2Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S78S5S49A1S5S41A1A2SeG2S11G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_2Be : ltac2:(tb__ "0|0|
S0S4S7S49S5S41A1A2S41A3"). Proof. vmr. Qed.
Lemma NX3b_2Be : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S41A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_2Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S41A1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_2Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S2aSbS2A1A3S41A3S5bA3"). Proof. unfold run4_2Be; reflexivity. Qed.
Lemma L4_2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S2aSbS2A1A3A2ScA3S0S4S37U0S5bA2S48A3A2"). Proof. Time (split; [vmr | unfold Ems_2Be; reflexivity]). Qed.
Lemma D4_2Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S78S5S48A1S5S3aA1A2SeG2S11G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_2Be : ltac2:(tb__ "0|0|
S0S4S7S48S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma W4_2Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_2Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S79S3aS7fS2eS3aA1A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_2Be : ltac2:(tb__ "0|0|
S0S9S7bS3aS7fS2eS3aA1S53S85S6S4S8S80A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_2Be : ltac2:(tb__ "0|0|
S0S4S7cS2eS3aA1S7fS32S3aS53A5S55A3"). Proof. unfold TM0_2Be, TM0_of, RM_2Be; reflexivity. Qed.
Lemma FBM_2Be : ltac2:(tb__ "0|3|
S1S0S9S7eS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7eS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S74S38G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_2Be : ltac2:(tb__ "0|0|
S0S4S86S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX5_2Be : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_2Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S29SbS2A1A3S4eA3S5cA3"). Proof. unfold run5_2Be; reflexivity. Qed.
Lemma L5_2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS5cSaS2S29SbS2A1A3A2ScA3S0S4S37U0S5cA2S61A3A2"). Proof. Time (split; [vmr | unfold Eq_2Be; reflexivity]). Qed.
Lemma AXQ_2Be : ltac2:(tb__ "0|0|
S0SfS4A1S75S61S33A2SeS4S3bA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_2Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S79S3bS2cS3cA1S2fS3bS3cA2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_2Be : ltac2:(tb__ "0|0|
S0S9S7bS3bS2cS3cA1S2fS3bS3cA2S54SaS4S30S3cA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_2Be : ltac2:(tb__ "0|0|
S0S4S7cS2fS3bS3cA2S2cS3cA1S30S3cA1S3bS54A5S56A3"). Proof. unfold TQ0_2Be, TQ0_of, RQ_2Be; reflexivity. Qed.
Lemma FBQ_2Be : ltac2:(tb__ "0|3|
S1S0S9S7eS15S1aS13S5S3bA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7eS15S1aS13S5S56A1A1A1G2A3ScA3S0S9S74S38G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_2Be : ltac2:(tb__ "0|0|
S0S4S86S56S17S5S3bA1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX6_2Be : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S4fA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_2Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S28SaS2S2dSbS2A1A3A3S4fA3S52A3"). Proof. unfold run6_2Be; reflexivity. Qed.
Lemma L6_2Be : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S37U0S52A2S6cA3S0S4S37U1S52A2S72A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_2Be | unfold Xf_2Be]; reflexivity]). Qed.

End F0A_c2Be.

(* [comment removed for export] *)
Module F0A_c2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "C4_2Bf"; "EQ_2Bf"; "q_2Bf"; "C2_2Bf_1"; "C2_2Bf_2"; "C2_2Bf_3"; "C2_2Bf_4"; "C3_2Bf"; "CD_2Bf"; "P0_2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "Ems_2Bf"; "Eps_2Bf"; "S1c_2Bf_1"; "S1c_2Bf_2"; "S1c_2Bf_3"; "S1c_2Bf_4"; "TM_2Bf"; "TQ_2Bf"; "run1_2Bf"; "run3_2Bf"; "run6_2Bf"; "RM_2Bf"; "RQ_2Bf"; "TM0_2Bf"; "TQ0_2Bf"; "run2_2Bf_1"; "run2_2Bf_2"; "run2_2Bf_3"; "run2_2Bf_4"; "run4_2Bf"; "run5_2Bf"; "EfD_2Bf_1"; "EfD_2Bf_2"; "EfD_2Bf_3"; "EfD_2Bf_4"; "Eq_2Bf"; "RD_2Bf_1"; "RD_2Bf_2"; "RD_2Bf_3"; "RD_2Bf_4"; "TDr_2Bf_1"; "TDr_2Bf_2"; "TDr_2Bf_3"; "TDr_2Bf_4"; "exits1_2Bf"; "Ebg_2Bf"; "Edr_2Bf"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "W_2Bf"; "Xf_2Bf"; "st_2Bf"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_2Bf : list ulink := Wcan 2.
Definition st_2Bf : ustop := UStopLe.
Definition q_2Bf : qvar := QBf.
Definition P0_2Bf : axst := ltac2:(tb__ "0|0|
S31S71S73S3cA3").

Definition run1_2Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S27SbS2A1A3S43A3").

Definition S1c_2Bf_1 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z1A3").
Definition C2_2Bf_1 : axst := C2_of S1c_2Bf_1.
Definition run2_2Bf_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_2Bf_1 : axst := leaf 0 run2_2Bf_1.
Definition ED_2Bf_1 : axst := ED_of EfD_2Bf_1.
Definition RD_2Bf_1 : list sobj := RD_of ED_2Bf_1 1.
Definition TD_2Bf_1 : axst := TD_of ED_2Bf_1 1.
Definition TDr_2Bf_1 : axst := TDr_of TD_2Bf_1.
Definition S1c_2Bf_2 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z2A3").
Definition C2_2Bf_2 : axst := C2_of S1c_2Bf_2.
Definition run2_2Bf_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3eA3").
Definition EfD_2Bf_2 : axst := leaf 0 run2_2Bf_2.
Definition ED_2Bf_2 : axst := ED_of EfD_2Bf_2.
Definition RD_2Bf_2 : list sobj := RD_of ED_2Bf_2 2.
Definition TD_2Bf_2 : axst := TD_of ED_2Bf_2 2.
Definition TDr_2Bf_2 : axst := TDr_of TD_2Bf_2.
Definition S1c_2Bf_3 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z3A3").
Definition C2_2Bf_3 : axst := C2_of S1c_2Bf_3.
Definition run2_2Bf_3 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3fA3").
Definition EfD_2Bf_3 : axst := leaf 0 run2_2Bf_3.
Definition ED_2Bf_3 : axst := ED_of EfD_2Bf_3.
Definition RD_2Bf_3 : list sobj := RD_of ED_2Bf_3 3.
Definition TD_2Bf_3 : axst := TD_of ED_2Bf_3 3.
Definition TDr_2Bf_3 : axst := TDr_of TD_2Bf_3.
Definition S1c_2Bf_4 : axst := ltac2:(tb__ "0|0|
S21S37U0S50A2S17S5S43A1A1Z4A3").
Definition C2_2Bf_4 : axst := C2_of S1c_2Bf_4.
Definition run2_2Bf_4 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S40A3").
Definition EfD_2Bf_4 : axst := leaf 0 run2_2Bf_4.
Definition ED_2Bf_4 : axst := ED_of EfD_2Bf_4.
Definition RD_2Bf_4 : list sobj := RD_of ED_2Bf_4 4.
Definition TD_2Bf_4 : axst := TD_of ED_2Bf_4 4.
Definition TDr_2Bf_4 : axst := TDr_of TD_2Bf_4.
Definition exits1_2Bf : list axst := ltac2:(tb__ "0|0|
SaS4S4aSaS4S4bSaS4S4cSaS4S4dSbS4A1A3A3A3A3").

Definition CD_2Bf : axst := CD_of TDr_2Bf_1.
Definition run3_2Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S2bSaS2S26SbS2A1A3A3S42A3").
Definition Eps_2Bf : axst := leaf 0 run3_2Bf.
Definition Ebg_2Bf : axst := leaf 1 run3_2Bf.
Definition C3_2Bf : axst := C3_of Eps_2Bf.
Definition run4_2Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S2aSbS2A1A3S41A3").
Definition Ems_2Bf : axst := leaf 0 run4_2Bf.
Definition C4_2Bf : axst := C4_of Ems_2Bf.
Definition RM_2Bf : list sobj := RM_of C4_2Bf.
Definition TM0_2Bf : axst := TM0_of C4_2Bf.
Definition TM_2Bf : axst := TM_of C4_2Bf.
Definition run5_2Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S29SbS2A1A3S4eA3").
Definition Eq_2Bf : axst := leaf 0 run5_2Bf.
Definition EQ_2Bf : axst := EQ_of Eq_2Bf.
Definition RQ_2Bf : list sobj := RQ_of EQ_2Bf q_2Bf.
Definition TQ0_2Bf : axst := TQ0_of EQ_2Bf q_2Bf.
Definition TQ_2Bf : axst := TQ_of EQ_2Bf q_2Bf.
Definition run6_2Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S28SaS2S2dSbS2A1A3A3S4fA3").
Definition Edr_2Bf : axst := leaf 0 run6_2Bf.
Definition Xf_2Bf : axst := leaf 1 run6_2Bf.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_2Bf : ltac2:(tb__ "0|0|
S0S9S83S39S1cSaS2S27SbS2A1A3S38SaS4S43SbS4A1A3S6aA6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_2Bf exits1_2Bf run1_2Bf); [unfold run1_2Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_2Bf : ltac2:(tb__ "0|2|
S0S9S84S39S1cSaS2S27SbS2A1A3S38SaS81S82S43Z1S1bZ0M0A1M1A3SbS81A1A3S85S4S81S4S82R1G0G1A3LE;S6aA4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_2Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_2Bf) run1_2Bf); [unfold run1_2Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_2Bf_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4aA1S5S3dA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S4aA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Bf_1 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S4aS5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_2Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3dA3S57A3"). Proof. unfold run2_2Bf_1; reflexivity. Qed.
Lemma L2_2Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS57SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S57A2S5dA3A2"). Proof. Time (split; [vmr | unfold EfD_2Bf_1; reflexivity]). Qed.
Lemma AXD_2Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5dS22A2SeS4S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S44S76Z1M1A1S1fS44G1A2A3SeG0S62A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Bf_1 : ltac2:(tb__ "0|1|
S0S9S7aS44S76Z1M0A1S1fS44G0A2S62SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6dS23A2SeS4S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Bf_1 : ltac2:(tb__ "0|0|
S0S9S7dS66S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Bf_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4bA1S5S3eA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S4bA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Bf_2 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S4bS5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_2Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3eA3S58A3"). Proof. unfold run2_2Bf_2; reflexivity. Qed.
Lemma L2_2Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS58SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S58A2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_2Bf_2; reflexivity]). Qed.
Lemma AXD_2Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5eS22A2SeS4S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S45S76Z2M1A1S1fS45G1A2A3SeG0S63A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Bf_2 : ltac2:(tb__ "0|1|
S0S9S7aS45S76Z2M0A1S1fS45G0A2S63SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6eS23A2SeS4S67A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Bf_2 : ltac2:(tb__ "0|0|
S0S9S7dS67S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Bf_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4cA1S5S3fA1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Bf_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3fA1M0A1ScA3S1S0S3S13G0A1S13S5S4cA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Bf_3 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S3fA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Bf_3 : ltac2:(tb__ "0|0|
S0S4S7S4cS5S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_2Bf_3 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3fA3S59A3"). Proof. unfold run2_2Bf_3; reflexivity. Qed.
Lemma L2_2Bf_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS59SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S59A2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_2Bf_3; reflexivity]). Qed.
Lemma AXD_2Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S75S5fS22A2SeS4S46A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Bf_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S46S76Z3M1A1S1fS46G1A2A3SeG0S64A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Bf_3 : ltac2:(tb__ "0|1|
S0S9S7aS46S76Z3M0A1S1fS46G0A2S64SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Bf_3 : ltac2:(tb__ "0|0|
S0SfS4A1S75S6fS23A2SeS4S68A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Bf_3 : ltac2:(tb__ "0|0|
S0S9S7dS68S42A2ScA3"). Proof. Time vmr. Qed.
Lemma D2_2Bf_4 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S78S5S4dA1S5S40A1A2SeG3S11G1G2SaG0S11S14S14S24S25A4SbG0A1A3S20A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_2Bf_4 : ltac2:(tb__ "0|1|
S1S0S9S19S5S40A1M0A1ScA3S1S0S3S13G0A1S13S5S4dA1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_2Bf_4 : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S40A1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_2Bf_4 : ltac2:(tb__ "0|0|
S0S4S7S4dS5S40A1A2S40A3"). Proof. vmr. Qed.
Lemma RUN2_2Bf_4 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S40A3S5aA3"). Proof. unfold run2_2Bf_4; reflexivity. Qed.
Lemma L2_2Bf_4 : ltac2:(tb__ "0|0|
S1S0S9S1eS5aSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S5aA2S60A3A2"). Proof. Time (split; [vmr | unfold EfD_2Bf_4; reflexivity]). Qed.
Lemma AXD_2Bf_4 : ltac2:(tb__ "0|0|
S0SfS4A1S75S60S22A2SeS4S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_2Bf_4 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S79S47S76Z4M1A1S1fS47G1A2A3SeG0S65A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_2Bf_4 : ltac2:(tb__ "0|1|
S0S9S7aS47S76Z4M0A1S1fS47G0A2S65SaS4S77G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_2Bf_4 : ltac2:(tb__ "0|0|
S0SfS4A1S75S70S23A2SeS4S69A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_2Bf_4 : ltac2:(tb__ "0|0|
S0S9S7dS69S42A2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S2bSaS2S26SbS2A1A3A3S42A3S51A3"). Proof. unfold run3_2Bf; reflexivity. Qed.
Lemma L3_2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S2bSaS2S26SbS2A1A3A3A2ScA3S1S0S4S37U0S51A2S49A3S0S4S37U1S51A2S6bA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_2Bf | unfold Ebg_2Bf]; reflexivity]). Qed.
Lemma NX3_2Bf : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S42A1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_2Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S78S5S49A1S5S41A1A2SeG2S11G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_2Bf : ltac2:(tb__ "0|0|
S0S4S7S49S5S41A1A2S41A3"). Proof. vmr. Qed.
Lemma NX3b_2Bf : ltac2:(tb__ "0|0|
S0S9S74S38S13S5S41A1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_2Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S41A1M0A1ScA3S1S0S3S13G0A1S13S5S49A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S2aSbS2A1A3S41A3S5bA3"). Proof. unfold run4_2Bf; reflexivity. Qed.
Lemma L4_2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS5bSaS2S2aSbS2A1A3A2ScA3S0S4S37U0S5bA2S48A3A2"). Proof. Time (split; [vmr | unfold Ems_2Bf; reflexivity]). Qed.
Lemma D4_2Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S78S5S48A1S5S3aA1A2SeG2S11G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_2Bf : ltac2:(tb__ "0|0|
S0S4S7S48S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma W4_2Bf : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S12A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_2Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S79S3aS7fS2eS3aA1A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_2Bf : ltac2:(tb__ "0|0|
S0S9S7bS3aS7fS2eS3aA1S53S85S6S4S8S80A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_2Bf : ltac2:(tb__ "0|0|
S0S4S7cS2eS3aA1S7fS32S3aS53A5S55A3"). Proof. unfold TM0_2Bf, TM0_of, RM_2Bf; reflexivity. Qed.
Lemma FBM_2Bf : ltac2:(tb__ "0|3|
S1S0S9S7eS15S1aS13S5S3aA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7eS15S1aS13S5S55A1A1A1G2A3ScA3S0S9S74S38G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_2Bf : ltac2:(tb__ "0|0|
S0S4S86S55S17S5S3aA1A1A2S4eA3"). Proof. vmr. Qed.
Lemma NX5_2Bf : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S4eA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S29SbS2A1A3S4eA3S5cA3"). Proof. unfold run5_2Bf; reflexivity. Qed.
Lemma L5_2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS5cSaS2S29SbS2A1A3A2ScA3S0S4S37U0S5cA2S61A3A2"). Proof. Time (split; [vmr | unfold Eq_2Bf; reflexivity]). Qed.
Lemma AXQ_2Bf : ltac2:(tb__ "0|0|
S0SfS4A1S75S61S33A2SeS4S3bA2A3"). Proof. Time vmr. Qed.
Lemma HeQ_2Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S79S3bS2cS3cA1S2fS3bS3cA2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_2Bf : ltac2:(tb__ "0|0|
S0S9S7bS3bS2cS3cA1S2fS3bS3cA2S54SaS4S30S3cA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_2Bf : ltac2:(tb__ "0|0|
S0S4S7cS2fS3bS3cA2S2cS3cA1S30S3cA1S3bS54A5S56A3"). Proof. unfold TQ0_2Bf, TQ0_of, RQ_2Bf; reflexivity. Qed.
Lemma FBQ_2Bf : ltac2:(tb__ "0|3|
S1S0S9S7eS15S1aS13S5S3bA1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S7eS15S1aS13S5S56A1A1A1G2A3ScA3S0S9S74S38G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_2Bf : ltac2:(tb__ "0|0|
S0S4S86S56S17S5S3bA1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX6_2Bf : ltac2:(tb__ "0|1|
S1S0S9S74S38S13S5S4fA1M0A1A2ScA3S0S9S16G0A1S12A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_2Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S28SaS2S2dSbS2A1A3A3S4fA3S52A3"). Proof. unfold run6_2Bf; reflexivity. Qed.
Lemma L6_2Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S28SaS2S2dSbS2A1A3A3A2ScA3S1S0S4S37U0S52A2S6cA3S0S4S37U1S52A2S72A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_2Bf | unfold Xf_2Bf]; reflexivity]). Qed.

End F0A_c2Bf.

(* [comment removed for export] *)
Module SegD_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_main"; "chkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "SZMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_states SegD_main.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Open Scope Z_scope.

Lemma chkD_1 : chkD 1 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_2 : chkD 2 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_3 : chkD 3 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_4 : chkD 4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_5 : chkD 5 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_6 : chkD 6 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_7 : chkD 7 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_8 : chkD 8 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_9 : chkD 9 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_10 : chkD 10 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma chkD_all : ltac2:(tb__ "0|0|
S5S3S0Z1R1A2S0R1S7A2A2S4S1S6R2A1S2A3F_;Fsz;").
Proof.
  intros sz H. unfold SZMAX in H.
  assert (D : sz = 1 \/ sz = 2 \/ sz = 3 \/ sz = 4 \/ sz = 5 \/ sz = 6 \/ sz = 7 \/ sz = 8 \/ sz = 9 \/ sz = 10) by lia.
  destruct D as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; rewrite E;
  [exact chkD_1 | exact chkD_2 | exact chkD_3 | exact chkD_4 | exact chkD_5 | exact chkD_6 | exact chkD_7 | exact chkD_8 | exact chkD_9 | exact chkD_10].
Qed.
End SegD_chk.

