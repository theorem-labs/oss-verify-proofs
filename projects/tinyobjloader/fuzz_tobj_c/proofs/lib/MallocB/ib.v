(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.

(* [comment removed for export] *)
Module F0A_c1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A"; "C4_1A"; "EQ_1A"; "q_1A"; "C2_1A_1"; "C2_1A_2"; "C2_1A_3"; "C3_1A"; "CD_1A"; "P0_1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "Ems_1A"; "Eps_1A"; "S1c_1A_1"; "S1c_1A_2"; "S1c_1A_3"; "TM_1A"; "TQ_1A"; "run3_1A"; "run6_1A"; "RM_1A"; "RQ_1A"; "TM0_1A"; "TQ0_1A"; "run1_1A"; "run2_1A_1"; "run2_1A_2"; "run2_1A_3"; "run4_1A"; "run5_1A"; "EfD_1A_1"; "EfD_1A_2"; "EfD_1A_3"; "Eq_1A"; "RD_1A_1"; "RD_1A_2"; "RD_1A_3"; "TDr_1A_1"; "TDr_1A_2"; "TDr_1A_3"; "exits1_1A"; "Ebg_1A"; "Edr_1A"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "Xf_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_1A : list ulink := Wcan 1.
Definition st_1A : ustop := UStopLe.
Definition q_1A : qvar := QA.
Definition P0_1A : axst := P0_f W_1A st_1A q_1A.

Definition run1_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_1A_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_1A_1 : axst := C2_of S1c_1A_1.
Definition run2_1A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_1A_1 : axst := leaf 0 run2_1A_1.
Definition ED_1A_1 : axst := ED_of EfD_1A_1.
Definition RD_1A_1 : list sobj := RD_of ED_1A_1 1.
Definition TD_1A_1 : axst := TD_of ED_1A_1 1.
Definition TDr_1A_1 : axst := TDr_of TD_1A_1.
Definition S1c_1A_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_1A_2 : axst := C2_of S1c_1A_2.
Definition run2_1A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_1A_2 : axst := leaf 0 run2_1A_2.
Definition ED_1A_2 : axst := ED_of EfD_1A_2.
Definition RD_1A_2 : list sobj := RD_of ED_1A_2 2.
Definition TD_1A_2 : axst := TD_of ED_1A_2 2.
Definition TDr_1A_2 : axst := TDr_of TD_1A_2.
Definition S1c_1A_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_1A_3 : axst := C2_of S1c_1A_3.
Definition run2_1A_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_1A_3 : axst := leaf 0 run2_1A_3.
Definition ED_1A_3 : axst := ED_of EfD_1A_3.
Definition RD_1A_3 : list sobj := RD_of ED_1A_3 3.
Definition TD_1A_3 : axst := TD_of ED_1A_3 3.
Definition TDr_1A_3 : axst := TDr_of TD_1A_3.
Definition exits1_1A : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_1A : axst := CD_of TDr_1A_1.
Definition run3_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_1A : axst := leaf 0 run3_1A.
Definition Ebg_1A : axst := leaf 1 run3_1A.
Definition C3_1A : axst := C3_of Eps_1A.
Definition run4_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_1A : axst := leaf 0 run4_1A.
Definition C4_1A : axst := C4_of Ems_1A.
Definition RM_1A : list sobj := RM_of C4_1A.
Definition TM0_1A : axst := TM0_of C4_1A.
Definition TM_1A : axst := TM_of C4_1A.
Definition run5_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_1A : axst := leaf 0 run5_1A.
Definition EQ_1A : axst := EQ_of Eq_1A.
Definition RQ_1A : list sobj := RQ_of EQ_1A q_1A.
Definition TQ0_1A : axst := TQ0_of EQ_1A q_1A.
Definition TQ_1A : axst := TQ_of EQ_1A q_1A.
Definition run6_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_1A : axst := leaf 0 run6_1A.
Definition Xf_1A : axst := leaf 1 run6_1A.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_1A : ltac2:(tb__ "0|0|
S0S9S77S68S1cSaS2S21SbS2A1A3S67SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_1A exits1_1A run1_1A); [unfold run1_1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_1A : ltac2:(tb__ "0|2|
S0S9S78S68S1cSaS2S21SbS2A1A3S67SaS75S76S3fZ1S1bZ0M0A1M1A3SbS75A1A3S7aS4S75S4S76R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_1A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_1A) run1_1A); [unfold run1_1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_1A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_1 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_1A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_1A_1; reflexivity. Qed.
Lemma L2_1A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_1; reflexivity]). Qed.
Lemma AXD_1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS40S6bZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_1 : ltac2:(tb__ "0|1|
S0S9S6fS40S6bZ1M0A1S1fS40G0A2S5aSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_1 : ltac2:(tb__ "0|0|
S0S9S79S5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_2 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_1A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_1A_2; reflexivity. Qed.
Lemma L2_1A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_2; reflexivity]). Qed.
Lemma AXD_1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS41S6bZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_2 : ltac2:(tb__ "0|1|
S0S9S6fS41S6bZ2M0A1S1fS41G0A2S5bSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_2 : ltac2:(tb__ "0|0|
S0S9S79S5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1A_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_3 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_1A_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_1A_3; reflexivity. Qed.
Lemma L2_1A_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_3; reflexivity]). Qed.
Lemma AXD_1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS42S6bZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_3 : ltac2:(tb__ "0|1|
S0S9S6fS42S6bZ3M0A1S1fS42G0A2S5cSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_3 : ltac2:(tb__ "0|0|
S0S9S79S5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_1A; reflexivity. Qed.
Lemma L3_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_1A | unfold Ebg_1A]; reflexivity]). Qed.
Lemma NX3_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6dS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_1A : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_1A : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_1A; reflexivity. Qed.
Lemma L4_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_1A; reflexivity]). Qed.
Lemma D4_1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6dS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_1A : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S6eS37S73S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_1A : ltac2:(tb__ "0|0|
S0S9S70S37S73S2dS37A1S4cS7aS6S4S8S74A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_1A : ltac2:(tb__ "0|0|
S0S4S71S2dS37A1S73S31S37S4cA5S4eA3"). Proof. unfold TM0_1A, TM0_of, RM_1A; reflexivity. Qed.
Lemma FBM_1A : ltac2:(tb__ "0|3|
S1S0S9S72S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S72S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S69S67G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_1A : ltac2:(tb__ "0|0|
S0S4S7bS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_1A; reflexivity. Qed.
Lemma L5_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_1A; reflexivity]). Qed.
Lemma AXQ_1A : ltac2:(tb__ "0|0|
S0SfS4A1S6aS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S6eS38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_1A : ltac2:(tb__ "0|0|
S0S9S70S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_1A : ltac2:(tb__ "0|0|
S0S4S71S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_1A, TQ0_of, RQ_1A; reflexivity. Qed.
Lemma FBQ_1A : ltac2:(tb__ "0|3|
S1S0S9S72S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S72S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S69S67G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_1A : ltac2:(tb__ "0|0|
S0S4S7bS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_1A; reflexivity. Qed.
Lemma L6_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S66A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_1A | unfold Xf_1A]; reflexivity]). Qed.

End F0A_c1A.

(* [comment removed for export] *)
Module F0A_c1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "C4_1Be"; "EQ_1Be"; "q_1Be"; "C2_1Be_1"; "C2_1Be_2"; "C2_1Be_3"; "C3_1Be"; "CD_1Be"; "P0_1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "Ems_1Be"; "Eps_1Be"; "S1c_1Be_1"; "S1c_1Be_2"; "S1c_1Be_3"; "TM_1Be"; "TQ_1Be"; "run3_1Be"; "run6_1Be"; "RM_1Be"; "RQ_1Be"; "TM0_1Be"; "TQ0_1Be"; "run1_1Be"; "run2_1Be_1"; "run2_1Be_2"; "run2_1Be_3"; "run4_1Be"; "run5_1Be"; "EfD_1Be_1"; "EfD_1Be_2"; "EfD_1Be_3"; "Eq_1Be"; "RD_1Be_1"; "RD_1Be_2"; "RD_1Be_3"; "TDr_1Be_1"; "TDr_1Be_2"; "TDr_1Be_3"; "exits1_1Be"; "Ebg_1Be"; "Edr_1Be"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "W_1Be"; "Xf_1Be"; "st_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_1Be : list ulink := Wcan 1.
Definition st_1Be : ustop := UStopLe.
Definition q_1Be : qvar := QBe.
Definition P0_1Be : axst := ltac2:(tb__ "0|0|
S31S67S69S3aA3").

Definition run1_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_1Be_1 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z1A3").
Definition C2_1Be_1 : axst := C2_of S1c_1Be_1.
Definition run2_1Be_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_1Be_1 : axst := leaf 0 run2_1Be_1.
Definition ED_1Be_1 : axst := ED_of EfD_1Be_1.
Definition RD_1Be_1 : list sobj := RD_of ED_1Be_1 1.
Definition TD_1Be_1 : axst := TD_of ED_1Be_1 1.
Definition TDr_1Be_1 : axst := TDr_of TD_1Be_1.
Definition S1c_1Be_2 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z2A3").
Definition C2_1Be_2 : axst := C2_of S1c_1Be_2.
Definition run2_1Be_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_1Be_2 : axst := leaf 0 run2_1Be_2.
Definition ED_1Be_2 : axst := ED_of EfD_1Be_2.
Definition RD_1Be_2 : list sobj := RD_of ED_1Be_2 2.
Definition TD_1Be_2 : axst := TD_of ED_1Be_2 2.
Definition TDr_1Be_2 : axst := TDr_of TD_1Be_2.
Definition S1c_1Be_3 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z3A3").
Definition C2_1Be_3 : axst := C2_of S1c_1Be_3.
Definition run2_1Be_3 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_1Be_3 : axst := leaf 0 run2_1Be_3.
Definition ED_1Be_3 : axst := ED_of EfD_1Be_3.
Definition RD_1Be_3 : list sobj := RD_of ED_1Be_3 3.
Definition TD_1Be_3 : axst := TD_of ED_1Be_3 3.
Definition TDr_1Be_3 : axst := TDr_of TD_1Be_3.
Definition exits1_1Be : list axst := ltac2:(tb__ "0|0|
SaS4S46SaS4S47SaS4S48SbS4A1A3A3A3").

Definition CD_1Be : axst := CD_of TDr_1Be_1.
Definition run3_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3").
Definition Eps_1Be : axst := leaf 0 run3_1Be.
Definition Ebg_1Be : axst := leaf 1 run3_1Be.
Definition C3_1Be : axst := C3_of Eps_1Be.
Definition run4_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S25SbS2A1A3S3eA3").
Definition Ems_1Be : axst := leaf 0 run4_1Be.
Definition C4_1Be : axst := C4_of Ems_1Be.
Definition RM_1Be : list sobj := RM_of C4_1Be.
Definition TM0_1Be : axst := TM0_of C4_1Be.
Definition TM_1Be : axst := TM_of C4_1Be.
Definition run5_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S23SbS2A1A3S49A3").
Definition Eq_1Be : axst := leaf 0 run5_1Be.
Definition EQ_1Be : axst := EQ_of Eq_1Be.
Definition RQ_1Be : list sobj := RQ_of EQ_1Be q_1Be.
Definition TQ0_1Be : axst := TQ0_of EQ_1Be q_1Be.
Definition TQ_1Be : axst := TQ_of EQ_1Be q_1Be.
Definition run6_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3").
Definition Edr_1Be : axst := leaf 0 run6_1Be.
Definition Xf_1Be : axst := leaf 1 run6_1Be.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_1Be : ltac2:(tb__ "0|0|
S0S9S7aS6bS1cSaS2S21SbS2A1A3S6aSaS4S40SbS4A1A3S61A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_1Be exits1_1Be run1_1Be); [unfold run1_1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_1Be : ltac2:(tb__ "0|2|
S0S9S7bS6bS1cSaS2S21SbS2A1A3S6aSaS78S79S40Z1S1bZ0M0A1M1A3SbS78A1A3S7dS4S78S4S79R1G0G1A3LE;S61A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_1Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_1Be) run1_1Be); [unfold run1_1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_1Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_1 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_1 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_1Be_1; reflexivity. Qed.
Lemma L2_1Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_1; reflexivity]). Qed.
Lemma AXD_1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S41S6eZ1M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_1 : ltac2:(tb__ "0|1|
S0S9S72S41S6eZ1M0A1S1fS41G0A2S5bSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_1 : ltac2:(tb__ "0|0|
S0S9S7cS5eS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_2 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_2 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_1Be_2; reflexivity. Qed.
Lemma L2_1Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_2; reflexivity]). Qed.
Lemma AXD_1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S42S6eZ2M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_2 : ltac2:(tb__ "0|1|
S0S9S72S42S6eZ2M0A1S1fS42G0A2S5cSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_2 : ltac2:(tb__ "0|0|
S0S9S7cS5fS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S48A1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_3 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_3 : ltac2:(tb__ "0|0|
S0S4S7S48S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3dA3S54A3"). Proof. unfold run2_1Be_3; reflexivity. Qed.
Lemma L2_1Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S54A2S59A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_3; reflexivity]). Qed.
Lemma AXD_1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS59S2aA2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S43S6eZ3M1A1S1fS43G1A2A3SeG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_3 : ltac2:(tb__ "0|1|
S0S9S72S43S6eZ3M0A1S1fS43G0A2S5dSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS66S2bA2SeS4S60A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_3 : ltac2:(tb__ "0|0|
S0S9S7cS60S3fA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3S4bA3"). Proof. unfold run3_1Be; reflexivity. Qed.
Lemma L3_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S37U0S4bA2S45A3S0S4S37U1S4bA2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_1Be | unfold Ebg_1Be]; reflexivity]). Qed.
Lemma NX3_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S3fA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S45A1S5S3eA1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_1Be : ltac2:(tb__ "0|0|
S0S4S7S45S5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma NX3b_1Be : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S25SbS2A1A3S3eA3S55A3"). Proof. unfold run4_1Be; reflexivity. Qed.
Lemma L4_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S25SbS2A1A3A2ScA3S0S4S37U0S55A2S44A3A2"). Proof. Time (split; [vmr | unfold Ems_1Be; reflexivity]). Qed.
Lemma D4_1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S44A1S5S38A1A2SeG2S12G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_1Be : ltac2:(tb__ "0|0|
S0S4S7S44S5S38A1A2S38A3"). Proof. vmr. Qed.
Lemma W4_1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S38A1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S38S76S2dS38A1A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_1Be : ltac2:(tb__ "0|0|
S0S9S73S38S76S2dS38A1S4dS7dS6S4S8S77A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_1Be : ltac2:(tb__ "0|0|
S0S4S74S2dS38A1S76S32S38S4dA5S4fA3"). Proof. unfold TM0_1Be, TM0_of, RM_1Be; reflexivity. Qed.
Lemma FBM_1Be : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_1Be : ltac2:(tb__ "0|0|
S0S4S7eS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX5_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S23SbS2A1A3S49A3S56A3"). Proof. unfold run5_1Be; reflexivity. Qed.
Lemma L5_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S23SbS2A1A3A2ScA3S0S4S37U0S56A2S5aA3A2"). Proof. Time (split; [vmr | unfold Eq_1Be; reflexivity]). Qed.
Lemma AXQ_1Be : ltac2:(tb__ "0|0|
S0SfS4A1S6dS5aS33A2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S39S27S3aA1S2eS39S3aA2A3SeG0S4eA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_1Be : ltac2:(tb__ "0|0|
S0S9S73S39S27S3aA1S2eS39S3aA2S4eSaS4S30S3aA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_1Be : ltac2:(tb__ "0|0|
S0S4S74S2eS39S3aA2S27S3aA1S30S3aA1S39S4eA5S50A3"). Proof. unfold TQ0_1Be, TQ0_of, RQ_1Be; reflexivity. Qed.
Lemma FBQ_1Be : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S50A1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_1Be : ltac2:(tb__ "0|0|
S0S4S7eS50S17S5S39A1A1A2S4aA3"). Proof. vmr. Qed.
Lemma NX6_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S4aA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3S4cA3"). Proof. unfold run6_1Be; reflexivity. Qed.
Lemma L6_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4cSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S37U0S4cA2S63A3S0S4S37U1S4cA2S68A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_1Be | unfold Xf_1Be]; reflexivity]). Qed.

End F0A_c1Be.

(* [comment removed for export] *)
Module F0A_c1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "C4_1Bf"; "EQ_1Bf"; "q_1Bf"; "C2_1Bf_1"; "C2_1Bf_2"; "C2_1Bf_3"; "C3_1Bf"; "CD_1Bf"; "P0_1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "Ems_1Bf"; "Eps_1Bf"; "S1c_1Bf_1"; "S1c_1Bf_2"; "S1c_1Bf_3"; "TM_1Bf"; "TQ_1Bf"; "run3_1Bf"; "run6_1Bf"; "RM_1Bf"; "RQ_1Bf"; "TM0_1Bf"; "TQ0_1Bf"; "run1_1Bf"; "run2_1Bf_1"; "run2_1Bf_2"; "run2_1Bf_3"; "run4_1Bf"; "run5_1Bf"; "EfD_1Bf_1"; "EfD_1Bf_2"; "EfD_1Bf_3"; "Eq_1Bf"; "RD_1Bf_1"; "RD_1Bf_2"; "RD_1Bf_3"; "TDr_1Bf_1"; "TDr_1Bf_2"; "TDr_1Bf_3"; "exits1_1Bf"; "Ebg_1Bf"; "Edr_1Bf"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "W_1Bf"; "Xf_1Bf"; "st_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
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
Module SegQ3D_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "bool"; "true"; "app"; "prod"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SVar"; "SPBranch"; "ss_lenient"; "ss_next"; "SAlu"; "SPNot"; "SPUle"; "swf"; "SPAlign"; "cell"; "DUnknown"; "SPUlt"; "mkCell"; "mkObj"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "vXK"; "vXF"; "vXS"; "vXL"; "PD"; "NXR"; "mkR"; "O_mtx00"; "PostQ3R"; "RETR"; "STK"; "SWD"; "ZQ"; "cb_cells"; "post_ruR"; "spD"; "spR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "O_sb"; "runA"; "add"; "NPRE"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "mkD"; "vB"; "vBC"; "DBH"; "DIH"; "DT"; "vS7"; "DH"; "DI"; "DTs"; "F_DI"; "O_it"; "RC"; "RI"; "ruI"; "DBx"; "DSEC"; "s9'"; "vBN"; "vBS"; "DQC"; "DQI"; "vS9"; "F_D"; "F_DT"; "OBD"; "O_b"; "QCRET2"; "QIRET2"; "runD0"; "runDB"; "runDI"; "runDT"; "runRC"; "runRI"; "vIT"; "DH0"; "DHn"; "DIc"; "DQCs"; "DQIs"; "DTc"; "F_czB"; "F_nzB"; "PostQ3Rs"; "TsD0"; "TsDB"; "TsRC"; "TsRI"; "clsB"; "junkD"; "regsDH"; "ruB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "regs3"; "O_gmax"; "cbC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "chkN"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_NE"; "ALU_SUB"; "BC_EQ"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states"; "ALLOCG"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition DBH : Z := 0x3e6a4.
Definition DIH : Z := 0x3e6e4.
Definition DT : Z := 0x3e6fc.
Definition DQI : Z := 0x3e764.
Definition DQC : Z := 0x3eb68.
Definition QIRET2 : Z := 0x3e6f0.
Definition QCRET2 : Z := 0x3e728.
Definition DSEC : Z := 0x3e68c.

Definition vBN := SVar 160. Definition vBS := SVar 161. Definition vBC := SVar 162.
Definition vS7 := SVar 163. Definition vS9 := SVar 164. Definition vIT := SVar 165. Definition vB := SVar 166.
Definition junkD : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S1SaA2M0S2S1SaU1SePabA1A4S0G0S2S1SaU5SePacA1A4S0G0S2S1SaU6SePadA1A4S0G0S2S1SaU7SePb0A1A4S0G0S2S1SaUaSePa9A1A4S0G0S2S1SaUbSePbcA1A4S0G0S2S1SaUcSePbdA1A4S0G0S2S1SaUdSePbeA1A4S0G0S2S1SaUeSePbfA1A4S0G0S2S1SaUfSePc0A1A4S0G0S2S1SaU10SePc1A1A4S0G0S2S1SaU11SePc2A1A4S0G0S2S1SaU1cSePb4A1A4S0G0S2S1SaU1dSePb5A1A4S0G0S2S1SaU1eSePb6A1A4S0G0S2S1SaU1fSePb7A1A4S0G0S2S1SaU14SePc3A1A4S0G0S2S1SaU16SePc4A1A4S0G0S2S1SaU17SePc5A1A4S0G0S2S1SaU18SePc6A1A4S0G0S2S1SaU19SePc7A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition regsDH (ru : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S7bS70S6S7S1SaA2M0S6bS6G0S0G0S2S1SaU2S32A4S0G0S2S1SaU8S33A4S0G0S2S1SaU9SdS7cA1A4S0G0S2S1SaU12SdZeaa98A1A4S0G0S2S1SaU13SdZead08A1A4S0G0S2S1SaU15SdS7dZ2Z25A2A1A4S3G0A1A3A3A3A3A3A3Vru;A3A3A2").
Definition OBD (tk tf tl ts : sv) : list sobj := ltac2:(tb__ "0|0|
S6ScS2dS30S2eVtk;Vtf;Vtl;Vts;A4A2S0ScS2aS0ScS71S3ScA1A3A3A3").
Definition mkD (pc : Z) (ru : list (nat * sv)) (tk tf tl ts : sv) (extra : list sobj) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S29Vpc;S6cVru;A1S52Vtk;Vtf;Vtl;Vts;A4Vextra;VF;S28A6").
Definition O_b (nx : sv) : sobj := ltac2:(tb__ "0|4|
S7fS24Z0M0Z18S0S7S7S1cS1A2M1SaA2M2S2G1SaS2S1cS1G0U8M3A4Vnx;A4S0G2S2G1SaS2S1cS1Z8G3A4S4cA4S0G2S2G1SaS2S1cS1Z10G3A4S3bA4S3G2A1A3A3A3A4").
Definition O_it : sobj := ltac2:(tb__ "0|1|
S1bS3fSdN80A1M0SdN78A1S0S17S1aG0Z8S5cA3S3S17A1A3S18A5").
Definition clsB : sv := ltac2:(tb__ "0|0|
S12S79S12S78S12S76S3aS38A3SdZ1bA1A3SdZ3bA1A3").

Definition DH0 : axst := ltac2:(tb__ "0|1|
S39S3cS0S7S1SaA2M0S2S1SaUaS23A4S3G0A1A3S23S24S26S25S3ScA1S6SbS6eS6fA1S0SbS13SfS77S23SdZ0A1A3A1S3SbA1A3A3A8").

Definition F_D : list sprop := ltac2:(tb__ "0|0|
S6SbS6eS6fA1S0SbS14SdS7aA1S24A2S0SbS16Pb9Z4A2S3SbA1A3A3A3").
Definition DH : axst := ltac2:(tb__ "0|1|
S39S3cS0S7S1SaA2M0S2S1SaUaS23A4S3G0A1A3S23S24S26S25S0ScS34S0ScS53S4bA1S3ScA1A3A3S50A8").
Definition ruB (cz : bool) : list (nat * sv) := ltac2:(tb__ "0|3|
S6S7S1SaA2M0S0G0S2S1SaUaS4cA4S0G0S2S1SaUbS12S76S25S4cA3A4S0G0S2S1SaU14S24A4S0G0S2S1SaU16S3bA4S3G0A1M1A3A3A3A3S4S9G0A1Lcz;Vcz;G1S0G0S2S1SaU17S36S24SdZ98A1A2A4S0G0S2S1SaU18S36S3bSdZ10A1M2A2A4S0G0S2S1SaU19G2A4G1A3A3A3X4x2A3").
Definition F_nzB (nz : bool) : sprop := ltac2:(tb__ "0|1|
S4SbLnz;Vnz;SfS75S4bSdZ0A1A3M0S13G0A1X4x2").
Definition F_czB (cz : bool) : sprop := ltac2:(tb__ "0|1|
S4SbLcz;Vcz;SfS77S3bSdZ0A1A3M0S13G0A1X4x2").
Definition DBx (nz cz : bool) : axst := ltac2:(tb__ "0|0|
S39S4S1cLcz;Vcz;S3eS3dX4x2S6dVcz;A1S36S23SdN1A1A2S4bS4SaLnz;Vnz;S26S2fX4x2S12S76S25S4cA3S0ScS34S0ScS53S4bA1S3ScA1A3A3S6SbS50S0SbS63Vcz;A1S0SbS64Vnz;A1S3SbA1A3A3A3A8").

Definition ruI (s7 s9 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S1SaA2M0S2S1SaU14S3aA4S0G0S2S1SaU16S3bA4S0G0S2S1SaU17Vs7;A4S0G0S2S1SaU18S36S3bSdZ10A1A2A4S0G0S2S1SaU19Vs9;A4S3G0A1A3A3A3A3A3").
Definition F_DI : list sprop := ltac2:(tb__ "0|0|
S6SbS6eS6fA1S0SbS14SdS7aA1S3aA2S0SbS16Pa6Z4A2S0SbS14SdS7eS7aZ98A2A1S3fA2S0SbS16Pa3Z3A2S3SbA1A3A3A3A3A3").
Definition DI : axst := ltac2:(tb__ "0|0|
S39S3dS47S3fS4fA2S23S24S26S25S0ScS34S0ScS44S3ScA1A3A3S43A8").
Definition DQIs : axst := ltac2:(tb__ "0|1|
S39S4eS6S7S1SaA2M0S47S3fS4fA2S0G0S2S1SaUaS36SePaA1SdNb8A1A2A4S0G0S2S1SaUbS5cA4S0G0S2S1SaU1SdS55A1A4S3G0A1A3A3A3A3S23S24S26S25S0ScS34S0ScS44S3ScA1A3A3S43A8").

Definition RI : axst := ltac2:(tb__ "0|0|
S39S55S47S3fS4fA2S23S24S26S25S0ScS34S0ScS44S3ScA1A3A3S43A8").
Definition s9' : sv := add vS9 (SLit 1).
Definition DIc : axst := ltac2:(tb__ "0|0|
S39S3dS47S36S3fSdZ8A1A2S4aA2S23S24S26S25S0ScS34S0ScS44S3ScA1A3A3S6SbS43S0SbSfS75S4aS36S3bSdZ10A1A2A3S3SbA1A3A3A8").
Definition DTc : axst := ltac2:(tb__ "0|0|
S39S3eS47S36S3fSdZ8A1A2S4aA2S23S24S26S25S0ScS34S0ScS44S3ScA1A3A3S6SbS43S0SbS13SfS75S4aS36S3bSdZ10A1A2A3A1S3SbA1A3A3A8").

Definition F_DT : list sprop := ltac2:(tb__ "0|0|
S6SbS6eS6fA1S0SbS14SdS7aA1S3aA2S0SbS16Pa6Z4A2S0SbS14S38S3aA2S0SbS19S3aS36S38SdS7dZ2Z25A2A1A2A2S3SbA1A3A3A3A3A3").
Definition DTs : axst := ltac2:(tb__ "0|1|
S39S3eS0S7S1SaA2M0S2S1SaU14S3aA4S3G0A1A3S23S24S26S25S0ScS34S3ScA1A3S51A8").
Definition DQCs : axst := ltac2:(tb__ "0|1|
S39S4dS0S7S1SaA2M0S2S1SaU14S3aA4S0G0S2S1SaUaS72A4S0G0S2S1SaUbSdS7cA1A4S0G0S2S1SaUcS6aA4S0G0S2S1SaUdS3aA4S0G0S2S1SaU1SdS54A1A4S3G0A1A3A3A3A3A3A3S23S24S26S25S0ScS34S3ScA1A3S51A8").

Definition RC : axst := ltac2:(tb__ "0|1|
S39S54S0S7S1SaA2M0S2S1SaU14S3aA4S3G0A1A3S23S24S26S25S0ScS34S3ScA1A3S6eS6fA1A8").
Definition DHn : axst := ltac2:(tb__ "0|1|
S39S3cS0S7S1SaA2M0S2S1SaU14S3aA4S0G0S2S1SaUaS23A4S3G0A1A3A3S23S24S26S25S0ScS34S3ScA1A3S6SbS6eS6fA1S0SbSfS75S23SdZ0A1A3S3SbA1A3A3A8").
Definition PostQ3Rs : axst := ltac2:(tb__ "0|1|
S29S2cS7bS70S31A2S52SePa0A1M0SePa1A1SePa2A1SePa3A1A4S0ScS34S3ScA1A3S6SbS6eS6fA1S0SbS13SfS75G0SdZ0A1A3A1S3SbA1A3A3S28A6").

Definition runD0 : list leafA := ltac2:(tb__ "0|0|
S35U12cS0S1cS3cS3S1cA1A3S27A3").
Definition runDB : list leafA := ltac2:(tb__ "0|0|
S35U12cS0S1cS3dS0S1cS3eS0S1cS49S3S1cA1A3A3A3S40A3").
Definition runDI : list leafA := ltac2:(tb__ "0|0|
S35U64S0S1cS4eS3S1cA1A3S41A3").
Definition runRI : list leafA := ltac2:(tb__ "0|0|
S35U64S0S1cS3dS0S1cS3eS3S1cA1A3A3S46A3").
Definition runDT : list leafA := ltac2:(tb__ "0|0|
S35U64S0S1cS4dS0S1cS49S3S1cA1A3A3S42A3").
Definition runRC : list leafA := ltac2:(tb__ "0|0|
S35U12cS0S1cS3cS3S1cA1A3S45A3").
Lemma runD0_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U12cS0S1cS3cS3S1cA1A3S27A3S56A3"). Proof. unfold runD0. reflexivity. Qed.
Lemma runDB_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U12cS0S1cS3dS0S1cS3eS0S1cS49S3S1cA1A3A3A3S40A3S57A3"). Proof. unfold runDB. reflexivity. Qed.
Lemma runDI_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U64S0S1cS4eS3S1cA1A3S41A3S58A3"). Proof. unfold runDI. reflexivity. Qed.
Lemma runRI_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U64S0S1cS3dS0S1cS3eS3S1cA1A3A3S46A3S5bA3"). Proof. unfold runRI. reflexivity. Qed.
Lemma runDT_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U64S0S1cS4dS0S1cS49S3S1cA1A3A3S42A3S59A3"). Proof. unfold runDT. reflexivity. Qed.
Lemma runRC_eq : ltac2:(tb__ "0|0|
S1dS9S21A1S35U12cS0S1cS3cS3S1cA1A3S45A3S5aA3"). Proof. unfold runRC. reflexivity. Qed.
Definition TsD0 : list axst := ltac2:(tb__ "0|0|
S0S1fS2bS0S1fS5dS3S1fA1A3A3").
Definition TsDB : list axst := ltac2:(tb__ "0|0|
S0S1fS48S5S5A2S0S1fS48S5S8A2S0S1fS48S8S5A2S0S1fS48S8S8A2S3S1fA1A3A3A3A3").
Definition TsRI : list axst := ltac2:(tb__ "0|0|
S0S1fS5fS0S1fS62S3S1fA1A3A3").
Definition TsRC : list axst := ltac2:(tb__ "0|0|
S0S1fS5eS0S1fS65S3S1fA1A3A3").
Lemma chkD0 : ltac2:(tb__ "0|0|
S1dS4S73S56S66A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkDB : ltac2:(tb__ "0|0|
S1dS4S73S57S67A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkDI : ltac2:(tb__ "0|0|
S1dS4S73S58S0S1fS61S3S1fA1A3A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkRI : ltac2:(tb__ "0|0|
S1dS4S73S5bS69A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkDT : ltac2:(tb__ "0|0|
S1dS4S73S59S0S1fS60S3S1fA1A3A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkRC : ltac2:(tb__ "0|0|
S1dS4S73S5aS68A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxsD : ltac2:(tb__ "0|6|
S1eS1eS1dS4S10S20S27A1M0A1S8A3S74S37S11G0A1A2A2S1eS1eS1dS4S10S20S40A1M1A1S8A3S74S37S11G1A1A2A2S1eS1eS1dS4S10S20S41A1M2A1S8A3S74S37S11G2A1A2A2S1eS1eS1dS4S10S20S46A1M3A1S8A3S74S37S11G3A1A2A2S1eS1eS1dS4S10S20S42A1M4A1S8A3S74S37S11G4A1A2A2S1eS1dS4S10S20S45A1M5A1S8A3S74S37S11G5A1A2A2A2A2A2A2A2").
Proof. repeat split; try reflexivity; unfold Pos.le; cbn; discriminate. Qed.
Lemma presD_wf : ltac2:(tb__ "0|0|
S1eS1dS4S22S40A1S5A3S1eS1dS4S15S20S40A1A1S5A3S1eS1dS4S22S41A1S5A3S1eS1dS4S15S20S41A1A1S5A3S1eS1dS4S22S46A1S5A3S1eS1dS4S15S20S46A1A1S5A3S1eS1dS4S22S42A1S5A3S1eS1dS4S15S20S42A1A1S5A3S1eS1dS4S22S45A1S5A3S1dS4S15S20S45A1A1S5A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQ3D_states.

(* [comment removed for export] *)
Module F0A_c2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "C4_2A"; "EQ_2A"; "q_2A"; "C2_2A_1"; "C2_2A_2"; "C2_2A_3"; "C2_2A_4"; "C3_2A"; "CD_2A"; "P0_2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "Ems_2A"; "Eps_2A"; "S1c_2A_1"; "S1c_2A_2"; "S1c_2A_3"; "S1c_2A_4"; "TM_2A"; "TQ_2A"; "run1_2A"; "run3_2A"; "run6_2A"; "RM_2A"; "RQ_2A"; "TM0_2A"; "TQ0_2A"; "run2_2A_1"; "run2_2A_2"; "run2_2A_3"; "run2_2A_4"; "run4_2A"; "run5_2A"; "EfD_2A_1"; "EfD_2A_2"; "EfD_2A_3"; "EfD_2A_4"; "Eq_2A"; "RD_2A_1"; "RD_2A_2"; "RD_2A_3"; "RD_2A_4"; "TDr_2A_1"; "TDr_2A_2"; "TDr_2A_3"; "TDr_2A_4"; "exits1_2A"; "Ebg_2A"; "Edr_2A"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "Xf_2A"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
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

