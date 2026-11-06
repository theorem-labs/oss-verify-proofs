(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic ib.
From Stdlib Require NArith PArith Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.

(* [comment removed for export] *)
Module F0A_cL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf"; "C4_L1Bf"; "EQ_L1Bf"; "q_L1Bf"; "C2_L1Bf_1"; "C2_L1Bf_2"; "C2_L1Bf_3"; "C3_L1Bf"; "CD_L1Bf"; "P0_L1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "Ems_L1Bf"; "Eps_L1Bf"; "S1c_L1Bf_1"; "S1c_L1Bf_2"; "S1c_L1Bf_3"; "TM_L1Bf"; "TQ_L1Bf"; "run3_L1Bf"; "run6_L1Bf"; "RM_L1Bf"; "RQ_L1Bf"; "TM0_L1Bf"; "TQ0_L1Bf"; "run1_L1Bf"; "run2_L1Bf_1"; "run2_L1Bf_2"; "run2_L1Bf_3"; "run4_L1Bf"; "run5_L1Bf"; "EfD_L1Bf_1"; "EfD_L1Bf_2"; "EfD_L1Bf_3"; "Eq_L1Bf"; "RD_L1Bf_1"; "RD_L1Bf_2"; "RD_L1Bf_3"; "TDr_L1Bf_1"; "TDr_L1Bf_2"; "TDr_L1Bf_3"; "exits1_L1Bf"; "Ebg_L1Bf"; "Edr_L1Bf"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "W_L1Bf"; "Xf_L1Bf"; "st_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A"; "C4_L2A"; "EQ_L2A"; "q_L2A"; "C2_L2A_1"; "C2_L2A_2"; "C2_L2A_3"; "C2_L2A_4"; "C3_L2A"; "CD_L2A"; "P0_L2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "Ems_L2A"; "Eps_L2A"; "S1c_L2A_1"; "S1c_L2A_2"; "S1c_L2A_3"; "S1c_L2A_4"; "TM_L2A"; "TQ_L2A"; "run1_L2A"; "run3_L2A"; "run6_L2A"; "RM_L2A"; "RQ_L2A"; "TM0_L2A"; "TQ0_L2A"; "run2_L2A_1"; "run2_L2A_2"; "run2_L2A_3"; "run2_L2A_4"; "run4_L2A"; "run5_L2A"; "EfD_L2A_1"; "EfD_L2A_2"; "EfD_L2A_3"; "EfD_L2A_4"; "Eq_L2A"; "RD_L2A_1"; "RD_L2A_2"; "RD_L2A_3"; "RD_L2A_4"; "TDr_L2A_1"; "TDr_L2A_2"; "TDr_L2A_3"; "TDr_L2A_4"; "exits1_L2A"; "Ebg_L2A"; "Edr_L2A"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "W_L2A"; "Xf_L2A"; "st_L2A"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
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
Module SegQ3G_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SLit"; "sv"; "SPBranch"; "SVar"; "SPNot"; "SPUle"; "SPAlign"; "SAlu"; "cell"; "DUnknown"; "SPUlt"; "mkCell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "app"; "bool"; "nat"; "pair"; "false"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "ZQ"; "vXK"; "NXR"; "mkR"; "vCSZ"; "vXF"; "SW"; "vXL"; "vXS"; "Xg"; "vCUR"; "F_nz"; "OC"; "regsC"; "F_H"; "LEXIT"; "LHEAD"; "O_cur"; "vCN"; "F_Hk"; "F_go"; "F_stop"; "Headk"; "OH"; "O_gqC"; "vK"; "vTF"; "vTS"; "F_H0"; "Head0"; "O_gqH"; "PostQ3R"; "RETR"; "post_ruR"; "regsH"; "regsX"; "vJK"; "vJL"; "vN"; "vS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "O_sb"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "mkD"; "s9'"; "vBN"; "DI"; "DTs"; "DBH"; "DH"; "DIH"; "DT"; "F_D"; "F_DI"; "F_czB"; "F_nzB"; "O_b"; "ruB"; "ruI"; "vB"; "vBC"; "vBS"; "vS7"; "OBD"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_NE"; "BC_EQ"; "ALU_SUB"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "HIGH_SHADOW_END"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "regs3"; "vMIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states"; "DBIg"; "DBTg"; "Exit0g"; "Exitkg"; "F_b"; "F_b24"; "F_new"; "O_itg"; "O_new"; "Cont0g"; "Contkg"; "DH0g"; "DHng"; "DIcg"; "DTcg"; "PXg"; "PostQ3Rg"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition O_new : sobj := ltac2:(tb__ "0|4|
S7aS2cZ0M0Z10SfS17S17S60S14A2M1S3A2M2S15G1S3S15S60S14G0U8M3A4S5Pc6A1A4SfG2S15G1S3S15S60S14Z8G3A4S5Pc7A1A4S10G2A1A3A3A4").
Definition F_new : list sprop := ltac2:(tb__ "0|0|
SfS0S6S4S5cS43S40S2N1A1A2S2Z0A1A3A1SfS0S7S2S5fA1S2cA2SfS0S8Pa4Z3A2S10S0A1A3A3A3").
Definition Cont0g : axst := ltac2:(tb__ "0|0|
S1dS2aS27S11S2Z1A1A2S26S20S1aS24S1aS1eA4A1SfS1S32S11A1SfS1S6dSfS1S2bS1aS1eA2S10S1A1A3A3A3S12S0S12S0S28SfS0S2eSfS0S25S11A1S10S0A1A3A3A3S6bA3S1cA6").
Definition Contkg : axst := ltac2:(tb__ "0|2|
S1dS2aS27S11S43S33S2Z1A1A2M0A2S26S20S3eS34S3fS43S35S1eA2A4A1SfS1S32S11A1SfS1S6dSfS1S2bS1aS1eA2S10S1A1A3A3A3S12S0S12S0S2dSfS0S2eSfS0S25S11A1S10S0A1M1A3A3A3S12S0S6bSfS0S6S4S5cG0S2Z0A1A3A1G1A3A3A3S1cA6").
Definition Exit0g (nz : bool) : axst := ltac2:(tb__ "0|1|
S1dS29S27Vnz;S2Z1A1M0A2S26S20G0S24S24S1eA4A1S10S1A1S12S0S28SfS0S2fSfS0S25Vnz;A1S10S0A1A3A3A3S1cA6").
Definition Exitkg (nz : bool) : axst := ltac2:(tb__ "0|1|
S1dS29S27Vnz;S43S33S2Z1A1A2M0A2S26S20G0S34S24S43S35S1eA2A4A1S10S1A1S12S0S2dSfS0S2fSfS0S25Vnz;A1S10S0A1A3A3A3S1cA6").
Definition PXg : axst := ltac2:(tb__ "0|0|
S1dS29S3dS31S20S1aS1aS1aS1aA4A1S10S1A1S12S0S36SfS0S4S5eS64S41A3S10S0A1A3A3S1cA6").

Lemma PH_Head0 : ltac2:(tb__ "0|0|
S18S79S1dS2aS3cS24S1aS1aA3S31S20S1aS1aS1aS1aA4A1SfS1S38SfS1S2bS2cS1eA2S10S1A1A3A3S28S1cA6S37A3"). Proof. reflexivity. Qed.
Lemma chkG_R : ltac2:(tb__ "0|0|
S19S18S13S42S6eS30A2S11A3S19S18S13S42S6fS30A2S11A3S19S18S13S42S67S11A1S23A2S11A3S19S18S13S42S67S16A1S23A2S11A3S19S18S13S42S68S11A1S23A2S11A3S19S18S13S42S68S16A1S23A2S11A3S18S13S42S74S23A2S11A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F_b : list sprop := ltac2:(tb__ "0|0|
SfS0S7S2S5fA1S1fA2SfS0S8Pb9Z4A2S10S0A1A3A3").
Definition DH0g : axst := ltac2:(tb__ "0|1|
S46S4bSfS17S14S3A2M0S15S14S3UaS1bA4S10G0A1A3S1bS1fS21S22SfS1S44SfS1S53S48A1S10S1A1A3A3S12S0S12S0S61S62A1SfS0S6S4S5cS1bS2Z0A1A3A1S10S0A1A3A3S69A3A8").
Definition DHng : axst := ltac2:(tb__ "0|1|
S46S4bSfS17S14S3A2M0S15S14S3U14S56A4SfG0S15S14S3UaS1bA4S10G0A1A3A3S1bS1fS21S22SfS1S44SfS1S53S48A1S10S1A1A3A3S12S0S12S0S61S62A1SfS0S4S5bS1bS2Z0A1A3S10S0A1A3A3S69A3A8").
Definition O_itg (base : sv) : sobj := ltac2:(tb__ "0|1|
SeVbase;S2N80A1M0S2N78A1SfSaSdG0Z8S5Pc6A1A3S10SaA1A3SbA5").
Definition DBIg (nz : bool) : axst := ltac2:(tb__ "0|3|
S46S4dS54S16A1S43S1bS2N1A1A2S48S13S3Lnz;Vnz;S21S1aX13x2S9S5dS22S58A3SfS1S44SfS1S6cS43S1fS2Z98M0A1A2M1A1S10S1A1A3A3S12S0S12S0S4fSfS0S51S16A1SfS0S52Vnz;A1S10S0A1M2A3A3A3SfS0S7S2S76S5fG0A2A1G1A2SfS0S8Pb9Z4A2G2A3A3A3A8").
Definition DIcg : axst := ltac2:(tb__ "0|2|
S46S4dS55S43S59S2Z8A1A2M0S47A2S1bS1fS21S22SfS1S44SfS1S6cG0A1S10S1A1A3A3S12S0S12S0S50SfS0S4S5bS47S43S57S2Z10A1A2A3S10S0A1M1A3A3SfS0S7S2S76S5fZ98A2A1G0A2G1A3A3A8").
Definition F_b24 (b : sv) : list sprop := ltac2:(tb__ "0|0|
SfS0S7S45Vb;A2SfS0ScVb;S43S45S2S77Z2Z25A2A1A2A2S10S0A1A3A3").
Definition DTcg : axst := ltac2:(tb__ "0|0|
S46S4eS55S43S59S2Z8A1A2S47A2S1bS1fS21S22SfS1S44S10S1A1A3S12S0S12S0S50SfS0S6S4S5bS47S43S57S2Z10A1A2A3A1S10S0A1A3A3S6aS56A1A3A8").
Definition DBTg (nz : bool) : axst := ltac2:(tb__ "0|0|
S46S4eS54S11A1S43S1bS2N1A1A2S48S13S3Lnz;Vnz;S21S1aX13x2S9S5dS22S58A3SfS1S44S10S1A1A3S12S0S12S0S4fSfS0S51S11A1SfS0S52Vnz;A1S10S0A1A3A3A3S6aS1fA1A3A8").
Definition PostQ3Rg : axst := ltac2:(tb__ "0|1|
S1dS3aS78S63S3bA2S5aS5Pa0A1M0S5Pa1A1S5Pa2A1S5Pa3A1A4S10S1A1S12S0S61S62A1SfS0S6S4S5bG0S2Z0A1A3A1S10S0A1A3A3S1cA6").
Lemma chkG_D : ltac2:(tb__ "0|0|
S19S18S13S42S70S4cA2S11A3S19S18S13S42S71S4cA2S11A3S19S18S13S42S65S11A1S49A2S11A3S19S18S13S42S65S16A1S49A2S11A3S19S18S13S42S72S49A2S11A3S19S18S13S42S73S4aA2S11A3S19S18S13S42S66S11A1S4aA2S11A3S19S18S13S42S66S16A1S4aA2S11A3S18S13S42S75S39A2S11A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQ3G_states.

(* [comment removed for export] *)
Module F0A_cL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be"; "C4_L2Be"; "EQ_L2Be"; "q_L2Be"; "C2_L2Be_1"; "C2_L2Be_2"; "C2_L2Be_3"; "C2_L2Be_4"; "C3_L2Be"; "CD_L2Be"; "P0_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "Ems_L2Be"; "Eps_L2Be"; "S1c_L2Be_1"; "S1c_L2Be_2"; "S1c_L2Be_3"; "S1c_L2Be_4"; "TM_L2Be"; "TQ_L2Be"; "run1_L2Be"; "run3_L2Be"; "run6_L2Be"; "RM_L2Be"; "RQ_L2Be"; "TM0_L2Be"; "TQ0_L2Be"; "run2_L2Be_1"; "run2_L2Be_2"; "run2_L2Be_3"; "run2_L2Be_4"; "run4_L2Be"; "run5_L2Be"; "EfD_L2Be_1"; "EfD_L2Be_2"; "EfD_L2Be_3"; "EfD_L2Be_4"; "Eq_L2Be"; "RD_L2Be_1"; "RD_L2Be_2"; "RD_L2Be_3"; "RD_L2Be_4"; "TDr_L2Be_1"; "TDr_L2Be_2"; "TDr_L2Be_3"; "TDr_L2Be_4"; "exits1_L2Be"; "Ebg_L2Be"; "Edr_L2Be"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "W_L2Be"; "Xf_L2Be"; "st_L2Be"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf"; "C4_L2Bf"; "EQ_L2Bf"; "q_L2Bf"; "C2_L2Bf_1"; "C2_L2Bf_2"; "C2_L2Bf_3"; "C2_L2Bf_4"; "C3_L2Bf"; "CD_L2Bf"; "P0_L2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "Ems_L2Bf"; "Eps_L2Bf"; "S1c_L2Bf_1"; "S1c_L2Bf_2"; "S1c_L2Bf_3"; "S1c_L2Bf_4"; "TM_L2Bf"; "TQ_L2Bf"; "run1_L2Bf"; "run3_L2Bf"; "run6_L2Bf"; "RM_L2Bf"; "RQ_L2Bf"; "TM0_L2Bf"; "TQ0_L2Bf"; "run2_L2Bf_1"; "run2_L2Bf_2"; "run2_L2Bf_3"; "run2_L2Bf_4"; "run4_L2Bf"; "run5_L2Bf"; "EfD_L2Bf_1"; "EfD_L2Bf_2"; "EfD_L2Bf_3"; "EfD_L2Bf_4"; "Eq_L2Bf"; "RD_L2Bf_1"; "RD_L2Bf_2"; "RD_L2Bf_3"; "RD_L2Bf_4"; "TDr_L2Bf_1"; "TDr_L2Bf_2"; "TDr_L2Bf_3"; "TDr_L2Bf_4"; "exits1_L2Bf"; "Ebg_L2Bf"; "Edr_L2Bf"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "W_L2Bf"; "Xf_L2Bf"; "st_L2Bf"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
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

(* [comment removed for export] *)
Module LiveGeom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "sub"; "lt"; "div"; "mul"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "rz"; "is_primary"; "region_beg"; "ClassID"; "PG"; "Size"; "needed"; "dyn_in"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_live"; "AA"; "sec_chunk"; "aa_geom"; "ag_spacebeg"; "aa_cls"; "aa_sec"; "ageom"; "class_state"; "cs_cache"; "cs_empty"; "cs_free_array"; "sc_map_beg"; "sc_map_size"; "topG"; "@Corelib.Init.Datatypes"; "pair"; "bool"; "list"; "nat"; "prod"; "Some"; "false"; "option"; "true"; "app"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "live_ids"; "nthZ"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma nodup_map_filter_pos : forall (T U : Type) (f : T -> U) (p : T -> bool) (l : list T) i j x y,
  NoDup (map f (List.filter p l)) -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y ->
  p x = true -> p y = true -> f x <> f y.
Proof.
  intros T U f p. induction l as [|h l IH]; intros i j x y ND Hij Hi Hj Px Py; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. cbn [List.filter] in ND. rewrite Px in ND. cbn [map] in ND.
    inversion ND as [|? ? NI ND']; subst. intros E. apply NI. rewrite E. apply list_elem_of_In. apply in_map. apply filter_In. split; [exact (nth_error_In _ _ Hj) | exact Py].
  - cbn [nth_error] in Hi. apply (IH i j x y); try assumption; [|lia].
    cbn [List.filter] in ND. destruct (p h); [cbn [map] in ND; inversion ND; subst; assumption | exact ND].
Qed.

Lemma nodup_map_sfilter_pos : forall (T U : Type) (f : T -> U) (p : T -> bool) (l : list T) i j x y,
  NoDup (map f (filter (fun t => Is_true (p t)) l)) -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y ->
  p x = true -> p y = true -> f x <> f y.
Proof.
  intros T U f p. induction l as [|h l IH]; intros i j x y ND Hij Hi Hj Px Py; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. rewrite list_basics.list.filter_cons_True in ND by (rewrite Px; exact I). cbn [map] in ND.
    inversion ND as [|? ? NI ND']; subst. intros E. apply NI. rewrite E. apply list_elem_of_In. apply in_map. apply list_elem_of_In.
    apply list_basics.list.list_elem_of_filter. split; [rewrite Py; exact I | apply list_elem_of_In; exact (nth_error_In _ _ Hj)].
  - cbn [nth_error] in Hi. apply (IH i j x y); try assumption; [|lia].
    destruct (p h) eqn:Ph.
    + rewrite list_basics.list.filter_cons_True in ND by (rewrite Ph; exact I). cbn [map] in ND. inversion ND; subst; assumption.
    + rewrite list_basics.list.filter_cons_False in ND by (rewrite Ph; intros []). exact ND.
Qed.

Lemma live_prim_facts : ltac2:(tb__ "0|5|
S17S32S27S36Q40A1A1S31S0S0S33Vsegs;R6R5R4R3A5S2fS29S0S0A2S25S0S0R3R2A4S16R7A1A3S9S26SeR3A1S2dA3S10S13R4A1A1S0SfS1aS19RaA1A1R1A2S0S4S4R7SdR6A1A2R1A2S0S8S8S1Z1M0R7A2S1R7Zfc00A2A2S8S8S1G0R3A2S1R3Z1eA2A2S8S1Z0M1R1A2S8S9S0S3R1S12R3A1M2A2G1A3S8S1S2R1G2A2S15A2S8S1S2SdR7A1M3R7A2G2A2S8S9S0S3G2Z10M4A2G1A3S8S8S1G4G3A2S1G3Z800A2A2S9S0S3G3G4A2G1A3A2A2A2A2A2A2A2A2Tx;Trb;Tc;F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n (HG & HR & HF & HRest & HM & HI3 & HB) Hin HP c rb x.
  destruct HRest as (Hsep & _ & HPR & _). destruct (Hsep b n Hin) as (Hn1 & _).
  assert (Hn : 1 <= n <= 64512).
  { split; [exact Hn1|]. destruct (Z_le_dec 64513 n) as [L|L]; [|lia]. rewrite (not_primary_large n L) in HP. discriminate. }
  pose proof (slot_ok_all n Hn) as SO. unfold slot_ok in SO.
  apply andb_prop in SO as [SO S5]. apply andb_prop in SO as [SO S4]. apply andb_prop in SO as [SO S3]. apply andb_prop in SO as [_ S2].
  apply Z.leb_le in S2, S4, S5. apply Z.eqb_eq in S3. unfold slot in S2, S3. fold c in S2, S3, S4, S5.
  destruct HPR as (_ & _ & _ & P4). destruct (P4 c (conj S4 S5)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
  destruct (LV b n Hin HP eq_refl) as (L1 & L2 & L3). fold rb in L1, L2, L3. fold x in L2, L3.
  pose proof (rz_bound n) as RZ.
  assert (RZ16 : rz n mod 16 = 0).
  { unfold rz. rewrite Z.shiftl_mul_pow2 by (unfold rz_log; repeat destruct (_ <=? _); lia). rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (ND : rz n + n <= needed n).
  { unfold needed, kChunkHeader2Size. pose proof (Z.div_mod (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as MB. unfold round_up. lia. }
  repeat split; try lia.
Qed.

Lemma live_sec_facts : ltac2:(tb__ "0|3|
S17S32S27S36Q40A1A1S31S0S0S33Vsegs;R6R5R4R3A5S2fS29S0S0A2S25S0S0R3R2A4S16R7A1A3S9S26SeR3A1S2bA3SaS28S28SaS18S18S8S9S2cS18A1S30S18S1cRbA1R2A3S2aS18R1A2A3S8S9S0R7S2S2S22R1A1M0S11A2Z800M1A2A3S8S1Z1R6A2S8S1S2S2R7R6A2G1A2S2G0S23R1A1M2A2A2S8S9S0S3G0S11A2Z0A3S14S24S19RbA1A1G0G2A3A2A2A2A2A2Lch;A2Li;A2F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n (HG & HR & HF & HRest & HM & HI3 & HB) Hin HP.
  destruct HRest as (Hsep & _ & _ & HS & _). destruct (Hsep b n Hin) as (Hn1 & _).
  destruct HI3 as (_ & LIV3 & _). destruct (LIV3 b n Hin) as [E|(ch & Hch & Eb & Esz)]; [rewrite E in HP; discriminate|].
  destruct (In_nth_error _ _ Hch) as (i & Hi). exists i, ch. split; [exact Hi|]. split; [exact Eb|]. split; [exact Hn1|].
  destruct HS as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
  pose proof (round_up_ge8 n) as R8. unfold PG in *. split; [lia|]. split; [exact D6 | exact D10].
Qed.

Lemma rz_sec : ltac2:(tb__ "0|0|
S0S1Z1R1A2S9S26SeR2A1S2bA3S9S0SdR3A1Z800A3F_;F_;Fn;").
Proof.
  intros n Hn HP. apply rz_large. destruct (Z_le_dec 64513 n) as [L|L]; [exact L|]. rewrite (primary_small n ltac:(lia)) in HP. discriminate.
Qed.

Lemma aligned_apart : ltac2:(tb__ "0|1|
S0S0S0S5Z0M0R3A2S9S0S3R3R4A2G0A3S9S0S3R3R5A2G0A3SbS9S0R5R4A3A1ScS1S2R6R7A2R5A2S1S2R5R7A2R6A2A2F_;F_;F_;F_;Fy;Fx;FS;").
Proof.
  intros S x y HS Hx Hy Hne. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hy; [|lia].
  destruct Hx as [p ->]. destruct Hy as [q ->]. assert (p <> q) by (intros ->; apply Hne; reflexivity). nia.
Qed.

Lemma live_pair_apart : ltac2:(tb__ "0|2|
S17S32S27S36Q40A1A1S31S28S28S0S0S0S0S33Vsegs;RaR9R8R7A5S37R7R6A2S9S2cS29S0S0A2M0A1M1S30G0S16RcA1R8A3S2aG0S25S0S0R6R5A4A2A3S9G1S30G0S16RdA1R8A3S2aG0S25S0S0R5R4A4A2A3ScS1S2R8R7A2S4R6SdR5A1A2A2S1S2R6R5A2S4R8SdR7A1A2A2A2F_;F_;F_;F_;Fn';Fb';Fn;Fb;Fj;Fi;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md i j b n b' n' HA Hij Hi Hj.
  pose proof (nth_error_In _ _ Hi) as Hin. pose proof (nth_error_In _ _ Hj) as Hin'.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in SP2.
  destruct (is_primary n) eqn:EP; destruct (is_primary n') eqn:EP'.
  -
    pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. pose proof (live_prim_facts A rho tp md b' n' HA Hin' EP') as F'. cbn zeta in F, F'.
    set (c := ClassID (needed n)) in *. set (c' := ClassID (needed n')) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16). destruct F' as (Hn' & Hc' & X0' & XM' & XU' & XS' & S16' & RZ' & RZ16').
    destruct (Z.eq_dec c c') as [Ec|Nc].
    +
      destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & P4).
      destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
      apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (ND & _ & _).
      unfold live_ids in ND.
      pose proof (nodup_map_sfilter_pos _ _ (fun bn : Z * Z => (fst bn - rz (snd bn) - region_beg (ag_spacebeg (aa_geom A)) c) / 16)
                    (fun bn : Z * Z => is_primary (snd bn) && (ClassID (needed (snd bn)) =? c)) (aa_live A) i j (b, n) (b', n') ND Hij Hi Hj) as NE.
      cbn [fst snd] in NE. rewrite EP, EP' in NE. fold c c' in NE. rewrite <- Ec in NE. rewrite Z.eqb_refl in NE. specialize (NE eq_refl eq_refl).
      rewrite <- Ec in *. pose proof (Size_pos c Hc) as SPc.
      assert (NX : b - rz n - region_beg (ag_spacebeg (aa_geom A)) c <> b' - rz n' - region_beg (ag_spacebeg (aa_geom A)) c) by (intros E; apply NE; rewrite E; reflexivity).
      destruct (aligned_apart (Size c) _ _ SPc XM XM' NX) as [D|D]; [left | right]; lia.
    +
      unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c Hc). pose proof (Size_pos c' Hc').
      assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; [left | right]; nia.
  -
    pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. cbn zeta in F. set (c := ClassID (needed n)) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (live_sec_facts A rho tp md b' n' HA Hin' EP') as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n' Hn1 EP') as RZs.
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, PG in *. pose proof (Size_pos c Hc).
    destruct DS as [DS|DS]; [right | left]; nia.
  -
    pose proof (live_prim_facts A rho tp md b' n' HA Hin' EP') as F. cbn zeta in F. set (c := ClassID (needed n')) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n Hn1 EP) as RZs.
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, PG in *. pose proof (Size_pos c Hc).
    destruct DS as [DS|DS]; [left | right]; nia.
  -
    destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct (live_sec_facts A rho tp md b' n' HA Hin' EP') as (k' & ch' & Hk' & Eb' & Hn1' & Hend' & _ & _).
    pose proof (rz_sec n Hn1 EP) as RZs. pose proof (rz_sec n' Hn1' EP') as RZs'.
    destruct HI3 as (_ & _ & SEC3 & _ & _ & ND6 & _).
    apply list_relations.list.NoDup_app in ND6 as (ND6 & _ & _).
    pose proof (nodup_map_filter_pos _ _ (fun bn : Z * Z => fst bn) (fun bn : Z * Z => negb (is_primary (snd bn))) (aa_live A) i j (b, n) (b', n') ND6 Hij Hi Hj) as NE.
    cbn [fst snd] in NE. rewrite EP, EP' in NE. specialize (NE eq_refl eq_refl).
    destruct (Nat.eq_dec k k') as [Ek|Nk].
    + exfalso. subst k'. rewrite Hk in Hk'. injection Hk' as <-. apply NE. lia.
    + destruct (SEC3 k ch Hk) as (_ & _ & _ & _ & DJ & _). destruct (DJ k' ch' Hk' Nk) as [D|D]; unfold PG in *; [left | right]; lia.
Qed.

Lemma live_id_in : ltac2:(tb__ "0|0|
S1dS17S0S0S0S2fS29S0S0A2S25S0S0R3R2A4S16R4A1A3S9S26SeR3A1S2dA3S9S0S10S13R4A1A1R3A3S2fS0S6S4S4R6SdR5A1A2SfS1aR8A1R4A2A2Z10A2S34R8R7R4A3A3F_;F_;F_;Fc;Fn;Fb;FA;FG;").
Proof.
  intros G A b n c Hin HP Hc. unfold live_ids. apply in_map_iff. exists (b, n). split; [reflexivity|].
  apply list_elem_of_In. apply list_basics.list.list_elem_of_filter. split; [|apply list_elem_of_In; exact Hin].
  cbn [snd]. rewrite HP, Hc, Z.eqb_refl. exact I.
Qed.

Lemma slot_not_live : ltac2:(tb__ "0|2|
S17S32S27S36Q40A1A1S31S0S0S0S33Vsegs;R7R6R5R4A5S8S1Z1R4A2S1R4Z1eA2A2S2fS0R4S2eS0S21S35S1eS1bR9A1R5S20A4M0A1S1fG0A1A3A3S8S1S2SfS1aS19RaA1A1R6A2S7Z10R5A2A2M1R4A2S5R4S2G1S12R6A1A2A2A2SbS38S16RbA1R5A2A1F_;F_;F_;F_;Fz;Fx;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c x z HA Hc Hx Hz (b & n & Hin & Hzb).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in SP2.
  destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & P4).
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _).
  destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
  pose proof (Size_pos c Hc) as SPc.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. cbn zeta in F. set (c' := ClassID (needed n)) in *.
    destruct F as (Hn & Hc' & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (Z.eq_dec c' c) as [Ec|Nc].
    +
      pose proof (live_id_in (aa_geom A) A b n c Hin EP Ec) as Hid. rewrite Ec in *.
      set (o := b - rz n - region_beg (ag_spacebeg (aa_geom A)) c) in *.
      assert (NE : x <> o / 16).
      { intros E. apply list_relations.list.NoDup_app in ND as (_ & D1 & ND). apply list_relations.list.NoDup_app in ND as (_ & D2 & _).
        apply in_app_or in Hx as [Hf|Hcch].
        - apply (D1 x (proj2 (list_elem_of_In _ _) Hf)). apply list_elem_of_In. apply in_or_app. right. apply in_or_app. left. rewrite E. exact Hid.
        - apply (D2 x (proj2 (list_elem_of_In _ _) Hcch)). apply list_elem_of_In. apply in_or_app. left. rewrite E. exact Hid. }
      assert (O16 : o = 16 * (o / 16)).
      { assert (D16 : (16 | o)) by (apply (Z.divide_trans _ (Size c)); [apply Z.mod_divide; [lia | exact S16] | apply Z.mod_divide; [lia | exact XM]]).
        destruct D16 as [q Eq]. rewrite Eq. rewrite Z.div_mul by lia. lia. }
      assert (NX : 16 * x <> o) by lia.
      rewrite Z.mul_comm in X2.
      destruct (aligned_apart (Size c) (16 * x) o SPc X2 XM NX) as [D|D]; unfold o in *; lia.
    +
      unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. pose proof (Size_pos c' Hc').
      assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia.
  - destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, PG in *. destruct DS as [DS|DS]; nia.
Qed.

End WithSegs.
End LiveGeom.

