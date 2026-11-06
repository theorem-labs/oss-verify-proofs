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
From Stdlib Require NArith PArith Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.

(* [comment removed for export] *)
Module F0A_c2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "C4_2Be"; "EQ_2Be"; "q_2Be"; "C2_2Be_1"; "C2_2Be_2"; "C2_2Be_3"; "C2_2Be_4"; "C3_2Be"; "CD_2Be"; "P0_2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "Ems_2Be"; "Eps_2Be"; "S1c_2Be_1"; "S1c_2Be_2"; "S1c_2Be_3"; "S1c_2Be_4"; "TM_2Be"; "TQ_2Be"; "run1_2Be"; "run3_2Be"; "run6_2Be"; "RM_2Be"; "RQ_2Be"; "TM0_2Be"; "TQ0_2Be"; "run2_2Be_1"; "run2_2Be_2"; "run2_2Be_3"; "run2_2Be_4"; "run4_2Be"; "run5_2Be"; "EfD_2Be_1"; "EfD_2Be_2"; "EfD_2Be_3"; "EfD_2Be_4"; "Eq_2Be"; "RD_2Be_1"; "RD_2Be_2"; "RD_2Be_3"; "RD_2Be_4"; "TDr_2Be_1"; "TDr_2Be_2"; "TDr_2Be_3"; "TDr_2Be_4"; "exits1_2Be"; "Ebg_2Be"; "Edr_2Be"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "W_2Be"; "Xf_2Be"; "st_2Be"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "C4_2Bf"; "EQ_2Bf"; "q_2Bf"; "C2_2Bf_1"; "C2_2Bf_2"; "C2_2Bf_3"; "C2_2Bf_4"; "C3_2Bf"; "CD_2Bf"; "P0_2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "Ems_2Bf"; "Eps_2Bf"; "S1c_2Bf_1"; "S1c_2Bf_2"; "S1c_2Bf_3"; "S1c_2Bf_4"; "TM_2Bf"; "TQ_2Bf"; "run1_2Bf"; "run3_2Bf"; "run6_2Bf"; "RM_2Bf"; "RQ_2Bf"; "TM0_2Bf"; "TQ0_2Bf"; "run2_2Bf_1"; "run2_2Bf_2"; "run2_2Bf_3"; "run2_2Bf_4"; "run4_2Bf"; "run5_2Bf"; "EfD_2Bf_1"; "EfD_2Bf_2"; "EfD_2Bf_3"; "EfD_2Bf_4"; "Eq_2Bf"; "RD_2Bf_1"; "RD_2Bf_2"; "RD_2Bf_3"; "RD_2Bf_4"; "TDr_2Bf_1"; "TDr_2Bf_2"; "TDr_2Bf_3"; "TDr_2Bf_4"; "exits1_2Bf"; "Ebg_2Bf"; "Edr_2Bf"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "W_2Bf"; "Xf_2Bf"; "st_2Bf"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
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
Module InvFoot.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "of_nat"; "div"; "pow"; "leb"; "mul"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "sec_chunk"; "aa_sec"; "ageom"; "aa_cls"; "aa_live"; "qbatch"; "class_state"; "ag_spacebeg"; "sc_map_beg"; "aa_cache_inited"; "ag_pab"; "sc_map_size"; "aa_depot"; "ag_thread"; "topG"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "cs_allocated_user"; "cs_empty"; "qb_addr"; "sc_size"; "@Corelib.Init.Datatypes"; "list"; "option"; "bool"; "prod"; "true"; "Some"; "andb"; "false"; "nat"; "negb"; "orb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "c_addr"; "cell_ok"; "acell"; "c_w"; "view"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "primary_repr"; "secondary_repr"; "batch_repr"; "alloc_magic_ok"; "class_repr"; "ia_inv"; "inv3"; "live_block_repr"; "misc_inv"; "nthZ"; "q_item_ok"; "qhdr_repr"; "qlinks"; "quarantine_repr"; "thread_inv"; "geom_ok"; "live_sep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "kSpaceSize"; "rz"; "is_primary"; "kPtrArrayReserve"; "ClassID"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "needed"; "region_beg"; "FS_total"; "Sh"; "round_up"; "PG"; "dyn_in"; "dyn_ok"; "kQuarantineBatchSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "STORE"; "MAP1"; "DFPw"; "dfp_static"; "MAP1N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot"; "dstatw"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot.Zones"; "prim_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dstatw (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S67Vz;A1S1S3S1S5S6S64Z10A2Vz;A2S7Vz;S6S64Z18A2A2A2A1S3S1S5S65Vz;A2S7Vz;S6S65Z8A2A2A2A1A2A2").
Lemma dstat_range : ltac2:(tb__ "0|0|
SfS67R1A1S1S5S64R2A2S7R2S6S65SdZ8S68A2A2A2A2F_;Fz;").
Proof. intros z Hz. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia. Qed.
Lemma dstat_img : ltac2:(tb__ "0|0|
SfS67R1A1S1S5S52R2A2S7R2S51A2A2F_;Fz;").
Proof. intros z Hz. pose proof (dstat_range z Hz). unfold STORE, MAP1, MAP1N, IMG_LO, IMG_HI in *. lia. Qed.

Section Zones.
Variables (Gg : ageom) (secs : list sec_chunk) (m m' : bview).

Hypothesis AGimg : ltac2:(tb__ "0|0|
SfS1S5S52R1A2S7R1S51A2A2S3S70R2A1A1S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Hypothesis AGsp : ltac2:(tb__ "0|1|
SfS1S5S19VGg;A1M0R1A2S7R1S6S6G0S53A2Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGth : ltac2:(tb__ "0|1|
SfS1S5S1fVGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGctx : ltac2:(tb__ "0|1|
SfS1S5S25VGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGdtls : ltac2:(tb__ "0|1|
SfS1S5S26VGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGfs : ltac2:(tb__ "0|1|
SfS1S5S27VGg;A1M0R1A2S7R1S6G0S5dA2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGpab : ltac2:(tb__ "0|1|
SfS1S5S1cVGg;A1M0R1A2S7R1S6G0S56A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGsec : ltac2:(tb__ "0|1|
S12SfS6dS12R2Vsecs;A3S1S5S1aR3A1M0R2A2S7R2S6G0S1dR3A1A2A2A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;Fch;").
Hypothesis AGband : ltac2:(tb__ "0|0|
SfS1S5S59R1A2S7R1S58A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis HG : geom_ok Gg.

Lemma AGlow : ltac2:(tb__ "0|0|
SfS5S52R1A2S7R2S64A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof. intros z H1 H2. apply AGimg; [unfold STORE, IMG_LO, IMG_HI in *; lia|]. intros [D _]. pose proof (dstat_range z D). lia. Qed.
Lemma AGhigh : ltac2:(tb__ "0|0|
SfS5S6S65SdZ8S68A2A2R1A2S7R2S51A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof. intros z H1 H2. apply AGimg; [unfold MAP1, MAP1N, IMG_LO, IMG_HI in *; lia|]. intros [D _]. pose proof (dstat_range z D). lia. Qed.
Lemma cell_ok_low : ltac2:(tb__ "0|0|
S3cS5S52S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S64A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGlow; lia. Qed.
Lemma cell_ok_sp : ltac2:(tb__ "0|1|
S3cS5S19VGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6S6G0S53A2Z1000A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGsp; lia. Qed.
Lemma cell_ok_th : ltac2:(tb__ "0|1|
S3cS5S1fVGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6G0Z1000A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGth; lia. Qed.
Lemma cell_ok_pab : ltac2:(tb__ "0|1|
S3cS5S1cVGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6G0S56A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGpab; lia. Qed.
Lemma cell_ok_sec : ltac2:(tb__ "0|0|
S12S3cS6dS12R2Vsecs;A3S5S1aR3A1S3aR2A1A2S5S6S3aR3A1S9S3dR3A1A1A2S6S1aR4A1S1dR4A1A2A2S3bVm;R4A2S3bVm';R5A2F_;F_;F_;F_;Fc;Fch;").
Proof. intros ch c Hch H1 H2. apply cell_ok_agree. intros k Hk. apply (AGsec ch); [exact Hch | lia]. Qed.
Lemma cell_ok_band : ltac2:(tb__ "0|0|
S3cS5S59S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S58A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGband; lia. Qed.

Lemma AGsh : ltac2:(tb__ "0|0|
SfSfSfS5Z0R3A2S7R3SbZ2Z2fA2A2S1S5S5eR5A1R3A2S5R3S5eR4A1A2A2S0S2dS37Q8A1A1Vm';R4A1Vm;R4A1A3F_;F_;F_;Fz;Fy;Fx;").
Proof.
  intros x y z Hx Hy Hz. apply AGband. pose proof (Sh_in_band x) as SX. pose proof (Sh_in_band y) as SY.
  unfold Sh in *. pose proof (Z.div_le_mono 0 x 8 ltac:(lia) Hx).
  assert (x < 2 ^ 47 \/ 2 ^ 47 <= x) as [L|L] by lia.
  - specialize (SX ltac:(lia)). assert (y < 2 ^ 47) by lia. destruct (Z_lt_le_dec y 0).
    + pose proof (Z.div_le_mono y x 8 ltac:(lia) ltac:(lia)). lia.
    + specialize (SY ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x z 8 ltac:(lia)). pose proof (Z.div_le_mono (2 ^ 47) x 8 ltac:(lia) L). lia.
Qed.

Lemma rtc_inv_z : ltac2:(tb__ "0|0|
S3fVm;VGg;A2S3fVm';VGg;A2F_;").
Proof.
  intros HR. unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR]. intros z Hz.
  unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - unfold rtc_cells_img in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y;
      first [ apply AGlow; unfold IMG_LO, STORE; lia
            | apply AGhigh; unfold MAP1, MAP1N, IMG_HI; lia
            | apply AGimg; [unfold IMG_LO, IMG_HI; lia | intros (_ & N1 & N2); unfold STORE, MAP1 in N1, N2; lia] ] |]).
    destruct Hc.
  - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. pose proof (geom_nums _ HG) as (F1 & F2 & _). rewrite FS_total_val in F2.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y;
      first [ apply AGth; lia | apply AGctx; lia | apply AGdtls; lia | apply AGfs; rewrite FS_total_val; lia ] |]).
    destruct Hc.
Qed.

Lemma thread_inv_z : ltac2:(tb__ "0|0|
S4eVm;VGg;A2S4eVm';VGg;A2F_;").
Proof.
  intros [T1 T2]. split; [rewrite AGth by lia; exact T1|]. eapply present_agree; [|exact T2]. intros z Hz. apply AGth. lia.
Qed.

Lemma misc_inv_z : ltac2:(tb__ "0|0|
S48Vm;A1S48Vm';A1F_;").
Proof.
  intros (H1 & H2 & H3). split; [|split].
  - eapply cells_ok_frame; [|exact H1]. intros z Hz. unfold cells_footb in Hz.
    apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
    apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; apply AGlow; unfold IMG_LO, STORE; lia.
  - intros z Hz. rewrite AGlow by (unfold IMG_LO, STORE; lia). exact (H2 z Hz).
  - intros z Hz. rewrite AGhigh by (unfold ERRNO_A, MAP1, MAP1N, IMG_HI in *; lia). exact (H3 z Hz).
Qed.

Lemma ia_inv_z : ltac2:(tb__ "0|0|
S10S10S0S2eS21R1A1S21R2A1A3S45Vm;R3A2S45Vm';R3A2F_;F_;FA';FA;").
Proof.
  intros A A' EI H. unfold ia_inv in *. rewrite EI. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END in *.
  assert (AG : forall z, 0xef2c0 <= z < 0x17db4c -> m' z = m z) by (intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia).
  rewrite !AG by lia. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  destruct (aa_internal_inited A); destruct H4 as [H5 H6]; (split; [exact H5|]); intros z Hz; rewrite AG by lia; exact (H6 z Hz).
Qed.

Lemma class_repr_z : ltac2:(tb__ "0|0|
S10S10SfS18S1S5Z1R2A2S5R2Z1eA2A2S0S2eS1bR4A1S1bR5A1A3S0S2cS2fSfSfA2A1S16R5A1S16R6A1A3S0S2cS17A1S6cR6A1S6cR7A1A3S44Vm;VGg;R8R6R5A5S44Vm';VGg;R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;").
Proof.
  intros A A' c cs Hc Hci Hlv Hq P4.
  pose proof (geom_nums Gg HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & S1 & S2 & S0 & TG).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  unfold class_repr in P4 |- *. rewrite Hci.
  set (ri := region_info (ag_spacebeg Gg) c) in *. set (fa := free_array (ag_spacebeg Gg) c) in *.
  assert (RI : ag_spacebeg Gg <= ri /\ ri + 128 <= ag_spacebeg Gg + 2 ^ 37 + 4096) by (unfold ri, region_info; rewrite kSpaceSize_val; unfold kRegionInfoStride; lia).
  set (rb := region_beg (ag_spacebeg Gg) c) in *.
  assert (RB : ag_spacebeg Gg <= rb /\ rb + 2 ^ 32 <= ag_spacebeg Gg + 2 ^ 37) by (unfold rb, region_beg, kRegionSize; lia).
  assert (FA : fa = rb + kUserSpaceSize) by (unfold fa, free_array, rb; reflexivity).
  unfold live_ids. rewrite Hlv, Hq.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *. rewrite kSpaceSize_val in *.
  assert (CS : forall cc, rb <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= rb + 2 ^ 32 -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_sp; rewrite ?kSpaceSize_val; lia. }
  assert (CR : forall cc, ri <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= ri + 128 -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_sp; rewrite ?kSpaceSize_val; lia. }
  split; [apply CR; [cbn [c_addr]; unfold RI_mutex; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mutex; lia | exact C1]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_num_freed; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_free_array; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_allocated_user; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_allocated_meta; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_user; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_meta; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_exhausted; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AGsp; unfold kRegionInfoStride in Hz; rewrite ?kSpaceSize_val; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. assert (Li : (i < length (cs_free_array cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). apply CS; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (C9 i x Hi)]. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AGsp; rewrite ?kSpaceSize_val; lia|].
  split; [exact N7|].
  split; [eapply present_but_agree; [|exact PU]; intros z Hz _; apply AGsp; rewrite ?kSpaceSize_val; lia|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply (AGsh rb (rb + cs_mapped_user cs)); lia|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AGth; lia|].
  split; [exact ND|]. split; [exact LV|].
  split.
  - intros Hx. destruct (CI Hx) as (D1 & D2 & D3 & D4 & D5).
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D1]|].
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D2]|].
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D3]|]. split; [|exact D5].
    intros i x Hi. assert (Li : (i < length (cs_cache cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (max_count_le c) as MC.
    apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (D4 i x Hi)].
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hx. destruct (CN Hx) as [D1 D2]. split; [exact D1|]. eapply filled_agree; [|exact D2]. intros z Hz. apply AGth. lia.
Qed.

Lemma primary_repr_z : ltac2:(tb__ "0|1|
S10S10S0S14S11R2A1M0VGg;A3S0S14G0S11R3A1A3S0S2cS18A1S15R3A1S15R4A1A3S0S2eS1bR4A1S1bR5A1A3S0S2cS2fSfSfA2A1S16R5A1S16R6A1A3S0S2cS17A1S6cR6A1S6cR7A1A3S40Vm;R8A2S40Vm';R8A2F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG Eg Ec Eci El Eq (P1 & P2 & P3 & P4). unfold primary_repr. rewrite Eg, Ec, EG in *.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. intros c Hc. apply (class_repr_z A A' c _ Hc Eci El Eq (P4 c Hc)).
Qed.

Lemma secondary_repr_z : ltac2:(tb__ "0|1|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1M0S13R3A1Vsecs;A3S0S14S11R3A1S11R4A1A3S0G0S13R4A1S13R5A1A3S0SfS22R5A1S22R6A1A3S0S2cS2fSfSfA2A1S16R6A1S16R7A1A3S41Vm;R8A2S41Vm';R8A2F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ESS Eg Es Ep El (S1 & SP & S2 & S3 & S4 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite Eg, Es, Ep, El, EG, ESS in *.
  pose proof (topG_range Gg) as TGR.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_In _ _ Hi) as Hch. pose proof D10 as (X1 & X2 & X3 & _).
    assert (Li : (i < length secs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D1]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D2]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D3]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D4]|].
    split; [apply cell_ok_pab; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold kPtrArrayReserve in *; lia | exact D5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply (AGsec ch); [exact Hch | lia]|].
    eapply present_agree; [|exact D14]. intros z Hz. apply (AGsh (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch)); lia. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AGpab; unfold kPtrArrayReserve in *; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  unfold SEC_INST in *.
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I1]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I2]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I3]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I4]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I5]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I8]|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia.
Qed.

Definition prim_okb (n : Z) : bool := ltac2:(tb__ "0|1|
S36S35S55Vn;A1A1S32ScZ1S57S5bVn;A1A1M0A2ScG0Z1eA2A2A2").
Lemma prim_okb_all : ltac2:(tb__ "0|1|
SfS1S5Z1M0R1A2S7R1S6G0Z10000A2A2A2S0S2eS72R2A1S30A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_okb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma round_up_ge8 : ltac2:(tb__ "0|0|
SfS5R1S5fR1Z8A2A2Fz;").
Proof. intros z. unfold round_up. pose proof (Z.div_mod (z + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 8 - 1) 8 ltac:(lia)). lia. Qed.
Lemma primary_cls : ltac2:(tb__ "0|2|
SfS5Z1M0R1A2S0S2eS55R2A1S30A3S1S5G0S57S5bR3A1A1M1A2S5G1Z1eA2A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_okb_all n ltac:(lia)) as H. unfold prim_okb in H. rewrite HP in H. cbn [negb orb] in H.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma Size_pos : ltac2:(tb__ "0|0|
SfS1S5Z1R1A2S5R1Z1eA2A2S7Z0S5aR2A1A2F_;Fc;").
Proof. intros c Hc. pose proof (forall_rangeZ_ok (fun c => 0 <? Size c) 1 30 c ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(lia)) as H. apply Z.ltb_lt in H. exact H. Qed.

Lemma prim_below_in_space : ltac2:(tb__ "0|1|
S10SfSfSfSfS40Vm;R5A2S0S14S11R6A1VGg;A3S1S5Z1R6A2S5R6Z1eA2A2S5S5cS19VGg;A1M0R7A2S8R6S54R5A1A2A2S5S6S8S8R7S54R6A1A2S5cG0R8A2A2S5aR8A1A2S28S49S18S15R9A1R8S29A4A1A2S1S5S8R8S54R7A1A2R6A2S7R6R8A2A2S1S5G0R7A2S7R7S6S6G0S53A2Z1000A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fn;Fu;Fc;FA;").
Proof.
  intros A c u n z (_ & _ & _ & P4) EG Hc R1 R2 Hz. rewrite EG in P4.
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
  pose proof (rz_bound n). unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. rewrite kSpaceSize_val.
  unfold region_beg, kRegionSize in R1, R2 |- *.
  pose proof (Size_pos c Hc). nia.
Qed.

Lemma alloc_magic_ok_z : ltac2:(tb__ "0|0|
SfSfSfS1S5S8R3S54R2A1A2R1A2S7R1R3A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S43Vm;R3R2A3S43Vm';R4R3A3F_;F_;Fn;Fu;").
Proof.
  intros u n AG [H|[H1 H2]]; [left; exact H|right]. pose proof (rz_bound n) as RZ.
  split; (eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia|assumption]).
Qed.

Lemma div8_superadd : ltac2:(tb__ "0|2|
SfSfS5Z0R2A2M0G0S5S6SaR4Z8M1A2SaR3G1A2A2SaS6R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a 8 ltac:(lia)). pose proof (Z.mul_div_le b 8 ltac:(lia)). lia.
Qed.

Lemma chunk_zone : ltac2:(tb__ "0|4|
S10SfSfS0S14S11R3A1VGg;A3S0S2cS12A1S13R4A1Vsecs;A3S40Vm;R5A2S41Vm;R6A2S5S6S51Z800M0A2R6A2S5Z1R6A2S0S2eS55R7A1S30A3S57S5bR8A1A1SfS5cS19VGg;A1R1A2SfS1S5R1S8RbS54RaA1A2M1A2S1S0SfSeS8G1R1A2M2S5aR2A1M3A2Z0A3S5S6G2G3A2S28S49S18S15RcA1R2S29A4A1A2A2A2Trb;Tc;F_;S0S2eS55R8A1S33A3S4S12S12S1S6dS12R1S13RcA1A3S1S0SfRbS6S6S1aR1A1S60A2G0A2A3S0SfS2bR1A1S6S5fRaZ8A2Z1000A2A3A2A2Lch;A2F_;S1SfS1S5G1R1A2S7R1RbA2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S7S6S6RaR9A2Z7A2SbZ2Z2fA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fu;FA;").
Proof.
  intros A u n EG ES HP HS Hu Hn QP QS. pose proof (rz_bound n) as RZ. pose proof (topG_range Gg) as TGR.
  pose proof (geom_nums Gg HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2.
  destruct (is_primary n) eqn:EP.
  - destruct (QP eq_refl) as (R1 & R2 & R3). pose proof (primary_cls n ltac:(lia) EP) as Hc.
    destruct HP as (_ & _ & _ & P4). rewrite EG in P4. destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
    pose proof (Size_pos _ Hc) as SP. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3.
    assert (NS : n <= 65536).
    { unfold is_primary, needed, kMaxSize, kChunkHeader2Size in EP. apply Z.leb_le in EP. pose proof (round_up_ge8 (Z.max n 16)). lia. }
    split; [|nia]. intros z Hz. apply AGsp. rewrite kSpaceSize_val. nia.
  - destruct (QS eq_refl) as (ch & Hch & Eu & Esz). rewrite ES in Hch.
    destruct HS as (HS1 & _). rewrite ES, EG in HS1. destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    pose proof (round_up_ge8 n). unfold PG in *.
    split; [|lia]. intros z Hz. apply (AGsec ch); [exact Hch | lia].
Qed.

Lemma q_item_ok_z : ltac2:(tb__ "0|1|
S10S10S2fSfSfA2S0S14S11R3A1VGg;A3S0S2cS12A1M0S13R4A1Vsecs;A3S0S14S11R4A1S11R5A1A3S0S2cS18A1S15R5A1S15R6A1A3S0G0S13R6A1S13R7A1A3S40Vm;R8A2S41Vm;R9A2S4aVm;RaR8A3S4aVm';RaR9A3F_;F_;F_;F_;F_;F_;F_;F_;Fit;FA';FA;").
Proof.
  intros A A' it EG ES Eg Ec Es HP HS HQ. unfold q_item_ok in HQ |- *. cbn zeta in HQ |- *. rewrite Eg, Ec, Es.
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (rz_bound (snd it)) as RZ.
  destruct (chunk_zone A (fst it) (snd it) EG ES HP HS Q1 Q2 ltac:(intros E; rewrite <- EG; exact (Q9 E)) Q10) as [BEL UB].
  split; [exact Q1|]. split; [exact Q2|].
  split; [rewrite BEL by lia; exact Q3|].
  split; [eapply present_agree; [|exact Q4]; intros z Hz; apply BEL; lia|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia|exact Q5]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia|exact Q6]|].
  split; [eapply present_agree; [|exact Q7]; intros z Hz; apply BEL; lia|].
  split; [eapply alloc_magic_ok_z; [exact BEL | exact Q8]|].
  split; [exact Q9|]. split; [exact Q10|].
  eapply present_agree; [|exact Q11]. intros z Hz. unfold IMG_HI in Q1.
  apply (AGsh (fst it) (fst it + snd it + 7)); [lia | exact UB |].
  pose proof (div8_superadd (fst it) (snd it + 7) ltac:(lia) ltac:(lia)). unfold Sh in *. rewrite <- Z.add_assoc. lia.
Qed.

Lemma batch_in_space : ltac2:(tb__ "0|2|
S10S17SfS0S14S11R3A1VGg;A3S40Vm;R4A2S42Vm;R5R4A3S1S5S2aR5A1M0R4A2S7R4S6G0S63A2A2A2S1S5S19VGg;A1M1R5A2S7R5S6S6G1S53A2Z1000A2A2A2F_;F_;F_;F_;Fz;Fb;FA;").
Proof.
  intros A b z EG (_ & _ & _ & P4) (_ & _ & _ & _ & _ & _ & _ & (x & Ex & X0 & _ & XB)) Hz. rewrite EG in P4, Ex.
  destruct (P4 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in Ex. rewrite kSpaceSize_val. lia.
Qed.

Lemma batch_repr_z : ltac2:(tb__ "0|1|
S10S10S17S0S14S11R3A1VGg;A3S0S2cS12A1M0S13R4A1Vsecs;A3S0S14S11R4A1S11R5A1A3S0S2cS18A1S15R5A1S15R6A1A3S0G0S13R6A1S13R7A1A3S40Vm;R8A2S41Vm;R9A2S42Vm;RaR8A3S42Vm';RaR9A3F_;F_;F_;F_;F_;F_;F_;F_;Fb;FA';FA;").
Proof.
  intros A A' b EG ES Eg Ec Es HP HS HB. pose proof HB as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (BS : forall z, qb_addr b <= z < qb_addr b + kQuarantineBatchSize -> m' z = m z).
  { intros z Hz. apply AGsp. exact (batch_in_space A b z EG HP HB Hz). }
  unfold batch_repr. rewrite Eg, Ec. unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
  split; [exact B0|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact B1]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact B2]|].
  split; [exact B3|]. split; [exact B4|].
  split; [eapply present_agree; [|exact B5]; intros z Hz; apply BS; lia|].
  split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. assert (Li : (i < length (qb_items b))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact I1]|].
  exact (q_item_ok_z A A' it EG ES Eg Ec Es HP HS I2).
Qed.

Lemma qlinks_z : ltac2:(tb__ "0|0|
S10S2cS17A1S0S14S11R2A1VGg;A3S40Vm;R3A2S71S17S42Vm;R4A2R3A3S4cVm;R4A2S4cVm';R5A2F_;F_;F_;F_;Fl;FA;").
Proof.
  intros A l EG HP. induction l as [|b r IH]; intros HF H; [exact I|]. cbn in H |- *. destruct H as [H1 H2].
  apply Forall_cons_iff in HF as [Hb Hr].
  split; [|exact (IH Hr H2)].
  eapply (cell_ok_agree m m'); [|exact H1]. cbn [c_addr c_w]. intros k Hk. apply AGsp. apply (batch_in_space A b _ EG HP Hb). unfold kQuarantineBatchSize. lia.
Qed.

Lemma qhdr_repr_z : ltac2:(tb__ "0|0|
SfS2cS17A1SfS1S5R3R1A2S7R1S6R3Z20A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S4bVm;R3R2A3S4bVm';R4R3A3F_;F_;Fl;Fhdr;").
Proof.
  intros hdr l AG (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AG; lia|].
  eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | exact Q4].
Qed.

Lemma quarantine_repr_z : ltac2:(tb__ "0|2|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1M0S13R3A1Vsecs;A3S0S14S11R3A1S11R4A1A3S0S2cS18A1S15R4A1S15R5A1A3S0G0S13R5A1S13R6A1A3S0S2cS17A1M1S24R6A1S24R7A1A3S0G1S23R7A1S23R8A1A3S40Vm;R9A2S41Vm;RaA2S4dVm;RbA2S4dVm';RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ES Eg Ec Es E1 E2 HP HS (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). unfold quarantine_repr. rewrite Eg, E1, E2.
  pose proof (proj1 (Forall_app _ _ _) Q1) as [HB1 HB2].
  split; [apply Forall_forall; intros b Hb; apply (batch_repr_z A A' b EG ES Eg Ec Es HP HS); exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_z A _ EG HP HB1 Q2)|]. split; [exact (qlinks_z A _ EG HP HB2 Q3)|].
  split; [apply qhdr_repr_z; [intros z Hz; apply AGth; rewrite EG in Hz; lia | exact Q4]|].
  unfold QG in *.
  split; [apply qhdr_repr_z; [intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia | exact Q5]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact Q6]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact Q7]|].
  split; [exact Q8|]. exact Q9.
Qed.

Lemma live_block_repr_z : ltac2:(tb__ "0|0|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1S13R3A1Vsecs;A3S0S2cS2fSfSfA2A1S16R3A1S16R4A1A3S50R5A1S46R6A1S40Vm;R7A2S41Vm;R8A2S47Vm;R9A2S47Vm';R9A2F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ES El Hsep HI3 HP HS Hlive b n Hin. rewrite El in Hin.
  destruct (Hlive b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6). destruct (Hsep b n Hin) as (S1 & S2 & S3 & _).
  pose proof (rz_bound n) as RZ. destruct HI3 as (_ & LIV3 & _).
  assert (CZ : (forall z, b - rz n <= z < b -> m' z = m z) /\ b + n + 7 < 2 ^ 47).
  { apply (chunk_zone A b n EG ES HP HS ltac:(unfold IMG_HI in *; lia) ltac:(lia)).
    - intros EP. destruct HP as (_ & _ & _ & P4). rewrite EG in P4.
      pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (P4 _ Hc) as X. cbn zeta.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
      exact (LV b n Hin EP eq_refl).
    - intros EP. destruct (LIV3 b n Hin) as [X|X]; [rewrite EP in X; discriminate X | exact X]. }
  destruct CZ as [BEL UB].
  split; [rewrite BEL by lia; exact L1|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia | exact L2]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia | exact L3]|].
  split.
  - destruct L4 as [L4a L4b]. unfold IMG_HI in *. pose proof (div8_superadd b (n + 7) ltac:(lia) ltac:(lia)) as D8.
    pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono n (n + 7) 8 ltac:(lia) ltac:(lia)).
    split.
    + intros g Hg. rewrite (AGsh b (b + n + 7)); [exact (L4a g Hg) | lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; lia].
    + intros Hn. rewrite (AGsh b (b + n + 7)); [exact (L4b Hn) | lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; lia].
  - split; [eapply alloc_magic_ok_z; [exact BEL | exact L5]|].
    destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite BEL by lia; exact Ht | exact Hm4].
Qed.
End Zones.

Section Frame.
Let segs : list Segment := segsA.

Lemma view_agree : ltac2:(tb__ "0|4|
S37Q40M0A1S2dS37Q8A1A1M1F_;M2G2SfS1S5Z0R1A2S7R1SbZ2Z40A2A2A2S0G1R3S38G0R2A2M3A1R4G3A1A3F_;S0G1S3eVsegs;R3R2A3S3eVsegs;R4R2A3A3F_;Fz;Ff';Ff;").
Proof.
  intros f f' z H. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  - rewrite !view_in by lia. unfold rd_of. rewrite H by lia. reflexivity.
  - rewrite !view_out by lia. reflexivity.
  - rewrite !view_out by lia. reflexivity.
Qed.

Lemma zones_not_DFPw : ltac2:(tb__ "0|9|
S10SfS4fS11R2A1A1S46R3A1S34S12S0S2dS12A1S6eS12S13R6A1R2A3S31S12R1A2A3S61S20S11R7A1A1S1aR2A1S1dR2A1A3F_;Fch;Fi;S62S20S11R5A1M0A1S1cG0A1S56A3S11R6A1S14S2S1S1S5S52R6A2S7R6S51A2A2S3S70R6A1A1A2S2S1S5S19R1A1M1R6A2S7R6S6S6G1S53A2Z1000M2A2A2A2S2S1S5S1fR1A1M3R6A2S7R6S6G3G2A2A2A2S2S1S5S25R1A1M4R6A2S7R6S6G4G2A2A2A2S2S1S5S26R1A1M5R6A2S7R6S6G5G2A2A2A2S2S1S5S27R1A1M6R6A2S7R6S6G6S5dA2A2A2S2S1S5S1cR1A1M7R6A2S7R6S6G7S56A2A2A2S2S4S12S12S1S6dS12R1S13R8A1A3S1S5S1aR1A1M8R7A2S7R7S6G8S1dR1A1A2A2A2A2Lch;A2S2S1S5S59R6A2S7R6S58A2A2S5S20R1A1R6A2A2A2A2A2A2A2A2A2A2S3S66S1eR8A1R7A2A1F_;TG;F_;F_;F_;F_;Fz;FA;").
Proof.
  intros A z HG HI3 HSEC HPAB. cbn zeta. intros HZ HD. destruct HI3 as (_ & _ & _ & _ & DEP3 & _).
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI).
  pose proof (dyn_ok_big _ _ _ HPAB ltac:(unfold kPtrArrayReserve; lia)) as PB. destruct HPAB as [_ (_ & _ & P3 & _ & P5)].
  assert (BLK : forall b L, In (b, L) (dblocks (aa_depot A)) -> b <= z < b + L -> False).
  { intros b L Hb Hbz. destruct (DEP3 (b, L) Hb) as (DI' & ST & SC & SD & SF & SS & SP & SX). cbn [fst snd] in *.
    unfold sepZ in ST, SC, SD, SF, SS, SP. cbn [fst snd] in ST, SC, SD, SF, SS, SP.
    assert (HL : 0xf000 < L).
    { unfold dblocks in Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_map_iff in Hb as (x & E & _); injection E as <- <-; unfold NBSZ, FBSZ; lia. }
    pose proof (dyn_in_big _ _ _ DI' HL) as BI. destruct DI' as (_ & _ & W3 & _ & W5).
    destruct HZ as [[HZ ND]|[HZ|[HZ|[HZ|[HZ|[HZ|[HZ|[(ch & Hch & HZ)|[HZ|HZ]]]]]]]]];

      first [ clear - Hbz HZ BI; lia | clear - Hbz HZ ST; lia | clear - Hbz HZ SC; lia | clear - Hbz HZ SD; lia
            | clear - Hbz HZ SF; rewrite ?FS_total_val in *; lia | clear - Hbz HZ SS; lia | clear - Hbz HZ SP; lia | clear - Hbz HZ SP PB P3 P5; lia
            | clear - Hbz HZ W3 W5 BI; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia
            | pose proof (SX ch Hch) as X; unfold sepZ in X; cbn [fst snd] in X; clear - Hbz HZ X; lia
            | lia
            | pose proof (SX ch Hch) as X; unfold sepZ in X; cbn [fst snd] in X; lia
            | rewrite FS_total_val in *; lia
            | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia ]. }
  destruct HD as [(Hs & N1 & N2)|[(b & Hb & Hbz)|(b & Hb & Hbz)]].
  - pose proof (dstat_img z Hs) as ZI. unfold IMG_LO, IMG_HI in ZI.
    destruct HZ as [[HZ ND]|[HZ|[HZ|[HZ|[HZ|[HZ|[HZ|[(ch & Hch & HZ)|[HZ|HZ]]]]]]]]].
    + apply ND. exact (conj Hs (conj N1 N2)).
    + unfold IMG_HI in *. lia.
    + unfold IMG_LO, IMG_HI in TI. lia.
    + unfold IMG_LO, IMG_HI in CI. lia.
    + unfold IMG_LO, IMG_HI in DI. lia.
    + unfold IMG_HI in F1. lia.
    + unfold IMG_HI in PB. lia.
    + destruct (In_nth_error _ _ Hch) as (i & Hi). pose proof (dyn_in_big _ _ _ (HSEC i ch Hi)) as CB'.
      destruct (HSEC i ch Hi) as (_ & X2 & _ & X4 & _). unfold IMG_LO, IMG_HI in X4, CB'. lia.
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HZ. lia.
    + lia.
  - apply (BLK b NBSZ); [|exact Hbz]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists b. auto.
  - apply (BLK b FBSZ); [|exact Hbz]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists b. auto.
Qed.

Theorem AInvX_frameV : ltac2:(tb__ "0|0|
S10S6aS6aS2cS37Q40A1A1S6fS6bR5R4R2R1A4SfS3S66S1eR7A1R1A2A1S0S2dS37Q8A1A1S3eVsegs;S69R6A1R2A3S3eVsegs;S69R7A1R2A3A3F_;Fz;S6bR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvX in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view segsA (rm rho)) in *. set (m' := view segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & R5 & _ & R7 & R8 & R9).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG G) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).
  pose proof (fun z HZ => AV z (zones_not_DFPw A z HG HI3 HSEC HPAB HZ)) as ZN. cbn beta in ZN.

  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply ZN. do 7 right. left. exists ch. exact (conj Hch Hz). }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z) by (intros; apply ZN; tauto).
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  {
    replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. intros HD. pose proof (fs_footb_DFP A z HG HI3 (DFPw_DFP _ _ HD)) as X. unfold G in E. rewrite X in E. discriminate E. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].

  Ltac zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split; [eapply (live_block_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (primary_repr_z G mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (quarantine_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [exact I|].
  split; [eapply (ia_inv_z mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Theorem AInvX_frameD : ltac2:(tb__ "0|2|
S10S6aS6aS2cS37Q40M0A1M1A1S6fS6bR5R4R2R1A4G1S3S66S1eR7A1S39G0R1A2A2A1S0S2dS37Q8A1A1S69R6R2A2S69R7R2A2A3F_;Fa;S6bR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX Hrm. apply (AInvX_frameV A rho rho' tp md HX).
  intros z Hz. apply view_agree. intros Hr. apply Hrm. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64%N) with (2 ^ 64). rewrite Z.mod_small by exact Hr. exact Hz.
Qed.
End Frame.
End InvFoot.

(* [comment removed for export] *)
Module F0A_cls.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "sv"; "SPUlt"; "SVar"; "SAlu"; "SPAlign"; "FcsrFrm0"; "SPBranch"; "SPEq"; "SPNot"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "app"; "list"; "nat"; "nil"; "pair"; "prod"; "true"; "None"; "false"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "pow"; "sub"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "vN8"; "qvar"; "vN8g"; "FACTS"; "F_cas"; "OBJS0"; "P0_f"; "VFACT"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "LOW_SHADOW_BEG"; "IMG_HI"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "F_pc"; "blk_cls"; "cls_hyp"; "P0_fc"; "blk_geo"; "cls_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "AE_A"; "V_FREE_A1"; "ae_free"; "free_depth"; "mkA"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.Lists.List"; "hd"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition blk_cls (p n : Z) : Prop := ltac2:(tb__ "0|0|
S29S19S18Vp;Vn;A2S2fA2S19S2eS1cVp;Z10A2A2A2").

Definition cls_hyp (hi : bool) (p n : Z) : Prop := ltac2:(tb__ "0|0|
SeOLhi;Vhi;S19S2eS1cVp;Z10A2A2S19S18Vp;Vn;A2S2fA2Xex2").
Lemma cls_hyp_blk : ltac2:(tb__ "0|0|
SeS1eS1eS36R3R2R1A3S35R3R2A2F_;Fn;Fp;Fhi;").
Proof. intros [|] p n H; [right | left]; exact H. Qed.
Lemma blk_cls_cases : ltac2:(tb__ "0|0|
S1eS1eS35R2R1A2S2aSeSeS36R1R4R3A3Lhi;A2F_;Fn;Fp;").
Proof. intros p n [H|H]; [exists false | exists true]; exact H. Qed.

Definition blk_geo (p n8 : Z) : Prop := ltac2:(tb__ "0|0|
S29S28S19S18S2cZ1000A2Vp;A2S19S18Vp;Vn8;A2S2bA2A2S19S18S2dZ10A2Vp;A2A2").
Definition cls_geo (hi : bool) (p n8 : Z) : Prop := ltac2:(tb__ "0|0|
SeOLhi;Vhi;S19S18S2dZ10A2Vp;A2S28S19S18S2cZ1000A2Vp;A2S19S18Vp;Vn8;A2S2bA2A2Xex2").
Lemma cls_geo_blk : ltac2:(tb__ "0|0|
SeS1eS1eS39R3R2R1A3S38R3R2A2F_;Fn8;Fp;Fhi;").
Proof. intros [|] p n8 H; [right | left]; exact H. Qed.

Lemma lo_round8 : ltac2:(tb__ "0|2|
S1eS1eS1eS27S1eS1aR3Z8M0A2Z0M1A3S27S1eS1aR2G0A2G1A3S1dR3S18R4G0A2A2S19S18R6R5A2S2bA2S19S18R7R5A2S2bA2F_;F_;F_;F_;Fn8;Fn;Fp;").
Proof.
  intros p n n8 Hp Hn8 Hlt Hle. unfold LOW_SHADOW_BEG in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as E1. pose proof (Z.div_mod n8 8 ltac:(lia)) as E2. rewrite Hp in E1. rewrite Hn8 in E2. lia.
Qed.

Definition F_pL : list sprop := ltac2:(tb__ "0|a|
SdS0S2S1S18Z7fff7f800000Z1000M0A2A1S5PaA1A2SdS0S7PcM1Z4A2SdS0S2S1S18S2cG0A2A1S5G1A1M2A2SdS0S2S6S30G2S1fA3M3S1S2bA1A2SdS0S4S6S30G2S5PdA1M4A3S1Z7fffff800000A1M5A2SdS0S2S1Z1A1G4A2SdS0SbS9S32G2S1Z0A1A3A1SdS0S4G2S1S1bZ2M6Z2fA2A1M7A2SdS0S7P69Z3M8A2SdS0S2G4S1fA2SdS0S4S1fS6S30G4S1Z8A1M9A3A2SdS0S2G3G5A2SdS0S2G9S1fA2SdS0S4S1fG7A2SdS0SaS6S31S21S1G8A1A3S1fA2SdS0S4S21S1S1bG6Z2cA2A1A2S12S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_pc (hi : bool) : list sprop := if hi then F_p else F_pL.
Definition FACTSc (hi : bool) (W : list ulink) (st : ustop) (q : qvar) : list sprop := ltac2:(tb__ "0|0|
SfS0SfS0SfS0SfS0SfS0S42VW;Vst;A2S41S3fA1A3S47A3S34Vhi;A1A3S23A3S26Vq;A1A3").
Definition P0_fc (hi : bool) (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|1|
S40ScS3eS3cA1S45S44SdS14S11S3A2M0S13S11S3U4S1S49A1A4SdG0S13S11S3UbS5S3dA1A4S12G0A1A3A3A2S43S8S16S3A1S24VW;Vq;A2S33Vhi;VW;Vst;Vq;A4S48S17A9S12S14S3S3A2A1A2").
Lemma FACTSc_hi : ltac2:(tb__ "0|0|
S10S3aA1S3bS20S27S10S0A1S33S15R3R2R1A4S22R3R2R1A3A3Fq;Fst;FW;").
Proof. reflexivity. Qed.
Lemma P0_fc_hi : ltac2:(tb__ "0|0|
S10S3aA1S3bS20S27S46S37S15R3R2R1A4S25R3R2R1A3A3Fq;Fst;FW;").
Proof. reflexivity. Qed.

Lemma F_pc_hd : ltac2:(tb__ "0|0|
SeS27S0S4aS0S7P1Z0A2S34R1A1A3S2S1S18Z7fff7f800000Z1000A2A1S5PaA1A2A3Fhi;").
Proof. intros [|]; reflexivity. Qed.
End F0A_cls.

