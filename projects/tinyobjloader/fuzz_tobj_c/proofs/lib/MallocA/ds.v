(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
From Stdlib Require NArith PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk dl.

(* [comment removed for export] *)
Module F0A_cLCf1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "false"; "prod"; "pair"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "BIGX"; "F_typ"; "MSE"; "PSE"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cLCf1"; "C4_LCf1"; "ED_LCf1_1"; "ED_LCf1_2"; "ED_LCf1_3"; "EC_LCf1"; "C2_LCf1_1"; "C2_LCf1_2"; "C2_LCf1_3"; "C3_LCf1"; "P0_LCf1"; "CD_LCf1"; "RR_LCf1"; "T1_LCf1"; "TR_LCf1"; "sR_LCf1"; "Ems_LCf1"; "Eps_LCf1"; "PMID_LCf1"; "RD_LCf1_1"; "RD_LCf1_2"; "RD_LCf1_3"; "S1c_LCf1_1"; "S1c_LCf1_2"; "S1c_LCf1_3"; "TM_LCf1"; "TRs_LCf1"; "exits1_LCf1"; "run3_LCf1"; "RM_LCf1"; "TD_LCf1_1"; "TD_LCf1_2"; "TD_LCf1_3"; "TM0_LCf1"; "run1_LCf1"; "run2_LCf1_1"; "run2_LCf1_2"; "run2_LCf1_3"; "run4_LCf1"; "run5_LCf1"; "run5d_LCf1"; "Ebg_LCf1"; "EfD_LCf1_1"; "EfD_LCf1_2"; "EfD_LCf1_3"; "Erf_LCf1"; "Erq2_LCf1"; "Erq_LCf1"; "KEPT1_LCf1"; "T0_LCf1"; "T2_LCf1"; "TDr_LCf1_1"; "TDr_LCf1_2"; "TDr_LCf1_3"; "W_LCf1"; "st_LCf1"; "KEPT_LCf1"; "XR_LCf1"; "XS_LCf1"; "XW_LCf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf"; "TQ_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LCf1 : list ulink := Wcan 1.
Definition st_LCf1 : ustop := UStopLe.
Definition P0_LCf1 : axst := ltac2:(tb__ "0|0|
SadS9S76S77S2A4").

Definition run1_LCf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S25S5S13A1A3S4aA3").

Definition S1c_LCf1_1 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z1A3").
Definition C2_LCf1_1 : axst := C2_of S1c_LCf1_1.
Definition run2_LCf1_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S46A3").
Definition EfD_LCf1_1 : axst := leaf 0 run2_LCf1_1.
Definition ED_LCf1_1 : axst := ED_of EfD_LCf1_1.
Definition RD_LCf1_1 : list sobj := RD_of ED_LCf1_1 1.
Definition TD_LCf1_1 : axst := TD_of ED_LCf1_1 1.
Definition TDr_LCf1_1 : axst := TDr_of TD_LCf1_1.
Definition S1c_LCf1_2 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z2A3").
Definition C2_LCf1_2 : axst := C2_of S1c_LCf1_2.
Definition run2_LCf1_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S47A3").
Definition EfD_LCf1_2 : axst := leaf 0 run2_LCf1_2.
Definition ED_LCf1_2 : axst := ED_of EfD_LCf1_2.
Definition RD_LCf1_2 : list sobj := RD_of ED_LCf1_2 2.
Definition TD_LCf1_2 : axst := TD_of ED_LCf1_2 2.
Definition TDr_LCf1_2 : axst := TDr_of TD_LCf1_2.
Definition S1c_LCf1_3 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z3A3").
Definition C2_LCf1_3 : axst := C2_of S1c_LCf1_3.
Definition run2_LCf1_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S48A3").
Definition EfD_LCf1_3 : axst := leaf 0 run2_LCf1_3.
Definition ED_LCf1_3 : axst := ED_of EfD_LCf1_3.
Definition RD_LCf1_3 : list sobj := RD_of ED_LCf1_3 3.
Definition TD_LCf1_3 : axst := TD_of ED_LCf1_3 3.
Definition TDr_LCf1_3 : axst := TDr_of TD_LCf1_3.
Definition exits1_LCf1 : list axst := ltac2:(tb__ "0|0|
S4SeS56S4SeS57S4SeS58S5SeA1A3A3A3").

Definition CD_LCf1 : axst := CD_of TDr_LCf1_1.
Definition run3_LCf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S29S4S13S26S5S13A1A3A3S4bA3").
Definition Eps_LCf1 : axst := leaf 0 run3_LCf1.
Definition Ebg_LCf1 : axst := leaf 1 run3_LCf1.
Definition C3_LCf1 : axst := C3_of Eps_LCf1.
Definition run4_LCf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S28S5S13A1A3S49A3").
Definition Ems_LCf1 : axst := leaf 0 run4_LCf1.
Definition C4_LCf1 : axst := C4_of Ems_LCf1.
Definition RM_LCf1 : list sobj := RM_of C4_LCf1.
Definition TM0_LCf1 : axst := TM0_of C4_LCf1.
Definition TM_LCf1 : axst := TM_of C4_LCf1.

Definition run5_LCf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S97S5S13A1A3S59A3").
Definition Erf_LCf1 : axst := leaf 0 run5_LCf1.
Definition XR_LCf1 : list axform := XRC Erf_LCf1.
Definition EC_LCf1 : axst := EC_of Erf_LCf1.
Definition sR_LCf1 : wsub := sR_of (E3_of Erf_LCf1).
Definition RR_LCf1 : list sobj := RR_of EC_LCf1 sR_LCf1.
Definition KEPT_LCf1 : list sobj := KEPT_of EC_LCf1 RR_LCf1.

Definition T0_LCf1 : axst := ltac2:(tb__ "0|0|
SaeS45S4fS4cA3").
Definition XS_LCf1 : list axform := XS_of T0_LCf1.
Definition T1_LCf1 : axst := T1_of T0_LCf1.
Definition KEPT1_LCf1 : list sobj := KEPT1_of T1_LCf1.
Definition T2_LCf1 : axst := T2_of T1_LCf1.
Definition TR_LCf1 : axst := TR_of T1_LCf1.

Definition TRs_LCf1 : axst := TRs_of TR_LCf1.
Definition run5d_LCf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S3aS5S13A1A3S5aA3").
Definition Erq_LCf1 : axst := leaf 0 run5d_LCf1.
Definition XW_LCf1 : list axform := XW Erq_LCf1.
Definition Erq2_LCf1 : axst := Erq2_of Erq_LCf1.

Definition PMID_LCf1 : axst := ltac2:(tb__ "0|0|
Sa4S9S76S77S88S86S17S87S7cS2A1A4S7dS2A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LCf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS4aA1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_LCf1 : ltac2:(tb__ "0|0|
S0S3S8cS40S21S4S13S25S5S13A1A3S3fS4SeS4aS5SeA1A3S5bA6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LCf1 exits1_LCf1 run1_LCf1); [unfold run1_LCf1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LCf1 : ltac2:(tb__ "0|2|
S0S3S8dS40S21S4S13S25S5S13A1A3S3fS4S8aS8bS4aZ1S1cZ0M0A1M1A3S5S8aA1A3S88SeS8aSeS8bR1G0G1A3LE;S5bA4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LCf1 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf1) run1_LCf1); [unfold run1_LCf1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LCf1_1 : ltac2:(tb__ "0|4|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS56A1SfS46A1A2S8G3SbG1G2S4G0SbS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf1_1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS46A1M0A1S2A3S1S0S14S15G0A1S15SfS56A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf1_1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS46A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LCf1_1 : ltac2:(tb__ "0|0|
S0SeS11S56SfS46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_LCf1_1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S46A3S63A3"). Proof. unfold run2_LCf1_1; reflexivity. Qed.
Lemma L2_LCf1_1 : ltac2:(tb__ "0|0|
S1S0S3S24S63S4S13S23S5S13A1A3A2S2A3S0SeS39U0S63A2S6aA3A2"). Proof. Time (split; [vmr | unfold EfD_LCf1_1; reflexivity]). Qed.
Lemma AXD_LCf1_1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6aS2bA2S8SeS42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf1_1 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS42S82Z1M1A1S22S42G1A2A3S8G0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf1_1 : ltac2:(tb__ "0|1|
S0S3S91S42S82Z1M0A1S22S42G0A2S53S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf1_1 : ltac2:(tb__ "0|1|
S0SeS5eS8eS90S22S42Z1M0A2S82G0A1S83G0A1S42S53A5S1aSfS42A1A1A2A3").
Proof. unfold TD_LCf1_1, TD_of, RD_LCf1_1; reflexivity. Qed.
Lemma DCHK_LCf1_1 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z1M1S42S5eS22S42G1A2S53A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf1_1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S5eS2cA2S8SeS73A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf1_1 : ltac2:(tb__ "0|0|
S0S3S99S73S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_LCf1_2 : ltac2:(tb__ "0|4|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS57A1SfS47A1A2S8G3SbG1G2S4G0SbS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf1_2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS47A1M0A1S2A3S1S0S14S15G0A1S15SfS57A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf1_2 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS47A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LCf1_2 : ltac2:(tb__ "0|0|
S0SeS11S57SfS47A1A2S47A3"). Proof. vmr. Qed.
Lemma RUN2_LCf1_2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S47A3S64A3"). Proof. unfold run2_LCf1_2; reflexivity. Qed.
Lemma L2_LCf1_2 : ltac2:(tb__ "0|0|
S1S0S3S24S64S4S13S23S5S13A1A3A2S2A3S0SeS39U0S64A2S6bA3A2"). Proof. Time (split; [vmr | unfold EfD_LCf1_2; reflexivity]). Qed.
Lemma AXD_LCf1_2 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6bS2bA2S8SeS43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf1_2 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS43S82Z2M1A1S22S43G1A2A3S8G0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf1_2 : ltac2:(tb__ "0|1|
S0S3S91S43S82Z2M0A1S22S43G0A2S54S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf1_2 : ltac2:(tb__ "0|1|
S0SeS5fS8eS90S22S43Z2M0A2S82G0A1S83G0A1S43S54A5S1aSfS43A1A1A2A3").
Proof. unfold TD_LCf1_2, TD_of, RD_LCf1_2; reflexivity. Qed.
Lemma DCHK_LCf1_2 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z2M1S43S5fS22S43G1A2S54A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf1_2 : ltac2:(tb__ "0|0|
S0S7SeA1S81S5fS2cA2S8SeS74A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf1_2 : ltac2:(tb__ "0|0|
S0S3S99S74S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_LCf1_3 : ltac2:(tb__ "0|4|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS58A1SfS48A1A2S8G3SbG1G2S4G0SbS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf1_3 : ltac2:(tb__ "0|1|
S1S0S3S19SfS48A1M0A1S2A3S1S0S14S15G0A1S15SfS58A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf1_3 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS48A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LCf1_3 : ltac2:(tb__ "0|0|
S0SeS11S58SfS48A1A2S48A3"). Proof. vmr. Qed.
Lemma RUN2_LCf1_3 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S48A3S65A3"). Proof. unfold run2_LCf1_3; reflexivity. Qed.
Lemma L2_LCf1_3 : ltac2:(tb__ "0|0|
S1S0S3S24S65S4S13S23S5S13A1A3A2S2A3S0SeS39U0S65A2S6cA3A2"). Proof. Time (split; [vmr | unfold EfD_LCf1_3; reflexivity]). Qed.
Lemma AXD_LCf1_3 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6cS2bA2S8SeS44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf1_3 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS44S82Z3M1A1S22S44G1A2A3S8G0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf1_3 : ltac2:(tb__ "0|1|
S0S3S91S44S82Z3M0A1S22S44G0A2S55S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf1_3 : ltac2:(tb__ "0|1|
S0SeS60S8eS90S22S44Z3M0A2S82G0A1S83G0A1S44S55A5S1aSfS44A1A1A2A3").
Proof. unfold TD_LCf1_3, TD_of, RD_LCf1_3; reflexivity. Qed.
Lemma DCHK_LCf1_3 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z3M1S44S60S22S44G1A2S55A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf1_3 : ltac2:(tb__ "0|0|
S0S7SeA1S81S60S2cA2S8SeS75A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf1_3 : ltac2:(tb__ "0|0|
S0S3S99S75S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_LCf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S29S4S13S26S5S13A1A3A3S4bA3S5cA3"). Proof. unfold run3_LCf1; reflexivity. Qed.
Lemma L3_LCf1 : ltac2:(tb__ "0|0|
S1S0S3S24S5cS4S13S29S4S13S26S5S13A1A3A3A2S2A3S1S0SeS39U0S5cA2S51A3S0SeS39U1S5cA2S69A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LCf1 | unfold Ebg_LCf1]; reflexivity]). Qed.
Lemma NX3_LCf1 : ltac2:(tb__ "0|1|
S1S0S3S84S3fS15SfS4bA1M0A1A2S2A3S0S3S1bG0A1S9A3A2"). Proof. split; vmr. Qed.

Lemma BGF_LCf1 : ltac2:(tb__ "0|0|
S0S3S9bS18S20Sb3A1S1aSfS69A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_LCf1 : ltac2:(tb__ "0|3|
S0S7SaS6SaS16S16A2A1M0S6S18A1M1A2M2A1S89SfS51A1SfS49A1A2S8G2SbG0G1S34S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LCf1 : ltac2:(tb__ "0|0|
S0SeS11S51SfS49A1A2S49A3"). Proof. vmr. Qed.
Lemma NX3b_LCf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS49A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_LCf1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS49A1M0A1S2A3S1S0S14S15G0A1S15SfS51A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LCf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S28S5S13A1A3S49A3S66A3"). Proof. unfold run4_LCf1; reflexivity. Qed.
Lemma L4_LCf1 : ltac2:(tb__ "0|0|
S1S0S3S24S66S4S13S28S5S13A1A3A2S2A3S0SeS39U0S66A2S50A3A2"). Proof. Time (split; [vmr | unfold Ems_LCf1; reflexivity]). Qed.
Lemma D4_LCf1 : ltac2:(tb__ "0|3|
S0S7SaS6SaS16S16A2A1M0S6S18A1M1A2M2A1S89SfS50A1SfS41A1A2S8G2SbG0G1S35S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LCf1 : ltac2:(tb__ "0|0|
S0SeS11S50SfS41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LCf1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS41A1M0A1S2A3S1S0S14S15G0A1S15SfS50A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LCf1 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S8fS41S93S2eS41A1A3S8G0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LCf1 : ltac2:(tb__ "0|0|
S0S3S92S41S93S2eS41A1S5dS88S10SeS12S94A4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_LCf1 : ltac2:(tb__ "0|0|
S0SeS90S2eS41A1S93S31S41S5dA5S61A3"). Proof. unfold TM0_LCf1, TM0_of, RM_LCf1; reflexivity. Qed.
Lemma FBM_LCf1 : ltac2:(tb__ "0|3|
S1S0S3S9aS18S1dS15SfS41A1M0A1M1A1S1aG0A1M2A3S2A3S1S0S3S9aS18S1dS15SfS61A1A1A1G2A3S2A3S0S3S84S3fG1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LCf1 : ltac2:(tb__ "0|0|
S0SeS8eS61S1aSfS41A1A1A2S59A3"). Proof. vmr. Qed.

Lemma NX5_LCf1 : ltac2:(tb__ "0|1|
S1S0S3S84S3fS15SfS59A1M0A1A2S2A3S0S3S1bG0A1S9A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LCf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S97S5S13A1A3S59A3S67A3"). Proof. unfold run5_LCf1; reflexivity. Qed.
Lemma L5_LCf1 : ltac2:(tb__ "0|0|
S1S0S3S24S67S4S13S97S5S13A1A3A2S2A3S0SeS39U0S67A2S6dA3A2"). Proof. Time (split; [vmr | unfold Erf_LCf1; reflexivity]). Qed.
Lemma AXR_LCf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6dS79A2S8SeS45A2A3"). Proof. Time vmr. Qed.

Lemma HER_LCf1 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S8fS45S96S4fA3S8G0S4cA2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LCf1 : ltac2:(tb__ "0|0|
S0S3S91S45S96S4fS4cS4SeS98S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_LCf1 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS45A1A1ScS17S78S4cA3A3"). Proof. Time vmr. Qed.
Lemma HT0_LCf1 : ltac2:(tb__ "0|0|
S0SeS71S8eS90S4fS96S98S45S4cA5S1aSfS45A1A1A2A3"). Proof. unfold T0_LCf1, T0_of; reflexivity. Qed.
Lemma HXS_LCf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S71S7aA2S8SeS4dA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LCf1 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS4dA1A1ScS17S70S4S17S30S4S17S87S7fA1S4S17S87S80A1S5S17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LCf1 : ltac2:(tb__ "0|0|
S0SeS72S11S4dSafSfS4dA1S70A2A2A3"). Proof. unfold T2_LCf1, T2_of, KEPT1_LCf1; reflexivity. Qed.
Lemma HTR_LCf1 : ltac2:(tb__ "0|2|
S0SeS4eSa9S72S4S86SaaSacS15SfS4dA1A1M0S85G0A1M1A3S5S86A1A3S85G1A1A3A3"). Proof. unfold TR_LCf1, TR_of, T2_LCf1; reflexivity. Qed.
Lemma RCHK_LCf1 : ltac2:(tb__ "0|0|
S0S3SabU1S2S45S4dS4eS4fS4cSacA8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_LCf1 : ltac2:(tb__ "0|0|
S0SeS5aSa9S4eSb5S15SfS4eA1A1A3A3"). Proof. unfold TRs_LCf1, TRs_of; reflexivity. Qed.
Lemma CCHK_LCf1 : ltac2:(tb__ "0|0|
S0S3Sb6U1S3S37L_;S2S33S32X3x2S4eS5aA4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LCf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S3aS5S13A1A3S5aA3S68A3"). Proof. unfold run5d_LCf1; reflexivity. Qed.
Lemma L5d_LCf1 : ltac2:(tb__ "0|0|
S1S0S3S24S68S4S13S3aS5S13A1A3A2S2A3S0SeS39U0S68A2S6fA3A2"). Proof. Time (split; [vmr | unfold Erq_LCf1; reflexivity]). Qed.
Lemma AXW_LCf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6fS7bA2S8SeS6eA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LCf1 : ltac2:(tb__ "0|0|
S0S3S36S6eSb4A2S2A3"). Proof. Time vmr. Qed.

Lemma Wa_LCf1 : ltac2:(tb__ "0|0|
S0S3S19S9dS3cU1A1S3bA2A1S2A3"). Proof. vmr. Qed.
Lemma Da_LCf1 : ltac2:(tb__ "0|5|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS3eS3dS3cU1A1M4S3bA3A1S9dG4S3bA2A2S8G3SbG1G2S4G0SbS16S16S1fP18A1S1cSb2A1A4S5G0A1A3S5S18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa0S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa1S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa2S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_LCf1 : ltac2:(tb__ "0|0|
S0S3S9aS18S1dSb1A1S9eS9S3cU1A1S3bS7dS2A1A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_LCf1 : ltac2:(tb__ "0|4|
S0S7SeA1S81Sa3S9S3cU1M0A1M1S3bS7cS2A1M2S7dS2A1M3A5S9cG0SdS86G2A2A2A2S8SeS9fS9G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LCf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS52A1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_LCf1__runs : ltac2:(tb__ "0|0|
S6S7S6S10A1A1A1") := ltac2:(tb__ "0|0|
Sb0S40S21S4S13S25S5S13A1A3S4SeS52S5SeA1A3A4").
Lemma Cert1m_LCf1 : ltac2:(tb__ "0|0|
S0S3S8cS40S21S4S13S25S5S13A1A3S3fS4SeS52S5SeA1A3S5bA6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LCf1] exits1_LCf1 Cert1m_LCf1__runs); [unfold Cert1m_LCf1__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LCf1 : ltac2:(tb__ "0|2|
S0S3S8dS40S21S4S13S25S5S13A1A3S3fS4S8aS8bS52Z1S1cZ0M0A1M1A3S5S8aA1A3S88SeS8aSeS8bR1G0G1A3LE;S5bA4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LCf1 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf1) Cert1m_LCf1__runs); [unfold Cert1m_LCf1__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa5S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa6S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_LCf1 : ltac2:(tb__ "0|0|
S0S3S19Sa7S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_LCf1 : ltac2:(tb__ "0|4|
S0S7SeA1S81Sa8S9S3cU1M0A1M1S3bS7cS2A1M2S7dS2A1M3A5S9cG0SdS86G2A2A2A2S8SeSa4S9G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cLCf1.

(* [comment removed for export] *)
Module F0A_aLCf1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cLCf1"; "ED_LCf1_1"; "ED_LCf1_2"; "ED_LCf1_3"; "TD_LCf1_1"; "TD_LCf1_2"; "TD_LCf1_3"; "P0_LCf1"; "PMID_LCf1"; "TM_LCf1"; "exits1_LCf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aLCf1.ALCf1"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_asmC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cLCf1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALCf1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S34U1S1S16R6VKc;R5A6S45R1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S34U1S1S16R6VKc;R5A6S45R1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6S23SbS3aS23R2S46A3S27Vsegs;R12S29Vsegs;S34G1S1SfR11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_LCf1 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_LCf1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 1 UStopLe false keep ok A Kc rho rho1 Ebg_LCf1 Q BGF_LCf1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1 UStopLe false Eps_LCf1 C3_LCf1 Ems_LCf1 C4_LCf1 TM0_LCf1 run4_LCf1 RM_LCf1 D3_LCf1 W3_LCf1 EQ3_LCf1 NX3b_LCf1 RUN4_LCf1 L4_LCf1 D4_LCf1 W4_LCf1 EQ4_LCf1
             HeM_LCf1 HchkM_LCf1 HTM_LCf1 FBM_LCf1 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LCf1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_LCf1_1 C2_LCf1_1 EfD_LCf1_1 ED_LCf1_1 run2_LCf1_1 D2_LCf1_1 W2_LCf1_1 NX2_LCf1_1 EQ2_LCf1_1 RUN2_LCf1_1 L2_LCf1_1 AXD_LCf1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_LCf1_1 TDr_LCf1_1 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_1 ENTD_LCf1_1 RUN3_LCf1 L3_LCf1 NX3_LCf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LCf1_2 C2_LCf1_2 EfD_LCf1_2 ED_LCf1_2 run2_LCf1_2 D2_LCf1_2 W2_LCf1_2 NX2_LCf1_2 EQ2_LCf1_2 RUN2_LCf1_2 L2_LCf1_2 AXD_LCf1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_LCf1_2 TDr_LCf1_2 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_2 ENTD_LCf1_2 RUN3_LCf1 L3_LCf1 NX3_LCf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_LCf1_3 C2_LCf1_3 EfD_LCf1_3 ED_LCf1_3 run2_LCf1_3 D2_LCf1_3 W2_LCf1_3 NX2_LCf1_3 EQ2_LCf1_3 RUN2_LCf1_3 L2_LCf1_3 AXD_LCf1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_LCf1_3 TDr_LCf1_3 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_3 ENTD_LCf1_3 RUN3_LCf1 L3_LCf1 NX3_LCf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5S23SbS3aS23R2S46A3S26Vsegs;S29Vsegs;S34G1S1SfR10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_LCf1 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_LCf1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 1 UStopLe false keep A Kc rho rho1 Ebg_LCf1 Q BGF_LCf1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1 UStopLe false Eps_LCf1 C3_LCf1 Ems_LCf1 C4_LCf1 TM0_LCf1 run4_LCf1 RM_LCf1 D3_LCf1 W3_LCf1 EQ3_LCf1 NX3b_LCf1 RUN4_LCf1 L4_LCf1 D4_LCf1 W4_LCf1 EQ4_LCf1
             HeM_LCf1 HchkM_LCf1 HTM_LCf1 FBM_LCf1 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LCf1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_LCf1_1 C2_LCf1_1 EfD_LCf1_1 ED_LCf1_1 run2_LCf1_1 D2_LCf1_1 W2_LCf1_1 NX2_LCf1_1 EQ2_LCf1_1 RUN2_LCf1_1 L2_LCf1_1 AXD_LCf1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_LCf1_1 TDr_LCf1_1 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_1 ENTD_LCf1_1 RUN3_LCf1 L3_LCf1 NX3_LCf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LCf1_2 C2_LCf1_2 EfD_LCf1_2 ED_LCf1_2 run2_LCf1_2 D2_LCf1_2 W2_LCf1_2 NX2_LCf1_2 EQ2_LCf1_2 RUN2_LCf1_2 L2_LCf1_2 AXD_LCf1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_LCf1_2 TDr_LCf1_2 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_2 ENTD_LCf1_2 RUN3_LCf1 L3_LCf1 NX3_LCf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_LCf1_3 C2_LCf1_3 EfD_LCf1_3 ED_LCf1_3 run2_LCf1_3 D2_LCf1_3 W2_LCf1_3 NX2_LCf1_3 EQ2_LCf1_3 RUN2_LCf1_3 L2_LCf1_3 AXD_LCf1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_LCf1_3 TDr_LCf1_3 CD_LCf1 Eps_LCf1 Ebg_LCf1 run3_LCf1 AXDr_LCf1_3 ENTD_LCf1_3 RUN3_LCf1 L3_LCf1 NX3_LCf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1SfRfReRcA6S43R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true P0_LCf1 exits1_LCf1 Cert1_LCf1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1SfReRdRbA6S43R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true P0_LCf1 exits1_LCf1 NX0_LCf1 ECert1_LCf1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Theorem free_spine_m_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1SfRfReRcA6S44R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true PMID_LCf1 exits1_LCf1 Cert1m_LCf1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_m_LCf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1SfReRdRbA6S44R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true PMID_LCf1 exits1_LCf1 NX0m_LCf1 ECert1m_LCf1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1fS4dS54R2A2S1cS20S2cR2A2S22R2S2dA2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS56R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS55R2A1A1F_;Fa;").

Theorem hdf_LCf1_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3dS40R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_1 TD_LCf1_1 (sD_of ED_LCf1_1 1) RD_LCf1_1 HeD_LCf1_1 HchkD_LCf1_1 HTD_LCf1_1 DCHK_LCf1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf1_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3dS40R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_1 TD_LCf1_1 (sD_of ED_LCf1_1 1) RD_LCf1_1 HeD_LCf1_1 HchkD_LCf1_1 HTD_LCf1_1 DCHK_LCf1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.
Theorem hdf_LCf1_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3eS41R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_2 TD_LCf1_2 (sD_of ED_LCf1_2 2) RD_LCf1_2 HeD_LCf1_2 HchkD_LCf1_2 HTD_LCf1_2 DCHK_LCf1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf1_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3eS41R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_2 TD_LCf1_2 (sD_of ED_LCf1_2 2) RD_LCf1_2 HeD_LCf1_2 HchkD_LCf1_2 HTD_LCf1_2 DCHK_LCf1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.
Theorem hdf_LCf1_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3fS42R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_3 TD_LCf1_3 (sD_of ED_LCf1_3 3) RD_LCf1_3 HeD_LCf1_3 HchkD_LCf1_3 HTD_LCf1_3 DCHK_LCf1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf1_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3fS42R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf1_3 TD_LCf1_3 (sD_of ED_LCf1_3 3) RD_LCf1_3 HeD_LCf1_3 HchkD_LCf1_3 HTD_LCf1_3 DCHK_LCf1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.

Lemma tail_LCf1 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S2aSaRcS28RaA1A3S4bSaRdS28RbA1A3S50ReRcA2S2bSaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S3aS12S0S0A2S11S0S0ReRdA4S18R12A1A3S47RfReA2S1bS13S19R14A1SfA3S30SfR15A2S35R14S31R16R14R12R11R10RfA6A2S1bS0S49R10A1S39A3S4eS3cVCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2fSaS4aR16R15S14S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 1 true CST XGL HCST HXGL TM_LCf1 Erf_LCf1 EC_LCf1 run5_LCf1 XR_LCf1 NX5_LCf1 RUN5_LCf1 L5_LCf1 AXR_LCf1 T0_LCf1 T1_LCf1 T2_LCf1 TR_LCf1 sR_LCf1 RR_LCf1 KEPT_LCf1 KEPT1_LCf1 XS_LCf1 eFRc HER_LCf1 Hchk_LCf1 OBJS_LCf1 HT0_LCf1 HXS_LCf1 OBJS1_LCf1 HT2_LCf1 HTR_LCf1 RCHK_LCf1 TRs_LCf1 Erq_LCf1 Erq2_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.TQ_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.Edr_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.Xf_L1Bf run5d_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.run6_L1Bf XW_LCf1 HTRs_LCf1 CCHK_LCf1 RUN5d_LCf1 L5d_LCf1 AXW_LCf1 ENTQ_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.NX6_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.RUN6_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.L6_L1Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_qL1Bf.f0_drain_L1Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d7.F0A_xiL1Bf.f0_exit_L1Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LCf1 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S51RaA1S2bSaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S3aS12S0S0A2S11S0S0RcRbA4S18R10A1A3S47RdRcA2S1bS13S19R12A1SfA3S30SfR13A2S35R12S31R14R12R10RfReRdA6A2S1bS0S49ReA1S39A3S4fS3cVCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2fSaS4aR14R13S14S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 1 true CST XGL HCST HXGL TM_LCf1 Erf_LCf1 EC_LCf1 run5_LCf1 XR_LCf1 NX5_LCf1 RUN5_LCf1 L5_LCf1 AXR_LCf1 T0_LCf1 T1_LCf1 T2_LCf1 TR_LCf1 sR_LCf1 RR_LCf1 KEPT_LCf1 KEPT1_LCf1 XS_LCf1 eFRc HER_LCf1 Hchk_LCf1 OBJS_LCf1 HT0_LCf1 HXS_LCf1 OBJS1_LCf1 HT2_LCf1 HTR_LCf1 RCHK_LCf1 TRs_LCf1 Erq_LCf1 Erq2_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.TQ_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.Edr_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.Xf_L1Bf run5d_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.run6_L1Bf XW_LCf1 HTRs_LCf1 CCHK_LCf1 RUN5d_LCf1 L5d_LCf1 AXW_LCf1 ENTQ_LCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.NX6_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.RUN6_L1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.L6_L1Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_qL1Bf.ef0_drain_L1Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d7.F0A_xiL1Bf.ef0_exit_L1Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Cf_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S21R6R5A2S38A2S1bS13S19RbA1SfA3S30SfRcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 1) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate false 1 UStopLe (NVC true) (VFC true) Wa_LCf1 Da_LCf1 Wb_LCf1 Wc_LCf1 Wd_LCf1 Fb_LCf1 XI_LCf1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_LCf1 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_LCf1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LCf1 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_Cf_1 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S20S21R4R3A2S38A2S1bS13S19R9A1SfA3S30SfRaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 1) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate false 1 UStopLe (NVC true) (VFC true) Wa_LCf1 Da_LCf1 Wb_LCf1 Wc_LCf1 Wd_LCf1 Fb_LCf1 XI_LCf1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_LCf1 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_LCf1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_LCf1 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1cS1dS1cS20S2cR2A2S22R2S2dA2A2A1S1dS1cS20Z180e88R2A2S22R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_Cf_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S21R6R5A2S38A2S1bS13S19RbA1S16A3S30SfRcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 1) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 1 UStopLe (NVC true) (VFC true) Wbm_LCf1 Wcm_LCf1 Wdm_LCf1 Fb_LCf1 XIm_LCf1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_LCf1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_LCf1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LCf1 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_Cf_1 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S20S21R4R3A2S38A2S1bS13S19R9A1S16A3S30SfRaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 1) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false 1 UStopLe (NVC true) (VFC true) Wbm_LCf1 Wcm_LCf1 Wdm_LCf1 Fb_LCf1 XIm_LCf1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_LCf1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_LCf1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_LCf1 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALCf1.
End F0A_aLCf1.

(* [comment removed for export] *)
Module F0A_cCe1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "false"; "option"; "Some"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "BIGX"; "F_typ"; "MSE"; "PSE"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCe1"; "C4_Ce1"; "ED_Ce1_1"; "ED_Ce1_2"; "ED_Ce1_3"; "EC_Ce1"; "C2_Ce1_1"; "C2_Ce1_2"; "C2_Ce1_3"; "C3_Ce1"; "P0_Ce1"; "CD_Ce1"; "RR_Ce1"; "T1_Ce1"; "TR_Ce1"; "sR_Ce1"; "Ems_Ce1"; "Eps_Ce1"; "PMID_Ce1"; "RD_Ce1_1"; "RD_Ce1_2"; "RD_Ce1_3"; "S1c_Ce1_1"; "S1c_Ce1_2"; "S1c_Ce1_3"; "TM_Ce1"; "TRs_Ce1"; "exits1_Ce1"; "run3_Ce1"; "RM_Ce1"; "TD_Ce1_1"; "TD_Ce1_2"; "TD_Ce1_3"; "TM0_Ce1"; "run1_Ce1"; "run2_Ce1_1"; "run2_Ce1_2"; "run2_Ce1_3"; "run4_Ce1"; "run5_Ce1"; "run5d_Ce1"; "Ebg_Ce1"; "EfD_Ce1_1"; "EfD_Ce1_2"; "EfD_Ce1_3"; "Erf_Ce1"; "Erq2_Ce1"; "Erq_Ce1"; "KEPT1_Ce1"; "T0_Ce1"; "T2_Ce1"; "TDr_Ce1_1"; "TDr_Ce1_2"; "TDr_Ce1_3"; "W_Ce1"; "st_Ce1"; "KEPT_Ce1"; "XR_Ce1"; "XS_Ce1"; "XW_Ce1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg";
"sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "TQ_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_Ce1 : list ulink := Wcan 1.
Definition st_Ce1 : ustop := UStopLe.
Definition P0_Ce1 : axst := ltac2:(tb__ "0|0|
SadS8S76S77ScA4").

Definition run1_Ce1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S25SaS13A1A3S4aA3").

Definition S1c_Ce1_1 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aS3S4aA1A1Z1A3").
Definition C2_Ce1_1 : axst := C2_of S1c_Ce1_1.
Definition run2_Ce1_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S46A3").
Definition EfD_Ce1_1 : axst := leaf 0 run2_Ce1_1.
Definition ED_Ce1_1 : axst := ED_of EfD_Ce1_1.
Definition RD_Ce1_1 : list sobj := RD_of ED_Ce1_1 1.
Definition TD_Ce1_1 : axst := TD_of ED_Ce1_1 1.
Definition TDr_Ce1_1 : axst := TDr_of TD_Ce1_1.
Definition S1c_Ce1_2 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aS3S4aA1A1Z2A3").
Definition C2_Ce1_2 : axst := C2_of S1c_Ce1_2.
Definition run2_Ce1_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S47A3").
Definition EfD_Ce1_2 : axst := leaf 0 run2_Ce1_2.
Definition ED_Ce1_2 : axst := ED_of EfD_Ce1_2.
Definition RD_Ce1_2 : list sobj := RD_of ED_Ce1_2 2.
Definition TD_Ce1_2 : axst := TD_of ED_Ce1_2 2.
Definition TDr_Ce1_2 : axst := TDr_of TD_Ce1_2.
Definition S1c_Ce1_3 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aS3S4aA1A1Z3A3").
Definition C2_Ce1_3 : axst := C2_of S1c_Ce1_3.
Definition run2_Ce1_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S48A3").
Definition EfD_Ce1_3 : axst := leaf 0 run2_Ce1_3.
Definition ED_Ce1_3 : axst := ED_of EfD_Ce1_3.
Definition RD_Ce1_3 : list sobj := RD_of ED_Ce1_3 3.
Definition TD_Ce1_3 : axst := TD_of ED_Ce1_3 3.
Definition TDr_Ce1_3 : axst := TDr_of TD_Ce1_3.
Definition exits1_Ce1 : list axst := ltac2:(tb__ "0|0|
S9S2S56S9S2S57S9S2S58SaS2A1A3A3A3").

Definition CD_Ce1 : axst := CD_of TDr_Ce1_1.
Definition run3_Ce1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S29S9S13S26SaS13A1A3A3S4bA3").
Definition Eps_Ce1 : axst := leaf 0 run3_Ce1.
Definition Ebg_Ce1 : axst := leaf 1 run3_Ce1.
Definition C3_Ce1 : axst := C3_of Eps_Ce1.
Definition run4_Ce1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S28SaS13A1A3S49A3").
Definition Ems_Ce1 : axst := leaf 0 run4_Ce1.
Definition C4_Ce1 : axst := C4_of Ems_Ce1.
Definition RM_Ce1 : list sobj := RM_of C4_Ce1.
Definition TM0_Ce1 : axst := TM0_of C4_Ce1.
Definition TM_Ce1 : axst := TM_of C4_Ce1.

Definition run5_Ce1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S97SaS13A1A3S59A3").
Definition Erf_Ce1 : axst := leaf 0 run5_Ce1.
Definition XR_Ce1 : list axform := XRC Erf_Ce1.
Definition EC_Ce1 : axst := EC_of Erf_Ce1.
Definition sR_Ce1 : wsub := sR_of (E3_of Erf_Ce1).
Definition RR_Ce1 : list sobj := RR_of EC_Ce1 sR_Ce1.
Definition KEPT_Ce1 : list sobj := KEPT_of EC_Ce1 RR_Ce1.

Definition T0_Ce1 : axst := ltac2:(tb__ "0|0|
SaeS45S4fS4cA3").
Definition XS_Ce1 : list axform := XS_of T0_Ce1.
Definition T1_Ce1 : axst := T1_of T0_Ce1.
Definition KEPT1_Ce1 : list sobj := KEPT1_of T1_Ce1.
Definition T2_Ce1 : axst := T2_of T1_Ce1.
Definition TR_Ce1 : axst := TR_of T1_Ce1.

Definition TRs_Ce1 : axst := TRs_of TR_Ce1.
Definition run5d_Ce1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S3aSaS13A1A3S5aA3").
Definition Erq_Ce1 : axst := leaf 0 run5d_Ce1.
Definition XW_Ce1 : list axform := XW Erq_Ce1.
Definition Erq2_Ce1 : axst := Erq2_of Erq_Ce1.

Definition PMID_Ce1 : axst := ltac2:(tb__ "0|0|
Sa4S8S76S77S88S86S17S87S7cScA1A4S7dScA1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_Ce1 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S4aA1A1A2S8A3"). Proof. vmr. Qed.
Lemma Cert1_Ce1 : ltac2:(tb__ "0|0|
S0S7S8cS40S21S9S13S25SaS13A1A3S3fS9S2S4aSaS2A1A3S5bA6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_Ce1 exits1_Ce1 run1_Ce1); [unfold run1_Ce1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_Ce1 : ltac2:(tb__ "0|2|
S0S7S8dS40S21S9S13S25SaS13A1A3S3fS9S8aS8bS4aZ1S1cZ0M0A1M1A3SaS8aA1A3S88S2S8aS2S8bR1G0G1A3LE;S5bA4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_Ce1 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_Ce1) run1_Ce1); [unfold run1_Ce1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_Ce1_1 : ltac2:(tb__ "0|4|
S0SdSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S89S3S56A1S3S46A1A2SeG3S10G1G2S9G0S10S16S16S2dS2fA4SaG0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Ce1_1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S46A1M0A1S8A3S1S0S14S15G0A1S15S3S56A1A1A3S0S7S1bG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Ce1_1 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S46A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_Ce1_1 : ltac2:(tb__ "0|0|
S0S2S5S56S3S46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_Ce1_1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S46A3S63A3"). Proof. unfold run2_Ce1_1; reflexivity. Qed.
Lemma L2_Ce1_1 : ltac2:(tb__ "0|0|
S1S0S7S24S63S9S13S23SaS13A1A3A2S8A3S0S2S39U0S63A2S6aA3A2"). Proof. Time (split; [vmr | unfold EfD_Ce1_1; reflexivity]). Qed.
Lemma AXD_Ce1_1 : ltac2:(tb__ "0|0|
S0SdS2A1S81S6aS2bA2SeS2S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Ce1_1 : ltac2:(tb__ "0|2|
S0SdSbS17A1M0A1S8fS42S82Z1M1A1S22S42G1A2A3SeG0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Ce1_1 : ltac2:(tb__ "0|1|
S0S7S91S42S82Z1M0A1S22S42G0A2S53S9S2S83G0A1SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_Ce1_1 : ltac2:(tb__ "0|1|
S0S2S5eS8eS90S22S42Z1M0A2S82G0A1S83G0A1S42S53A5S1aS3S42A1A1A2A3").
Proof. unfold TD_Ce1_1, TD_of, RD_Ce1_1; reflexivity. Qed.
Lemma DCHK_Ce1_1 : ltac2:(tb__ "0|2|
S0S7S95U1M0S7eS7cScA1G0A2Z1M1S42S5eS22S42G1A2S53A7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_Ce1_1 : ltac2:(tb__ "0|0|
S0SdS2A1S81S5eS2cA2SeS2S73A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Ce1_1 : ltac2:(tb__ "0|0|
S0S7S99S73S4bA2S8A3"). Proof. Time vmr. Qed.
Lemma D2_Ce1_2 : ltac2:(tb__ "0|4|
S0SdSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S89S3S57A1S3S47A1A2SeG3S10G1G2S9G0S10S16S16S2dS2fA4SaG0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Ce1_2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S47A1M0A1S8A3S1S0S14S15G0A1S15S3S57A1A1A3S0S7S1bG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Ce1_2 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S47A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_Ce1_2 : ltac2:(tb__ "0|0|
S0S2S5S57S3S47A1A2S47A3"). Proof. vmr. Qed.
Lemma RUN2_Ce1_2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S47A3S64A3"). Proof. unfold run2_Ce1_2; reflexivity. Qed.
Lemma L2_Ce1_2 : ltac2:(tb__ "0|0|
S1S0S7S24S64S9S13S23SaS13A1A3A2S8A3S0S2S39U0S64A2S6bA3A2"). Proof. Time (split; [vmr | unfold EfD_Ce1_2; reflexivity]). Qed.
Lemma AXD_Ce1_2 : ltac2:(tb__ "0|0|
S0SdS2A1S81S6bS2bA2SeS2S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Ce1_2 : ltac2:(tb__ "0|2|
S0SdSbS17A1M0A1S8fS43S82Z2M1A1S22S43G1A2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Ce1_2 : ltac2:(tb__ "0|1|
S0S7S91S43S82Z2M0A1S22S43G0A2S54S9S2S83G0A1SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_Ce1_2 : ltac2:(tb__ "0|1|
S0S2S5fS8eS90S22S43Z2M0A2S82G0A1S83G0A1S43S54A5S1aS3S43A1A1A2A3").
Proof. unfold TD_Ce1_2, TD_of, RD_Ce1_2; reflexivity. Qed.
Lemma DCHK_Ce1_2 : ltac2:(tb__ "0|2|
S0S7S95U1M0S7eS7cScA1G0A2Z2M1S43S5fS22S43G1A2S54A7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_Ce1_2 : ltac2:(tb__ "0|0|
S0SdS2A1S81S5fS2cA2SeS2S74A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Ce1_2 : ltac2:(tb__ "0|0|
S0S7S99S74S4bA2S8A3"). Proof. Time vmr. Qed.
Lemma D2_Ce1_3 : ltac2:(tb__ "0|4|
S0SdSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S89S3S58A1S3S48A1A2SeG3S10G1G2S9G0S10S16S16S2dS2fA4SaG0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Ce1_3 : ltac2:(tb__ "0|1|
S1S0S7S19S3S48A1M0A1S8A3S1S0S14S15G0A1S15S3S58A1A1A3S0S7S1bG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Ce1_3 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S48A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_Ce1_3 : ltac2:(tb__ "0|0|
S0S2S5S58S3S48A1A2S48A3"). Proof. vmr. Qed.
Lemma RUN2_Ce1_3 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S48A3S65A3"). Proof. unfold run2_Ce1_3; reflexivity. Qed.
Lemma L2_Ce1_3 : ltac2:(tb__ "0|0|
S1S0S7S24S65S9S13S23SaS13A1A3A2S8A3S0S2S39U0S65A2S6cA3A2"). Proof. Time (split; [vmr | unfold EfD_Ce1_3; reflexivity]). Qed.
Lemma AXD_Ce1_3 : ltac2:(tb__ "0|0|
S0SdS2A1S81S6cS2bA2SeS2S44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Ce1_3 : ltac2:(tb__ "0|2|
S0SdSbS17A1M0A1S8fS44S82Z3M1A1S22S44G1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Ce1_3 : ltac2:(tb__ "0|1|
S0S7S91S44S82Z3M0A1S22S44G0A2S55S9S2S83G0A1SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_Ce1_3 : ltac2:(tb__ "0|1|
S0S2S60S8eS90S22S44Z3M0A2S82G0A1S83G0A1S44S55A5S1aS3S44A1A1A2A3").
Proof. unfold TD_Ce1_3, TD_of, RD_Ce1_3; reflexivity. Qed.
Lemma DCHK_Ce1_3 : ltac2:(tb__ "0|2|
S0S7S95U1M0S7eS7cScA1G0A2Z3M1S44S60S22S44G1A2S55A7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_Ce1_3 : ltac2:(tb__ "0|0|
S0SdS2A1S81S60S2cA2SeS2S75A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Ce1_3 : ltac2:(tb__ "0|0|
S0S7S99S75S4bA2S8A3"). Proof. Time vmr. Qed.
Lemma RUN3_Ce1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S29S9S13S26SaS13A1A3A3S4bA3S5cA3"). Proof. unfold run3_Ce1; reflexivity. Qed.
Lemma L3_Ce1 : ltac2:(tb__ "0|0|
S1S0S7S24S5cS9S13S29S9S13S26SaS13A1A3A3A2S8A3S1S0S2S39U0S5cA2S51A3S0S2S39U1S5cA2S69A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_Ce1 | unfold Ebg_Ce1]; reflexivity]). Qed.
Lemma NX3_Ce1 : ltac2:(tb__ "0|1|
S1S0S7S84S3fS15S3S4bA1M0A1A2S8A3S0S7S1bG0A1ScA3A2"). Proof. split; vmr. Qed.

Lemma BGF_Ce1 : ltac2:(tb__ "0|0|
S0S7S9bS18S20Sb3A1S1aS3S69A1A1A3S8A3"). Proof. vmr. Qed.
Lemma D3_Ce1 : ltac2:(tb__ "0|3|
S0SdSfSbSfS16S16A2A1M0SbS18A1M1A2M2A1S89S3S51A1S3S49A1A2SeG2S10G0G1S34SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_Ce1 : ltac2:(tb__ "0|0|
S0S2S5S51S3S49A1A2S49A3"). Proof. vmr. Qed.
Lemma NX3b_Ce1 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S49A1A1A2S8A3"). Proof. vmr. Qed.
Lemma W3_Ce1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S49A1M0A1S8A3S1S0S14S15G0A1S15S3S51A1A1A3S0S7S1bG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_Ce1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S28SaS13A1A3S49A3S66A3"). Proof. unfold run4_Ce1; reflexivity. Qed.
Lemma L4_Ce1 : ltac2:(tb__ "0|0|
S1S0S7S24S66S9S13S28SaS13A1A3A2S8A3S0S2S39U0S66A2S50A3A2"). Proof. Time (split; [vmr | unfold Ems_Ce1; reflexivity]). Qed.
Lemma D4_Ce1 : ltac2:(tb__ "0|3|
S0SdSfSbSfS16S16A2A1M0SbS18A1M1A2M2A1S89S3S50A1S3S41A1A2SeG2S10G0G1S35SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_Ce1 : ltac2:(tb__ "0|0|
S0S2S5S50S3S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_Ce1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S41A1M0A1S8A3S1S0S14S15G0A1S15S3S50A1A1A3S0S7S1bG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_Ce1 : ltac2:(tb__ "0|1|
S0SdSbS17A1M0A1S8fS41S93S2eS41A1A3SeG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_Ce1 : ltac2:(tb__ "0|0|
S0S7S92S41S93S2eS41A1S5dS88S4S2S6S94A4A5S8A3"). Proof. Time vmr. Qed.
Lemma HTM_Ce1 : ltac2:(tb__ "0|0|
S0S2S90S2eS41A1S93S31S41S5dA5S61A3"). Proof. unfold TM0_Ce1, TM0_of, RM_Ce1; reflexivity. Qed.
Lemma FBM_Ce1 : ltac2:(tb__ "0|3|
S1S0S7S9aS18S1dS15S3S41A1M0A1M1A1S1aG0A1M2A3S8A3S1S0S7S9aS18S1dS15S3S61A1A1A1G2A3S8A3S0S7S84S3fG1A2S8A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_Ce1 : ltac2:(tb__ "0|0|
S0S2S8eS61S1aS3S41A1A1A2S59A3"). Proof. vmr. Qed.

Lemma NX5_Ce1 : ltac2:(tb__ "0|1|
S1S0S7S84S3fS15S3S59A1M0A1A2S8A3S0S7S1bG0A1ScA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_Ce1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S97SaS13A1A3S59A3S67A3"). Proof. unfold run5_Ce1; reflexivity. Qed.
Lemma L5_Ce1 : ltac2:(tb__ "0|0|
S1S0S7S24S67S9S13S97SaS13A1A3A2S8A3S0S2S39U0S67A2S6dA3A2"). Proof. Time (split; [vmr | unfold Erf_Ce1; reflexivity]). Qed.
Lemma AXR_Ce1 : ltac2:(tb__ "0|0|
S0SdS2A1S81S6dS79A2SeS2S45A2A3"). Proof. Time vmr. Qed.

Lemma HER_Ce1 : ltac2:(tb__ "0|1|
S0SdSbS17A1M0A1S8fS45S96S4fA3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma Hchk_Ce1 : ltac2:(tb__ "0|0|
S0S7S91S45S96S4fS4cS9S2S98SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma OBJS_Ce1 : ltac2:(tb__ "0|0|
S0SbS17A1S1eS3S45A1A1S11S17S78S4cA3A3"). Proof. Time vmr. Qed.
Lemma HT0_Ce1 : ltac2:(tb__ "0|0|
S0S2S71S8eS90S4fS96S98S45S4cA5S1aS3S45A1A1A2A3"). Proof. unfold T0_Ce1, T0_of; reflexivity. Qed.
Lemma HXS_Ce1 : ltac2:(tb__ "0|0|
S0SdS2A1S81S71S7aA2SeS2S4dA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_Ce1 : ltac2:(tb__ "0|0|
S0SbS17A1S1eS3S4dA1A1S11S17S70S9S17S30S9S17S87S7fA1S9S17S87S80A1SaS17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_Ce1 : ltac2:(tb__ "0|0|
S0S2S72S5S4dSafS3S4dA1S70A2A2A3"). Proof. unfold T2_Ce1, T2_of, KEPT1_Ce1; reflexivity. Qed.
Lemma HTR_Ce1 : ltac2:(tb__ "0|2|
S0S2S4eSa9S72S9S86SaaSacS15S3S4dA1A1M0S85G0A1M1A3SaS86A1A3S85G1A1A3A3"). Proof. unfold TR_Ce1, TR_of, T2_Ce1; reflexivity. Qed.
Lemma RCHK_Ce1 : ltac2:(tb__ "0|0|
S0S7SabU1ScS45S4dS4eS4fS4cSacA8S8A3"). Proof. Time vmr. Qed.

Lemma HTRs_Ce1 : ltac2:(tb__ "0|0|
S0S2S5aSa9S4eSb5S15S3S4eA1A1A3A3"). Proof. unfold TRs_Ce1, TRs_of; reflexivity. Qed.
Lemma CCHK_Ce1 : ltac2:(tb__ "0|0|
S0S7Sb6U1S7S37L_;ScS33S32X7x2S4eS5aA4S8A3"). Proof. Time vmr. Qed.
Lemma RUN5d_Ce1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S3aSaS13A1A3S5aA3S68A3"). Proof. unfold run5d_Ce1; reflexivity. Qed.
Lemma L5d_Ce1 : ltac2:(tb__ "0|0|
S1S0S7S24S68S9S13S3aSaS13A1A3A2S8A3S0S2S39U0S68A2S6fA3A2"). Proof. Time (split; [vmr | unfold Erq_Ce1; reflexivity]). Qed.
Lemma AXW_Ce1 : ltac2:(tb__ "0|0|
S0SdS2A1S81S6fS7bA2SeS2S6eA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_Ce1 : ltac2:(tb__ "0|0|
S0S7S36S6eSb4A2S8A3"). Proof. Time vmr. Qed.

Lemma Wa_Ce1 : ltac2:(tb__ "0|0|
S0S7S19S9dS3cU1A1S3bA2A1S8A3"). Proof. vmr. Qed.
Lemma Da_Ce1 : ltac2:(tb__ "0|5|
S0SdSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S89S3S3eS3dS3cU1A1M4S3bA3A1S9dG4S3bA2A2SeG3S10G1G2S9G0S10S16S16S1fP18A1S1cSb2A1A4SaG0A1A3SaS18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa0S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wc_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa1S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wd_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa2S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Fb_Ce1 : ltac2:(tb__ "0|0|
S0S7S9aS18S1dSb1A1S9eS8S3cU1A1S3bS7dScA1A4A3S8A3"). Proof. vmr. Qed.
Lemma XI_Ce1 : ltac2:(tb__ "0|4|
S0SdS2A1S81Sa3S8S3cU1M0A1M1S3bS7cScA1M2S7dScA1M3A5S9cG0S12S86G2A2A2A2SeS2S9fS8G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_Ce1 : ltac2:(tb__ "0|0|
S0S7S84S3fS15S3S52A1A1A2S8A3"). Proof. vmr. Qed.
Definition Cert1m_Ce1__runs : ltac2:(tb__ "0|0|
SbSdSbS4A1A1A1") := ltac2:(tb__ "0|0|
Sb0S40S21S9S13S25SaS13A1A3S9S2S52SaS2A1A3A4").
Lemma Cert1m_Ce1 : ltac2:(tb__ "0|0|
S0S7S8cS40S21S9S13S25SaS13A1A3S3fS9S2S52SaS2A1A3S5bA6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_Ce1] exits1_Ce1 Cert1m_Ce1__runs); [unfold Cert1m_Ce1__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_Ce1 : ltac2:(tb__ "0|2|
S0S7S8dS40S21S9S13S25SaS13A1A3S3fS9S8aS8bS52Z1S1cZ0M0A1M1A3SaS8aA1A3S88S2S8aS2S8bR1G0G1A3LE;S5bA4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_Ce1 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_Ce1) Cert1m_Ce1__runs); [unfold Cert1m_Ce1__runs; reflexivity | vmr]. Qed.
Lemma Wbm_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa5S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wcm_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa6S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wdm_Ce1 : ltac2:(tb__ "0|0|
S0S7S19Sa7S3cU1A1S3bS7cScA1A3A1S8A3"). Proof. vmr. Qed.
Lemma XIm_Ce1 : ltac2:(tb__ "0|4|
S0SdS2A1S81Sa8S8S3cU1M0A1M1S3bS7cScA1M2S7dScA1M3A5S9cG0S12S86G2A2A2A2SeS2Sa4S8G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cCe1.

(* [comment removed for export] *)
Module F0A_aCe1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "pair"; "prod"; "true"; "bool"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCe1"; "ED_Ce1_1"; "ED_Ce1_2"; "ED_Ce1_3"; "TD_Ce1_1"; "TD_Ce1_2"; "TD_Ce1_3"; "P0_Ce1"; "PMID_Ce1"; "TM_Ce1"; "exits1_Ce1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aCe1.ACe1"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_asmC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCe1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require de.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACe1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S34U1S1S10R6VKc;R5A6S45R1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S34U1S1S10R6VKc;R5A6S45R1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6S23SbS3aS23R2S46A3S27Vsegs;R12S29Vsegs;S34G1S1S13R11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_Ce1 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_Ce1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 1 UStopLe false keep ok A Kc rho rho1 Ebg_Ce1 Q BGF_Ce1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1 UStopLe false Eps_Ce1 C3_Ce1 Ems_Ce1 C4_Ce1 TM0_Ce1 run4_Ce1 RM_Ce1 D3_Ce1 W3_Ce1 EQ3_Ce1 NX3b_Ce1 RUN4_Ce1 L4_Ce1 D4_Ce1 W4_Ce1 EQ4_Ce1
             HeM_Ce1 HchkM_Ce1 HTM_Ce1 FBM_Ce1 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_Ce1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Ce1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_Ce1_1 C2_Ce1_1 EfD_Ce1_1 ED_Ce1_1 run2_Ce1_1 D2_Ce1_1 W2_Ce1_1 NX2_Ce1_1 EQ2_Ce1_1 RUN2_Ce1_1 L2_Ce1_1 AXD_Ce1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Ce1_1 TDr_Ce1_1 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_1 ENTD_Ce1_1 RUN3_Ce1 L3_Ce1 NX3_Ce1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_Ce1_2 C2_Ce1_2 EfD_Ce1_2 ED_Ce1_2 run2_Ce1_2 D2_Ce1_2 W2_Ce1_2 NX2_Ce1_2 EQ2_Ce1_2 RUN2_Ce1_2 L2_Ce1_2 AXD_Ce1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Ce1_2 TDr_Ce1_2 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_2 ENTD_Ce1_2 RUN3_Ce1 L3_Ce1 NX3_Ce1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_Ce1_3 C2_Ce1_3 EfD_Ce1_3 ED_Ce1_3 run2_Ce1_3 D2_Ce1_3 W2_Ce1_3 NX2_Ce1_3 EQ2_Ce1_3 RUN2_Ce1_3 L2_Ce1_3 AXD_Ce1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Ce1_3 TDr_Ce1_3 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_3 ENTD_Ce1_3 RUN3_Ce1 L3_Ce1 NX3_Ce1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5S23SbS3aS23R2S46A3S26Vsegs;S29Vsegs;S34G1S1S13R10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_Ce1 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_Ce1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 1 UStopLe false keep A Kc rho rho1 Ebg_Ce1 Q BGF_Ce1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1 UStopLe false Eps_Ce1 C3_Ce1 Ems_Ce1 C4_Ce1 TM0_Ce1 run4_Ce1 RM_Ce1 D3_Ce1 W3_Ce1 EQ3_Ce1 NX3b_Ce1 RUN4_Ce1 L4_Ce1 D4_Ce1 W4_Ce1 EQ4_Ce1
             HeM_Ce1 HchkM_Ce1 HTM_Ce1 FBM_Ce1 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_Ce1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Ce1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_Ce1_1 C2_Ce1_1 EfD_Ce1_1 ED_Ce1_1 run2_Ce1_1 D2_Ce1_1 W2_Ce1_1 NX2_Ce1_1 EQ2_Ce1_1 RUN2_Ce1_1 L2_Ce1_1 AXD_Ce1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Ce1_1 TDr_Ce1_1 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_1 ENTD_Ce1_1 RUN3_Ce1 L3_Ce1 NX3_Ce1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_Ce1_2 C2_Ce1_2 EfD_Ce1_2 ED_Ce1_2 run2_Ce1_2 D2_Ce1_2 W2_Ce1_2 NX2_Ce1_2 EQ2_Ce1_2 RUN2_Ce1_2 L2_Ce1_2 AXD_Ce1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Ce1_2 TDr_Ce1_2 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_2 ENTD_Ce1_2 RUN3_Ce1 L3_Ce1 NX3_Ce1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_Ce1_3 C2_Ce1_3 EfD_Ce1_3 ED_Ce1_3 run2_Ce1_3 D2_Ce1_3 W2_Ce1_3 NX2_Ce1_3 EQ2_Ce1_3 RUN2_Ce1_3 L2_Ce1_3 AXD_Ce1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Ce1_3 TDr_Ce1_3 CD_Ce1 Eps_Ce1 Ebg_Ce1 run3_Ce1 AXDr_Ce1_3 ENTD_Ce1_3 RUN3_Ce1 L3_Ce1 NX3_Ce1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1S13RfReRcA6S43R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true P0_Ce1 exits1_Ce1 Cert1_Ce1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Ce1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1S13ReRdRbA6S43R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true P0_Ce1 exits1_Ce1 NX0_Ce1 ECert1_Ce1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Ce1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Theorem free_spine_m_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1S13RfReRcA6S44R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true PMID_Ce1 exits1_Ce1 Cert1m_Ce1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Ce1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_m_Ce1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1S13ReRdRbA6S44R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true PMID_Ce1 exits1_Ce1 NX0m_Ce1 ECert1m_Ce1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Ce1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1fS4dS54R2A2S1cS20S2cR2A2S22R2S2dA2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS56R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS55R2A1A1F_;Fa;").

Theorem hdf_Ce1_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3dS40R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC false) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_1 TD_Ce1_1 (sD_of ED_Ce1_1 1) RD_Ce1_1 HeD_Ce1_1 HchkD_Ce1_1 HTD_Ce1_1 DCHK_Ce1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Ce1_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3dS40R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC false) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_1 TD_Ce1_1 (sD_of ED_Ce1_1 1) RD_Ce1_1 HeD_Ce1_1 HchkD_Ce1_1 HTD_Ce1_1 DCHK_Ce1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) Q).
Qed.
Theorem hdf_Ce1_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3eS41R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC false) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_2 TD_Ce1_2 (sD_of ED_Ce1_2 2) RD_Ce1_2 HeD_Ce1_2 HchkD_Ce1_2 HTD_Ce1_2 DCHK_Ce1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Ce1_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3eS41R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC false) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_2 TD_Ce1_2 (sD_of ED_Ce1_2 2) RD_Ce1_2 HeD_Ce1_2 HchkD_Ce1_2 HTD_Ce1_2 DCHK_Ce1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) Q).
Qed.
Theorem hdf_Ce1_3 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3fS42R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC false) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_3 TD_Ce1_3 (sD_of ED_Ce1_3 3) RD_Ce1_3 HeD_Ce1_3 HchkD_Ce1_3 HTD_Ce1_3 DCHK_Ce1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Ce1_3 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30S10RfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3fS42R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC false) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce1_3 TD_Ce1_3 (sD_of ED_Ce1_3 3) RD_Ce1_3 HeD_Ce1_3 HchkD_Ce1_3 HTD_Ce1_3 DCHK_Ce1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 1) Q).
Qed.

Lemma tail_Ce1 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbSfSeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S2aSaRcS28RaA1A3S4bSaRdS28RbA1A3S50ReRcA2S2bSaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S3aS12S0S0A2S11S0S0ReRdA4S18R12A1A3S47RfReA2S1bS14S19R14A1S13A3S30S10R15A2S35R14S31R16R14R12R11R10RfA6A2S1bS0S49R10A1S39A3S4eS3cVCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2fSaS4aR16R15S15S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R18Z18A2R17A5A4S16G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 1 false CST XGL HCST HXGL TM_Ce1 Erf_Ce1 EC_Ce1 run5_Ce1 XR_Ce1 NX5_Ce1 RUN5_Ce1 L5_Ce1 AXR_Ce1 T0_Ce1 T1_Ce1 T2_Ce1 TR_Ce1 sR_Ce1 RR_Ce1 KEPT_Ce1 KEPT1_Ce1 XS_Ce1 eFRc HER_Ce1 Hchk_Ce1 OBJS_Ce1 HT0_Ce1 HXS_Ce1 OBJS1_Ce1 HT2_Ce1 HTR_Ce1 RCHK_Ce1 TRs_Ce1 Erq_Ce1 Erq2_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.TQ_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.Edr_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.Xf_1Be run5d_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.run6_1Be XW_Ce1 HTRs_Ce1 CCHK_Ce1 RUN5d_Ce1 L5d_Ce1 AXW_Ce1 ENTQ_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.NX6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.RUN6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.L6_1Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1Be.f0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_xi1Be.f0_exit_1Be CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Ce1 : ltac2:(tb__ "0|3|
S17S2SbSfSeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S51RaA1S2bSaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S3aS12S0S0A2S11S0S0RcRbA4S18R10A1A3S47RdRcA2S1bS14S19R12A1S13A3S30S10R13A2S35R12S31R14R12R10RfReRdA6A2S1bS0S49ReA1S39A3S4fS3cVCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2fSaS4aR14R13S15S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R16Z18A2R15A5A4S16G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 1 false CST XGL HCST HXGL TM_Ce1 Erf_Ce1 EC_Ce1 run5_Ce1 XR_Ce1 NX5_Ce1 RUN5_Ce1 L5_Ce1 AXR_Ce1 T0_Ce1 T1_Ce1 T2_Ce1 TR_Ce1 sR_Ce1 RR_Ce1 KEPT_Ce1 KEPT1_Ce1 XS_Ce1 eFRc HER_Ce1 Hchk_Ce1 OBJS_Ce1 HT0_Ce1 HXS_Ce1 OBJS1_Ce1 HT2_Ce1 HTR_Ce1 RCHK_Ce1 TRs_Ce1 Erq_Ce1 Erq2_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.TQ_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.Edr_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.Xf_1Be run5d_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.run6_1Be XW_Ce1 HTRs_Ce1 CCHK_Ce1 RUN5d_Ce1 L5d_Ce1 AXW_Ce1 ENTQ_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.NX6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.RUN6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.L6_1Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.de.F0A_q1Be.ef0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d2.F0A_xi1Be.ef0_exit_1Be CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Ce_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S15S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S38S21R6Z10A2A2S1bS14S19RbA1S13A3S30S10RcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 1) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C true _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate true 1 UStopLe (NVC false) (VFC false) Wa_Ce1 Da_Ce1 Wb_Ce1 Wc_Ce1 Wd_Ce1 Fb_Ce1 XI_Ce1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_Ce1 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_Ce1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Ce1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Ce1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_Ce1 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_Ce_1 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S15S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S20S38S21R4Z10A2A2S1bS14S19R9A1S13A3S30S10RaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 1) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C true _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate true 1 UStopLe (NVC false) (VFC false) Wa_Ce1 Da_Ce1 Wb_Ce1 Wc_Ce1 Wd_Ce1 Fb_Ce1 XI_Ce1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_Ce1 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_Ce1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Ce1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Ce1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_Ce1 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1cS1dS1cS20S2cR2A2S22R2S2dA2A2A1S1dS1cS20Z180e88R2A2S22R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_Ce_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S15S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S38S21R6Z10A2A2S1bS14S19RbA1S10A3S30S10RcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts true (Wcan 1) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 1 UStopLe (NVC false) (VFC false) Wbm_Ce1 Wcm_Ce1 Wdm_Ce1 Fb_Ce1 XIm_Ce1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_Ce1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_Ce1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Ce1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Ce1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_Ce1 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_Ce_1 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S15S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S20S38S21R4Z10A2A2S1bS14S19R9A1S10A3S30S10RaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 1 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts true (Wcan 1) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true 1 UStopLe (NVC false) (VFC false) Wbm_Ce1 Wcm_Ce1 Wdm_Ce1 Fb_Ce1 XIm_Ce1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_Ce1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_Ce1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Ce1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Ce1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_Ce1 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ACe1.
End F0A_aCe1.

(* [comment removed for export] *)
Module F0A_cCf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "false"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "MSE"; "PSE"; "sM_of"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCf2"; "C4_Cf2"; "ED_Cf2_1"; "ED_Cf2_2"; "ED_Cf2_3"; "ED_Cf2_4"; "EC_Cf2"; "P0_Cf2"; "C2_Cf2_1"; "C2_Cf2_2"; "C2_Cf2_3"; "C2_Cf2_4"; "C3_Cf2"; "CD_Cf2"; "RR_Cf2"; "T1_Cf2"; "TR_Cf2"; "sR_Cf2"; "Ems_Cf2"; "Eps_Cf2"; "PMID_Cf2"; "RD_Cf2_1"; "RD_Cf2_2"; "RD_Cf2_3"; "RD_Cf2_4"; "S1c_Cf2_1"; "S1c_Cf2_2"; "S1c_Cf2_3"; "S1c_Cf2_4"; "TM_Cf2"; "TRs_Cf2"; "exits1_Cf2"; "run1_Cf2"; "run3_Cf2"; "RM_Cf2"; "TD_Cf2_1"; "TD_Cf2_2"; "TD_Cf2_3"; "TD_Cf2_4"; "TM0_Cf2"; "run2_Cf2_1"; "run2_Cf2_2"; "run2_Cf2_3"; "run2_Cf2_4"; "run4_Cf2"; "run5_Cf2"; "run5d_Cf2"; "Ebg_Cf2"; "EfD_Cf2_1"; "EfD_Cf2_2"; "EfD_Cf2_3"; "EfD_Cf2_4"; "Erf_Cf2"; "Erq2_Cf2"; "Erq_Cf2"; "KEPT1_Cf2"; "T0_Cf2"; "T2_Cf2"; "TDr_Cf2_1"; "TDr_Cf2_2"; "TDr_Cf2_3"; "TDr_Cf2_4"; "W_Cf2"; "st_Cf2"; "KEPT_Cf2"; "XR_Cf2"; "XS_Cf2"; "XW_Cf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g";
"se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "TQ_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_Cf2 : list ulink := Wcan 2.
Definition st_Cf2 : ustop := UStopLe.
Definition P0_Cf2 : axst := ltac2:(tb__ "0|0|
Sb5S2S84S85S2A4").

Definition run1_Cf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S25S5S13A1A3S4dA3").

Definition S1c_Cf2_1 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aSfS4dA1A1Z1A3").
Definition C2_Cf2_1 : axst := C2_of S1c_Cf2_1.
Definition run2_Cf2_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S4eA3").
Definition EfD_Cf2_1 : axst := leaf 0 run2_Cf2_1.
Definition ED_Cf2_1 : axst := ED_of EfD_Cf2_1.
Definition RD_Cf2_1 : list sobj := RD_of ED_Cf2_1 1.
Definition TD_Cf2_1 : axst := TD_of ED_Cf2_1 1.
Definition TDr_Cf2_1 : axst := TDr_of TD_Cf2_1.
Definition S1c_Cf2_2 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aSfS4dA1A1Z2A3").
Definition C2_Cf2_2 : axst := C2_of S1c_Cf2_2.
Definition run2_Cf2_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S4fA3").
Definition EfD_Cf2_2 : axst := leaf 0 run2_Cf2_2.
Definition ED_Cf2_2 : axst := ED_of EfD_Cf2_2.
Definition RD_Cf2_2 : list sobj := RD_of ED_Cf2_2 2.
Definition TD_Cf2_2 : axst := TD_of ED_Cf2_2 2.
Definition TDr_Cf2_2 : axst := TDr_of TD_Cf2_2.
Definition S1c_Cf2_3 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aSfS4dA1A1Z3A3").
Definition C2_Cf2_3 : axst := C2_of S1c_Cf2_3.
Definition run2_Cf2_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S50A3").
Definition EfD_Cf2_3 : axst := leaf 0 run2_Cf2_3.
Definition ED_Cf2_3 : axst := ED_of EfD_Cf2_3.
Definition RD_Cf2_3 : list sobj := RD_of ED_Cf2_3 3.
Definition TD_Cf2_3 : axst := TD_of ED_Cf2_3 3.
Definition TDr_Cf2_3 : axst := TDr_of TD_Cf2_3.
Definition S1c_Cf2_4 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aSfS4dA1A1Z4A3").
Definition C2_Cf2_4 : axst := C2_of S1c_Cf2_4.
Definition run2_Cf2_4 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S51A3").
Definition EfD_Cf2_4 : axst := leaf 0 run2_Cf2_4.
Definition ED_Cf2_4 : axst := ED_of EfD_Cf2_4.
Definition RD_Cf2_4 : list sobj := RD_of ED_Cf2_4 4.
Definition TD_Cf2_4 : axst := TD_of ED_Cf2_4 4.
Definition TDr_Cf2_4 : axst := TDr_of TD_Cf2_4.
Definition exits1_Cf2 : list axst := ltac2:(tb__ "0|0|
S4SeS5fS4SeS60S4SeS61S4SeS62S5SeA1A3A3A3A3").

Definition CD_Cf2 : axst := CD_of TDr_Cf2_1.
Definition run3_Cf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S2eS4S13S2cS5S13A1A3A3S53A3").
Definition Eps_Cf2 : axst := leaf 0 run3_Cf2.
Definition Ebg_Cf2 : axst := leaf 1 run3_Cf2.
Definition C3_Cf2 : axst := C3_of Eps_Cf2.
Definition run4_Cf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S2dS5S13A1A3S52A3").
Definition Ems_Cf2 : axst := leaf 0 run4_Cf2.
Definition C4_Cf2 : axst := C4_of Ems_Cf2.
Definition RM_Cf2 : list sobj := RM_of C4_Cf2.
Definition TM0_Cf2 : axst := TM0_of C4_Cf2.
Definition TM_Cf2 : axst := TM_of C4_Cf2.

Definition run5_Cf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13Sa0S5S13A1A3S63A3").
Definition Erf_Cf2 : axst := leaf 0 run5_Cf2.
Definition XR_Cf2 : list axform := XRC Erf_Cf2.
Definition EC_Cf2 : axst := EC_of Erf_Cf2.
Definition sR_Cf2 : wsub := sR_of (E3_of Erf_Cf2).
Definition RR_Cf2 : list sobj := RR_of EC_Cf2 sR_Cf2.
Definition KEPT_Cf2 : list sobj := KEPT_of EC_Cf2 RR_Cf2.

Definition T0_Cf2 : axst := ltac2:(tb__ "0|0|
Sb6S4cS57S54A3").
Definition XS_Cf2 : list axform := XS_of T0_Cf2.
Definition T1_Cf2 : axst := T1_of T0_Cf2.
Definition KEPT1_Cf2 : list sobj := KEPT1_of T1_Cf2.
Definition T2_Cf2 : axst := T2_of T1_Cf2.
Definition TR_Cf2 : axst := TR_of T1_Cf2.

Definition TRs_Cf2 : axst := TRs_of TR_Cf2.
Definition run5d_Cf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S3aS5S13A1A3S64A3").
Definition Erq_Cf2 : axst := leaf 0 run5d_Cf2.
Definition XW_Cf2 : list axform := XW Erq_Cf2.
Definition Erq2_Cf2 : axst := Erq2_of Erq_Cf2.

Definition PMID_Cf2 : axst := ltac2:(tb__ "0|0|
SacS2S84S85S91S8fS17S90S42S2A1A4S43S2A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_Cf2 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS4dA1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_Cf2 : ltac2:(tb__ "0|0|
S0S3S94S3cS21S4S13S25S5S13A1A3S3bS4SeS4dS5SeA1A3S65A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_Cf2 exits1_Cf2 run1_Cf2); [unfold run1_Cf2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_Cf2 : ltac2:(tb__ "0|2|
S0S3S95S3cS21S4S13S25S5S13A1A3S3bS4S92S93S4dZ1S1cZ0M0A1M1A3S5S92A1A3S91SeS92SeS93R1G0G1A3LE;S65A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_Cf2 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf2) run1_Cf2); [unfold run1_Cf2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_Cf2_1 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S8eSfS5fA1SfS4eA1A2S8G3SaG1G2S4G0SaS16S16S2aS2bA4S5G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf2_1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS4eA1M0A1S2A3S1S0S14S15G0A1S15SfS5fA1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf2_1 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS4eA1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf2_1 : ltac2:(tb__ "0|0|
S0SeS11S5fSfS4eA1A2S4eA3"). Proof. vmr. Qed.
Lemma RUN2_Cf2_1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S4eA3S6eA3"). Proof. unfold run2_Cf2_1; reflexivity. Qed.
Lemma L2_Cf2_1 : ltac2:(tb__ "0|0|
S1S0S3S24S6eS4S13S23S5S13A1A3A2S2A3S0SeS39U0S6eA2S76A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf2_1; reflexivity]). Qed.
Lemma AXD_Cf2_1 : ltac2:(tb__ "0|0|
S0S7SeA1S41S76S28A2S8SeS48A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf2_1 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S97S48S8aZ1M1A1S22S48G1A2A3S8G0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf2_1 : ltac2:(tb__ "0|1|
S0S3S99S48S8aZ1M0A1S22S48G0A2S5bS4SeS8bG0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf2_1 : ltac2:(tb__ "0|1|
S0SeS69S96S98S22S48Z1M0A2S8aG0A1S8bG0A1S48S5bA5S1aSfS48A1A1A2A3").
Proof. unfold TD_Cf2_1, TD_of, RD_Cf2_1; reflexivity. Qed.
Lemma DCHK_Cf2_1 : ltac2:(tb__ "0|2|
S0S3S9bU2M0S44S42S2A1G0A2Z1M1S48S69S22S48G1A2S5bA7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf2_1 : ltac2:(tb__ "0|0|
S0S7SeA1S41S69S29A2S8SeS80A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf2_1 : ltac2:(tb__ "0|0|
S0S3S9cS80S53A2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf2_2 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S8eSfS60A1SfS4fA1A2S8G3SaG1G2S4G0SaS16S16S2aS2bA4S5G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf2_2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS4fA1M0A1S2A3S1S0S14S15G0A1S15SfS60A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf2_2 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS4fA1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf2_2 : ltac2:(tb__ "0|0|
S0SeS11S60SfS4fA1A2S4fA3"). Proof. vmr. Qed.
Lemma RUN2_Cf2_2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S4fA3S6fA3"). Proof. unfold run2_Cf2_2; reflexivity. Qed.
Lemma L2_Cf2_2 : ltac2:(tb__ "0|0|
S1S0S3S24S6fS4S13S23S5S13A1A3A2S2A3S0SeS39U0S6fA2S77A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf2_2; reflexivity]). Qed.
Lemma AXD_Cf2_2 : ltac2:(tb__ "0|0|
S0S7SeA1S41S77S28A2S8SeS49A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf2_2 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S97S49S8aZ2M1A1S22S49G1A2A3S8G0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf2_2 : ltac2:(tb__ "0|1|
S0S3S99S49S8aZ2M0A1S22S49G0A2S5cS4SeS8bG0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf2_2 : ltac2:(tb__ "0|1|
S0SeS6aS96S98S22S49Z2M0A2S8aG0A1S8bG0A1S49S5cA5S1aSfS49A1A1A2A3").
Proof. unfold TD_Cf2_2, TD_of, RD_Cf2_2; reflexivity. Qed.
Lemma DCHK_Cf2_2 : ltac2:(tb__ "0|2|
S0S3S9bU2M0S44S42S2A1G0A2Z2M1S49S6aS22S49G1A2S5cA7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf2_2 : ltac2:(tb__ "0|0|
S0S7SeA1S41S6aS29A2S8SeS81A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf2_2 : ltac2:(tb__ "0|0|
S0S3S9cS81S53A2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf2_3 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S8eSfS61A1SfS50A1A2S8G3SaG1G2S4G0SaS16S16S2aS2bA4S5G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf2_3 : ltac2:(tb__ "0|1|
S1S0S3S19SfS50A1M0A1S2A3S1S0S14S15G0A1S15SfS61A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf2_3 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS50A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf2_3 : ltac2:(tb__ "0|0|
S0SeS11S61SfS50A1A2S50A3"). Proof. vmr. Qed.
Lemma RUN2_Cf2_3 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S50A3S70A3"). Proof. unfold run2_Cf2_3; reflexivity. Qed.
Lemma L2_Cf2_3 : ltac2:(tb__ "0|0|
S1S0S3S24S70S4S13S23S5S13A1A3A2S2A3S0SeS39U0S70A2S78A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf2_3; reflexivity]). Qed.
Lemma AXD_Cf2_3 : ltac2:(tb__ "0|0|
S0S7SeA1S41S78S28A2S8SeS4aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf2_3 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S97S4aS8aZ3M1A1S22S4aG1A2A3S8G0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf2_3 : ltac2:(tb__ "0|1|
S0S3S99S4aS8aZ3M0A1S22S4aG0A2S5dS4SeS8bG0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf2_3 : ltac2:(tb__ "0|1|
S0SeS6bS96S98S22S4aZ3M0A2S8aG0A1S8bG0A1S4aS5dA5S1aSfS4aA1A1A2A3").
Proof. unfold TD_Cf2_3, TD_of, RD_Cf2_3; reflexivity. Qed.
Lemma DCHK_Cf2_3 : ltac2:(tb__ "0|2|
S0S3S9bU2M0S44S42S2A1G0A2Z3M1S4aS6bS22S4aG1A2S5dA7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf2_3 : ltac2:(tb__ "0|0|
S0S7SeA1S41S6bS29A2S8SeS82A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf2_3 : ltac2:(tb__ "0|0|
S0S3S9cS82S53A2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf2_4 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S8eSfS62A1SfS51A1A2S8G3SaG1G2S4G0SaS16S16S2aS2bA4S5G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf2_4 : ltac2:(tb__ "0|1|
S1S0S3S19SfS51A1M0A1S2A3S1S0S14S15G0A1S15SfS62A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf2_4 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS51A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf2_4 : ltac2:(tb__ "0|0|
S0SeS11S62SfS51A1A2S51A3"). Proof. vmr. Qed.
Lemma RUN2_Cf2_4 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S51A3S71A3"). Proof. unfold run2_Cf2_4; reflexivity. Qed.
Lemma L2_Cf2_4 : ltac2:(tb__ "0|0|
S1S0S3S24S71S4S13S23S5S13A1A3A2S2A3S0SeS39U0S71A2S79A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf2_4; reflexivity]). Qed.
Lemma AXD_Cf2_4 : ltac2:(tb__ "0|0|
S0S7SeA1S41S79S28A2S8SeS4bA2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf2_4 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S97S4bS8aZ4M1A1S22S4bG1A2A3S8G0S5eA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf2_4 : ltac2:(tb__ "0|1|
S0S3S99S4bS8aZ4M0A1S22S4bG0A2S5eS4SeS8bG0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf2_4 : ltac2:(tb__ "0|1|
S0SeS6cS96S98S22S4bZ4M0A2S8aG0A1S8bG0A1S4bS5eA5S1aSfS4bA1A1A2A3").
Proof. unfold TD_Cf2_4, TD_of, RD_Cf2_4; reflexivity. Qed.
Lemma DCHK_Cf2_4 : ltac2:(tb__ "0|2|
S0S3S9bU2M0S44S42S2A1G0A2Z4M1S4bS6cS22S4bG1A2S5eA7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf2_4 : ltac2:(tb__ "0|0|
S0S7SeA1S41S6cS29A2S8SeS83A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf2_4 : ltac2:(tb__ "0|0|
S0S3S9cS83S53A2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_Cf2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S2eS4S13S2cS5S13A1A3A3S53A3S67A3"). Proof. unfold run3_Cf2; reflexivity. Qed.
Lemma L3_Cf2 : ltac2:(tb__ "0|0|
S1S0S3S24S67S4S13S2eS4S13S2cS5S13A1A3A3A2S2A3S1S0SeS39U0S67A2S59A3S0SeS39U1S67A2S75A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_Cf2 | unfold Ebg_Cf2]; reflexivity]). Qed.
Lemma NX3_Cf2 : ltac2:(tb__ "0|1|
S1S0S3S8cS3bS15SfS53A1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_Cf2 : ltac2:(tb__ "0|0|
S0S3Sa3S18S20SbbA1S1aSfS75A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_Cf2 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S8eSfS59A1SfS52A1A2S8G2SaG0G1S34S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_Cf2 : ltac2:(tb__ "0|0|
S0SeS11S59SfS52A1A2S52A3"). Proof. vmr. Qed.
Lemma NX3b_Cf2 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS52A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_Cf2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS52A1M0A1S2A3S1S0S14S15G0A1S15SfS59A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_Cf2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S2dS5S13A1A3S52A3S72A3"). Proof. unfold run4_Cf2; reflexivity. Qed.
Lemma L4_Cf2 : ltac2:(tb__ "0|0|
S1S0S3S24S72S4S13S2dS5S13A1A3A2S2A3S0SeS39U0S72A2S58A3A2"). Proof. Time (split; [vmr | unfold Ems_Cf2; reflexivity]). Qed.
Lemma D4_Cf2 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S8eSfS58A1SfS47A1A2S8G2SaG0G1S35S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_Cf2 : ltac2:(tb__ "0|0|
S0SeS11S58SfS47A1A2S47A3"). Proof. vmr. Qed.
Lemma W4_Cf2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS47A1M0A1S2A3S1S0S14S15G0A1S15SfS58A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_Cf2 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S97S47S9dS2fS47A1A3S8G0S68A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_Cf2 : ltac2:(tb__ "0|0|
S0S3S9aS47S9dS2fS47A1S68S91S10SeS12S9eA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_Cf2 : ltac2:(tb__ "0|0|
S0SeS98S2fS47A1S9dS31S47S68A5S6dA3"). Proof. unfold TM0_Cf2, TM0_of, RM_Cf2; reflexivity. Qed.
Lemma FBM_Cf2 : ltac2:(tb__ "0|3|
S1S0S3Sa2S18S1dS15SfS47A1M0A1M1A1S1aG0A1M2A3S2A3S1S0S3Sa2S18S1dS15SfS6dA1A1A1G2A3S2A3S0S3S8cS3bG1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_Cf2 : ltac2:(tb__ "0|0|
S0SeS96S6dS1aSfS47A1A1A2S63A3"). Proof. vmr. Qed.

Lemma NX5_Cf2 : ltac2:(tb__ "0|1|
S1S0S3S8cS3bS15SfS63A1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_Cf2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13Sa0S5S13A1A3S63A3S73A3"). Proof. unfold run5_Cf2; reflexivity. Qed.
Lemma L5_Cf2 : ltac2:(tb__ "0|0|
S1S0S3S24S73S4S13Sa0S5S13A1A3A2S2A3S0SeS39U0S73A2S7aA3A2"). Proof. Time (split; [vmr | unfold Erf_Cf2; reflexivity]). Qed.
Lemma AXR_Cf2 : ltac2:(tb__ "0|0|
S0S7SeA1S41S7aS87A2S8SeS4cA2A3"). Proof. Time vmr. Qed.

Lemma HER_Cf2 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S97S4cS9fS57A3S8G0S54A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_Cf2 : ltac2:(tb__ "0|0|
S0S3S99S4cS9fS57S54S4SeSa1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_Cf2 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS4cA1A1ScS17S86S54A3A3"). Proof. Time vmr. Qed.
Lemma HT0_Cf2 : ltac2:(tb__ "0|0|
S0SeS7eS96S98S57S9fSa1S4cS54A5S1aSfS4cA1A1A2A3"). Proof. unfold T0_Cf2, T0_of; reflexivity. Qed.
Lemma HXS_Cf2 : ltac2:(tb__ "0|0|
S0S7SeA1S41S7eS88A2S8SeS55A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_Cf2 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS55A1A1ScS17S7dS4S17S30S4S17S90S45A1S4S17S90S46A1S5S17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_Cf2 : ltac2:(tb__ "0|0|
S0SeS7fS11S55Sb7SfS55A1S7dA2A2A3"). Proof. unfold T2_Cf2, T2_of, KEPT1_Cf2; reflexivity. Qed.
Lemma HTR_Cf2 : ltac2:(tb__ "0|2|
S0SeS56Sb1S7fS4S8fSb2Sb4S15SfS55A1A1M0S8dG0A1M1A3S5S8fA1A3S8dG1A1A3A3"). Proof. unfold TR_Cf2, TR_of, T2_Cf2; reflexivity. Qed.
Lemma RCHK_Cf2 : ltac2:(tb__ "0|0|
S0S3Sb3U2S2S4cS55S56S57S54Sb4A8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_Cf2 : ltac2:(tb__ "0|0|
S0SeS64Sb1S56SbdS15SfS56A1A1A3A3"). Proof. unfold TRs_Cf2, TRs_of; reflexivity. Qed.
Lemma CCHK_Cf2 : ltac2:(tb__ "0|0|
S0S3SbeU2S3S37L_;S2S33S32X3x2S56S64A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_Cf2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S3aS5S13A1A3S64A3S74A3"). Proof. unfold run5d_Cf2; reflexivity. Qed.
Lemma L5d_Cf2 : ltac2:(tb__ "0|0|
S1S0S3S24S74S4S13S3aS5S13A1A3A2S2A3S0SeS39U0S74A2S7cA3A2"). Proof. Time (split; [vmr | unfold Erq_Cf2; reflexivity]). Qed.
Lemma AXW_Cf2 : ltac2:(tb__ "0|0|
S0S7SeA1S41S7cS89A2S8SeS7bA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_Cf2 : ltac2:(tb__ "0|0|
S0S3S36S7bSbcA2S2A3"). Proof. Time vmr. Qed.

Lemma Wa_Cf2 : ltac2:(tb__ "0|0|
S0S3S19Sa5S3eU2A1S3dA2A1S2A3"). Proof. vmr. Qed.
Lemma Da_Cf2 : ltac2:(tb__ "0|5|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S8eSfS40S3fS3eU2A1M4S3dA3A1Sa5G4S3dA2A2S8G3SaG1G2S4G0SaS16S16S1fP18A1S1cSbaA1A4S5G0A1A3S5S18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_Cf2 : ltac2:(tb__ "0|0|
S0S3S19Sa8S3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_Cf2 : ltac2:(tb__ "0|0|
S0S3S19Sa9S3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_Cf2 : ltac2:(tb__ "0|0|
S0S3S19SaaS3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_Cf2 : ltac2:(tb__ "0|0|
S0S3Sa2S18S1dSb9A1Sa6S2S3eU2A1S3dS43S2A1A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_Cf2 : ltac2:(tb__ "0|4|
S0S7SeA1S41SabS2S3eU2M0A1M1S3dS42S2A1M2S43S2A1M3A5Sa4G0SdS8fG2A2A2A2S8SeSa7S2G1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_Cf2 : ltac2:(tb__ "0|0|
S0S3S8cS3bS15SfS5aA1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_Cf2__runs : ltac2:(tb__ "0|0|
S6S7S6S10A1A1A1") := ltac2:(tb__ "0|0|
Sb8S3cS21S4S13S25S5S13A1A3S4SeS5aS5SeA1A3A4").
Lemma Cert1m_Cf2 : ltac2:(tb__ "0|0|
S0S3S94S3cS21S4S13S25S5S13A1A3S3bS4SeS5aS5SeA1A3S65A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_Cf2] exits1_Cf2 Cert1m_Cf2__runs); [unfold Cert1m_Cf2__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_Cf2 : ltac2:(tb__ "0|2|
S0S3S95S3cS21S4S13S25S5S13A1A3S3bS4S92S93S5aZ1S1cZ0M0A1M1A3S5S92A1A3S91SeS92SeS93R1G0G1A3LE;S65A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_Cf2 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf2) Cert1m_Cf2__runs); [unfold Cert1m_Cf2__runs; reflexivity | vmr]. Qed.
Lemma Wbm_Cf2 : ltac2:(tb__ "0|0|
S0S3S19SadS3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_Cf2 : ltac2:(tb__ "0|0|
S0S3S19SaeS3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_Cf2 : ltac2:(tb__ "0|0|
S0S3S19SafS3eU2A1S3dS42S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_Cf2 : ltac2:(tb__ "0|4|
S0S7SeA1S41Sb0S2S3eU2M0A1M1S3dS42S2A1M2S43S2A1M3A5Sa4G0SdS8fG2A2A2A2S8SeSacS2G1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cCf2.

(* [comment removed for export] *)
Module F0A_aCf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCf2"; "ED_Cf2_1"; "ED_Cf2_2"; "ED_Cf2_3"; "ED_Cf2_4"; "TD_Cf2_1"; "TD_Cf2_2"; "TD_Cf2_3"; "TD_Cf2_4"; "P0_Cf2"; "PMID_Cf2"; "TM_Cf2"; "exits1_Cf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aCf2.ACf2"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_asmC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_cCf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dl.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACf2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS23Vsegs;Vok;S25Vsegs;S2dU2S1S16R6VKc;R5A6S4aR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS22Vsegs;S25Vsegs;S2dU2S1S16R6VKc;R5A6S4aR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6S2aSbS37S2aR2S4bA3S23Vsegs;R13S25Vsegs;S2dG1S1SfR12R11RfA6R3R2ReA5RdA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_Cf2 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_Cf2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 2 UStopLe false keep ok A Kc rho rho1 Ebg_Cf2 Q BGF_Cf2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2 UStopLe false Eps_Cf2 C3_Cf2 Ems_Cf2 C4_Cf2 TM0_Cf2 run4_Cf2 RM_Cf2 D3_Cf2 W3_Cf2 EQ3_Cf2 NX3b_Cf2 RUN4_Cf2 L4_Cf2 D4_Cf2 W4_Cf2 EQ4_Cf2
             HeM_Cf2 HchkM_Cf2 HTM_Cf2 FBM_Cf2 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_Cf2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2 UStopLe true S1c_Cf2_1 C2_Cf2_1 EfD_Cf2_1 ED_Cf2_1 run2_Cf2_1 D2_Cf2_1 W2_Cf2_1 NX2_Cf2_1 EQ2_Cf2_1 RUN2_Cf2_1 L2_Cf2_1 AXD_Cf2_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_Cf2_1 TDr_Cf2_1 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_1 ENTD_Cf2_1 RUN3_Cf2 L3_Cf2 NX3_Cf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_Cf2_2 C2_Cf2_2 EfD_Cf2_2 ED_Cf2_2 run2_Cf2_2 D2_Cf2_2 W2_Cf2_2 NX2_Cf2_2 EQ2_Cf2_2 RUN2_Cf2_2 L2_Cf2_2 AXD_Cf2_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_Cf2_2 TDr_Cf2_2 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_2 ENTD_Cf2_2 RUN3_Cf2 L3_Cf2 NX3_Cf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_Cf2_3 C2_Cf2_3 EfD_Cf2_3 ED_Cf2_3 run2_Cf2_3 D2_Cf2_3 W2_Cf2_3 NX2_Cf2_3 EQ2_Cf2_3 RUN2_Cf2_3 L2_Cf2_3 AXD_Cf2_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_Cf2_3 TDr_Cf2_3 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_3 ENTD_Cf2_3 RUN3_Cf2 L3_Cf2 NX3_Cf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_Cf2_4 C2_Cf2_4 EfD_Cf2_4 ED_Cf2_4 run2_Cf2_4 D2_Cf2_4 W2_Cf2_4 NX2_Cf2_4 EQ2_Cf2_4 RUN2_Cf2_4 L2_Cf2_4 AXD_Cf2_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_Cf2_4 TDr_Cf2_4 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_4 ENTD_Cf2_4 RUN3_Cf2 L3_Cf2 NX3_Cf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5S2aSbS37S2aR2S4bA3S22Vsegs;S25Vsegs;S2dG1S1SfR11R10ReA6R3R2RdA5RcA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_Cf2 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_Cf2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 2 UStopLe false keep A Kc rho rho1 Ebg_Cf2 Q BGF_Cf2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2 UStopLe false Eps_Cf2 C3_Cf2 Ems_Cf2 C4_Cf2 TM0_Cf2 run4_Cf2 RM_Cf2 D3_Cf2 W3_Cf2 EQ3_Cf2 NX3b_Cf2 RUN4_Cf2 L4_Cf2 D4_Cf2 W4_Cf2 EQ4_Cf2
             HeM_Cf2 HchkM_Cf2 HTM_Cf2 FBM_Cf2 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_Cf2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2 UStopLe true S1c_Cf2_1 C2_Cf2_1 EfD_Cf2_1 ED_Cf2_1 run2_Cf2_1 D2_Cf2_1 W2_Cf2_1 NX2_Cf2_1 EQ2_Cf2_1 RUN2_Cf2_1 L2_Cf2_1 AXD_Cf2_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_Cf2_1 TDr_Cf2_1 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_1 ENTD_Cf2_1 RUN3_Cf2 L3_Cf2 NX3_Cf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_Cf2_2 C2_Cf2_2 EfD_Cf2_2 ED_Cf2_2 run2_Cf2_2 D2_Cf2_2 W2_Cf2_2 NX2_Cf2_2 EQ2_Cf2_2 RUN2_Cf2_2 L2_Cf2_2 AXD_Cf2_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_Cf2_2 TDr_Cf2_2 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_2 ENTD_Cf2_2 RUN3_Cf2 L3_Cf2 NX3_Cf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_Cf2_3 C2_Cf2_3 EfD_Cf2_3 ED_Cf2_3 run2_Cf2_3 D2_Cf2_3 W2_Cf2_3 NX2_Cf2_3 EQ2_Cf2_3 RUN2_Cf2_3 L2_Cf2_3 AXD_Cf2_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_Cf2_3 TDr_Cf2_3 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_3 ENTD_Cf2_3 RUN3_Cf2 L3_Cf2 NX3_Cf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_Cf2_4 C2_Cf2_4 EfD_Cf2_4 ED_Cf2_4 run2_Cf2_4 D2_Cf2_4 W2_Cf2_4 NX2_Cf2_4 EQ2_Cf2_4 RUN2_Cf2_4 L2_Cf2_4 AXD_Cf2_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_Cf2_4 TDr_Cf2_4 CD_Cf2 Eps_Cf2 Ebg_Cf2 run3_Cf2 AXDr_Cf2_4 ENTD_Cf2_4 RUN3_Cf2 L3_Cf2 NX3_Cf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1SfR10RfRdA6S48R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true P0_Cf2 exits1_Cf2 Cert1_Cf2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1SfRfReRcA6S48R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true P0_Cf2 exits1_Cf2 NX0_Cf2 ECert1_Cf2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Theorem free_spine_m_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1SfR10RfRdA6S49R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true PMID_Cf2 exits1_Cf2 Cert1m_Cf2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_m_Cf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1SfRfReRcA6S49R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true PMID_Cf2 exits1_Cf2 NX0m_Cf2 ECert1m_Cf2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1fS4fS56R2A2S1cS27S31R2A2S29R2S32A2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS57R2A1A1F_;Fa;").

Theorem hdf_Cf2_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S40S44R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_1 TD_Cf2_1 (sD_of ED_Cf2_1 1) RD_Cf2_1 HeD_Cf2_1 HchkD_Cf2_1 HTD_Cf2_1 DCHK_Cf2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf2_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S40S44R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_1 TD_Cf2_1 (sD_of ED_Cf2_1 1) RD_Cf2_1 HeD_Cf2_1 HchkD_Cf2_1 HTD_Cf2_1 DCHK_Cf2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_Cf2_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S41S45R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_2 TD_Cf2_2 (sD_of ED_Cf2_2 2) RD_Cf2_2 HeD_Cf2_2 HchkD_Cf2_2 HTD_Cf2_2 DCHK_Cf2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf2_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S41S45R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_2 TD_Cf2_2 (sD_of ED_Cf2_2 2) RD_Cf2_2 HeD_Cf2_2 HchkD_Cf2_2 HTD_Cf2_2 DCHK_Cf2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_Cf2_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S42S46R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_3 TD_Cf2_3 (sD_of ED_Cf2_3 3) RD_Cf2_3 HeD_Cf2_3 HchkD_Cf2_3 HTD_Cf2_3 DCHK_Cf2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf2_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S42S46R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_3 TD_Cf2_3 (sD_of ED_Cf2_3 3) RD_Cf2_3 HeD_Cf2_3 HchkD_Cf2_3 HTD_Cf2_3 DCHK_Cf2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_Cf2_4 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S43S47R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_4 TD_Cf2_4 (sD_of ED_Cf2_4 4) RD_Cf2_4 HeD_Cf2_4 HchkD_Cf2_4 HTD_Cf2_4 DCHK_Cf2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf2_4 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S43S47R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf2_4 TD_Cf2_4 (sD_of ED_Cf2_4 4) RD_Cf2_4 HeD_Cf2_4 HchkD_Cf2_4 HTD_Cf2_4 DCHK_Cf2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.

Lemma tail_Cf2 : ltac2:(tb__ "0|3|
S20OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S26SaRcS24RaA1A3S4dSaRdS24RbA1A3S52ReRcA2S30SaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S37S12S0S0A2S11S0S0ReRdA4S18R12A1A3S3aRfReA2S1bS13S19R14A1SfA3S33SfR15A2S2eR14S34R16R14R12R11R10RfA6A2S1bS0S3cR10A1S3fA3S50S39VCST;VXGL;R18A3R19R18R17S34R18R16R14R13R12R11A6S36SaS4eR16R15S14S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 2 true CST XGL HCST HXGL TM_Cf2 Erf_Cf2 EC_Cf2 run5_Cf2 XR_Cf2 NX5_Cf2 RUN5_Cf2 L5_Cf2 AXR_Cf2 T0_Cf2 T1_Cf2 T2_Cf2 TR_Cf2 sR_Cf2 RR_Cf2 KEPT_Cf2 KEPT1_Cf2 XS_Cf2 eFRc HER_Cf2 Hchk_Cf2 OBJS_Cf2 HT0_Cf2 HXS_Cf2 OBJS1_Cf2 HT2_Cf2 HTR_Cf2 RCHK_Cf2 TRs_Cf2 Erq_Cf2 Erq2_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.TQ_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.Edr_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.Xf_2Bf run5d_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.run6_2Bf XW_Cf2 HTRs_Cf2 CCHK_Cf2 RUN5d_Cf2 L5d_Cf2 AXW_Cf2 ENTQ_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.NX6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.RUN6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.L6_2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_q2Bf.f0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d3.F0A_xi2Bf.f0_exit_2Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Cf2 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S53RaA1S30SaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S37S12S0S0A2S11S0S0RcRbA4S18R10A1A3S3aRdRcA2S1bS13S19R12A1SfA3S33SfR13A2S2eR12S34R14R12R10RfReRdA6A2S1bS0S3cReA1S3fA3S51S39VCST;VXGL;R16A3R16R15S34R16R14R12R11R10RfA6S36SaS4eR14R13S14S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 2 true CST XGL HCST HXGL TM_Cf2 Erf_Cf2 EC_Cf2 run5_Cf2 XR_Cf2 NX5_Cf2 RUN5_Cf2 L5_Cf2 AXR_Cf2 T0_Cf2 T1_Cf2 T2_Cf2 TR_Cf2 sR_Cf2 RR_Cf2 KEPT_Cf2 KEPT1_Cf2 XS_Cf2 eFRc HER_Cf2 Hchk_Cf2 OBJS_Cf2 HT0_Cf2 HXS_Cf2 OBJS1_Cf2 HT2_Cf2 HTR_Cf2 RCHK_Cf2 TRs_Cf2 Erq_Cf2 Erq2_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.TQ_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.Edr_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.Xf_2Bf run5d_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.run6_2Bf XW_Cf2 HTRs_Cf2 CCHK_Cf2 RUN5d_Cf2 L5d_Cf2 AXW_Cf2 ENTQ_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.NX6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.RUN6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.L6_2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.F0A_q2Bf.ef0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d3.F0A_xi2Bf.ef0_exit_2Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Cf_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S3eS28R6Z10A2A2S1bS13S19RbA1SfA3S33SfRcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 2) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate true 2 UStopLe (NVC true) (VFC true) Wa_Cf2 Da_Cf2 Wb_Cf2 Wc_Cf2 Wd_Cf2 Fb_Cf2 XI_Cf2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_Cf2 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_Cf2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_Cf2 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_Cf_2 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S27S3eS28R4Z10A2A2S1bS13S19R9A1SfA3S33SfRaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 2) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate true 2 UStopLe (NVC true) (VFC true) Wa_Cf2 Da_Cf2 Wb_Cf2 Wc_Cf2 Wd_Cf2 Fb_Cf2 XI_Cf2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_Cf2 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_Cf2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_Cf2 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1cS1dS1cS27S31R2A2S29R2S32A2A2A1S1dS1cS27Z180e88R2A2S29R2Z180e8cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_Cf_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S3eS28R6Z10A2A2S1bS13S19RbA1S16A3S33SfRcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Certi_2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts true (Wcan 2) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 2 UStopLe (NVC true) (VFC true) Wbm_Cf2 Wcm_Cf2 Wdm_Cf2 Fb_Cf2 XIm_Cf2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_Cf2 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_Cf2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_Cf2 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_Cf_2 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S27S3eS28R4Z10A2A2S1bS13S19R9A1S16A3S33SfRaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A.ECerti_2A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 2 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts true (Wcan 2) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true 2 UStopLe (NVC true) (VFC true) Wbm_Cf2 Wcm_Cf2 Wdm_Cf2 Fb_Cf2 XIm_Cf2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_Cf2 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_Cf2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_Cf2 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ACf2.
End F0A_aCf2.

