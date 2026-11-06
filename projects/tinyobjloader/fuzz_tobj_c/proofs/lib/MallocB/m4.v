(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
From Stdlib Require NArith PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ld lo.

(* [comment removed for export] *)
Module F0A_cLCf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "false"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "MSE"; "PSE"; "sM_of"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m4.F0A_cLCf2"; "C4_LCf2"; "ED_LCf2_1"; "ED_LCf2_2"; "ED_LCf2_3"; "ED_LCf2_4"; "EC_LCf2"; "P0_LCf2"; "C2_LCf2_1"; "C2_LCf2_2"; "C2_LCf2_3"; "C2_LCf2_4"; "C3_LCf2"; "CD_LCf2"; "RR_LCf2"; "T1_LCf2"; "TR_LCf2"; "sR_LCf2"; "Ems_LCf2"; "Eps_LCf2"; "PMID_LCf2"; "RD_LCf2_1"; "RD_LCf2_2"; "RD_LCf2_3"; "RD_LCf2_4"; "S1c_LCf2_1"; "S1c_LCf2_2"; "S1c_LCf2_3"; "S1c_LCf2_4"; "TM_LCf2"; "TRs_LCf2"; "exits1_LCf2"; "run1_LCf2"; "run3_LCf2"; "RM_LCf2"; "TD_LCf2_1"; "TD_LCf2_2"; "TD_LCf2_3"; "TD_LCf2_4"; "TM0_LCf2"; "run2_LCf2_1"; "run2_LCf2_2"; "run2_LCf2_3"; "run2_LCf2_4"; "run4_LCf2"; "run5_LCf2"; "run5d_LCf2"; "Ebg_LCf2"; "EfD_LCf2_1"; "EfD_LCf2_2"; "EfD_LCf2_3"; "EfD_LCf2_4"; "Erf_LCf2"; "Erq2_LCf2"; "Erq_LCf2"; "KEPT1_LCf2"; "T0_LCf2"; "T2_LCf2"; "TDr_LCf2_1"; "TDr_LCf2_2"; "TDr_LCf2_3"; "TDr_LCf2_4"; "W_LCf2"; "st_LCf2"; "KEPT_LCf2"; "XR_LCf2"; "XS_LCf2"; "XW_LCf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf"; "TQ_L2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LCf2 : list ulink := Wcan 2.
Definition st_LCf2 : ustop := UStopLe.
Definition P0_LCf2 : axst := ltac2:(tb__ "0|0|
Sb5SeS84S85S7A4").

Definition run1_LCf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S25SaS13A1A3S4dA3").

Definition S1c_LCf2_1 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z1A3").
Definition C2_LCf2_1 : axst := C2_of S1c_LCf2_1.
Definition run2_LCf2_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S4eA3").
Definition EfD_LCf2_1 : axst := leaf 0 run2_LCf2_1.
Definition ED_LCf2_1 : axst := ED_of EfD_LCf2_1.
Definition RD_LCf2_1 : list sobj := RD_of ED_LCf2_1 1.
Definition TD_LCf2_1 : axst := TD_of ED_LCf2_1 1.
Definition TDr_LCf2_1 : axst := TDr_of TD_LCf2_1.
Definition S1c_LCf2_2 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z2A3").
Definition C2_LCf2_2 : axst := C2_of S1c_LCf2_2.
Definition run2_LCf2_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S4fA3").
Definition EfD_LCf2_2 : axst := leaf 0 run2_LCf2_2.
Definition ED_LCf2_2 : axst := ED_of EfD_LCf2_2.
Definition RD_LCf2_2 : list sobj := RD_of ED_LCf2_2 2.
Definition TD_LCf2_2 : axst := TD_of ED_LCf2_2 2.
Definition TDr_LCf2_2 : axst := TDr_of TD_LCf2_2.
Definition S1c_LCf2_3 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z3A3").
Definition C2_LCf2_3 : axst := C2_of S1c_LCf2_3.
Definition run2_LCf2_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S50A3").
Definition EfD_LCf2_3 : axst := leaf 0 run2_LCf2_3.
Definition ED_LCf2_3 : axst := ED_of EfD_LCf2_3.
Definition RD_LCf2_3 : list sobj := RD_of ED_LCf2_3 3.
Definition TD_LCf2_3 : axst := TD_of ED_LCf2_3 3.
Definition TDr_LCf2_3 : axst := TDr_of TD_LCf2_3.
Definition S1c_LCf2_4 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z4A3").
Definition C2_LCf2_4 : axst := C2_of S1c_LCf2_4.
Definition run2_LCf2_4 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S23SaS13A1A3S51A3").
Definition EfD_LCf2_4 : axst := leaf 0 run2_LCf2_4.
Definition ED_LCf2_4 : axst := ED_of EfD_LCf2_4.
Definition RD_LCf2_4 : list sobj := RD_of ED_LCf2_4 4.
Definition TD_LCf2_4 : axst := TD_of ED_LCf2_4 4.
Definition TDr_LCf2_4 : axst := TDr_of TD_LCf2_4.
Definition exits1_LCf2 : list axst := ltac2:(tb__ "0|0|
S9S2S5fS9S2S60S9S2S61S9S2S62SaS2A1A3A3A3A3").

Definition CD_LCf2 : axst := CD_of TDr_LCf2_1.
Definition run3_LCf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S2eS9S13S2cSaS13A1A3A3S53A3").
Definition Eps_LCf2 : axst := leaf 0 run3_LCf2.
Definition Ebg_LCf2 : axst := leaf 1 run3_LCf2.
Definition C3_LCf2 : axst := C3_of Eps_LCf2.
Definition run4_LCf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S2dSaS13A1A3S52A3").
Definition Ems_LCf2 : axst := leaf 0 run4_LCf2.
Definition C4_LCf2 : axst := C4_of Ems_LCf2.
Definition RM_LCf2 : list sobj := RM_of C4_LCf2.
Definition TM0_LCf2 : axst := TM0_of C4_LCf2.
Definition TM_LCf2 : axst := TM_of C4_LCf2.

Definition run5_LCf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13Sa0SaS13A1A3S63A3").
Definition Erf_LCf2 : axst := leaf 0 run5_LCf2.
Definition XR_LCf2 : list axform := XRC Erf_LCf2.
Definition EC_LCf2 : axst := EC_of Erf_LCf2.
Definition sR_LCf2 : wsub := sR_of (E3_of Erf_LCf2).
Definition RR_LCf2 : list sobj := RR_of EC_LCf2 sR_LCf2.
Definition KEPT_LCf2 : list sobj := KEPT_of EC_LCf2 RR_LCf2.

Definition T0_LCf2 : axst := ltac2:(tb__ "0|0|
Sb6S4cS57S54A3").
Definition XS_LCf2 : list axform := XS_of T0_LCf2.
Definition T1_LCf2 : axst := T1_of T0_LCf2.
Definition KEPT1_LCf2 : list sobj := KEPT1_of T1_LCf2.
Definition T2_LCf2 : axst := T2_of T1_LCf2.
Definition TR_LCf2 : axst := TR_of T1_LCf2.

Definition TRs_LCf2 : axst := TRs_of TR_LCf2.
Definition run5d_LCf2 : list leafA := ltac2:(tb__ "0|0|
S38S21S9S13S3aSaS13A1A3S64A3").
Definition Erq_LCf2 : axst := leaf 0 run5d_LCf2.
Definition XW_LCf2 : list axform := XW Erq_LCf2.
Definition Erq2_LCf2 : axst := Erq2_of Erq_LCf2.

Definition PMID_LCf2 : axst := ltac2:(tb__ "0|0|
SacSeS84S85S91S8fS17S90S42S7A1A4S43S7A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LCf2 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S4dA1A1A2S7A3"). Proof. vmr. Qed.
Lemma Cert1_LCf2 : ltac2:(tb__ "0|0|
S0S8S94S3cS21S9S13S25SaS13A1A3S3bS9S2S4dSaS2A1A3S65A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LCf2 exits1_LCf2 run1_LCf2); [unfold run1_LCf2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LCf2 : ltac2:(tb__ "0|2|
S0S8S95S3cS21S9S13S25SaS13A1A3S3bS9S92S93S4dZ1S1cZ0M0A1M1A3SaS92A1A3S91S2S92S2S93R1G0G1A3LE;S65A4A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LCf2 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf2) run1_LCf2); [unfold run1_LCf2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LCf2_1 : ltac2:(tb__ "0|4|
S0ScSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S8eS3S5fA1S3S4eA1A2SdG3S10G1G2S9G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf2_1 : ltac2:(tb__ "0|1|
S1S0S8S19S3S4eA1M0A1S7A3S1S0S14S15G0A1S15S3S5fA1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf2_1 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S4eA1A1A2S7A3"). Proof. vmr. Qed.
Lemma EQ2_LCf2_1 : ltac2:(tb__ "0|0|
S0S2S5S5fS3S4eA1A2S4eA3"). Proof. vmr. Qed.
Lemma RUN2_LCf2_1 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S4eA3S6eA3"). Proof. unfold run2_LCf2_1; reflexivity. Qed.
Lemma L2_LCf2_1 : ltac2:(tb__ "0|0|
S1S0S8S24S6eS9S13S23SaS13A1A3A2S7A3S0S2S39U0S6eA2S76A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf2_1; reflexivity]). Qed.
Lemma AXD_LCf2_1 : ltac2:(tb__ "0|0|
S0ScS2A1S41S76S28A2SdS2S48A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf2_1 : ltac2:(tb__ "0|2|
S0ScSbS17A1M0A1S97S48S8aZ1M1A1S22S48G1A2A3SdG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf2_1 : ltac2:(tb__ "0|1|
S0S8S99S48S8aZ1M0A1S22S48G0A2S5bS9S2S8bG0A1SaS2A1A3A5S7A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf2_1 : ltac2:(tb__ "0|1|
S0S2S69S96S98S22S48Z1M0A2S8aG0A1S8bG0A1S48S5bA5S1aS3S48A1A1A2A3").
Proof. unfold TD_LCf2_1, TD_of, RD_LCf2_1; reflexivity. Qed.
Lemma DCHK_LCf2_1 : ltac2:(tb__ "0|2|
S0S8S9bU2M0S44S42S7A1G0A2Z1M1S48S69S22S48G1A2S5bA7S7A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf2_1 : ltac2:(tb__ "0|0|
S0ScS2A1S41S69S29A2SdS2S80A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf2_1 : ltac2:(tb__ "0|0|
S0S8S9cS80S53A2S7A3"). Proof. Time vmr. Qed.
Lemma D2_LCf2_2 : ltac2:(tb__ "0|4|
S0ScSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S8eS3S60A1S3S4fA1A2SdG3S10G1G2S9G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf2_2 : ltac2:(tb__ "0|1|
S1S0S8S19S3S4fA1M0A1S7A3S1S0S14S15G0A1S15S3S60A1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf2_2 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S4fA1A1A2S7A3"). Proof. vmr. Qed.
Lemma EQ2_LCf2_2 : ltac2:(tb__ "0|0|
S0S2S5S60S3S4fA1A2S4fA3"). Proof. vmr. Qed.
Lemma RUN2_LCf2_2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S4fA3S6fA3"). Proof. unfold run2_LCf2_2; reflexivity. Qed.
Lemma L2_LCf2_2 : ltac2:(tb__ "0|0|
S1S0S8S24S6fS9S13S23SaS13A1A3A2S7A3S0S2S39U0S6fA2S77A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf2_2; reflexivity]). Qed.
Lemma AXD_LCf2_2 : ltac2:(tb__ "0|0|
S0ScS2A1S41S77S28A2SdS2S49A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf2_2 : ltac2:(tb__ "0|2|
S0ScSbS17A1M0A1S97S49S8aZ2M1A1S22S49G1A2A3SdG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf2_2 : ltac2:(tb__ "0|1|
S0S8S99S49S8aZ2M0A1S22S49G0A2S5cS9S2S8bG0A1SaS2A1A3A5S7A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf2_2 : ltac2:(tb__ "0|1|
S0S2S6aS96S98S22S49Z2M0A2S8aG0A1S8bG0A1S49S5cA5S1aS3S49A1A1A2A3").
Proof. unfold TD_LCf2_2, TD_of, RD_LCf2_2; reflexivity. Qed.
Lemma DCHK_LCf2_2 : ltac2:(tb__ "0|2|
S0S8S9bU2M0S44S42S7A1G0A2Z2M1S49S6aS22S49G1A2S5cA7S7A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf2_2 : ltac2:(tb__ "0|0|
S0ScS2A1S41S6aS29A2SdS2S81A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf2_2 : ltac2:(tb__ "0|0|
S0S8S9cS81S53A2S7A3"). Proof. Time vmr. Qed.
Lemma D2_LCf2_3 : ltac2:(tb__ "0|4|
S0ScSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S8eS3S61A1S3S50A1A2SdG3S10G1G2S9G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf2_3 : ltac2:(tb__ "0|1|
S1S0S8S19S3S50A1M0A1S7A3S1S0S14S15G0A1S15S3S61A1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf2_3 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S50A1A1A2S7A3"). Proof. vmr. Qed.
Lemma EQ2_LCf2_3 : ltac2:(tb__ "0|0|
S0S2S5S61S3S50A1A2S50A3"). Proof. vmr. Qed.
Lemma RUN2_LCf2_3 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S50A3S70A3"). Proof. unfold run2_LCf2_3; reflexivity. Qed.
Lemma L2_LCf2_3 : ltac2:(tb__ "0|0|
S1S0S8S24S70S9S13S23SaS13A1A3A2S7A3S0S2S39U0S70A2S78A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf2_3; reflexivity]). Qed.
Lemma AXD_LCf2_3 : ltac2:(tb__ "0|0|
S0ScS2A1S41S78S28A2SdS2S4aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf2_3 : ltac2:(tb__ "0|2|
S0ScSbS17A1M0A1S97S4aS8aZ3M1A1S22S4aG1A2A3SdG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf2_3 : ltac2:(tb__ "0|1|
S0S8S99S4aS8aZ3M0A1S22S4aG0A2S5dS9S2S8bG0A1SaS2A1A3A5S7A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf2_3 : ltac2:(tb__ "0|1|
S0S2S6bS96S98S22S4aZ3M0A2S8aG0A1S8bG0A1S4aS5dA5S1aS3S4aA1A1A2A3").
Proof. unfold TD_LCf2_3, TD_of, RD_LCf2_3; reflexivity. Qed.
Lemma DCHK_LCf2_3 : ltac2:(tb__ "0|2|
S0S8S9bU2M0S44S42S7A1G0A2Z3M1S4aS6bS22S4aG1A2S5dA7S7A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf2_3 : ltac2:(tb__ "0|0|
S0ScS2A1S41S6bS29A2SdS2S82A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf2_3 : ltac2:(tb__ "0|0|
S0S8S9cS82S53A2S7A3"). Proof. Time vmr. Qed.
Lemma D2_LCf2_4 : ltac2:(tb__ "0|4|
S0ScSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S8eS3S62A1S3S51A1A2SdG3S10G1G2S9G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf2_4 : ltac2:(tb__ "0|1|
S1S0S8S19S3S51A1M0A1S7A3S1S0S14S15G0A1S15S3S62A1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf2_4 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S51A1A1A2S7A3"). Proof. vmr. Qed.
Lemma EQ2_LCf2_4 : ltac2:(tb__ "0|0|
S0S2S5S62S3S51A1A2S51A3"). Proof. vmr. Qed.
Lemma RUN2_LCf2_4 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S23SaS13A1A3S51A3S71A3"). Proof. unfold run2_LCf2_4; reflexivity. Qed.
Lemma L2_LCf2_4 : ltac2:(tb__ "0|0|
S1S0S8S24S71S9S13S23SaS13A1A3A2S7A3S0S2S39U0S71A2S79A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf2_4; reflexivity]). Qed.
Lemma AXD_LCf2_4 : ltac2:(tb__ "0|0|
S0ScS2A1S41S79S28A2SdS2S4bA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf2_4 : ltac2:(tb__ "0|2|
S0ScSbS17A1M0A1S97S4bS8aZ4M1A1S22S4bG1A2A3SdG0S5eA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf2_4 : ltac2:(tb__ "0|1|
S0S8S99S4bS8aZ4M0A1S22S4bG0A2S5eS9S2S8bG0A1SaS2A1A3A5S7A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf2_4 : ltac2:(tb__ "0|1|
S0S2S6cS96S98S22S4bZ4M0A2S8aG0A1S8bG0A1S4bS5eA5S1aS3S4bA1A1A2A3").
Proof. unfold TD_LCf2_4, TD_of, RD_LCf2_4; reflexivity. Qed.
Lemma DCHK_LCf2_4 : ltac2:(tb__ "0|2|
S0S8S9bU2M0S44S42S7A1G0A2Z4M1S4bS6cS22S4bG1A2S5eA7S7A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf2_4 : ltac2:(tb__ "0|0|
S0ScS2A1S41S6cS29A2SdS2S83A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf2_4 : ltac2:(tb__ "0|0|
S0S8S9cS83S53A2S7A3"). Proof. Time vmr. Qed.
Lemma RUN3_LCf2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S2eS9S13S2cSaS13A1A3A3S53A3S67A3"). Proof. unfold run3_LCf2; reflexivity. Qed.
Lemma L3_LCf2 : ltac2:(tb__ "0|0|
S1S0S8S24S67S9S13S2eS9S13S2cSaS13A1A3A3A2S7A3S1S0S2S39U0S67A2S59A3S0S2S39U1S67A2S75A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LCf2 | unfold Ebg_LCf2]; reflexivity]). Qed.
Lemma NX3_LCf2 : ltac2:(tb__ "0|1|
S1S0S8S8cS3bS15S3S53A1M0A1A2S7A3S0S8S1bG0A1SeA3A2"). Proof. split; vmr. Qed.

Lemma BGF_LCf2 : ltac2:(tb__ "0|0|
S0S8Sa3S18S20SbbA1S1aS3S75A1A1A3S7A3"). Proof. vmr. Qed.
Lemma D3_LCf2 : ltac2:(tb__ "0|3|
S0ScSfSbSfS16S16A2A1M0SbS18A1M1A2M2A1S8eS3S59A1S3S52A1A2SdG2S10G0G1S34SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LCf2 : ltac2:(tb__ "0|0|
S0S2S5S59S3S52A1A2S52A3"). Proof. vmr. Qed.
Lemma NX3b_LCf2 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S52A1A1A2S7A3"). Proof. vmr. Qed.
Lemma W3_LCf2 : ltac2:(tb__ "0|1|
S1S0S8S19S3S52A1M0A1S7A3S1S0S14S15G0A1S15S3S59A1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LCf2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S2dSaS13A1A3S52A3S72A3"). Proof. unfold run4_LCf2; reflexivity. Qed.
Lemma L4_LCf2 : ltac2:(tb__ "0|0|
S1S0S8S24S72S9S13S2dSaS13A1A3A2S7A3S0S2S39U0S72A2S58A3A2"). Proof. Time (split; [vmr | unfold Ems_LCf2; reflexivity]). Qed.
Lemma D4_LCf2 : ltac2:(tb__ "0|3|
S0ScSfSbSfS16S16A2A1M0SbS18A1M1A2M2A1S8eS3S58A1S3S47A1A2SdG2S10G0G1S35SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LCf2 : ltac2:(tb__ "0|0|
S0S2S5S58S3S47A1A2S47A3"). Proof. vmr. Qed.
Lemma W4_LCf2 : ltac2:(tb__ "0|1|
S1S0S8S19S3S47A1M0A1S7A3S1S0S14S15G0A1S15S3S58A1A1A3S0S8S1bG0A1SeA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LCf2 : ltac2:(tb__ "0|1|
S0ScSbS17A1M0A1S97S47S9dS2fS47A1A3SdG0S68A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LCf2 : ltac2:(tb__ "0|0|
S0S8S9aS47S9dS2fS47A1S68S91S4S2S6S9eA4A5S7A3"). Proof. Time vmr. Qed.
Lemma HTM_LCf2 : ltac2:(tb__ "0|0|
S0S2S98S2fS47A1S9dS31S47S68A5S6dA3"). Proof. unfold TM0_LCf2, TM0_of, RM_LCf2; reflexivity. Qed.
Lemma FBM_LCf2 : ltac2:(tb__ "0|3|
S1S0S8Sa2S18S1dS15S3S47A1M0A1M1A1S1aG0A1M2A3S7A3S1S0S8Sa2S18S1dS15S3S6dA1A1A1G2A3S7A3S0S8S8cS3bG1A2S7A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LCf2 : ltac2:(tb__ "0|0|
S0S2S96S6dS1aS3S47A1A1A2S63A3"). Proof. vmr. Qed.

Lemma NX5_LCf2 : ltac2:(tb__ "0|1|
S1S0S8S8cS3bS15S3S63A1M0A1A2S7A3S0S8S1bG0A1SeA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LCf2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13Sa0SaS13A1A3S63A3S73A3"). Proof. unfold run5_LCf2; reflexivity. Qed.
Lemma L5_LCf2 : ltac2:(tb__ "0|0|
S1S0S8S24S73S9S13Sa0SaS13A1A3A2S7A3S0S2S39U0S73A2S7aA3A2"). Proof. Time (split; [vmr | unfold Erf_LCf2; reflexivity]). Qed.
Lemma AXR_LCf2 : ltac2:(tb__ "0|0|
S0ScS2A1S41S7aS87A2SdS2S4cA2A3"). Proof. Time vmr. Qed.

Lemma HER_LCf2 : ltac2:(tb__ "0|1|
S0ScSbS17A1M0A1S97S4cS9fS57A3SdG0S54A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LCf2 : ltac2:(tb__ "0|0|
S0S8S99S4cS9fS57S54S9S2Sa1SaS2A1A3A5S7A3"). Proof. Time vmr. Qed.
Lemma OBJS_LCf2 : ltac2:(tb__ "0|0|
S0SbS17A1S1eS3S4cA1A1S11S17S86S54A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LCf2 : ltac2:(tb__ "0|0|
S0S2S7eS96S98S57S9fSa1S4cS54A5S1aS3S4cA1A1A2A3"). Proof. unfold T0_LCf2, T0_of; reflexivity. Qed.
Lemma HXS_LCf2 : ltac2:(tb__ "0|0|
S0ScS2A1S41S7eS88A2SdS2S55A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LCf2 : ltac2:(tb__ "0|0|
S0SbS17A1S1eS3S55A1A1S11S17S7dS9S17S30S9S17S90S45A1S9S17S90S46A1SaS17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LCf2 : ltac2:(tb__ "0|0|
S0S2S7fS5S55Sb7S3S55A1S7dA2A2A3"). Proof. unfold T2_LCf2, T2_of, KEPT1_LCf2; reflexivity. Qed.
Lemma HTR_LCf2 : ltac2:(tb__ "0|2|
S0S2S56Sb1S7fS9S8fSb2Sb4S15S3S55A1A1M0S8dG0A1M1A3SaS8fA1A3S8dG1A1A3A3"). Proof. unfold TR_LCf2, TR_of, T2_LCf2; reflexivity. Qed.
Lemma RCHK_LCf2 : ltac2:(tb__ "0|0|
S0S8Sb3U2S7S4cS55S56S57S54Sb4A8S7A3"). Proof. Time vmr. Qed.

Lemma HTRs_LCf2 : ltac2:(tb__ "0|0|
S0S2S64Sb1S56SbdS15S3S56A1A1A3A3"). Proof. unfold TRs_LCf2, TRs_of; reflexivity. Qed.
Lemma CCHK_LCf2 : ltac2:(tb__ "0|0|
S0S8SbeU2S8S37L_;S7S33S32X8x2S56S64A4S7A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LCf2 : ltac2:(tb__ "0|0|
S0SbS4A1S38S21S9S13S3aSaS13A1A3S64A3S74A3"). Proof. unfold run5d_LCf2; reflexivity. Qed.
Lemma L5d_LCf2 : ltac2:(tb__ "0|0|
S1S0S8S24S74S9S13S3aSaS13A1A3A2S7A3S0S2S39U0S74A2S7cA3A2"). Proof. Time (split; [vmr | unfold Erq_LCf2; reflexivity]). Qed.
Lemma AXW_LCf2 : ltac2:(tb__ "0|0|
S0ScS2A1S41S7cS89A2SdS2S7bA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LCf2 : ltac2:(tb__ "0|0|
S0S8S36S7bSbcA2S7A3"). Proof. Time vmr. Qed.

Lemma Wa_LCf2 : ltac2:(tb__ "0|0|
S0S8S19Sa5S3eU2A1S3dA2A1S7A3"). Proof. vmr. Qed.
Lemma Da_LCf2 : ltac2:(tb__ "0|5|
S0ScSfSbSfS16S16A2M0A1M1SbS18A1M2A2M3A1S8eS3S40S3fS3eU2A1M4S3dA3A1Sa5G4S3dA2A2SdG3S10G1G2S9G0S10S16S16S1fP18A1S1cSbaA1A4SaG0A1A3SaS18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LCf2 : ltac2:(tb__ "0|0|
S0S8S19Sa8S3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma Wc_LCf2 : ltac2:(tb__ "0|0|
S0S8S19Sa9S3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma Wd_LCf2 : ltac2:(tb__ "0|0|
S0S8S19SaaS3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma Fb_LCf2 : ltac2:(tb__ "0|0|
S0S8Sa2S18S1dSb9A1Sa6SeS3eU2A1S3dS43S7A1A4A3S7A3"). Proof. vmr. Qed.
Lemma XI_LCf2 : ltac2:(tb__ "0|4|
S0ScS2A1S41SabSeS3eU2M0A1M1S3dS42S7A1M2S43S7A1M3A5Sa4G0S12S8fG2A2A2A2SdS2Sa7SeG1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LCf2 : ltac2:(tb__ "0|0|
S0S8S8cS3bS15S3S5aA1A1A2S7A3"). Proof. vmr. Qed.
Definition Cert1m_LCf2__runs : ltac2:(tb__ "0|0|
SbScSbS4A1A1A1") := ltac2:(tb__ "0|0|
Sb8S3cS21S9S13S25SaS13A1A3S9S2S5aSaS2A1A3A4").
Lemma Cert1m_LCf2 : ltac2:(tb__ "0|0|
S0S8S94S3cS21S9S13S25SaS13A1A3S3bS9S2S5aSaS2A1A3S65A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LCf2] exits1_LCf2 Cert1m_LCf2__runs); [unfold Cert1m_LCf2__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LCf2 : ltac2:(tb__ "0|2|
S0S8S95S3cS21S9S13S25SaS13A1A3S3bS9S92S93S5aZ1S1cZ0M0A1M1A3SaS92A1A3S91S2S92S2S93R1G0G1A3LE;S65A4A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LCf2 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf2) Cert1m_LCf2__runs); [unfold Cert1m_LCf2__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LCf2 : ltac2:(tb__ "0|0|
S0S8S19SadS3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma Wcm_LCf2 : ltac2:(tb__ "0|0|
S0S8S19SaeS3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma Wdm_LCf2 : ltac2:(tb__ "0|0|
S0S8S19SafS3eU2A1S3dS42S7A1A3A1S7A3"). Proof. vmr. Qed.
Lemma XIm_LCf2 : ltac2:(tb__ "0|4|
S0ScS2A1S41Sb0SeS3eU2M0A1M1S3dS42S7A1M2S43S7A1M3A5Sa4G0S12S8fG2A2A2A2SdS2SacSeG1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cLCf2.

(* [comment removed for export] *)
Module F0A_aLCf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m4.F0A_cLCf2"; "ED_LCf2_1"; "ED_LCf2_2"; "ED_LCf2_3"; "ED_LCf2_4"; "TD_LCf2_1"; "TD_LCf2_2"; "TD_LCf2_3"; "TD_LCf2_4"; "P0_LCf2"; "PMID_LCf2"; "TM_LCf2"; "exits1_LCf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m4.F0A_aLCf2.ALCf2"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m4.F0A_cLCf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ld.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALCf2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS23Vsegs;Vok;S25Vsegs;S2dU2S1S16R6VKc;R5A6S4aR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS22Vsegs;S25Vsegs;S2dU2S1S16R6VKc;R5A6S4aR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6S2aSbS37S2aR2S4bA3S23Vsegs;R13S25Vsegs;S2dG1S1SfR12R11RfA6R3R2ReA5RdA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_LCf2 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_LCf2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 2 UStopLe false keep ok A Kc rho rho1 Ebg_LCf2 Q BGF_LCf2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2 UStopLe false Eps_LCf2 C3_LCf2 Ems_LCf2 C4_LCf2 TM0_LCf2 run4_LCf2 RM_LCf2 D3_LCf2 W3_LCf2 EQ3_LCf2 NX3b_LCf2 RUN4_LCf2 L4_LCf2 D4_LCf2 W4_LCf2 EQ4_LCf2
             HeM_LCf2 HchkM_LCf2 HTM_LCf2 FBM_LCf2 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LCf2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2 UStopLe true S1c_LCf2_1 C2_LCf2_1 EfD_LCf2_1 ED_LCf2_1 run2_LCf2_1 D2_LCf2_1 W2_LCf2_1 NX2_LCf2_1 EQ2_LCf2_1 RUN2_LCf2_1 L2_LCf2_1 AXD_LCf2_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCf2_1 TDr_LCf2_1 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_1 ENTD_LCf2_1 RUN3_LCf2 L3_LCf2 NX3_LCf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCf2_2 C2_LCf2_2 EfD_LCf2_2 ED_LCf2_2 run2_LCf2_2 D2_LCf2_2 W2_LCf2_2 NX2_LCf2_2 EQ2_LCf2_2 RUN2_LCf2_2 L2_LCf2_2 AXD_LCf2_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCf2_2 TDr_LCf2_2 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_2 ENTD_LCf2_2 RUN3_LCf2 L3_LCf2 NX3_LCf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCf2_3 C2_LCf2_3 EfD_LCf2_3 ED_LCf2_3 run2_LCf2_3 D2_LCf2_3 W2_LCf2_3 NX2_LCf2_3 EQ2_LCf2_3 RUN2_LCf2_3 L2_LCf2_3 AXD_LCf2_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCf2_3 TDr_LCf2_3 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_3 ENTD_LCf2_3 RUN3_LCf2 L3_LCf2 NX3_LCf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCf2_4 C2_LCf2_4 EfD_LCf2_4 ED_LCf2_4 run2_LCf2_4 D2_LCf2_4 W2_LCf2_4 NX2_LCf2_4 EQ2_LCf2_4 RUN2_LCf2_4 L2_LCf2_4 AXD_LCf2_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCf2_4 TDr_LCf2_4 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_4 ENTD_LCf2_4 RUN3_LCf2 L3_LCf2 NX3_LCf2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5S2aSbS37S2aR2S4bA3S22Vsegs;S25Vsegs;S2dG1S1SfR11R10ReA6R3R2RdA5RcA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_LCf2 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_LCf2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 2 UStopLe false keep A Kc rho rho1 Ebg_LCf2 Q BGF_LCf2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2 UStopLe false Eps_LCf2 C3_LCf2 Ems_LCf2 C4_LCf2 TM0_LCf2 run4_LCf2 RM_LCf2 D3_LCf2 W3_LCf2 EQ3_LCf2 NX3b_LCf2 RUN4_LCf2 L4_LCf2 D4_LCf2 W4_LCf2 EQ4_LCf2
             HeM_LCf2 HchkM_LCf2 HTM_LCf2 FBM_LCf2 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LCf2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2 UStopLe true S1c_LCf2_1 C2_LCf2_1 EfD_LCf2_1 ED_LCf2_1 run2_LCf2_1 D2_LCf2_1 W2_LCf2_1 NX2_LCf2_1 EQ2_LCf2_1 RUN2_LCf2_1 L2_LCf2_1 AXD_LCf2_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCf2_1 TDr_LCf2_1 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_1 ENTD_LCf2_1 RUN3_LCf2 L3_LCf2 NX3_LCf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCf2_2 C2_LCf2_2 EfD_LCf2_2 ED_LCf2_2 run2_LCf2_2 D2_LCf2_2 W2_LCf2_2 NX2_LCf2_2 EQ2_LCf2_2 RUN2_LCf2_2 L2_LCf2_2 AXD_LCf2_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCf2_2 TDr_LCf2_2 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_2 ENTD_LCf2_2 RUN3_LCf2 L3_LCf2 NX3_LCf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCf2_3 C2_LCf2_3 EfD_LCf2_3 ED_LCf2_3 run2_LCf2_3 D2_LCf2_3 W2_LCf2_3 NX2_LCf2_3 EQ2_LCf2_3 RUN2_LCf2_3 L2_LCf2_3 AXD_LCf2_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCf2_3 TDr_LCf2_3 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_3 ENTD_LCf2_3 RUN3_LCf2 L3_LCf2 NX3_LCf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCf2_4 C2_LCf2_4 EfD_LCf2_4 ED_LCf2_4 run2_LCf2_4 D2_LCf2_4 W2_LCf2_4 NX2_LCf2_4 EQ2_LCf2_4 RUN2_LCf2_4 L2_LCf2_4 AXD_LCf2_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCf2_4 TDr_LCf2_4 CD_LCf2 Eps_LCf2 Ebg_LCf2 run3_LCf2 AXDr_LCf2_4 ENTD_LCf2_4 RUN3_LCf2 L3_LCf2 NX3_LCf2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1SfR10RfRdA6S48R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true P0_LCf2 exits1_LCf2 Cert1_LCf2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1SfRfReRcA6S48R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true P0_LCf2 exits1_LCf2 NX0_LCf2 ECert1_LCf2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Theorem free_spine_m_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbS10SeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1SfR10RfRdA6S49R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true PMID_LCf2 exits1_LCf2 Cert1m_LCf2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_m_LCf2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1SfRfReRcA6S49R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true PMID_LCf2 exits1_LCf2 NX0m_LCf2 ECert1m_LCf2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1fS4fS56R2A2S1cS27S31R2A2S29R2S32A2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS57R2A1A1F_;Fa;").

Theorem hdf_LCf2_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S40S44R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_1 TD_LCf2_1 (sD_of ED_LCf2_1 1) RD_LCf2_1 HeD_LCf2_1 HchkD_LCf2_1 HTD_LCf2_1 DCHK_LCf2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf2_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S40S44R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_1 TD_LCf2_1 (sD_of ED_LCf2_1 1) RD_LCf2_1 HeD_LCf2_1 HchkD_LCf2_1 HTD_LCf2_1 DCHK_LCf2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_LCf2_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S41S45R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_2 TD_LCf2_2 (sD_of ED_LCf2_2 2) RD_LCf2_2 HeD_LCf2_2 HchkD_LCf2_2 HTD_LCf2_2 DCHK_LCf2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf2_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S41S45R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_2 TD_LCf2_2 (sD_of ED_LCf2_2 2) RD_LCf2_2 HeD_LCf2_2 HchkD_LCf2_2 HTD_LCf2_2 DCHK_LCf2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_LCf2_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S42S46R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_3 TD_LCf2_3 (sD_of ED_LCf2_3 3) RD_LCf2_3 HeD_LCf2_3 HchkD_LCf2_3 HTD_LCf2_3 DCHK_LCf2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf2_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S42S46R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_3 TD_LCf2_3 (sD_of ED_LCf2_3 3) RD_LCf2_3 HeD_LCf2_3 HchkD_LCf2_3 HTD_LCf2_3 DCHK_LCf2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.
Theorem hdf_LCf2_4 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S43S47R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC true) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_4 TD_LCf2_4 (sD_of ED_LCf2_4 4) RD_LCf2_4 HeD_LCf2_4 HchkD_LCf2_4 HTD_LCf2_4 DCHK_LCf2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf2_4 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33SfRfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S43S47R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC true) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf2_4 TD_LCf2_4 (sD_of ED_LCf2_4 4) RD_LCf2_4 HeD_LCf2_4 HchkD_LCf2_4 HTD_LCf2_4 DCHK_LCf2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 2) Q).
Qed.

Lemma tail_LCf2 : ltac2:(tb__ "0|3|
S20OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S26SaRcS24RaA1A3S4dSaRdS24RbA1A3S52ReRcA2S30SaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S37S12S0S0A2S11S0S0ReRdA4S18R12A1A3S3aRfReA2S1bS13S19R14A1SfA3S33SfR15A2S2eR14S34R16R14R12R11R10RfA6A2S1bS0S3cR10A1S3fA3S50S39VCST;VXGL;R18A3R19R18R17S34R18R16R14R13R12R11A6S36SaS4eR16R15S14S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 2 true CST XGL HCST HXGL TM_LCf2 Erf_LCf2 EC_LCf2 run5_LCf2 XR_LCf2 NX5_LCf2 RUN5_LCf2 L5_LCf2 AXR_LCf2 T0_LCf2 T1_LCf2 T2_LCf2 TR_LCf2 sR_LCf2 RR_LCf2 KEPT_LCf2 KEPT1_LCf2 XS_LCf2 eFRc HER_LCf2 Hchk_LCf2 OBJS_LCf2 HT0_LCf2 HXS_LCf2 OBJS1_LCf2 HT2_LCf2 HTR_LCf2 RCHK_LCf2 TRs_LCf2 Erq_LCf2 Erq2_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.TQ_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.Edr_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.Xf_L2Bf run5d_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.run6_L2Bf XW_LCf2 HTRs_LCf2 CCHK_LCf2 RUN5d_LCf2 L5d_LCf2 AXW_LCf2 ENTQ_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.NX6_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.RUN6_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.L6_L2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Bf.f0_drain_L2Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Bf.f0_exit_L2Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LCf2 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S53RaA1S30SaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S37S12S0S0A2S11S0S0RcRbA4S18R10A1A3S3aRdRcA2S1bS13S19R12A1SfA3S33SfR13A2S2eR12S34R14R12R10RfReRdA6A2S1bS0S3cReA1S3fA3S51S39VCST;VXGL;R16A3R16R15S34R16R14R12R11R10RfA6S36SaS4eR14R13S14S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 2 true CST XGL HCST HXGL TM_LCf2 Erf_LCf2 EC_LCf2 run5_LCf2 XR_LCf2 NX5_LCf2 RUN5_LCf2 L5_LCf2 AXR_LCf2 T0_LCf2 T1_LCf2 T2_LCf2 TR_LCf2 sR_LCf2 RR_LCf2 KEPT_LCf2 KEPT1_LCf2 XS_LCf2 eFRc HER_LCf2 Hchk_LCf2 OBJS_LCf2 HT0_LCf2 HXS_LCf2 OBJS1_LCf2 HT2_LCf2 HTR_LCf2 RCHK_LCf2 TRs_LCf2 Erq_LCf2 Erq2_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.TQ_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.Edr_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.Xf_L2Bf run5d_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.run6_L2Bf XW_LCf2 HTRs_LCf2 CCHK_LCf2 RUN5d_LCf2 L5d_LCf2 AXW_LCf2 ENTQ_LCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.NX6_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.RUN6_L2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf.L6_L2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Bf.ef0_drain_L2Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Bf.ef0_exit_L2Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Cf_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S28R6R5A2S3eA2S1bS13S19RbA1SfA3S33SfRcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 2) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate false 2 UStopLe (NVC true) (VFC true) Wa_LCf2 Da_LCf2 Wb_LCf2 Wc_LCf2 Wd_LCf2 Fb_LCf2 XI_LCf2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_LCf2 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_LCf2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LCf2 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_Cf_2 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S27S28R4R3A2S3eA2S1bS13S19R9A1SfA3S33SfRaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 2) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate false 2 UStopLe (NVC true) (VFC true) Wa_LCf2 Da_LCf2 Wb_LCf2 Wc_LCf2 Wd_LCf2 Fb_LCf2 XI_LCf2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_LCf2 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_LCf2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_LCf2 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1cS1dS1cS27S31R2A2S29R2S32A2A2A1S1dS1cS27Z17db48R2A2S29R2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_Cf_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S28R6R5A2S3eA2S1bS13S19RbA1S16A3S33SfRcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Certi_2A ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instG_facts false (Wcan 2) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 2 UStopLe (NVC true) (VFC true) Wbm_LCf2 Wcm_LCf2 Wdm_LCf2 Fb_LCf2 XIm_LCf2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_LCf2 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_LCf2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LCf2 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_Cf_2 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S14S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S21S3R6A1S27S28R4R3A2S3eA2S1bS13S19R9A1S16A3S33SfRaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Dai_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wbi_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.Wci_2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m2A.ECerti_2A A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instG_facts false (Wcan 2) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false 2 UStopLe (NVC true) (VFC true) Wbm_LCf2 Wcm_LCf2 Wdm_LCf2 Fb_LCf2 XIm_LCf2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_LCf2 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_LCf2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_LCf2 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALCf2.
End F0A_aLCf2.

