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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq la lo.

(* [comment removed for export] *)
Module F0A_cCf1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "false"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "BIGX"; "F_typ"; "MSE"; "PSE"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cCf1"; "C4_Cf1"; "ED_Cf1_1"; "ED_Cf1_2"; "ED_Cf1_3"; "EC_Cf1"; "C2_Cf1_1"; "C2_Cf1_2"; "C2_Cf1_3"; "C3_Cf1"; "P0_Cf1"; "CD_Cf1"; "RR_Cf1"; "T1_Cf1"; "TR_Cf1"; "sR_Cf1"; "Ems_Cf1"; "Eps_Cf1"; "PMID_Cf1"; "RD_Cf1_1"; "RD_Cf1_2"; "RD_Cf1_3"; "S1c_Cf1_1"; "S1c_Cf1_2"; "S1c_Cf1_3"; "TM_Cf1"; "TRs_Cf1"; "exits1_Cf1"; "run3_Cf1"; "RM_Cf1"; "TD_Cf1_1"; "TD_Cf1_2"; "TD_Cf1_3"; "TM0_Cf1"; "run1_Cf1"; "run2_Cf1_1"; "run2_Cf1_2"; "run2_Cf1_3"; "run4_Cf1"; "run5_Cf1"; "run5d_Cf1"; "Ebg_Cf1"; "EfD_Cf1_1"; "EfD_Cf1_2"; "EfD_Cf1_3"; "Erf_Cf1"; "Erq2_Cf1"; "Erq_Cf1"; "KEPT1_Cf1"; "T0_Cf1"; "T2_Cf1"; "TDr_Cf1_1"; "TDr_Cf1_2"; "TDr_Cf1_3"; "W_Cf1"; "st_Cf1"; "KEPT_Cf1"; "XR_Cf1"; "XS_Cf1"; "XW_Cf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg";
"sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "TQ_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_Cf1 : list ulink := Wcan 1.
Definition st_Cf1 : ustop := UStopLe.
Definition P0_Cf1 : axst := ltac2:(tb__ "0|0|
SadS2S76S77S2A4").

Definition run1_Cf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S25S5S13A1A3S4aA3").

Definition S1c_Cf1_1 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z1A3").
Definition C2_Cf1_1 : axst := C2_of S1c_Cf1_1.
Definition run2_Cf1_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S46A3").
Definition EfD_Cf1_1 : axst := leaf 0 run2_Cf1_1.
Definition ED_Cf1_1 : axst := ED_of EfD_Cf1_1.
Definition RD_Cf1_1 : list sobj := RD_of ED_Cf1_1 1.
Definition TD_Cf1_1 : axst := TD_of ED_Cf1_1 1.
Definition TDr_Cf1_1 : axst := TDr_of TD_Cf1_1.
Definition S1c_Cf1_2 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z2A3").
Definition C2_Cf1_2 : axst := C2_of S1c_Cf1_2.
Definition run2_Cf1_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S47A3").
Definition EfD_Cf1_2 : axst := leaf 0 run2_Cf1_2.
Definition ED_Cf1_2 : axst := ED_of EfD_Cf1_2.
Definition RD_Cf1_2 : list sobj := RD_of ED_Cf1_2 2.
Definition TD_Cf1_2 : axst := TD_of ED_Cf1_2 2.
Definition TDr_Cf1_2 : axst := TDr_of TD_Cf1_2.
Definition S1c_Cf1_3 : axst := ltac2:(tb__ "0|0|
S2aS39U0S62A2S1aSfS4aA1A1Z3A3").
Definition C2_Cf1_3 : axst := C2_of S1c_Cf1_3.
Definition run2_Cf1_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S23S5S13A1A3S48A3").
Definition EfD_Cf1_3 : axst := leaf 0 run2_Cf1_3.
Definition ED_Cf1_3 : axst := ED_of EfD_Cf1_3.
Definition RD_Cf1_3 : list sobj := RD_of ED_Cf1_3 3.
Definition TD_Cf1_3 : axst := TD_of ED_Cf1_3 3.
Definition TDr_Cf1_3 : axst := TDr_of TD_Cf1_3.
Definition exits1_Cf1 : list axst := ltac2:(tb__ "0|0|
S4SeS56S4SeS57S4SeS58S5SeA1A3A3A3").

Definition CD_Cf1 : axst := CD_of TDr_Cf1_1.
Definition run3_Cf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S29S4S13S26S5S13A1A3A3S4bA3").
Definition Eps_Cf1 : axst := leaf 0 run3_Cf1.
Definition Ebg_Cf1 : axst := leaf 1 run3_Cf1.
Definition C3_Cf1 : axst := C3_of Eps_Cf1.
Definition run4_Cf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S28S5S13A1A3S49A3").
Definition Ems_Cf1 : axst := leaf 0 run4_Cf1.
Definition C4_Cf1 : axst := C4_of Ems_Cf1.
Definition RM_Cf1 : list sobj := RM_of C4_Cf1.
Definition TM0_Cf1 : axst := TM0_of C4_Cf1.
Definition TM_Cf1 : axst := TM_of C4_Cf1.

Definition run5_Cf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S97S5S13A1A3S59A3").
Definition Erf_Cf1 : axst := leaf 0 run5_Cf1.
Definition XR_Cf1 : list axform := XRC Erf_Cf1.
Definition EC_Cf1 : axst := EC_of Erf_Cf1.
Definition sR_Cf1 : wsub := sR_of (E3_of Erf_Cf1).
Definition RR_Cf1 : list sobj := RR_of EC_Cf1 sR_Cf1.
Definition KEPT_Cf1 : list sobj := KEPT_of EC_Cf1 RR_Cf1.

Definition T0_Cf1 : axst := ltac2:(tb__ "0|0|
SaeS45S4fS4cA3").
Definition XS_Cf1 : list axform := XS_of T0_Cf1.
Definition T1_Cf1 : axst := T1_of T0_Cf1.
Definition KEPT1_Cf1 : list sobj := KEPT1_of T1_Cf1.
Definition T2_Cf1 : axst := T2_of T1_Cf1.
Definition TR_Cf1 : axst := TR_of T1_Cf1.

Definition TRs_Cf1 : axst := TRs_of TR_Cf1.
Definition run5d_Cf1 : list leafA := ltac2:(tb__ "0|0|
S38S21S4S13S3aS5S13A1A3S5aA3").
Definition Erq_Cf1 : axst := leaf 0 run5d_Cf1.
Definition XW_Cf1 : list axform := XW Erq_Cf1.
Definition Erq2_Cf1 : axst := Erq2_of Erq_Cf1.

Definition PMID_Cf1 : axst := ltac2:(tb__ "0|0|
Sa4S2S76S77S88S86S17S87S7cS2A1A4S7dS2A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_Cf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS4aA1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_Cf1 : ltac2:(tb__ "0|0|
S0S3S8cS40S21S4S13S25S5S13A1A3S3fS4SeS4aS5SeA1A3S5bA6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_Cf1 exits1_Cf1 run1_Cf1); [unfold run1_Cf1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_Cf1 : ltac2:(tb__ "0|2|
S0S3S8dS40S21S4S13S25S5S13A1A3S3fS4S8aS8bS4aZ1S1cZ0M0A1M1A3S5S8aA1A3S88SeS8aSeS8bR1G0G1A3LE;S5bA4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_Cf1 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf1) run1_Cf1); [unfold run1_Cf1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_Cf1_1 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS56A1SfS46A1A2S8G3SaG1G2S4G0SaS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf1_1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS46A1M0A1S2A3S1S0S14S15G0A1S15SfS56A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf1_1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS46A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf1_1 : ltac2:(tb__ "0|0|
S0SeS11S56SfS46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_Cf1_1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S46A3S63A3"). Proof. unfold run2_Cf1_1; reflexivity. Qed.
Lemma L2_Cf1_1 : ltac2:(tb__ "0|0|
S1S0S3S24S63S4S13S23S5S13A1A3A2S2A3S0SeS39U0S63A2S6aA3A2"). Proof. Time (split; [vmr | unfold EfD_Cf1_1; reflexivity]). Qed.
Lemma AXD_Cf1_1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6aS2bA2S8SeS42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf1_1 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS42S82Z1M1A1S22S42G1A2A3S8G0S53A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf1_1 : ltac2:(tb__ "0|1|
S0S3S91S42S82Z1M0A1S22S42G0A2S53S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf1_1 : ltac2:(tb__ "0|1|
S0SeS5eS8eS90S22S42Z1M0A2S82G0A1S83G0A1S42S53A5S1aSfS42A1A1A2A3").
Proof. unfold TD_Cf1_1, TD_of, RD_Cf1_1; reflexivity. Qed.
Lemma DCHK_Cf1_1 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z1M1S42S5eS22S42G1A2S53A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf1_1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S5eS2cA2S8SeS73A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf1_1 : ltac2:(tb__ "0|0|
S0S3S99S73S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf1_2 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS57A1SfS47A1A2S8G3SaG1G2S4G0SaS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf1_2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS47A1M0A1S2A3S1S0S14S15G0A1S15SfS57A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf1_2 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS47A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf1_2 : ltac2:(tb__ "0|0|
S0SeS11S57SfS47A1A2S47A3"). Proof. vmr. Qed.
Lemma RUN2_Cf1_2 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S47A3S64A3"). Proof. unfold run2_Cf1_2; reflexivity. Qed.
Lemma L2_Cf1_2 : ltac2:(tb__ "0|0|
S1S0S3S24S64S4S13S23S5S13A1A3A2S2A3S0SeS39U0S64A2S6bA3A2"). Proof. Time (split; [vmr | unfold EfD_Cf1_2; reflexivity]). Qed.
Lemma AXD_Cf1_2 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6bS2bA2S8SeS43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf1_2 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS43S82Z2M1A1S22S43G1A2A3S8G0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf1_2 : ltac2:(tb__ "0|1|
S0S3S91S43S82Z2M0A1S22S43G0A2S54S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf1_2 : ltac2:(tb__ "0|1|
S0SeS5fS8eS90S22S43Z2M0A2S82G0A1S83G0A1S43S54A5S1aSfS43A1A1A2A3").
Proof. unfold TD_Cf1_2, TD_of, RD_Cf1_2; reflexivity. Qed.
Lemma DCHK_Cf1_2 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z2M1S43S5fS22S43G1A2S54A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf1_2 : ltac2:(tb__ "0|0|
S0S7SeA1S81S5fS2cA2S8SeS74A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf1_2 : ltac2:(tb__ "0|0|
S0S3S99S74S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf1_3 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS58A1SfS48A1A2S8G3SaG1G2S4G0SaS16S16S2dS2fA4S5G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf1_3 : ltac2:(tb__ "0|1|
S1S0S3S19SfS48A1M0A1S2A3S1S0S14S15G0A1S15SfS58A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf1_3 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS48A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf1_3 : ltac2:(tb__ "0|0|
S0SeS11S58SfS48A1A2S48A3"). Proof. vmr. Qed.
Lemma RUN2_Cf1_3 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S23S5S13A1A3S48A3S65A3"). Proof. unfold run2_Cf1_3; reflexivity. Qed.
Lemma L2_Cf1_3 : ltac2:(tb__ "0|0|
S1S0S3S24S65S4S13S23S5S13A1A3A2S2A3S0SeS39U0S65A2S6cA3A2"). Proof. Time (split; [vmr | unfold EfD_Cf1_3; reflexivity]). Qed.
Lemma AXD_Cf1_3 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6cS2bA2S8SeS44A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf1_3 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S8fS44S82Z3M1A1S22S44G1A2A3S8G0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf1_3 : ltac2:(tb__ "0|1|
S0S3S91S44S82Z3M0A1S22S44G0A2S55S4SeS83G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf1_3 : ltac2:(tb__ "0|1|
S0SeS60S8eS90S22S44Z3M0A2S82G0A1S83G0A1S44S55A5S1aSfS44A1A1A2A3").
Proof. unfold TD_Cf1_3, TD_of, RD_Cf1_3; reflexivity. Qed.
Lemma DCHK_Cf1_3 : ltac2:(tb__ "0|2|
S0S3S95U1M0S7eS7cS2A1G0A2Z3M1S44S60S22S44G1A2S55A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf1_3 : ltac2:(tb__ "0|0|
S0S7SeA1S81S60S2cA2S8SeS75A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf1_3 : ltac2:(tb__ "0|0|
S0S3S99S75S4bA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_Cf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S29S4S13S26S5S13A1A3A3S4bA3S5cA3"). Proof. unfold run3_Cf1; reflexivity. Qed.
Lemma L3_Cf1 : ltac2:(tb__ "0|0|
S1S0S3S24S5cS4S13S29S4S13S26S5S13A1A3A3A2S2A3S1S0SeS39U0S5cA2S51A3S0SeS39U1S5cA2S69A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_Cf1 | unfold Ebg_Cf1]; reflexivity]). Qed.
Lemma NX3_Cf1 : ltac2:(tb__ "0|1|
S1S0S3S84S3fS15SfS4bA1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_Cf1 : ltac2:(tb__ "0|0|
S0S3S9bS18S20Sb3A1S1aSfS69A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_Cf1 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S89SfS51A1SfS49A1A2S8G2SaG0G1S34S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_Cf1 : ltac2:(tb__ "0|0|
S0SeS11S51SfS49A1A2S49A3"). Proof. vmr. Qed.
Lemma NX3b_Cf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS49A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_Cf1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS49A1M0A1S2A3S1S0S14S15G0A1S15SfS51A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_Cf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S28S5S13A1A3S49A3S66A3"). Proof. unfold run4_Cf1; reflexivity. Qed.
Lemma L4_Cf1 : ltac2:(tb__ "0|0|
S1S0S3S24S66S4S13S28S5S13A1A3A2S2A3S0SeS39U0S66A2S50A3A2"). Proof. Time (split; [vmr | unfold Ems_Cf1; reflexivity]). Qed.
Lemma D4_Cf1 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S89SfS50A1SfS41A1A2S8G2SaG0G1S35S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_Cf1 : ltac2:(tb__ "0|0|
S0SeS11S50SfS41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_Cf1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS41A1M0A1S2A3S1S0S14S15G0A1S15SfS50A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_Cf1 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S8fS41S93S2eS41A1A3S8G0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_Cf1 : ltac2:(tb__ "0|0|
S0S3S92S41S93S2eS41A1S5dS88S10SeS12S94A4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_Cf1 : ltac2:(tb__ "0|0|
S0SeS90S2eS41A1S93S31S41S5dA5S61A3"). Proof. unfold TM0_Cf1, TM0_of, RM_Cf1; reflexivity. Qed.
Lemma FBM_Cf1 : ltac2:(tb__ "0|3|
S1S0S3S9aS18S1dS15SfS41A1M0A1M1A1S1aG0A1M2A3S2A3S1S0S3S9aS18S1dS15SfS61A1A1A1G2A3S2A3S0S3S84S3fG1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_Cf1 : ltac2:(tb__ "0|0|
S0SeS8eS61S1aSfS41A1A1A2S59A3"). Proof. vmr. Qed.

Lemma NX5_Cf1 : ltac2:(tb__ "0|1|
S1S0S3S84S3fS15SfS59A1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_Cf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S97S5S13A1A3S59A3S67A3"). Proof. unfold run5_Cf1; reflexivity. Qed.
Lemma L5_Cf1 : ltac2:(tb__ "0|0|
S1S0S3S24S67S4S13S97S5S13A1A3A2S2A3S0SeS39U0S67A2S6dA3A2"). Proof. Time (split; [vmr | unfold Erf_Cf1; reflexivity]). Qed.
Lemma AXR_Cf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6dS79A2S8SeS45A2A3"). Proof. Time vmr. Qed.

Lemma HER_Cf1 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S8fS45S96S4fA3S8G0S4cA2A3"). Proof. Time vmr. Qed.
Lemma Hchk_Cf1 : ltac2:(tb__ "0|0|
S0S3S91S45S96S4fS4cS4SeS98S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_Cf1 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS45A1A1ScS17S78S4cA3A3"). Proof. Time vmr. Qed.
Lemma HT0_Cf1 : ltac2:(tb__ "0|0|
S0SeS71S8eS90S4fS96S98S45S4cA5S1aSfS45A1A1A2A3"). Proof. unfold T0_Cf1, T0_of; reflexivity. Qed.
Lemma HXS_Cf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S71S7aA2S8SeS4dA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_Cf1 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS4dA1A1ScS17S70S4S17S30S4S17S87S7fA1S4S17S87S80A1S5S17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_Cf1 : ltac2:(tb__ "0|0|
S0SeS72S11S4dSafSfS4dA1S70A2A2A3"). Proof. unfold T2_Cf1, T2_of, KEPT1_Cf1; reflexivity. Qed.
Lemma HTR_Cf1 : ltac2:(tb__ "0|2|
S0SeS4eSa9S72S4S86SaaSacS15SfS4dA1A1M0S85G0A1M1A3S5S86A1A3S85G1A1A3A3"). Proof. unfold TR_Cf1, TR_of, T2_Cf1; reflexivity. Qed.
Lemma RCHK_Cf1 : ltac2:(tb__ "0|0|
S0S3SabU1S2S45S4dS4eS4fS4cSacA8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_Cf1 : ltac2:(tb__ "0|0|
S0SeS5aSa9S4eSb5S15SfS4eA1A1A3A3"). Proof. unfold TRs_Cf1, TRs_of; reflexivity. Qed.
Lemma CCHK_Cf1 : ltac2:(tb__ "0|0|
S0S3Sb6U1S3S37L_;S2S33S32X3x2S4eS5aA4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_Cf1 : ltac2:(tb__ "0|0|
S0S6S10A1S38S21S4S13S3aS5S13A1A3S5aA3S68A3"). Proof. unfold run5d_Cf1; reflexivity. Qed.
Lemma L5d_Cf1 : ltac2:(tb__ "0|0|
S1S0S3S24S68S4S13S3aS5S13A1A3A2S2A3S0SeS39U0S68A2S6fA3A2"). Proof. Time (split; [vmr | unfold Erq_Cf1; reflexivity]). Qed.
Lemma AXW_Cf1 : ltac2:(tb__ "0|0|
S0S7SeA1S81S6fS7bA2S8SeS6eA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_Cf1 : ltac2:(tb__ "0|0|
S0S3S36S6eSb4A2S2A3"). Proof. Time vmr. Qed.

Lemma Wa_Cf1 : ltac2:(tb__ "0|0|
S0S3S19S9dS3cU1A1S3bA2A1S2A3"). Proof. vmr. Qed.
Lemma Da_Cf1 : ltac2:(tb__ "0|5|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S89SfS3eS3dS3cU1A1M4S3bA3A1S9dG4S3bA2A2S8G3SaG1G2S4G0SaS16S16S1fP18A1S1cSb2A1A4S5G0A1A3S5S18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa0S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa1S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa2S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_Cf1 : ltac2:(tb__ "0|0|
S0S3S9aS18S1dSb1A1S9eS2S3cU1A1S3bS7dS2A1A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_Cf1 : ltac2:(tb__ "0|4|
S0S7SeA1S81Sa3S2S3cU1M0A1M1S3bS7cS2A1M2S7dS2A1M3A5S9cG0SdS86G2A2A2A2S8SeS9fS2G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_Cf1 : ltac2:(tb__ "0|0|
S0S3S84S3fS15SfS52A1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_Cf1__runs : ltac2:(tb__ "0|0|
S6S7S6S10A1A1A1") := ltac2:(tb__ "0|0|
Sb0S40S21S4S13S25S5S13A1A3S4SeS52S5SeA1A3A4").
Lemma Cert1m_Cf1 : ltac2:(tb__ "0|0|
S0S3S8cS40S21S4S13S25S5S13A1A3S3fS4SeS52S5SeA1A3S5bA6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_Cf1] exits1_Cf1 Cert1m_Cf1__runs); [unfold Cert1m_Cf1__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_Cf1 : ltac2:(tb__ "0|2|
S0S3S8dS40S21S4S13S25S5S13A1A3S3fS4S8aS8bS52Z1S1cZ0M0A1M1A3S5S8aA1A3S88SeS8aSeS8bR1G0G1A3LE;S5bA4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_Cf1 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf1) Cert1m_Cf1__runs); [unfold Cert1m_Cf1__runs; reflexivity | vmr]. Qed.
Lemma Wbm_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa5S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa6S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_Cf1 : ltac2:(tb__ "0|0|
S0S3S19Sa7S3cU1A1S3bS7cS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_Cf1 : ltac2:(tb__ "0|4|
S0S7SeA1S81Sa8S2S3cU1M0A1M1S3bS7cS2A1M2S7dS2A1M3A5S9cG0SdS86G2A2A2A2S8SeSa4S2G1S3bS88S86S17S87G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cCf1.

(* [comment removed for export] *)
Module F0A_aCf1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cCf1"; "ED_Cf1_1"; "ED_Cf1_2"; "ED_Cf1_3"; "TD_Cf1_1"; "TD_Cf1_2"; "TD_Cf1_3"; "P0_Cf1"; "PMID_Cf1"; "TM_Cf1"; "exits1_Cf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_aCf1.ACf1"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cCf1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACf1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S34U1S1S16R6VKc;R5A6S45R1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S36VA;R3A2S53Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S34U1S1S16R6VKc;R5A6S45R1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6S23SbS3aS23R2S46A3S27Vsegs;R12S29Vsegs;S34G1S1SfR11R10ReA6R3R2RdA5RcA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_Cf1 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_Cf1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 1 UStopLe false keep ok A Kc rho rho1 Ebg_Cf1 Q BGF_Cf1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1 UStopLe false Eps_Cf1 C3_Cf1 Ems_Cf1 C4_Cf1 TM0_Cf1 run4_Cf1 RM_Cf1 D3_Cf1 W3_Cf1 EQ3_Cf1 NX3b_Cf1 RUN4_Cf1 L4_Cf1 D4_Cf1 W4_Cf1 EQ4_Cf1
             HeM_Cf1 HchkM_Cf1 HTM_Cf1 FBM_Cf1 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_Cf1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1 UStopLe true S1c_Cf1_1 C2_Cf1_1 EfD_Cf1_1 ED_Cf1_1 run2_Cf1_1 D2_Cf1_1 W2_Cf1_1 NX2_Cf1_1 EQ2_Cf1_1 RUN2_Cf1_1 L2_Cf1_1 AXD_Cf1_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Cf1_1 TDr_Cf1_1 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_1 ENTD_Cf1_1 RUN3_Cf1 L3_Cf1 NX3_Cf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_Cf1_2 C2_Cf1_2 EfD_Cf1_2 ED_Cf1_2 run2_Cf1_2 D2_Cf1_2 W2_Cf1_2 NX2_Cf1_2 EQ2_Cf1_2 RUN2_Cf1_2 L2_Cf1_2 AXD_Cf1_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Cf1_2 TDr_Cf1_2 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_2 ENTD_Cf1_2 RUN3_Cf1 L3_Cf1 NX3_Cf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1 UStopLe true S1c_Cf1_3 C2_Cf1_3 EfD_Cf1_3 ED_Cf1_3 run2_Cf1_3 D2_Cf1_3 W2_Cf1_3 NX2_Cf1_3 EQ2_Cf1_3 RUN2_Cf1_3 L2_Cf1_3 AXD_Cf1_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1 UStopLe false TD_Cf1_3 TDr_Cf1_3 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_3 ENTD_Cf1_3 RUN3_Cf1 L3_Cf1 NX3_Cf1
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5S23SbS3aS23R2S46A3S26Vsegs;S29Vsegs;S34G1S1SfR10RfRdA6R3R2RcA5RbA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 1) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Eps_Cf1 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 1 UStopLe false A' Kc rho1') Ebg_Cf1 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 1 UStopLe false keep A Kc rho rho1 Ebg_Cf1 Q BGF_Cf1 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1 UStopLe false Eps_Cf1 C3_Cf1 Ems_Cf1 C4_Cf1 TM0_Cf1 run4_Cf1 RM_Cf1 D3_Cf1 W3_Cf1 EQ3_Cf1 NX3b_Cf1 RUN4_Cf1 L4_Cf1 D4_Cf1 W4_Cf1 EQ4_Cf1
             HeM_Cf1 HchkM_Cf1 HTM_Cf1 FBM_Cf1 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_Cf1. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf1 in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1 UStopLe true S1c_Cf1_1 C2_Cf1_1 EfD_Cf1_1 ED_Cf1_1 run2_Cf1_1 D2_Cf1_1 W2_Cf1_1 NX2_Cf1_1 EQ2_Cf1_1 RUN2_Cf1_1 L2_Cf1_1 AXD_Cf1_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Cf1_1 TDr_Cf1_1 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_1 ENTD_Cf1_1 RUN3_Cf1 L3_Cf1 NX3_Cf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_Cf1_2 C2_Cf1_2 EfD_Cf1_2 ED_Cf1_2 run2_Cf1_2 D2_Cf1_2 W2_Cf1_2 NX2_Cf1_2 EQ2_Cf1_2 RUN2_Cf1_2 L2_Cf1_2 AXD_Cf1_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Cf1_2 TDr_Cf1_2 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_2 ENTD_Cf1_2 RUN3_Cf1 L3_Cf1 NX3_Cf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1 UStopLe true S1c_Cf1_3 C2_Cf1_3 EfD_Cf1_3 ED_Cf1_3 run2_Cf1_3 D2_Cf1_3 W2_Cf1_3 NX2_Cf1_3 EQ2_Cf1_3 RUN2_Cf1_3 L2_Cf1_3 AXD_Cf1_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1 UStopLe false TD_Cf1_3 TDr_Cf1_3 CD_Cf1 Eps_Cf1 Ebg_Cf1 run3_Cf1 AXDr_Cf1_3 ENTD_Cf1_3 RUN3_Cf1 L3_Cf1 NX3_Cf1
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1SfRfReRcA6S43R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true P0_Cf1 exits1_Cf1 Cert1_Cf1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1SfReRdRbA6S43R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true P0_Cf1 exits1_Cf1 NX0_Cf1 ECert1_Cf1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Theorem free_spine_m_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S35R6R5A2S20SdG0ScR7PdA2A2S37A2S32U1M1S1RcRbRaR9R7S3dS40R5AaS32G1S1RdRcRbRaR8S3eS41R6AaS32G1S1ReRdRcRbR9S3fS42R7AaS4eRfReRdRcRaR8A6SbS27Vsegs;R10S29Vsegs;S34G1S1SfRfReRcA6S44R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM.
  apply (f0_s1c 1 UStopLe true PMID_Cf1 exits1_Cf1 Cert1m_Cf1 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf1 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HTM).
Qed.
Theorem efree_spine_m_Cf1 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S35R5R4A2S20SdG0ScR6PdA2A2S37A2S33U1M1S1RaR9R8R6S3dS40R4A9S33G1S1RbRaR9R7S3eS41R5A9S33G1S1RcRbRaR8S3fS42R6A9S4fRdRcRbR9R7A5SbS26Vsegs;S29Vsegs;S34G1S1SfReRdRbA6S44R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM.
  apply (ef0_s1c 1 UStopLe true PMID_Cf1 exits1_Cf1 NX0m_Cf1 ECert1m_Cf1 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf1 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1fS4dS54R2A2S1cS20S2cR2A2S22R2S2dA2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS56R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1dS55R2A1A1F_;Fa;").

Theorem hdf_Cf1_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3dS40R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_1 TD_Cf1_1 (sD_of ED_Cf1_1 1) RD_Cf1_1 HeD_Cf1_1 HchkD_Cf1_1 HTD_Cf1_1 DCHK_Cf1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf1_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3dS40R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_1 TD_Cf1_1 (sD_of ED_Cf1_1 1) RD_Cf1_1 HeD_Cf1_1 HchkD_Cf1_1 HTD_Cf1_1 DCHK_Cf1_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.
Theorem hdf_Cf1_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3eS41R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_2 TD_Cf1_2 (sD_of ED_Cf1_2 2) RD_Cf1_2 HeD_Cf1_2 HchkD_Cf1_2 HTD_Cf1_2 DCHK_Cf1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf1_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3eS41R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_2 TD_Cf1_2 (sD_of ED_Cf1_2 2) RD_Cf1_2 HeD_Cf1_2 HchkD_Cf1_2 HTD_Cf1_2 DCHK_Cf1_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.
Theorem hdf_Cf1_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S4bSaR3S28R12A1A3S32U1S1S3cVCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S3fS42R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 1 (rd_okG (NVC true) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_3 TD_Cf1_3 (sD_of ED_Cf1_3 3) RD_Cf1_3 HeD_Cf1_3 HchkD_Cf1_3 HTD_Cf1_3 DCHK_Cf1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf1_3 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S3bS0S0S0S48S3R8A1S2bSaRaR8R7R6A5S3aS12S0S0A2S11S0S0R6R5A4S18RbA1A3S47R7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S30SfRfA2S24OF_;S33U1S1S3cVCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S3fS42R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 1 (rd_okG (NVC true) 1) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf1_3 TD_Cf1_3 (sD_of ED_Cf1_3 3) RD_Cf1_3 HeD_Cf1_3 HchkD_Cf1_3 HTD_Cf1_3 DCHK_Cf1_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 1) Q).
Qed.

Lemma tail_Cf1 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S2aSaRcS28RaA1A3S4bSaRdS28RbA1A3S50ReRcA2S2bSaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S3aS12S0S0A2S11S0S0ReRdA4S18R12A1A3S47RfReA2S1bS13S19R14A1SfA3S30SfR15A2S35R14S31R16R14R12R11R10RfA6A2S1bS0S49R10A1S39A3S4eS3cVCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2fSaS4aR16R15S14S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 1 true CST XGL HCST HXGL TM_Cf1 Erf_Cf1 EC_Cf1 run5_Cf1 XR_Cf1 NX5_Cf1 RUN5_Cf1 L5_Cf1 AXR_Cf1 T0_Cf1 T1_Cf1 T2_Cf1 TR_Cf1 sR_Cf1 RR_Cf1 KEPT_Cf1 KEPT1_Cf1 XS_Cf1 eFRc HER_Cf1 Hchk_Cf1 OBJS_Cf1 HT0_Cf1 HXS_Cf1 OBJS1_Cf1 HT2_Cf1 HTR_Cf1 RCHK_Cf1 TRs_Cf1 Erq_Cf1 Erq2_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.TQ_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.Edr_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.Xf_1Bf run5d_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.run6_1Bf XW_Cf1 HTRs_Cf1 CCHK_Cf1 RUN5d_Cf1 L5d_Cf1 AXW_Cf1 ENTQ_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.NX6_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.RUN6_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.L6_1Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Bf.f0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Bf.f0_exit_1Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Cf1 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S51RaA1S2bSaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S3aS12S0S0A2S11S0S0RcRbA4S18R10A1A3S47RdRcA2S1bS13S19R12A1SfA3S30SfR13A2S35R12S31R14R12R10RfReRdA6A2S1bS0S49ReA1S39A3S4fS3cVCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2fSaS4aR14R13S14S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 1 true CST XGL HCST HXGL TM_Cf1 Erf_Cf1 EC_Cf1 run5_Cf1 XR_Cf1 NX5_Cf1 RUN5_Cf1 L5_Cf1 AXR_Cf1 T0_Cf1 T1_Cf1 T2_Cf1 TR_Cf1 sR_Cf1 RR_Cf1 KEPT_Cf1 KEPT1_Cf1 XS_Cf1 eFRc HER_Cf1 Hchk_Cf1 OBJS_Cf1 HT0_Cf1 HXS_Cf1 OBJS1_Cf1 HT2_Cf1 HTR_Cf1 RCHK_Cf1 TRs_Cf1 Erq_Cf1 Erq2_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.TQ_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.Edr_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.Xf_1Bf run5d_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.run6_1Bf XW_Cf1 HTRs_Cf1 CCHK_Cf1 RUN5d_Cf1 L5d_Cf1 AXW_Cf1 ENTQ_Cf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.NX6_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.RUN6_1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.L6_1Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Bf.ef0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Bf.ef0_exit_1Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Cf_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S38S21R6Z10A2A2S1bS13S19RbA1SfA3S30SfRcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 1) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate true 1 UStopLe (NVC true) (VFC true) Wa_Cf1 Da_Cf1 Wb_Cf1 Wc_Cf1 Wd_Cf1 Fb_Cf1 XI_Cf1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_Cf1 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_Cf1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_Cf1 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_Cf_1 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S20S38S21R4Z10A2A2S1bS13S19R9A1SfA3S30SfRaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 1) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate true 1 UStopLe (NVC true) (VFC true) Wa_Cf1 Da_Cf1 Wb_Cf1 Wc_Cf1 Wd_Cf1 Fb_Cf1 XI_Cf1 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_Cf1 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_Cf1_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf1_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf1_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_Cf1 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4dVCST;R1A2S1cS1dS1cS20S2cR2A2S22R2S2dA2A2A1S1dS1cS20Z17db48R2A2S22R2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_Cf_1 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S4bSaRaS28R8A1A3S20S38S21R6Z10A2A2S1bS13S19RbA1S16A3S30SfRcA2S20R8S37A2S50RfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Certi_1A ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instG_facts true (Wcan 1) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 1 UStopLe (NVC true) (VFC true) Wbm_Cf1 Wcm_Cf1 Wdm_Cf1 Fb_Cf1 XIm_Cf1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_Cf1 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_Cf1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_Cf1 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_Cf_1 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2fSaS4aR4R3S14S12S23S2eA2M1S11S23S2eS6S4S7U1A1M2S1A3S5S2bSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S20S38S21R4Z10A2A2S1bS13S19R9A1S16A3S30SfRaA2S20R6S37A2S51RbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Dai_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wbi_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.Wci_1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lq.F0A_m1A.ECerti_1A A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instG_facts true (Wcan 1) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 1) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 1 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 1 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true 1 UStopLe (NVC true) (VFC true) Wbm_Cf1 Wcm_Cf1 Wdm_Cf1 Fb_Cf1 XIm_Cf1 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_Cf1 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_Cf1_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf1_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf1_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_Cf1 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ACf1.
End F0A_aCf1.

(* [comment removed for export] *)
Module F0A_cLCe0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "false"; "list"; "option"; "Some"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "leaves_at"; "BIGX"; "MSE"; "PSE"; "sM_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCe0"; "C4_LCe0"; "ED_LCe0_1"; "ED_LCe0_2"; "EC_LCe0"; "C2_LCe0_1"; "C2_LCe0_2"; "C3_LCe0"; "P0_LCe0"; "RR_LCe0"; "T1_LCe0"; "CD_LCe0"; "TR_LCe0"; "sR_LCe0"; "Ems_LCe0"; "Eps_LCe0"; "PMID_LCe0"; "RD_LCe0_1"; "RD_LCe0_2"; "S1c_LCe0_1"; "S1c_LCe0_2"; "TM_LCe0"; "TRs_LCe0"; "exits1_LCe0"; "run3_LCe0"; "RM_LCe0"; "TD_LCe0_1"; "TD_LCe0_2"; "TM0_LCe0"; "run2_LCe0_1"; "run2_LCe0_2"; "run4_LCe0"; "run5_LCe0"; "run5d_LCe0"; "Ebg_LCe0"; "EfD_LCe0_1"; "EfD_LCe0_2"; "Erf_LCe0"; "Erq2_LCe0"; "Erq_LCe0"; "KEPT1_LCe0"; "T0_LCe0"; "T2_LCe0"; "TDr_LCe0_1"; "TDr_LCe0_2"; "W_LCe0"; "run1_LCe0"; "st_LCe0"; "KEPT_LCe0"; "XR_LCe0"; "XS_LCe0"; "XW_LCe0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be"; "TQ_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LCe0 : list ulink := Wcan 0.
Definition st_LCe0 : ustop := UStopLe.
Definition P0_LCe0 : axst := ltac2:(tb__ "0|0|
Sa4SbS6dS6fSbA4").

Definition run1_LCe0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S23SaS13A1A3S48A3").

Definition S1c_LCe0_1 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aS3S48A1A1Z1A3").
Definition C2_LCe0_1 : axst := C2_of S1c_LCe0_1.
Definition run2_LCe0_1 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S24SaS13A1A3S45A3").
Definition EfD_LCe0_1 : axst := leaf 0 run2_LCe0_1.
Definition ED_LCe0_1 : axst := ED_of EfD_LCe0_1.
Definition RD_LCe0_1 : list sobj := RD_of ED_LCe0_1 1.
Definition TD_LCe0_1 : axst := TD_of ED_LCe0_1 1.
Definition TDr_LCe0_1 : axst := TDr_of TD_LCe0_1.
Definition S1c_LCe0_2 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aS3S48A1A1Z2A3").
Definition C2_LCe0_2 : axst := C2_of S1c_LCe0_2.
Definition run2_LCe0_2 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S24SaS13A1A3S46A3").
Definition EfD_LCe0_2 : axst := leaf 0 run2_LCe0_2.
Definition ED_LCe0_2 : axst := ED_of EfD_LCe0_2.
Definition RD_LCe0_2 : list sobj := RD_of ED_LCe0_2 2.
Definition TD_LCe0_2 : axst := TD_of ED_LCe0_2 2.
Definition TDr_LCe0_2 : axst := TDr_of TD_LCe0_2.
Definition exits1_LCe0 : list axst := ltac2:(tb__ "0|0|
S8S2S53S8S2S54SaS2A1A3A3").

Definition CD_LCe0 : axst := CD_of TDr_LCe0_1.
Definition run3_LCe0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S28S8S13S26SaS13A1A3A3S4bA3").
Definition Eps_LCe0 : axst := leaf 0 run3_LCe0.
Definition Ebg_LCe0 : axst := leaf 1 run3_LCe0.
Definition C3_LCe0 : axst := C3_of Eps_LCe0.
Definition run4_LCe0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S27SaS13A1A3S47A3").
Definition Ems_LCe0 : axst := leaf 0 run4_LCe0.
Definition C4_LCe0 : axst := C4_of Ems_LCe0.
Definition RM_LCe0 : list sobj := RM_of C4_LCe0.
Definition TM0_LCe0 : axst := TM0_of C4_LCe0.
Definition TM_LCe0 : axst := TM_of C4_LCe0.

Definition run5_LCe0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S8eSaS13A1A3S55A3").
Definition Erf_LCe0 : axst := leaf 0 run5_LCe0.
Definition XR_LCe0 : list axform := XRC Erf_LCe0.
Definition EC_LCe0 : axst := EC_of Erf_LCe0.
Definition sR_LCe0 : wsub := sR_of (E3_of Erf_LCe0).
Definition RR_LCe0 : list sobj := RR_of EC_LCe0 sR_LCe0.
Definition KEPT_LCe0 : list sobj := KEPT_of EC_LCe0 RR_LCe0.

Definition T0_LCe0 : axst := ltac2:(tb__ "0|0|
Sa5S44S4dS49A3").
Definition XS_LCe0 : list axform := XS_of T0_LCe0.
Definition T1_LCe0 : axst := T1_of T0_LCe0.
Definition KEPT1_LCe0 : list sobj := KEPT1_of T1_LCe0.
Definition T2_LCe0 : axst := T2_of T1_LCe0.
Definition TR_LCe0 : axst := TR_of T1_LCe0.

Definition TRs_LCe0 : axst := TRs_of TR_LCe0.
Definition run5d_LCe0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S8S13S3eSaS13A1A3S56A3").
Definition Erq_LCe0 : axst := leaf 0 run5d_LCe0.
Definition XW_LCe0 : list axform := XW Erq_LCe0.
Definition Erq2_LCe0 : axst := Erq2_of Erq_LCe0.

Definition PMID_LCe0 : axst := ltac2:(tb__ "0|0|
S9bSbS6dS6fS7eS7cS17S7dS74SbA1A4S75SbA1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LCe0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S48A1A1A2S9A3"). Proof. vmr. Qed.
Lemma Cert1_LCe0 : ltac2:(tb__ "0|0|
S0S7S81S40S21S8S13S23SaS13A1A3S3fS8S2S48SaS2A1A3S57A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LCe0 exits1_LCe0 run1_LCe0); [unfold run1_LCe0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LCe0 : ltac2:(tb__ "0|2|
S0S7S82S40S21S8S13S23SaS13A1A3S3fS8S7fS80S48Z1S1cZ0M0A1M1A3SaS7fA1A3S7eS2S7fS2S80R1G0G1A3LE;S57A4A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LCe0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCe0) run1_LCe0); [unfold run1_LCe0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LCe0_1 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S53A1S3S45A1A2SeG3S10G1G2S8G0S10S16S16S2eS2fA4SaG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe0_1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S45A1M0A1S9A3S1S0S14S15G0A1S15S3S53A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe0_1 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S45A1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe0_1 : ltac2:(tb__ "0|0|
S0S2S5S53S3S45A1A2S45A3"). Proof. vmr. Qed.
Lemma RUN2_LCe0_1 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S24SaS13A1A3S45A3S5dA3"). Proof. unfold run2_LCe0_1; reflexivity. Qed.
Lemma L2_LCe0_1 : ltac2:(tb__ "0|0|
S1S0S7S25S5dS8S13S24SaS13A1A3A2S9A3S0S2S3dU0S5dA2S63A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe0_1; reflexivity]). Qed.
Lemma AXD_LCe0_1 : ltac2:(tb__ "0|0|
S0SdS2A1S79S63S2cA2SeS2S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe0_1 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S87S42S83Z1M1A1S22S42G1A2A3SeG0S51A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe0_1 : ltac2:(tb__ "0|1|
S0S7S89S42S83Z1M0A1S22S42G0A2S51S8S2S84G0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe0_1 : ltac2:(tb__ "0|1|
S0S2S5aS86S88S22S42Z1M0A2S83G0A1S84G0A1S42S51A5S1aS3S42A1A1A2A3").
Proof. unfold TD_LCe0_1, TD_of, RD_LCe0_1; reflexivity. Qed.
Lemma DCHK_LCe0_1 : ltac2:(tb__ "0|2|
S0S7S92U0M0S76S74SbA1G0A2Z1M1S42S5aS22S42G1A2S51A7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe0_1 : ltac2:(tb__ "0|0|
S0SdS2A1S79S5aS2dA2SeS2S6bA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe0_1 : ltac2:(tb__ "0|0|
S0S7Sa6S6bS4bA2S9A3"). Proof. Time vmr. Qed.
Lemma D2_LCe0_2 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S54A1S3S46A1A2SeG3S10G1G2S8G0S10S16S16S2eS2fA4SaG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe0_2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S46A1M0A1S9A3S1S0S14S15G0A1S15S3S54A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe0_2 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S46A1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe0_2 : ltac2:(tb__ "0|0|
S0S2S5S54S3S46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_LCe0_2 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S24SaS13A1A3S46A3S5eA3"). Proof. unfold run2_LCe0_2; reflexivity. Qed.
Lemma L2_LCe0_2 : ltac2:(tb__ "0|0|
S1S0S7S25S5eS8S13S24SaS13A1A3A2S9A3S0S2S3dU0S5eA2S64A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe0_2; reflexivity]). Qed.
Lemma AXD_LCe0_2 : ltac2:(tb__ "0|0|
S0SdS2A1S79S64S2cA2SeS2S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe0_2 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S87S43S83Z2M1A1S22S43G1A2A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe0_2 : ltac2:(tb__ "0|1|
S0S7S89S43S83Z2M0A1S22S43G0A2S52S8S2S84G0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe0_2 : ltac2:(tb__ "0|1|
S0S2S5bS86S88S22S43Z2M0A2S83G0A1S84G0A1S43S52A5S1aS3S43A1A1A2A3").
Proof. unfold TD_LCe0_2, TD_of, RD_LCe0_2; reflexivity. Qed.
Lemma DCHK_LCe0_2 : ltac2:(tb__ "0|2|
S0S7S92U0M0S76S74SbA1G0A2Z2M1S43S5bS22S43G1A2S52A7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe0_2 : ltac2:(tb__ "0|0|
S0SdS2A1S79S5bS2dA2SeS2S6cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe0_2 : ltac2:(tb__ "0|0|
S0S7Sa6S6cS4bA2S9A3"). Proof. Time vmr. Qed.
Lemma RUN3_LCe0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S28S8S13S26SaS13A1A3A3S4bA3S58A3"). Proof. unfold run3_LCe0; reflexivity. Qed.
Lemma L3_LCe0 : ltac2:(tb__ "0|0|
S1S0S7S25S58S8S13S28S8S13S26SaS13A1A3A3A2S9A3S1S0S2S3dU0S58A2S4fA3S0S2S3dU1S58A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LCe0 | unfold Ebg_LCe0]; reflexivity]). Qed.
Lemma NX3_LCe0 : ltac2:(tb__ "0|1|
S1S0S7S7aS3fS15S3S4bA1M0A1A2S9A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_LCe0 : ltac2:(tb__ "0|0|
S0S7S91S18S20SabA1S1aS3S62A1A1A3S9A3"). Proof. vmr. Qed.
Lemma D3_LCe0 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S85S3S4fA1S3S47A1A2SeG2S10G0G1S34SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LCe0 : ltac2:(tb__ "0|0|
S0S2S5S4fS3S47A1A2S47A3"). Proof. vmr. Qed.
Lemma NX3b_LCe0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S47A1A1A2S9A3"). Proof. vmr. Qed.
Lemma W3_LCe0 : ltac2:(tb__ "0|1|
S1S0S7S19S3S47A1M0A1S9A3S1S0S14S15G0A1S15S3S4fA1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LCe0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S27SaS13A1A3S47A3S5fA3"). Proof. unfold run4_LCe0; reflexivity. Qed.
Lemma L4_LCe0 : ltac2:(tb__ "0|0|
S1S0S7S25S5fS8S13S27SaS13A1A3A2S9A3S0S2S3dU0S5fA2S4eA3A2"). Proof. Time (split; [vmr | unfold Ems_LCe0; reflexivity]). Qed.
Lemma D4_LCe0 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S85S3S4eA1S3S41A1A2SeG2S10G0G1S35SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LCe0 : ltac2:(tb__ "0|0|
S0S2S5S4eS3S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LCe0 : ltac2:(tb__ "0|1|
S1S0S7S19S3S41A1M0A1S9A3S1S0S14S15G0A1S15S3S4eA1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LCe0 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S87S41S8bS29S41A1A3SeG0S59A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LCe0 : ltac2:(tb__ "0|0|
S0S7S8aS41S8bS29S41A1S59S7eS4S2S6S8cA4A5S9A3"). Proof. Time vmr. Qed.
Lemma HTM_LCe0 : ltac2:(tb__ "0|0|
S0S2S88S29S41A1S8bS31S41S59A5S5cA3"). Proof. unfold TM0_LCe0, TM0_of, RM_LCe0; reflexivity. Qed.
Lemma FBM_LCe0 : ltac2:(tb__ "0|3|
S1S0S7S90S18S1dS15S3S41A1M0A1M1A1S1aG0A1M2A3S9A3S1S0S7S90S18S1dS15S3S5cA1A1A1G2A3S9A3S0S7S7aS3fG1A2S9A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LCe0 : ltac2:(tb__ "0|0|
S0S2S86S5cS1aS3S41A1A1A2S55A3"). Proof. vmr. Qed.

Lemma NX5_LCe0 : ltac2:(tb__ "0|1|
S1S0S7S7aS3fS15S3S55A1M0A1A2S9A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LCe0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S8eSaS13A1A3S55A3S60A3"). Proof. unfold run5_LCe0; reflexivity. Qed.
Lemma L5_LCe0 : ltac2:(tb__ "0|0|
S1S0S7S25S60S8S13S8eSaS13A1A3A2S9A3S0S2S3dU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erf_LCe0; reflexivity]). Qed.
Lemma AXR_LCe0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S65S71A2SeS2S44A2A3"). Proof. Time vmr. Qed.

Lemma HER_LCe0 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S87S44S8dS4dA3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LCe0 : ltac2:(tb__ "0|0|
S0S7S89S44S8dS4dS49S8S2S8fSaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma OBJS_LCe0 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S44A1A1S11S17S70S49A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LCe0 : ltac2:(tb__ "0|0|
S0S2S69S86S88S4dS8dS8fS44S49A5S1aS3S44A1A1A2A3"). Proof. unfold T0_LCe0, T0_of; reflexivity. Qed.
Lemma HXS_LCe0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S69S72A2SeS2S4aA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LCe0 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S4aA1A1S11S17S68S8S17S30S8S17S7dS77A1S8S17S7dS78A1SaS17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LCe0 : ltac2:(tb__ "0|0|
S0S2S6aS5S4aSa7S3S4aA1S68A2A2A3"). Proof. unfold T2_LCe0, T2_of, KEPT1_LCe0; reflexivity. Qed.
Lemma HTR_LCe0 : ltac2:(tb__ "0|2|
S0S2S4cSa0S6aS8S7cSa1Sa3S15S3S4aA1A1M0S7bG0A1M1A3SaS7cA1A3S7bG1A1A3A3"). Proof. unfold TR_LCe0, TR_of, T2_LCe0; reflexivity. Qed.
Lemma RCHK_LCe0 : ltac2:(tb__ "0|0|
S0S7Sa2U0SbS44S4aS4cS4dS49Sa3A8S9A3"). Proof. Time vmr. Qed.

Lemma HTRs_LCe0 : ltac2:(tb__ "0|0|
S0S2S56Sa0S4cSadS15S3S4cA1A1A3A3"). Proof. unfold TRs_LCe0, TRs_of; reflexivity. Qed.
Lemma CCHK_LCe0 : ltac2:(tb__ "0|0|
S0S7SaeU0S7S37L_;SbS33S32X7x2S4cS56A4S9A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LCe0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S8S13S3eSaS13A1A3S56A3S61A3"). Proof. unfold run5d_LCe0; reflexivity. Qed.
Lemma L5d_LCe0 : ltac2:(tb__ "0|0|
S1S0S7S25S61S8S13S3eSaS13A1A3A2S9A3S0S2S3dU0S61A2S67A3A2"). Proof. Time (split; [vmr | unfold Erq_LCe0; reflexivity]). Qed.
Lemma AXW_LCe0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S67S73A2SeS2S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LCe0 : ltac2:(tb__ "0|0|
S0S7S36S66SacA2S9A3"). Proof. Time vmr. Qed.

Lemma Wa_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S94S39U0A1S38A2A1S9A3"). Proof. vmr. Qed.
Lemma Da_LCe0 : ltac2:(tb__ "0|5|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S3bS3aS39U0A1M4S38A3A1S94G4S38A2A2SeG3S10G1G2S8G0S10S16S16S1fP18A1S1cSaaA1A4SaG0A1A3SaS18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S97S39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wc_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S98S39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wd_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S99S39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Fb_LCe0 : ltac2:(tb__ "0|0|
S0S7S90S18S1dSa9A1S95SbS39U0A1S38S75SbA1A4A3S9A3"). Proof. vmr. Qed.
Lemma XI_LCe0 : ltac2:(tb__ "0|4|
S0SdS2A1S79S9aSbS39U0M0A1M1S38S74SbA1M2S75SbA1M3A5S93G0S12S7cG2A2A2A2SeS2S96SbG1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LCe0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S50A1A1A2S9A3"). Proof. vmr. Qed.
Definition Cert1m_LCe0__runs : ltac2:(tb__ "0|0|
ScSdScS4A1A1A1") := ltac2:(tb__ "0|0|
Sa8S40S21S8S13S23SaS13A1A3S8S2S50SaS2A1A3A4").
Lemma Cert1m_LCe0 : ltac2:(tb__ "0|0|
S0S7S81S40S21S8S13S23SaS13A1A3S3fS8S2S50SaS2A1A3S57A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LCe0] exits1_LCe0 Cert1m_LCe0__runs); [unfold Cert1m_LCe0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LCe0 : ltac2:(tb__ "0|2|
S0S7S82S40S21S8S13S23SaS13A1A3S3fS8S7fS80S50Z1S1cZ0M0A1M1A3SaS7fA1A3S7eS2S7fS2S80R1G0G1A3LE;S57A4A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LCe0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCe0) Cert1m_LCe0__runs); [unfold Cert1m_LCe0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S9cS39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wcm_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S9dS39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wdm_LCe0 : ltac2:(tb__ "0|0|
S0S7S19S9eS39U0A1S38S74SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma XIm_LCe0 : ltac2:(tb__ "0|4|
S0SdS2A1S79S9fSbS39U0M0A1M1S38S74SbA1M2S75SbA1M3A5S93G0S12S7cG2A2A2A2SeS2S9bSbG1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cLCe0.

(* [comment removed for export] *)
Module F0A_aLCe0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "pair"; "prod"; "true"; "bool"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCe0"; "ED_LCe0_1"; "ED_LCe0_2"; "TD_LCe0_1"; "TD_LCe0_2"; "P0_LCe0"; "PMID_LCe0"; "TM_LCe0"; "exits1_LCe0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_aLCe0.ALCe0"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCe0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require la.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALCe0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S3fU0S1S10R6VKc;R5A6S3bR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S3fU0S1S10R6VKc;R5A6S3bR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6S23SbS42S23R2S3cA3S27Vsegs;R11S29Vsegs;S3fG1S1S13R10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LCe0 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LCe0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_LCe0 Q BGF_LCe0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_LCe0 C3_LCe0 Ems_LCe0 C4_LCe0 TM0_LCe0 run4_LCe0 RM_LCe0 D3_LCe0 W3_LCe0 EQ3_LCe0 NX3b_LCe0 RUN4_LCe0 L4_LCe0 D4_LCe0 W4_LCe0 EQ4_LCe0
             HeM_LCe0 HchkM_LCe0 HTM_LCe0 FBM_LCe0 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LCe0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCe0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_LCe0_1 C2_LCe0_1 EfD_LCe0_1 ED_LCe0_1 run2_LCe0_1 D2_LCe0_1 W2_LCe0_1 NX2_LCe0_1 EQ2_LCe0_1 RUN2_LCe0_1 L2_LCe0_1 AXD_LCe0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_LCe0_1 TDr_LCe0_1 CD_LCe0 Eps_LCe0 Ebg_LCe0 run3_LCe0 AXDr_LCe0_1 ENTD_LCe0_1 RUN3_LCe0 L3_LCe0 NX3_LCe0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0 UStopLe true S1c_LCe0_2 C2_LCe0_2 EfD_LCe0_2 ED_LCe0_2 run2_LCe0_2 D2_LCe0_2 W2_LCe0_2 NX2_LCe0_2 EQ2_LCe0_2 RUN2_LCe0_2 L2_LCe0_2 AXD_LCe0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_LCe0_2 TDr_LCe0_2 CD_LCe0 Eps_LCe0 Ebg_LCe0 run3_LCe0 AXDr_LCe0_2 ENTD_LCe0_2 RUN3_LCe0 L3_LCe0 NX3_LCe0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5S23SbS42S23R2S3cA3S26Vsegs;S29Vsegs;S3fG1S1S13RfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LCe0 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LCe0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_LCe0 Q BGF_LCe0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_LCe0 C3_LCe0 Ems_LCe0 C4_LCe0 TM0_LCe0 run4_LCe0 RM_LCe0 D3_LCe0 W3_LCe0 EQ3_LCe0 NX3b_LCe0 RUN4_LCe0 L4_LCe0 D4_LCe0 W4_LCe0 EQ4_LCe0
             HeM_LCe0 HchkM_LCe0 HTM_LCe0 FBM_LCe0 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LCe0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCe0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_LCe0_1 C2_LCe0_1 EfD_LCe0_1 ED_LCe0_1 run2_LCe0_1 D2_LCe0_1 W2_LCe0_1 NX2_LCe0_1 EQ2_LCe0_1 RUN2_LCe0_1 L2_LCe0_1 AXD_LCe0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_LCe0_1 TDr_LCe0_1 CD_LCe0 Eps_LCe0 Ebg_LCe0 run3_LCe0 AXDr_LCe0_1 ENTD_LCe0_1 RUN3_LCe0 L3_LCe0 NX3_LCe0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_LCe0_2 C2_LCe0_2 EfD_LCe0_2 ED_LCe0_2 run2_LCe0_2 D2_LCe0_2 W2_LCe0_2 NX2_LCe0_2 EQ2_LCe0_2 RUN2_LCe0_2 L2_LCe0_2 AXD_LCe0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_LCe0_2 TDr_LCe0_2 CD_LCe0 Eps_LCe0 Ebg_LCe0 run3_LCe0 AXDr_LCe0_2 ENTD_LCe0_2 RUN3_LCe0 L3_LCe0 NX3_LCe0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1S13ReRdRbA6S39R1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true P0_LCe0 exits1_LCe0 Cert1_LCe0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCe0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1S13RdRcRaA6S39R1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true P0_LCe0 exits1_LCe0 NX0_LCe0 ECert1_LCe0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCe0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Theorem free_spine_m_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1S13ReRdRbA6S3aR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true PMID_LCe0 exits1_LCe0 Cert1m_LCe0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCe0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_m_LCe0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1S13RdRcRaA6S3aR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true PMID_LCe0 exits1_LCe0 NX0m_LCe0 ECert1m_LCe0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCe0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S22S4aS52R2A2S1fS1bS2eR2A2S1dR2S2fA2A2A2S21F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S54R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S53R2A1A1F_;Fa;").

Theorem hdf_LCe0_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S35S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC false) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe0_1 TD_LCe0_1 (sD_of ED_LCe0_1 1) RD_LCe0_1 HeD_LCe0_1 HchkD_LCe0_1 HTD_LCe0_1 DCHK_LCe0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe0_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S35S37R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC false) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe0_1 TD_LCe0_1 (sD_of ED_LCe0_1 1) RD_LCe0_1 HeD_LCe0_1 HchkD_LCe0_1 HTD_LCe0_1 DCHK_LCe0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.
Theorem hdf_LCe0_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S36S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC false) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe0_2 TD_LCe0_2 (sD_of ED_LCe0_2 2) RD_LCe0_2 HeD_LCe0_2 HchkD_LCe0_2 HTD_LCe0_2 DCHK_LCe0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe0_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S36S38R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC false) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe0_2 TD_LCe0_2 (sD_of ED_LCe0_2 2) RD_LCe0_2 HeD_LCe0_2 HchkD_LCe0_2 HTD_LCe0_2 DCHK_LCe0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.

Lemma tail_LCe0 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbSfSeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S2aSaRcS28RaA1A3S49SaRdS28RbA1A3S4eReRcA2S2dSaReRcR6R5A5S1aRfA1S1eS0SdG0ScRePcA2A2RcA3S1eS0SdG0ScRfPdA2A2RcA3S42S12S0S0A2S11S0S0ReRdA4S19R12A1A3S46RfReA2S1eS14S18R14A1S13A3S30S10R15A2S40R14S31R16R14R12R11R10RfA6A2S1eS0S48R10A1S34A3S4bS45VCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2cSaS44R16R15S15S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R18Z18A2R17A5A4S16G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 false CST XGL HCST HXGL TM_LCe0 Erf_LCe0 EC_LCe0 run5_LCe0 XR_LCe0 NX5_LCe0 RUN5_LCe0 L5_LCe0 AXR_LCe0 T0_LCe0 T1_LCe0 T2_LCe0 TR_LCe0 sR_LCe0 RR_LCe0 KEPT_LCe0 KEPT1_LCe0 XS_LCe0 eFRc HER_LCe0 Hchk_LCe0 OBJS_LCe0 HT0_LCe0 HXS_LCe0 OBJS1_LCe0 HT2_LCe0 HTR_LCe0 RCHK_LCe0 TRs_LCe0 Erq_LCe0 Erq2_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.TQ_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.Edr_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.Xf_L0Be run5d_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.run6_L0Be XW_LCe0 HTRs_LCe0 CCHK_LCe0 RUN5d_LCe0 L5d_LCe0 AXW_LCe0 ENTQ_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.NX6_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.RUN6_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.L6_L0Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Be.f0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Be.f0_exit_L0Be CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LCe0 : ltac2:(tb__ "0|3|
S17S2SbSfSeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S4fRaA1S2dSaRcRaR4R3A5S1aRdA1S1eS0SdG0ScRcPcA2A2RaA3S1eS0SdG0ScRdPdA2A2RaA3S42S12S0S0A2S11S0S0RcRbA4S19R10A1A3S46RdRcA2S1eS14S18R12A1S13A3S30S10R13A2S40R12S31R14R12R10RfReRdA6A2S1eS0S48ReA1S34A3S4cS45VCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2cSaS44R14R13S15S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R16Z18A2R15A5A4S16G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 false CST XGL HCST HXGL TM_LCe0 Erf_LCe0 EC_LCe0 run5_LCe0 XR_LCe0 NX5_LCe0 RUN5_LCe0 L5_LCe0 AXR_LCe0 T0_LCe0 T1_LCe0 T2_LCe0 TR_LCe0 sR_LCe0 RR_LCe0 KEPT_LCe0 KEPT1_LCe0 XS_LCe0 eFRc HER_LCe0 Hchk_LCe0 OBJS_LCe0 HT0_LCe0 HXS_LCe0 OBJS1_LCe0 HT2_LCe0 HTR_LCe0 RCHK_LCe0 TRs_LCe0 Erq_LCe0 Erq2_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.TQ_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.Edr_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.Xf_L0Be run5d_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.run6_L0Be XW_LCe0 HTRs_LCe0 CCHK_LCe0 RUN5d_LCe0 L5d_LCe0 AXW_LCe0 ENTQ_LCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.NX6_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.RUN6_L0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.L6_L0Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Be.ef0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Be.ef0_exit_L0Be CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Ce_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS1cR6R5A2S33A2S1eS14S18RbA1S13A3S30S10RcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C false _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate false 0 UStopLe (NVC false) (VFC false) Wa_LCe0 Da_LCe0 Wb_LCe0 Wc_LCe0 Wd_LCe0 Fb_LCe0 XI_LCe0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_LCe0 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_LCe0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCe0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LCe0 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_Ce_0 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S1bS1cR4R3A2S33A2S1eS14S18R9A1S13A3S30S10RaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C false _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate false 0 UStopLe (NVC false) (VFC false) Wa_LCe0 Da_LCe0 Wb_LCe0 Wc_LCe0 Wd_LCe0 Fb_LCe0 XI_LCe0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_LCe0 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_LCe0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCe0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_LCe0 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S1fS20S1fS1bS2eR2A2S1dR2S2fA2A2A1S20S1fS1bZ17db48R2A2S1dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_Ce_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS1cR6R5A2S33A2S1eS14S18RbA1S10A3S30S10RcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 0 UStopLe (NVC false) (VFC false) Wbm_LCe0 Wcm_LCe0 Wdm_LCe0 Fb_LCe0 XIm_LCe0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_LCe0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_LCe0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCe0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LCe0 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_Ce_0 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S1bS1cR4R3A2S33A2S1eS14S18R9A1S10A3S30S10RaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false 0 UStopLe (NVC false) (VFC false) Wbm_LCe0 Wcm_LCe0 Wdm_LCe0 Fb_LCe0 XIm_LCe0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_LCe0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_LCe0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCe0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_LCe0 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALCe0.
End F0A_aLCe0.

(* [comment removed for export] *)
Module F0A_cLCf0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "false"; "prod"; "pair"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "leaves_at"; "BIGX"; "MSE"; "PSE"; "sM_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCf0"; "C4_LCf0"; "ED_LCf0_1"; "ED_LCf0_2"; "EC_LCf0"; "C2_LCf0_1"; "C2_LCf0_2"; "C3_LCf0"; "P0_LCf0"; "RR_LCf0"; "T1_LCf0"; "CD_LCf0"; "TR_LCf0"; "sR_LCf0"; "Ems_LCf0"; "Eps_LCf0"; "PMID_LCf0"; "RD_LCf0_1"; "RD_LCf0_2"; "S1c_LCf0_1"; "S1c_LCf0_2"; "TM_LCf0"; "TRs_LCf0"; "exits1_LCf0"; "run3_LCf0"; "RM_LCf0"; "TD_LCf0_1"; "TD_LCf0_2"; "TM0_LCf0"; "run2_LCf0_1"; "run2_LCf0_2"; "run4_LCf0"; "run5_LCf0"; "run5d_LCf0"; "Ebg_LCf0"; "EfD_LCf0_1"; "EfD_LCf0_2"; "Erf_LCf0"; "Erq2_LCf0"; "Erq_LCf0"; "KEPT1_LCf0"; "T0_LCf0"; "T2_LCf0"; "TDr_LCf0_1"; "TDr_LCf0_2"; "W_LCf0"; "run1_LCf0"; "st_LCf0"; "KEPT_LCf0"; "XR_LCf0"; "XS_LCf0"; "XW_LCf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf"; "TQ_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LCf0 : list ulink := Wcan 0.
Definition st_LCf0 : ustop := UStopLe.
Definition P0_LCf0 : axst := ltac2:(tb__ "0|0|
Sa4S9S6dS6fS2A4").

Definition run1_LCf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S23S5S13A1A3S48A3").

Definition S1c_LCf0_1 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aSfS48A1A1Z1A3").
Definition C2_LCf0_1 : axst := C2_of S1c_LCf0_1.
Definition run2_LCf0_1 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S24S5S13A1A3S45A3").
Definition EfD_LCf0_1 : axst := leaf 0 run2_LCf0_1.
Definition ED_LCf0_1 : axst := ED_of EfD_LCf0_1.
Definition RD_LCf0_1 : list sobj := RD_of ED_LCf0_1 1.
Definition TD_LCf0_1 : axst := TD_of ED_LCf0_1 1.
Definition TDr_LCf0_1 : axst := TDr_of TD_LCf0_1.
Definition S1c_LCf0_2 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aSfS48A1A1Z2A3").
Definition C2_LCf0_2 : axst := C2_of S1c_LCf0_2.
Definition run2_LCf0_2 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S24S5S13A1A3S46A3").
Definition EfD_LCf0_2 : axst := leaf 0 run2_LCf0_2.
Definition ED_LCf0_2 : axst := ED_of EfD_LCf0_2.
Definition RD_LCf0_2 : list sobj := RD_of ED_LCf0_2 2.
Definition TD_LCf0_2 : axst := TD_of ED_LCf0_2 2.
Definition TDr_LCf0_2 : axst := TDr_of TD_LCf0_2.
Definition exits1_LCf0 : list axst := ltac2:(tb__ "0|0|
S4SeS53S4SeS54S5SeA1A3A3").

Definition CD_LCf0 : axst := CD_of TDr_LCf0_1.
Definition run3_LCf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S28S4S13S26S5S13A1A3A3S4bA3").
Definition Eps_LCf0 : axst := leaf 0 run3_LCf0.
Definition Ebg_LCf0 : axst := leaf 1 run3_LCf0.
Definition C3_LCf0 : axst := C3_of Eps_LCf0.
Definition run4_LCf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S27S5S13A1A3S47A3").
Definition Ems_LCf0 : axst := leaf 0 run4_LCf0.
Definition C4_LCf0 : axst := C4_of Ems_LCf0.
Definition RM_LCf0 : list sobj := RM_of C4_LCf0.
Definition TM0_LCf0 : axst := TM0_of C4_LCf0.
Definition TM_LCf0 : axst := TM_of C4_LCf0.

Definition run5_LCf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S8eS5S13A1A3S55A3").
Definition Erf_LCf0 : axst := leaf 0 run5_LCf0.
Definition XR_LCf0 : list axform := XRC Erf_LCf0.
Definition EC_LCf0 : axst := EC_of Erf_LCf0.
Definition sR_LCf0 : wsub := sR_of (E3_of Erf_LCf0).
Definition RR_LCf0 : list sobj := RR_of EC_LCf0 sR_LCf0.
Definition KEPT_LCf0 : list sobj := KEPT_of EC_LCf0 RR_LCf0.

Definition T0_LCf0 : axst := ltac2:(tb__ "0|0|
Sa5S44S4dS49A3").
Definition XS_LCf0 : list axform := XS_of T0_LCf0.
Definition T1_LCf0 : axst := T1_of T0_LCf0.
Definition KEPT1_LCf0 : list sobj := KEPT1_of T1_LCf0.
Definition T2_LCf0 : axst := T2_of T1_LCf0.
Definition TR_LCf0 : axst := TR_of T1_LCf0.

Definition TRs_LCf0 : axst := TRs_of TR_LCf0.
Definition run5d_LCf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S3eS5S13A1A3S56A3").
Definition Erq_LCf0 : axst := leaf 0 run5d_LCf0.
Definition XW_LCf0 : list axform := XW Erq_LCf0.
Definition Erq2_LCf0 : axst := Erq2_of Erq_LCf0.

Definition PMID_LCf0 : axst := ltac2:(tb__ "0|0|
S9bS9S6dS6fS7eS7cS17S7dS74S2A1A4S75S2A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LCf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS48A1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_LCf0 : ltac2:(tb__ "0|0|
S0S3S81S40S21S4S13S23S5S13A1A3S3fS4SeS48S5SeA1A3S57A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LCf0 exits1_LCf0 run1_LCf0); [unfold run1_LCf0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LCf0 : ltac2:(tb__ "0|2|
S0S3S82S40S21S4S13S23S5S13A1A3S3fS4S7fS80S48Z1S1cZ0M0A1M1A3S5S7fA1A3S7eSeS7fSeS80R1G0G1A3LE;S57A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LCf0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf0) run1_LCf0); [unfold run1_LCf0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LCf0_1 : ltac2:(tb__ "0|4|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS53A1SfS45A1A2S8G3SbG1G2S4G0SbS16S16S2eS2fA4S5G0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf0_1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS45A1M0A1S2A3S1S0S14S15G0A1S15SfS53A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf0_1 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS45A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LCf0_1 : ltac2:(tb__ "0|0|
S0SeS11S53SfS45A1A2S45A3"). Proof. vmr. Qed.
Lemma RUN2_LCf0_1 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S24S5S13A1A3S45A3S5dA3"). Proof. unfold run2_LCf0_1; reflexivity. Qed.
Lemma L2_LCf0_1 : ltac2:(tb__ "0|0|
S1S0S3S25S5dS4S13S24S5S13A1A3A2S2A3S0SeS3dU0S5dA2S63A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf0_1; reflexivity]). Qed.
Lemma AXD_LCf0_1 : ltac2:(tb__ "0|0|
S0S7SeA1S79S63S2cA2S8SeS42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf0_1 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S87S42S83Z1M1A1S22S42G1A2A3S8G0S51A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf0_1 : ltac2:(tb__ "0|1|
S0S3S89S42S83Z1M0A1S22S42G0A2S51S4SeS84G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf0_1 : ltac2:(tb__ "0|1|
S0SeS5aS86S88S22S42Z1M0A2S83G0A1S84G0A1S42S51A5S1aSfS42A1A1A2A3").
Proof. unfold TD_LCf0_1, TD_of, RD_LCf0_1; reflexivity. Qed.
Lemma DCHK_LCf0_1 : ltac2:(tb__ "0|2|
S0S3S92U0M0S76S74S2A1G0A2Z1M1S42S5aS22S42G1A2S51A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf0_1 : ltac2:(tb__ "0|0|
S0S7SeA1S79S5aS2dA2S8SeS6bA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf0_1 : ltac2:(tb__ "0|0|
S0S3Sa6S6bS4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_LCf0_2 : ltac2:(tb__ "0|4|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS54A1SfS46A1A2S8G3SbG1G2S4G0SbS16S16S2eS2fA4S5G0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCf0_2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS46A1M0A1S2A3S1S0S14S15G0A1S15SfS54A1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCf0_2 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS46A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LCf0_2 : ltac2:(tb__ "0|0|
S0SeS11S54SfS46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_LCf0_2 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S24S5S13A1A3S46A3S5eA3"). Proof. unfold run2_LCf0_2; reflexivity. Qed.
Lemma L2_LCf0_2 : ltac2:(tb__ "0|0|
S1S0S3S25S5eS4S13S24S5S13A1A3A2S2A3S0SeS3dU0S5eA2S64A3A2"). Proof. Time (split; [vmr | unfold EfD_LCf0_2; reflexivity]). Qed.
Lemma AXD_LCf0_2 : ltac2:(tb__ "0|0|
S0S7SeA1S79S64S2cA2S8SeS43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCf0_2 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S87S43S83Z2M1A1S22S43G1A2A3S8G0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCf0_2 : ltac2:(tb__ "0|1|
S0S3S89S43S83Z2M0A1S22S43G0A2S52S4SeS84G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_LCf0_2 : ltac2:(tb__ "0|1|
S0SeS5bS86S88S22S43Z2M0A2S83G0A1S84G0A1S43S52A5S1aSfS43A1A1A2A3").
Proof. unfold TD_LCf0_2, TD_of, RD_LCf0_2; reflexivity. Qed.
Lemma DCHK_LCf0_2 : ltac2:(tb__ "0|2|
S0S3S92U0M0S76S74S2A1G0A2Z2M1S43S5bS22S43G1A2S52A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCf0_2 : ltac2:(tb__ "0|0|
S0S7SeA1S79S5bS2dA2S8SeS6cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCf0_2 : ltac2:(tb__ "0|0|
S0S3Sa6S6cS4bA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_LCf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S28S4S13S26S5S13A1A3A3S4bA3S58A3"). Proof. unfold run3_LCf0; reflexivity. Qed.
Lemma L3_LCf0 : ltac2:(tb__ "0|0|
S1S0S3S25S58S4S13S28S4S13S26S5S13A1A3A3A2S2A3S1S0SeS3dU0S58A2S4fA3S0SeS3dU1S58A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LCf0 | unfold Ebg_LCf0]; reflexivity]). Qed.
Lemma NX3_LCf0 : ltac2:(tb__ "0|1|
S1S0S3S7aS3fS15SfS4bA1M0A1A2S2A3S0S3S1bG0A1S9A3A2"). Proof. split; vmr. Qed.

Lemma BGF_LCf0 : ltac2:(tb__ "0|0|
S0S3S91S18S20SabA1S1aSfS62A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_LCf0 : ltac2:(tb__ "0|3|
S0S7SaS6SaS16S16A2A1M0S6S18A1M1A2M2A1S85SfS4fA1SfS47A1A2S8G2SbG0G1S34S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LCf0 : ltac2:(tb__ "0|0|
S0SeS11S4fSfS47A1A2S47A3"). Proof. vmr. Qed.
Lemma NX3b_LCf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS47A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_LCf0 : ltac2:(tb__ "0|1|
S1S0S3S19SfS47A1M0A1S2A3S1S0S14S15G0A1S15SfS4fA1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LCf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S27S5S13A1A3S47A3S5fA3"). Proof. unfold run4_LCf0; reflexivity. Qed.
Lemma L4_LCf0 : ltac2:(tb__ "0|0|
S1S0S3S25S5fS4S13S27S5S13A1A3A2S2A3S0SeS3dU0S5fA2S4eA3A2"). Proof. Time (split; [vmr | unfold Ems_LCf0; reflexivity]). Qed.
Lemma D4_LCf0 : ltac2:(tb__ "0|3|
S0S7SaS6SaS16S16A2A1M0S6S18A1M1A2M2A1S85SfS4eA1SfS41A1A2S8G2SbG0G1S35S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LCf0 : ltac2:(tb__ "0|0|
S0SeS11S4eSfS41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LCf0 : ltac2:(tb__ "0|1|
S1S0S3S19SfS41A1M0A1S2A3S1S0S14S15G0A1S15SfS4eA1A1A3S0S3S1bG0A1S9A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LCf0 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S87S41S8bS29S41A1A3S8G0S59A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LCf0 : ltac2:(tb__ "0|0|
S0S3S8aS41S8bS29S41A1S59S7eS10SeS12S8cA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_LCf0 : ltac2:(tb__ "0|0|
S0SeS88S29S41A1S8bS31S41S59A5S5cA3"). Proof. unfold TM0_LCf0, TM0_of, RM_LCf0; reflexivity. Qed.
Lemma FBM_LCf0 : ltac2:(tb__ "0|3|
S1S0S3S90S18S1dS15SfS41A1M0A1M1A1S1aG0A1M2A3S2A3S1S0S3S90S18S1dS15SfS5cA1A1A1G2A3S2A3S0S3S7aS3fG1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LCf0 : ltac2:(tb__ "0|0|
S0SeS86S5cS1aSfS41A1A1A2S55A3"). Proof. vmr. Qed.

Lemma NX5_LCf0 : ltac2:(tb__ "0|1|
S1S0S3S7aS3fS15SfS55A1M0A1A2S2A3S0S3S1bG0A1S9A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LCf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S8eS5S13A1A3S55A3S60A3"). Proof. unfold run5_LCf0; reflexivity. Qed.
Lemma L5_LCf0 : ltac2:(tb__ "0|0|
S1S0S3S25S60S4S13S8eS5S13A1A3A2S2A3S0SeS3dU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erf_LCf0; reflexivity]). Qed.
Lemma AXR_LCf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S65S71A2S8SeS44A2A3"). Proof. Time vmr. Qed.

Lemma HER_LCf0 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S87S44S8dS4dA3S8G0S49A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LCf0 : ltac2:(tb__ "0|0|
S0S3S89S44S8dS4dS49S4SeS8fS5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_LCf0 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS44A1A1ScS17S70S49A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LCf0 : ltac2:(tb__ "0|0|
S0SeS69S86S88S4dS8dS8fS44S49A5S1aSfS44A1A1A2A3"). Proof. unfold T0_LCf0, T0_of; reflexivity. Qed.
Lemma HXS_LCf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S69S72A2S8SeS4aA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LCf0 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS4aA1A1ScS17S68S4S17S30S4S17S7dS77A1S4S17S7dS78A1S5S17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LCf0 : ltac2:(tb__ "0|0|
S0SeS6aS11S4aSa7SfS4aA1S68A2A2A3"). Proof. unfold T2_LCf0, T2_of, KEPT1_LCf0; reflexivity. Qed.
Lemma HTR_LCf0 : ltac2:(tb__ "0|2|
S0SeS4cSa0S6aS4S7cSa1Sa3S15SfS4aA1A1M0S7bG0A1M1A3S5S7cA1A3S7bG1A1A3A3"). Proof. unfold TR_LCf0, TR_of, T2_LCf0; reflexivity. Qed.
Lemma RCHK_LCf0 : ltac2:(tb__ "0|0|
S0S3Sa2U0S2S44S4aS4cS4dS49Sa3A8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_LCf0 : ltac2:(tb__ "0|0|
S0SeS56Sa0S4cSadS15SfS4cA1A1A3A3"). Proof. unfold TRs_LCf0, TRs_of; reflexivity. Qed.
Lemma CCHK_LCf0 : ltac2:(tb__ "0|0|
S0S3SaeU0S3S37L_;S2S33S32X3x2S4cS56A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LCf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S3eS5S13A1A3S56A3S61A3"). Proof. unfold run5d_LCf0; reflexivity. Qed.
Lemma L5d_LCf0 : ltac2:(tb__ "0|0|
S1S0S3S25S61S4S13S3eS5S13A1A3A2S2A3S0SeS3dU0S61A2S67A3A2"). Proof. Time (split; [vmr | unfold Erq_LCf0; reflexivity]). Qed.
Lemma AXW_LCf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S67S73A2S8SeS66A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LCf0 : ltac2:(tb__ "0|0|
S0S3S36S66SacA2S2A3"). Proof. Time vmr. Qed.

Lemma Wa_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S94S39U0A1S38A2A1S2A3"). Proof. vmr. Qed.
Lemma Da_LCf0 : ltac2:(tb__ "0|5|
S0S7SaS6SaS16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS3bS3aS39U0A1M4S38A3A1S94G4S38A2A2S8G3SbG1G2S4G0SbS16S16S1fP18A1S1cSaaA1A4S5G0A1A3S5S18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S97S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S98S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S99S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_LCf0 : ltac2:(tb__ "0|0|
S0S3S90S18S1dSa9A1S95S9S39U0A1S38S75S2A1A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_LCf0 : ltac2:(tb__ "0|4|
S0S7SeA1S79S9aS9S39U0M0A1M1S38S74S2A1M2S75S2A1M3A5S93G0SdS7cG2A2A2A2S8SeS96S9G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LCf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS50A1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_LCf0__runs : ltac2:(tb__ "0|0|
S6S7S6S10A1A1A1") := ltac2:(tb__ "0|0|
Sa8S40S21S4S13S23S5S13A1A3S4SeS50S5SeA1A3A4").
Lemma Cert1m_LCf0 : ltac2:(tb__ "0|0|
S0S3S81S40S21S4S13S23S5S13A1A3S3fS4SeS50S5SeA1A3S57A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LCf0] exits1_LCf0 Cert1m_LCf0__runs); [unfold Cert1m_LCf0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LCf0 : ltac2:(tb__ "0|2|
S0S3S82S40S21S4S13S23S5S13A1A3S3fS4S7fS80S50Z1S1cZ0M0A1M1A3S5S7fA1A3S7eSeS7fSeS80R1G0G1A3LE;S57A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LCf0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCf0) Cert1m_LCf0__runs); [unfold Cert1m_LCf0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S9cS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S9dS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_LCf0 : ltac2:(tb__ "0|0|
S0S3S19S9eS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_LCf0 : ltac2:(tb__ "0|4|
S0S7SeA1S79S9fS9S39U0M0A1M1S38S74S2A1M2S75S2A1M3A5S93G0SdS7cG2A2A2A2S8SeS9bS9G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cLCf0.

(* [comment removed for export] *)
Module F0A_aLCf0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCf0"; "ED_LCf0_1"; "ED_LCf0_2"; "TD_LCf0_1"; "TD_LCf0_2"; "P0_LCf0"; "PMID_LCf0"; "TM_LCf0"; "exits1_LCf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_aLCf0.ALCf0"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ly.F0A_cLCf0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require la.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALCf0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S3fU0S1S16R6VKc;R5A6S3bR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S3fU0S1S16R6VKc;R5A6S3bR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6S23SbS42S23R2S3cA3S27Vsegs;R11S29Vsegs;S3fG1S1SfR10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LCf0 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LCf0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_LCf0 Q BGF_LCf0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_LCf0 C3_LCf0 Ems_LCf0 C4_LCf0 TM0_LCf0 run4_LCf0 RM_LCf0 D3_LCf0 W3_LCf0 EQ3_LCf0 NX3b_LCf0 RUN4_LCf0 L4_LCf0 D4_LCf0 W4_LCf0 EQ4_LCf0
             HeM_LCf0 HchkM_LCf0 HTM_LCf0 FBM_LCf0 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LCf0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_LCf0_1 C2_LCf0_1 EfD_LCf0_1 ED_LCf0_1 run2_LCf0_1 D2_LCf0_1 W2_LCf0_1 NX2_LCf0_1 EQ2_LCf0_1 RUN2_LCf0_1 L2_LCf0_1 AXD_LCf0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_LCf0_1 TDr_LCf0_1 CD_LCf0 Eps_LCf0 Ebg_LCf0 run3_LCf0 AXDr_LCf0_1 ENTD_LCf0_1 RUN3_LCf0 L3_LCf0 NX3_LCf0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0 UStopLe true S1c_LCf0_2 C2_LCf0_2 EfD_LCf0_2 ED_LCf0_2 run2_LCf0_2 D2_LCf0_2 W2_LCf0_2 NX2_LCf0_2 EQ2_LCf0_2 RUN2_LCf0_2 L2_LCf0_2 AXD_LCf0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_LCf0_2 TDr_LCf0_2 CD_LCf0 Eps_LCf0 Ebg_LCf0 run3_LCf0 AXDr_LCf0_2 ENTD_LCf0_2 RUN3_LCf0 L3_LCf0 NX3_LCf0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5S23SbS42S23R2S3cA3S26Vsegs;S29Vsegs;S3fG1S1SfRfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LCf0 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LCf0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_LCf0 Q BGF_LCf0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_LCf0 C3_LCf0 Ems_LCf0 C4_LCf0 TM0_LCf0 run4_LCf0 RM_LCf0 D3_LCf0 W3_LCf0 EQ3_LCf0 NX3b_LCf0 RUN4_LCf0 L4_LCf0 D4_LCf0 W4_LCf0 EQ4_LCf0
             HeM_LCf0 HchkM_LCf0 HTM_LCf0 FBM_LCf0 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LCf0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCf0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_LCf0_1 C2_LCf0_1 EfD_LCf0_1 ED_LCf0_1 run2_LCf0_1 D2_LCf0_1 W2_LCf0_1 NX2_LCf0_1 EQ2_LCf0_1 RUN2_LCf0_1 L2_LCf0_1 AXD_LCf0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_LCf0_1 TDr_LCf0_1 CD_LCf0 Eps_LCf0 Ebg_LCf0 run3_LCf0 AXDr_LCf0_1 ENTD_LCf0_1 RUN3_LCf0 L3_LCf0 NX3_LCf0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_LCf0_2 C2_LCf0_2 EfD_LCf0_2 ED_LCf0_2 run2_LCf0_2 D2_LCf0_2 W2_LCf0_2 NX2_LCf0_2 EQ2_LCf0_2 RUN2_LCf0_2 L2_LCf0_2 AXD_LCf0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_LCf0_2 TDr_LCf0_2 CD_LCf0 Eps_LCf0 Ebg_LCf0 run3_LCf0 AXDr_LCf0_2 ENTD_LCf0_2 RUN3_LCf0 L3_LCf0 NX3_LCf0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1SfReRdRbA6S39R1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true P0_LCf0 exits1_LCf0 Cert1_LCf0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1SfRdRcRaA6S39R1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true P0_LCf0 exits1_LCf0 NX0_LCf0 ECert1_LCf0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Theorem free_spine_m_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1SfReRdRbA6S3aR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true PMID_LCf0 exits1_LCf0 Cert1m_LCf0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCf0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_m_LCf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1SfRdRcRaA6S3aR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true PMID_LCf0 exits1_LCf0 NX0m_LCf0 ECert1m_LCf0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCf0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S22S4aS52R2A2S1fS1bS2eR2A2S1dR2S2fA2A2A2S21F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S54R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S53R2A1A1F_;Fa;").

Theorem hdf_LCf0_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S35S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC true) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf0_1 TD_LCf0_1 (sD_of ED_LCf0_1 1) RD_LCf0_1 HeD_LCf0_1 HchkD_LCf0_1 HTD_LCf0_1 DCHK_LCf0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf0_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S35S37R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC true) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf0_1 TD_LCf0_1 (sD_of ED_LCf0_1 1) RD_LCf0_1 HeD_LCf0_1 HchkD_LCf0_1 HTD_LCf0_1 DCHK_LCf0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.
Theorem hdf_LCf0_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S36S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC true) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf0_2 TD_LCf0_2 (sD_of ED_LCf0_2 2) RD_LCf0_2 HeD_LCf0_2 HchkD_LCf0_2 HTD_LCf0_2 DCHK_LCf0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCf0_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S36S38R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC true) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCf0_2 TD_LCf0_2 (sD_of ED_LCf0_2 2) RD_LCf0_2 HeD_LCf0_2 HchkD_LCf0_2 HTD_LCf0_2 DCHK_LCf0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.

Lemma tail_LCf0 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S2aSaRcS28RaA1A3S49SaRdS28RbA1A3S4eReRcA2S2dSaReRcR6R5A5S1aRfA1S1eS0SdG0ScRePcA2A2RcA3S1eS0SdG0ScRfPdA2A2RcA3S42S12S0S0A2S11S0S0ReRdA4S19R12A1A3S46RfReA2S1eS13S18R14A1SfA3S30SfR15A2S40R14S31R16R14R12R11R10RfA6A2S1eS0S48R10A1S34A3S4bS45VCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2cSaS44R16R15S14S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 true CST XGL HCST HXGL TM_LCf0 Erf_LCf0 EC_LCf0 run5_LCf0 XR_LCf0 NX5_LCf0 RUN5_LCf0 L5_LCf0 AXR_LCf0 T0_LCf0 T1_LCf0 T2_LCf0 TR_LCf0 sR_LCf0 RR_LCf0 KEPT_LCf0 KEPT1_LCf0 XS_LCf0 eFRc HER_LCf0 Hchk_LCf0 OBJS_LCf0 HT0_LCf0 HXS_LCf0 OBJS1_LCf0 HT2_LCf0 HTR_LCf0 RCHK_LCf0 TRs_LCf0 Erq_LCf0 Erq2_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.TQ_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.Edr_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.Xf_L0Bf run5d_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.run6_L0Bf XW_LCf0 HTRs_LCf0 CCHK_LCf0 RUN5d_LCf0 L5d_LCf0 AXW_LCf0 ENTQ_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.NX6_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.RUN6_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.L6_L0Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Bf.f0_drain_L0Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Bf.f0_exit_L0Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LCf0 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S4fRaA1S2dSaRcRaR4R3A5S1aRdA1S1eS0SdG0ScRcPcA2A2RaA3S1eS0SdG0ScRdPdA2A2RaA3S42S12S0S0A2S11S0S0RcRbA4S19R10A1A3S46RdRcA2S1eS13S18R12A1SfA3S30SfR13A2S40R12S31R14R12R10RfReRdA6A2S1eS0S48ReA1S34A3S4cS45VCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2cSaS44R14R13S14S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 true CST XGL HCST HXGL TM_LCf0 Erf_LCf0 EC_LCf0 run5_LCf0 XR_LCf0 NX5_LCf0 RUN5_LCf0 L5_LCf0 AXR_LCf0 T0_LCf0 T1_LCf0 T2_LCf0 TR_LCf0 sR_LCf0 RR_LCf0 KEPT_LCf0 KEPT1_LCf0 XS_LCf0 eFRc HER_LCf0 Hchk_LCf0 OBJS_LCf0 HT0_LCf0 HXS_LCf0 OBJS1_LCf0 HT2_LCf0 HTR_LCf0 RCHK_LCf0 TRs_LCf0 Erq_LCf0 Erq2_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.TQ_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.Edr_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.Xf_L0Bf run5d_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.run6_L0Bf XW_LCf0 HTRs_LCf0 CCHK_LCf0 RUN5d_LCf0 L5d_LCf0 AXW_LCf0 ENTQ_LCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.NX6_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.RUN6_L0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.L6_L0Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_qL0Bf.ef0_drain_L0Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.la.F0A_xiL0Bf.ef0_exit_L0Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Cf_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS1cR6R5A2S33A2S1eS13S18RbA1SfA3S30SfRcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate false 0 UStopLe (NVC true) (VFC true) Wa_LCf0 Da_LCf0 Wb_LCf0 Wc_LCf0 Wd_LCf0 Fb_LCf0 XI_LCf0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_LCf0 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_LCf0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCf0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LCf0 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_Cf_0 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S1bS1cR4R3A2S33A2S1eS13S18R9A1SfA3S30SfRaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C false _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate false 0 UStopLe (NVC true) (VFC true) Wa_LCf0 Da_LCf0 Wb_LCf0 Wc_LCf0 Wd_LCf0 Fb_LCf0 XI_LCf0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_LCf0 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_LCf0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCf0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_LCf0 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S1fS20S1fS1bS2eR2A2S1dR2S2fA2A2A1S20S1fS1bZ17db48R2A2S1dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_Cf_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS1cR6R5A2S33A2S1eS13S18RbA1S16A3S30SfRcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Certi_0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 0 UStopLe (NVC true) (VFC true) Wbm_LCf0 Wcm_LCf0 Wdm_LCf0 Fb_LCf0 XIm_LCf0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_LCf0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_LCf0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCf0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LCf0 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_Cf_0 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S1bS1cR4R3A2S33A2S1eS13S18R9A1S16A3S30SfRaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Dai_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wbi_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.Wci_0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.F0A_m0A.ECerti_0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false 0 UStopLe (NVC true) (VFC true) Wbm_LCf0 Wcm_LCf0 Wdm_LCf0 Fb_LCf0 XIm_LCf0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_LCf0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_LCf0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCf0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_LCf0 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALCf0.
End F0A_aLCf0.

