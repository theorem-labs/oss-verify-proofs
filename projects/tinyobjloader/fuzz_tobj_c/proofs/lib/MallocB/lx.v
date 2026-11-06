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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo lq.

(* [comment removed for export] *)
Module F0A_cCe0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "false"; "list"; "option"; "Some"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "leaves_at"; "BIGX"; "MSE"; "PSE"; "sM_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe0"; "C4_Ce0"; "ED_Ce0_1"; "ED_Ce0_2"; "EC_Ce0"; "C2_Ce0_1"; "C2_Ce0_2"; "C3_Ce0"; "P0_Ce0"; "RR_Ce0"; "T1_Ce0"; "CD_Ce0"; "TR_Ce0"; "sR_Ce0"; "Ems_Ce0"; "Eps_Ce0"; "PMID_Ce0"; "RD_Ce0_1"; "RD_Ce0_2"; "S1c_Ce0_1"; "S1c_Ce0_2"; "TM_Ce0"; "TRs_Ce0"; "exits1_Ce0"; "run3_Ce0"; "RM_Ce0"; "TD_Ce0_1"; "TD_Ce0_2"; "TM0_Ce0"; "run2_Ce0_1"; "run2_Ce0_2"; "run4_Ce0"; "run5_Ce0"; "run5d_Ce0"; "Ebg_Ce0"; "EfD_Ce0_1"; "EfD_Ce0_2"; "Erf_Ce0"; "Erq2_Ce0"; "Erq_Ce0"; "KEPT1_Ce0"; "T0_Ce0"; "T2_Ce0"; "TDr_Ce0_1"; "TDr_Ce0_2"; "W_Ce0"; "run1_Ce0"; "st_Ce0"; "KEPT_Ce0"; "XR_Ce0"; "XS_Ce0"; "XW_Ce0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc";
"P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be"; "TQ_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_Ce0 : list ulink := Wcan 0.
Definition st_Ce0 : ustop := UStopLe.
Definition P0_Ce0 : axst := ltac2:(tb__ "0|0|
Sa4S8S6dS6fSbA4").

Definition run1_Ce0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S23SaS13A1A3S48A3").

Definition S1c_Ce0_1 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aS3S48A1A1Z1A3").
Definition C2_Ce0_1 : axst := C2_of S1c_Ce0_1.
Definition run2_Ce0_1 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S24SaS13A1A3S45A3").
Definition EfD_Ce0_1 : axst := leaf 0 run2_Ce0_1.
Definition ED_Ce0_1 : axst := ED_of EfD_Ce0_1.
Definition RD_Ce0_1 : list sobj := RD_of ED_Ce0_1 1.
Definition TD_Ce0_1 : axst := TD_of ED_Ce0_1 1.
Definition TDr_Ce0_1 : axst := TDr_of TD_Ce0_1.
Definition S1c_Ce0_2 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aS3S48A1A1Z2A3").
Definition C2_Ce0_2 : axst := C2_of S1c_Ce0_2.
Definition run2_Ce0_2 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S24SaS13A1A3S46A3").
Definition EfD_Ce0_2 : axst := leaf 0 run2_Ce0_2.
Definition ED_Ce0_2 : axst := ED_of EfD_Ce0_2.
Definition RD_Ce0_2 : list sobj := RD_of ED_Ce0_2 2.
Definition TD_Ce0_2 : axst := TD_of ED_Ce0_2 2.
Definition TDr_Ce0_2 : axst := TDr_of TD_Ce0_2.
Definition exits1_Ce0 : list axst := ltac2:(tb__ "0|0|
S9S2S53S9S2S54SaS2A1A3A3").

Definition CD_Ce0 : axst := CD_of TDr_Ce0_1.
Definition run3_Ce0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S28S9S13S26SaS13A1A3A3S4bA3").
Definition Eps_Ce0 : axst := leaf 0 run3_Ce0.
Definition Ebg_Ce0 : axst := leaf 1 run3_Ce0.
Definition C3_Ce0 : axst := C3_of Eps_Ce0.
Definition run4_Ce0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S27SaS13A1A3S47A3").
Definition Ems_Ce0 : axst := leaf 0 run4_Ce0.
Definition C4_Ce0 : axst := C4_of Ems_Ce0.
Definition RM_Ce0 : list sobj := RM_of C4_Ce0.
Definition TM0_Ce0 : axst := TM0_of C4_Ce0.
Definition TM_Ce0 : axst := TM_of C4_Ce0.

Definition run5_Ce0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S8eSaS13A1A3S55A3").
Definition Erf_Ce0 : axst := leaf 0 run5_Ce0.
Definition XR_Ce0 : list axform := XRC Erf_Ce0.
Definition EC_Ce0 : axst := EC_of Erf_Ce0.
Definition sR_Ce0 : wsub := sR_of (E3_of Erf_Ce0).
Definition RR_Ce0 : list sobj := RR_of EC_Ce0 sR_Ce0.
Definition KEPT_Ce0 : list sobj := KEPT_of EC_Ce0 RR_Ce0.

Definition T0_Ce0 : axst := ltac2:(tb__ "0|0|
Sa5S44S4dS49A3").
Definition XS_Ce0 : list axform := XS_of T0_Ce0.
Definition T1_Ce0 : axst := T1_of T0_Ce0.
Definition KEPT1_Ce0 : list sobj := KEPT1_of T1_Ce0.
Definition T2_Ce0 : axst := T2_of T1_Ce0.
Definition TR_Ce0 : axst := TR_of T1_Ce0.

Definition TRs_Ce0 : axst := TRs_of TR_Ce0.
Definition run5d_Ce0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S9S13S3eSaS13A1A3S56A3").
Definition Erq_Ce0 : axst := leaf 0 run5d_Ce0.
Definition XW_Ce0 : list axform := XW Erq_Ce0.
Definition Erq2_Ce0 : axst := Erq2_of Erq_Ce0.

Definition PMID_Ce0 : axst := ltac2:(tb__ "0|0|
S9bS8S6dS6fS7eS7cS17S7dS74SbA1A4S75SbA1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_Ce0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S48A1A1A2S8A3"). Proof. vmr. Qed.
Lemma Cert1_Ce0 : ltac2:(tb__ "0|0|
S0S7S81S40S21S9S13S23SaS13A1A3S3fS9S2S48SaS2A1A3S57A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_Ce0 exits1_Ce0 run1_Ce0); [unfold run1_Ce0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_Ce0 : ltac2:(tb__ "0|2|
S0S7S82S40S21S9S13S23SaS13A1A3S3fS9S7fS80S48Z1S1cZ0M0A1M1A3SaS7fA1A3S7eS2S7fS2S80R1G0G1A3LE;S57A4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_Ce0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_Ce0) run1_Ce0); [unfold run1_Ce0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_Ce0_1 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S53A1S3S45A1A2SeG3S10G1G2S9G0S10S16S16S2eS2fA4SaG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Ce0_1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S45A1M0A1S8A3S1S0S14S15G0A1S15S3S53A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Ce0_1 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S45A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_Ce0_1 : ltac2:(tb__ "0|0|
S0S2S5S53S3S45A1A2S45A3"). Proof. vmr. Qed.
Lemma RUN2_Ce0_1 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S24SaS13A1A3S45A3S5dA3"). Proof. unfold run2_Ce0_1; reflexivity. Qed.
Lemma L2_Ce0_1 : ltac2:(tb__ "0|0|
S1S0S7S25S5dS9S13S24SaS13A1A3A2S8A3S0S2S3dU0S5dA2S63A3A2"). Proof. Time (split; [vmr | unfold EfD_Ce0_1; reflexivity]). Qed.
Lemma AXD_Ce0_1 : ltac2:(tb__ "0|0|
S0SdS2A1S79S63S2cA2SeS2S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Ce0_1 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S87S42S83Z1M1A1S22S42G1A2A3SeG0S51A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Ce0_1 : ltac2:(tb__ "0|1|
S0S7S89S42S83Z1M0A1S22S42G0A2S51S9S2S84G0A1SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_Ce0_1 : ltac2:(tb__ "0|1|
S0S2S5aS86S88S22S42Z1M0A2S83G0A1S84G0A1S42S51A5S1aS3S42A1A1A2A3").
Proof. unfold TD_Ce0_1, TD_of, RD_Ce0_1; reflexivity. Qed.
Lemma DCHK_Ce0_1 : ltac2:(tb__ "0|2|
S0S7S92U0M0S76S74SbA1G0A2Z1M1S42S5aS22S42G1A2S51A7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_Ce0_1 : ltac2:(tb__ "0|0|
S0SdS2A1S79S5aS2dA2SeS2S6bA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Ce0_1 : ltac2:(tb__ "0|0|
S0S7Sa6S6bS4bA2S8A3"). Proof. Time vmr. Qed.
Lemma D2_Ce0_2 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S54A1S3S46A1A2SeG3S10G1G2S9G0S10S16S16S2eS2fA4SaG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Ce0_2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S46A1M0A1S8A3S1S0S14S15G0A1S15S3S54A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Ce0_2 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S46A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_Ce0_2 : ltac2:(tb__ "0|0|
S0S2S5S54S3S46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_Ce0_2 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S24SaS13A1A3S46A3S5eA3"). Proof. unfold run2_Ce0_2; reflexivity. Qed.
Lemma L2_Ce0_2 : ltac2:(tb__ "0|0|
S1S0S7S25S5eS9S13S24SaS13A1A3A2S8A3S0S2S3dU0S5eA2S64A3A2"). Proof. Time (split; [vmr | unfold EfD_Ce0_2; reflexivity]). Qed.
Lemma AXD_Ce0_2 : ltac2:(tb__ "0|0|
S0SdS2A1S79S64S2cA2SeS2S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Ce0_2 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S87S43S83Z2M1A1S22S43G1A2A3SeG0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Ce0_2 : ltac2:(tb__ "0|1|
S0S7S89S43S83Z2M0A1S22S43G0A2S52S9S2S84G0A1SaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_Ce0_2 : ltac2:(tb__ "0|1|
S0S2S5bS86S88S22S43Z2M0A2S83G0A1S84G0A1S43S52A5S1aS3S43A1A1A2A3").
Proof. unfold TD_Ce0_2, TD_of, RD_Ce0_2; reflexivity. Qed.
Lemma DCHK_Ce0_2 : ltac2:(tb__ "0|2|
S0S7S92U0M0S76S74SbA1G0A2Z2M1S43S5bS22S43G1A2S52A7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_Ce0_2 : ltac2:(tb__ "0|0|
S0SdS2A1S79S5bS2dA2SeS2S6cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Ce0_2 : ltac2:(tb__ "0|0|
S0S7Sa6S6cS4bA2S8A3"). Proof. Time vmr. Qed.
Lemma RUN3_Ce0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S28S9S13S26SaS13A1A3A3S4bA3S58A3"). Proof. unfold run3_Ce0; reflexivity. Qed.
Lemma L3_Ce0 : ltac2:(tb__ "0|0|
S1S0S7S25S58S9S13S28S9S13S26SaS13A1A3A3A2S8A3S1S0S2S3dU0S58A2S4fA3S0S2S3dU1S58A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_Ce0 | unfold Ebg_Ce0]; reflexivity]). Qed.
Lemma NX3_Ce0 : ltac2:(tb__ "0|1|
S1S0S7S7aS3fS15S3S4bA1M0A1A2S8A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_Ce0 : ltac2:(tb__ "0|0|
S0S7S91S18S20SabA1S1aS3S62A1A1A3S8A3"). Proof. vmr. Qed.
Lemma D3_Ce0 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S85S3S4fA1S3S47A1A2SeG2S10G0G1S34SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_Ce0 : ltac2:(tb__ "0|0|
S0S2S5S4fS3S47A1A2S47A3"). Proof. vmr. Qed.
Lemma NX3b_Ce0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S47A1A1A2S8A3"). Proof. vmr. Qed.
Lemma W3_Ce0 : ltac2:(tb__ "0|1|
S1S0S7S19S3S47A1M0A1S8A3S1S0S14S15G0A1S15S3S4fA1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_Ce0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S27SaS13A1A3S47A3S5fA3"). Proof. unfold run4_Ce0; reflexivity. Qed.
Lemma L4_Ce0 : ltac2:(tb__ "0|0|
S1S0S7S25S5fS9S13S27SaS13A1A3A2S8A3S0S2S3dU0S5fA2S4eA3A2"). Proof. Time (split; [vmr | unfold Ems_Ce0; reflexivity]). Qed.
Lemma D4_Ce0 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S85S3S4eA1S3S41A1A2SeG2S10G0G1S35SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_Ce0 : ltac2:(tb__ "0|0|
S0S2S5S4eS3S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_Ce0 : ltac2:(tb__ "0|1|
S1S0S7S19S3S41A1M0A1S8A3S1S0S14S15G0A1S15S3S4eA1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_Ce0 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S87S41S8bS29S41A1A3SeG0S59A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_Ce0 : ltac2:(tb__ "0|0|
S0S7S8aS41S8bS29S41A1S59S7eS4S2S6S8cA4A5S8A3"). Proof. Time vmr. Qed.
Lemma HTM_Ce0 : ltac2:(tb__ "0|0|
S0S2S88S29S41A1S8bS31S41S59A5S5cA3"). Proof. unfold TM0_Ce0, TM0_of, RM_Ce0; reflexivity. Qed.
Lemma FBM_Ce0 : ltac2:(tb__ "0|3|
S1S0S7S90S18S1dS15S3S41A1M0A1M1A1S1aG0A1M2A3S8A3S1S0S7S90S18S1dS15S3S5cA1A1A1G2A3S8A3S0S7S7aS3fG1A2S8A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_Ce0 : ltac2:(tb__ "0|0|
S0S2S86S5cS1aS3S41A1A1A2S55A3"). Proof. vmr. Qed.

Lemma NX5_Ce0 : ltac2:(tb__ "0|1|
S1S0S7S7aS3fS15S3S55A1M0A1A2S8A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_Ce0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S8eSaS13A1A3S55A3S60A3"). Proof. unfold run5_Ce0; reflexivity. Qed.
Lemma L5_Ce0 : ltac2:(tb__ "0|0|
S1S0S7S25S60S9S13S8eSaS13A1A3A2S8A3S0S2S3dU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erf_Ce0; reflexivity]). Qed.
Lemma AXR_Ce0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S65S71A2SeS2S44A2A3"). Proof. Time vmr. Qed.

Lemma HER_Ce0 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S87S44S8dS4dA3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_Ce0 : ltac2:(tb__ "0|0|
S0S7S89S44S8dS4dS49S9S2S8fSaS2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma OBJS_Ce0 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S44A1A1S11S17S70S49A3A3"). Proof. Time vmr. Qed.
Lemma HT0_Ce0 : ltac2:(tb__ "0|0|
S0S2S69S86S88S4dS8dS8fS44S49A5S1aS3S44A1A1A2A3"). Proof. unfold T0_Ce0, T0_of; reflexivity. Qed.
Lemma HXS_Ce0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S69S72A2SeS2S4aA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_Ce0 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S4aA1A1S11S17S68S9S17S30S9S17S7dS77A1S9S17S7dS78A1SaS17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_Ce0 : ltac2:(tb__ "0|0|
S0S2S6aS5S4aSa7S3S4aA1S68A2A2A3"). Proof. unfold T2_Ce0, T2_of, KEPT1_Ce0; reflexivity. Qed.
Lemma HTR_Ce0 : ltac2:(tb__ "0|2|
S0S2S4cSa0S6aS9S7cSa1Sa3S15S3S4aA1A1M0S7bG0A1M1A3SaS7cA1A3S7bG1A1A3A3"). Proof. unfold TR_Ce0, TR_of, T2_Ce0; reflexivity. Qed.
Lemma RCHK_Ce0 : ltac2:(tb__ "0|0|
S0S7Sa2U0SbS44S4aS4cS4dS49Sa3A8S8A3"). Proof. Time vmr. Qed.

Lemma HTRs_Ce0 : ltac2:(tb__ "0|0|
S0S2S56Sa0S4cSadS15S3S4cA1A1A3A3"). Proof. unfold TRs_Ce0, TRs_of; reflexivity. Qed.
Lemma CCHK_Ce0 : ltac2:(tb__ "0|0|
S0S7SaeU0S7S37L_;SbS33S32X7x2S4cS56A4S8A3"). Proof. Time vmr. Qed.
Lemma RUN5d_Ce0 : ltac2:(tb__ "0|0|
S0ScS4A1S3cS21S9S13S3eSaS13A1A3S56A3S61A3"). Proof. unfold run5d_Ce0; reflexivity. Qed.
Lemma L5d_Ce0 : ltac2:(tb__ "0|0|
S1S0S7S25S61S9S13S3eSaS13A1A3A2S8A3S0S2S3dU0S61A2S67A3A2"). Proof. Time (split; [vmr | unfold Erq_Ce0; reflexivity]). Qed.
Lemma AXW_Ce0 : ltac2:(tb__ "0|0|
S0SdS2A1S79S67S73A2SeS2S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_Ce0 : ltac2:(tb__ "0|0|
S0S7S36S66SacA2S8A3"). Proof. Time vmr. Qed.

Lemma Wa_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S94S39U0A1S38A2A1S8A3"). Proof. vmr. Qed.
Lemma Da_Ce0 : ltac2:(tb__ "0|5|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S85S3S3bS3aS39U0A1M4S38A3A1S94G4S38A2A2SeG3S10G1G2S9G0S10S16S16S1fP18A1S1cSaaA1A4SaG0A1A3SaS18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S97S39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wc_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S98S39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wd_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S99S39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Fb_Ce0 : ltac2:(tb__ "0|0|
S0S7S90S18S1dSa9A1S95S8S39U0A1S38S75SbA1A4A3S8A3"). Proof. vmr. Qed.
Lemma XI_Ce0 : ltac2:(tb__ "0|4|
S0SdS2A1S79S9aS8S39U0M0A1M1S38S74SbA1M2S75SbA1M3A5S93G0S12S7cG2A2A2A2SeS2S96S8G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_Ce0 : ltac2:(tb__ "0|0|
S0S7S7aS3fS15S3S50A1A1A2S8A3"). Proof. vmr. Qed.
Definition Cert1m_Ce0__runs : ltac2:(tb__ "0|0|
ScSdScS4A1A1A1") := ltac2:(tb__ "0|0|
Sa8S40S21S9S13S23SaS13A1A3S9S2S50SaS2A1A3A4").
Lemma Cert1m_Ce0 : ltac2:(tb__ "0|0|
S0S7S81S40S21S9S13S23SaS13A1A3S3fS9S2S50SaS2A1A3S57A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_Ce0] exits1_Ce0 Cert1m_Ce0__runs); [unfold Cert1m_Ce0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_Ce0 : ltac2:(tb__ "0|2|
S0S7S82S40S21S9S13S23SaS13A1A3S3fS9S7fS80S50Z1S1cZ0M0A1M1A3SaS7fA1A3S7eS2S7fS2S80R1G0G1A3LE;S57A4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_Ce0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_Ce0) Cert1m_Ce0__runs); [unfold Cert1m_Ce0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S9cS39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wcm_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S9dS39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma Wdm_Ce0 : ltac2:(tb__ "0|0|
S0S7S19S9eS39U0A1S38S74SbA1A3A1S8A3"). Proof. vmr. Qed.
Lemma XIm_Ce0 : ltac2:(tb__ "0|4|
S0SdS2A1S79S9fS8S39U0M0A1M1S38S74SbA1M2S75SbA1M3A5S93G0S12S7cG2A2A2A2SeS2S9bS8G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cCe0.

(* [comment removed for export] *)
Module F0A_aCe0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "pair"; "prod"; "true"; "bool"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe0"; "ED_Ce0_1"; "ED_Ce0_2"; "TD_Ce0_1"; "TD_Ce0_2"; "P0_Ce0"; "PMID_Ce0"; "TM_Ce0"; "exits1_Ce0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_aCe0.ACe0"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACe0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S3fU0S1S10R6VKc;R5A6S3bR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S3fU0S1S10R6VKc;R5A6S3bR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6S23SbS42S23R2S3cA3S27Vsegs;R11S29Vsegs;S3fG1S1S13R10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_Ce0 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_Ce0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_Ce0 Q BGF_Ce0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_Ce0 C3_Ce0 Ems_Ce0 C4_Ce0 TM0_Ce0 run4_Ce0 RM_Ce0 D3_Ce0 W3_Ce0 EQ3_Ce0 NX3b_Ce0 RUN4_Ce0 L4_Ce0 D4_Ce0 W4_Ce0 EQ4_Ce0
             HeM_Ce0 HchkM_Ce0 HTM_Ce0 FBM_Ce0 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_Ce0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Ce0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_Ce0_1 C2_Ce0_1 EfD_Ce0_1 ED_Ce0_1 run2_Ce0_1 D2_Ce0_1 W2_Ce0_1 NX2_Ce0_1 EQ2_Ce0_1 RUN2_Ce0_1 L2_Ce0_1 AXD_Ce0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_Ce0_1 TDr_Ce0_1 CD_Ce0 Eps_Ce0 Ebg_Ce0 run3_Ce0 AXDr_Ce0_1 ENTD_Ce0_1 RUN3_Ce0 L3_Ce0 NX3_Ce0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0 UStopLe true S1c_Ce0_2 C2_Ce0_2 EfD_Ce0_2 ED_Ce0_2 run2_Ce0_2 D2_Ce0_2 W2_Ce0_2 NX2_Ce0_2 EQ2_Ce0_2 RUN2_Ce0_2 L2_Ce0_2 AXD_Ce0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_Ce0_2 TDr_Ce0_2 CD_Ce0 Eps_Ce0 Ebg_Ce0 run3_Ce0 AXDr_Ce0_2 ENTD_Ce0_2 RUN3_Ce0 L3_Ce0 NX3_Ce0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5S23SbS42S23R2S3cA3S26Vsegs;S29Vsegs;S3fG1S1S13RfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_Ce0 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_Ce0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_Ce0 Q BGF_Ce0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_Ce0 C3_Ce0 Ems_Ce0 C4_Ce0 TM0_Ce0 run4_Ce0 RM_Ce0 D3_Ce0 W3_Ce0 EQ3_Ce0 NX3b_Ce0 RUN4_Ce0 L4_Ce0 D4_Ce0 W4_Ce0 EQ4_Ce0
             HeM_Ce0 HchkM_Ce0 HTM_Ce0 FBM_Ce0 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_Ce0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Ce0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_Ce0_1 C2_Ce0_1 EfD_Ce0_1 ED_Ce0_1 run2_Ce0_1 D2_Ce0_1 W2_Ce0_1 NX2_Ce0_1 EQ2_Ce0_1 RUN2_Ce0_1 L2_Ce0_1 AXD_Ce0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_Ce0_1 TDr_Ce0_1 CD_Ce0 Eps_Ce0 Ebg_Ce0 run3_Ce0 AXDr_Ce0_1 ENTD_Ce0_1 RUN3_Ce0 L3_Ce0 NX3_Ce0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_Ce0_2 C2_Ce0_2 EfD_Ce0_2 ED_Ce0_2 run2_Ce0_2 D2_Ce0_2 W2_Ce0_2 NX2_Ce0_2 EQ2_Ce0_2 RUN2_Ce0_2 L2_Ce0_2 AXD_Ce0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_Ce0_2 TDr_Ce0_2 CD_Ce0 Eps_Ce0 Ebg_Ce0 run3_Ce0 AXDr_Ce0_2 ENTD_Ce0_2 RUN3_Ce0 L3_Ce0 NX3_Ce0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1S13ReRdRbA6S39R1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true P0_Ce0 exits1_Ce0 Cert1_Ce0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Ce0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1S13RdRcRaA6S39R1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true P0_Ce0 exits1_Ce0 NX0_Ce0 ECert1_Ce0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Ce0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Theorem free_spine_m_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbSfSeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1S13ReRdRbA6S3aR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true PMID_Ce0 exits1_Ce0 Cert1m_Ce0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Ce0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_m_Ce0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1S13RdRcRaA6S3aR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true PMID_Ce0 exits1_Ce0 NX0m_Ce0 ECert1m_Ce0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Ce0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S22S4aS52R2A2S1fS1bS2eR2A2S1dR2S2fA2A2A2S21F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S54R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S53R2A1A1F_;Fa;").

Theorem hdf_Ce0_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S35S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC false) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce0_1 TD_Ce0_1 (sD_of ED_Ce0_1 1) RD_Ce0_1 HeD_Ce0_1 HchkD_Ce0_1 HTD_Ce0_1 DCHK_Ce0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_Ce0_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S35S37R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC false) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce0_1 TD_Ce0_1 (sD_of ED_Ce0_1 1) RD_Ce0_1 HeD_Ce0_1 HchkD_Ce0_1 HTD_Ce0_1 DCHK_Ce0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.
Theorem hdf_Ce0_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S36S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC false) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce0_2 TD_Ce0_2 (sD_of ED_Ce0_2 2) RD_Ce0_2 HeD_Ce0_2 HchkD_Ce0_2 HTD_Ce0_2 DCHK_Ce0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_Ce0_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30S10RfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S36S38R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC false) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Ce0_2 TD_Ce0_2 (sD_of ED_Ce0_2 2) RD_Ce0_2 HeD_Ce0_2 HchkD_Ce0_2 HTD_Ce0_2 DCHK_Ce0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.

Lemma tail_Ce0 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbSfSeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S2aSaRcS28RaA1A3S49SaRdS28RbA1A3S4eReRcA2S2dSaReRcR6R5A5S1aRfA1S1eS0SdG0ScRePcA2A2RcA3S1eS0SdG0ScRfPdA2A2RcA3S42S12S0S0A2S11S0S0ReRdA4S19R12A1A3S46RfReA2S1eS14S18R14A1S13A3S30S10R15A2S40R14S31R16R14R12R11R10RfA6A2S1eS0S48R10A1S34A3S4bS45VCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2cSaS44R16R15S15S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R18Z18A2R17A5A4S16G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 false CST XGL HCST HXGL TM_Ce0 Erf_Ce0 EC_Ce0 run5_Ce0 XR_Ce0 NX5_Ce0 RUN5_Ce0 L5_Ce0 AXR_Ce0 T0_Ce0 T1_Ce0 T2_Ce0 TR_Ce0 sR_Ce0 RR_Ce0 KEPT_Ce0 KEPT1_Ce0 XS_Ce0 eFRc HER_Ce0 Hchk_Ce0 OBJS_Ce0 HT0_Ce0 HXS_Ce0 OBJS1_Ce0 HT2_Ce0 HTR_Ce0 RCHK_Ce0 TRs_Ce0 Erq_Ce0 Erq2_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.TQ_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.Edr_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.Xf_0Be run5d_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.run6_0Be XW_Ce0 HTRs_Ce0 CCHK_Ce0 RUN5d_Ce0 L5d_Ce0 AXW_Ce0 ENTQ_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.NX6_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.RUN6_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.L6_0Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Be.f0_drain_0Be CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l6.F0A_xi0Be.f0_exit_0Be CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Ce0 : ltac2:(tb__ "0|3|
S17S2SbSfSeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S4fRaA1S2dSaRcRaR4R3A5S1aRdA1S1eS0SdG0ScRcPcA2A2RaA3S1eS0SdG0ScRdPdA2A2RaA3S42S12S0S0A2S11S0S0RcRbA4S19R10A1A3S46RdRcA2S1eS14S18R12A1S13A3S30S10R13A2S40R12S31R14R12R10RfReRdA6A2S1eS0S48ReA1S34A3S4cS45VCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2cSaS44R14R13S15S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R16Z18A2R15A5A4S16G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 false CST XGL HCST HXGL TM_Ce0 Erf_Ce0 EC_Ce0 run5_Ce0 XR_Ce0 NX5_Ce0 RUN5_Ce0 L5_Ce0 AXR_Ce0 T0_Ce0 T1_Ce0 T2_Ce0 TR_Ce0 sR_Ce0 RR_Ce0 KEPT_Ce0 KEPT1_Ce0 XS_Ce0 eFRc HER_Ce0 Hchk_Ce0 OBJS_Ce0 HT0_Ce0 HXS_Ce0 OBJS1_Ce0 HT2_Ce0 HTR_Ce0 RCHK_Ce0 TRs_Ce0 Erq_Ce0 Erq2_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.TQ_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.Edr_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.Xf_0Be run5d_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.run6_0Be XW_Ce0 HTRs_Ce0 CCHK_Ce0 RUN5d_Ce0 L5d_Ce0 AXW_Ce0 ENTQ_Ce0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.NX6_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.RUN6_0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.L6_0Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Be.ef0_drain_0Be CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l6.F0A_xi0Be.ef0_exit_0Be CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Ce_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS33S1cR6Z10A2A2S1eS14S18RbA1S13A3S30S10RcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C true _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate true 0 UStopLe (NVC false) (VFC false) Wa_Ce0 Da_Ce0 Wb_Ce0 Wc_Ce0 Wd_Ce0 Fb_Ce0 XI_Ce0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_Ce0 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_Ce0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Ce0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_Ce0 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_Ce_0 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S1bS33S1cR4Z10A2A2S1eS14S18R9A1S13A3S30S10RaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C true _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate true 0 UStopLe (NVC false) (VFC false) Wa_Ce0 Da_Ce0 Wb_Ce0 Wc_Ce0 Wd_Ce0 Fb_Ce0 XI_Ce0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_Ce0 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_Ce0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Ce0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_Ce0 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S1fS20S1fS1bS2eR2A2S1dR2S2fA2A2A1S20S1fS1bZ17db48R2A2S1dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_Ce_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS33S1cR6Z10A2A2S1eS14S18RbA1S10A3S30S10RcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 0 UStopLe (NVC false) (VFC false) Wbm_Ce0 Wcm_Ce0 Wdm_Ce0 Fb_Ce0 XIm_Ce0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_Ce0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_Ce0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Ce0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_Ce0 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_Ce_0 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S15S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S25S3R6A1S1bS33S1cR4Z10A2A2S1eS14S18R9A1S10A3S30S10RaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true 0 UStopLe (NVC false) (VFC false) Wbm_Ce0 Wcm_Ce0 Wdm_Ce0 Fb_Ce0 XIm_Ce0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_Ce0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_Ce0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Ce0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_Ce0 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ACe0.
End F0A_aCe0.

(* [comment removed for export] *)
Module F0A_cCe1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "false"; "option"; "Some"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "BIGX"; "F_typ"; "MSE"; "PSE"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe1"; "C4_Ce1"; "ED_Ce1_1"; "ED_Ce1_2"; "ED_Ce1_3"; "EC_Ce1"; "C2_Ce1_1"; "C2_Ce1_2"; "C2_Ce1_3"; "C3_Ce1"; "P0_Ce1"; "CD_Ce1"; "RR_Ce1"; "T1_Ce1"; "TR_Ce1"; "sR_Ce1"; "Ems_Ce1"; "Eps_Ce1"; "PMID_Ce1"; "RD_Ce1_1"; "RD_Ce1_2"; "RD_Ce1_3"; "S1c_Ce1_1"; "S1c_Ce1_2"; "S1c_Ce1_3"; "TM_Ce1"; "TRs_Ce1"; "exits1_Ce1"; "run3_Ce1"; "RM_Ce1"; "TD_Ce1_1"; "TD_Ce1_2"; "TD_Ce1_3"; "TM0_Ce1"; "run1_Ce1"; "run2_Ce1_1"; "run2_Ce1_2"; "run2_Ce1_3"; "run4_Ce1"; "run5_Ce1"; "run5d_Ce1"; "Ebg_Ce1"; "EfD_Ce1_1"; "EfD_Ce1_2"; "EfD_Ce1_3"; "Erf_Ce1"; "Erq2_Ce1"; "Erq_Ce1"; "KEPT1_Ce1"; "T0_Ce1"; "T2_Ce1"; "TDr_Ce1_1"; "TDr_Ce1_2"; "TDr_Ce1_3"; "W_Ce1"; "st_Ce1"; "KEPT_Ce1"; "XR_Ce1"; "XS_Ce1"; "XW_Ce1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg";
"sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "TQ_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "pair"; "prod"; "true"; "bool"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe1"; "ED_Ce1_1"; "ED_Ce1_2"; "ED_Ce1_3"; "TD_Ce1_1"; "TD_Ce1_2"; "TD_Ce1_3"; "P0_Ce1"; "PMID_Ce1"; "TM_Ce1"; "exits1_Ce1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_aCe1.ACe1"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCe1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lq.
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
  exact (c_tail 1 false CST XGL HCST HXGL TM_Ce1 Erf_Ce1 EC_Ce1 run5_Ce1 XR_Ce1 NX5_Ce1 RUN5_Ce1 L5_Ce1 AXR_Ce1 T0_Ce1 T1_Ce1 T2_Ce1 TR_Ce1 sR_Ce1 RR_Ce1 KEPT_Ce1 KEPT1_Ce1 XS_Ce1 eFRc HER_Ce1 Hchk_Ce1 OBJS_Ce1 HT0_Ce1 HXS_Ce1 OBJS1_Ce1 HT2_Ce1 HTR_Ce1 RCHK_Ce1 TRs_Ce1 Erq_Ce1 Erq2_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.TQ_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.Edr_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.Xf_1Be run5d_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.run6_1Be XW_Ce1 HTRs_Ce1 CCHK_Ce1 RUN5d_Ce1 L5d_Ce1 AXW_Ce1 ENTQ_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.NX6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.RUN6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.L6_1Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Be.f0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Be.f0_exit_1Be CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Ce1 : ltac2:(tb__ "0|3|
S17S2SbSfSeQ40M0A1A1M1S0S0S0S48G1S3bS3R9A1S51RaA1S2bSaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S3aS12S0S0A2S11S0S0RcRbA4S18R10A1A3S47RdRcA2S1bS14S19R12A1S13A3S30S10R13A2S35R12S31R14R12R10RfReRdA6A2S1bS0S49ReA1S39A3S4fS3cVCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2fSaS4aR14R13S15S12S23S2eA2M2S11S23S2eS6S4S7U1A1S1A3S5S2bSaA1VCST;VXGL;S52R16Z18A2R15A5A4S16G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 1 false CST XGL HCST HXGL TM_Ce1 Erf_Ce1 EC_Ce1 run5_Ce1 XR_Ce1 NX5_Ce1 RUN5_Ce1 L5_Ce1 AXR_Ce1 T0_Ce1 T1_Ce1 T2_Ce1 TR_Ce1 sR_Ce1 RR_Ce1 KEPT_Ce1 KEPT1_Ce1 XS_Ce1 eFRc HER_Ce1 Hchk_Ce1 OBJS_Ce1 HT0_Ce1 HXS_Ce1 OBJS1_Ce1 HT2_Ce1 HTR_Ce1 RCHK_Ce1 TRs_Ce1 Erq_Ce1 Erq2_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.TQ_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.Edr_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.Xf_1Be run5d_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.run6_1Be XW_Ce1 HTRs_Ce1 CCHK_Ce1 RUN5d_Ce1 L5d_Ce1 AXW_Ce1 ENTQ_Ce1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.NX6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.RUN6_1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.L6_1Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Be.ef0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Be.ef0_exit_1Be CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
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
S0S4dVCST;R1A2S1cS1dS1cS20S2cR2A2S22R2S2dA2A2A1S1dS1cS20Z17db48R2A2S22R2Z17db4cA2A2A1A2F_;Fa;").
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
Module F0A_cCf0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "false"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "leaves_at"; "BIGX"; "MSE"; "PSE"; "sM_of"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCf0"; "C4_Cf0"; "ED_Cf0_1"; "ED_Cf0_2"; "EC_Cf0"; "C2_Cf0_1"; "C2_Cf0_2"; "C3_Cf0"; "P0_Cf0"; "RR_Cf0"; "T1_Cf0"; "CD_Cf0"; "TR_Cf0"; "sR_Cf0"; "Ems_Cf0"; "Eps_Cf0"; "PMID_Cf0"; "RD_Cf0_1"; "RD_Cf0_2"; "S1c_Cf0_1"; "S1c_Cf0_2"; "TM_Cf0"; "TRs_Cf0"; "exits1_Cf0"; "run3_Cf0"; "RM_Cf0"; "TD_Cf0_1"; "TD_Cf0_2"; "TM0_Cf0"; "run2_Cf0_1"; "run2_Cf0_2"; "run4_Cf0"; "run5_Cf0"; "run5d_Cf0"; "Ebg_Cf0"; "EfD_Cf0_1"; "EfD_Cf0_2"; "Erf_Cf0"; "Erq2_Cf0"; "Erq_Cf0"; "KEPT1_Cf0"; "T0_Cf0"; "T2_Cf0"; "TDr_Cf0_1"; "TDr_Cf0_2"; "W_Cf0"; "run1_Cf0"; "st_Cf0"; "KEPT_Cf0"; "XR_Cf0"; "XS_Cf0"; "XW_Cf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc";
"P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf"; "TQ_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_Cf0 : list ulink := Wcan 0.
Definition st_Cf0 : ustop := UStopLe.
Definition P0_Cf0 : axst := ltac2:(tb__ "0|0|
Sa4S2S6dS6fS2A4").

Definition run1_Cf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S23S5S13A1A3S48A3").

Definition S1c_Cf0_1 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aSfS48A1A1Z1A3").
Definition C2_Cf0_1 : axst := C2_of S1c_Cf0_1.
Definition run2_Cf0_1 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S24S5S13A1A3S45A3").
Definition EfD_Cf0_1 : axst := leaf 0 run2_Cf0_1.
Definition ED_Cf0_1 : axst := ED_of EfD_Cf0_1.
Definition RD_Cf0_1 : list sobj := RD_of ED_Cf0_1 1.
Definition TD_Cf0_1 : axst := TD_of ED_Cf0_1 1.
Definition TDr_Cf0_1 : axst := TDr_of TD_Cf0_1.
Definition S1c_Cf0_2 : axst := ltac2:(tb__ "0|0|
S2bS3dU0S6eA2S1aSfS48A1A1Z2A3").
Definition C2_Cf0_2 : axst := C2_of S1c_Cf0_2.
Definition run2_Cf0_2 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S24S5S13A1A3S46A3").
Definition EfD_Cf0_2 : axst := leaf 0 run2_Cf0_2.
Definition ED_Cf0_2 : axst := ED_of EfD_Cf0_2.
Definition RD_Cf0_2 : list sobj := RD_of ED_Cf0_2 2.
Definition TD_Cf0_2 : axst := TD_of ED_Cf0_2 2.
Definition TDr_Cf0_2 : axst := TDr_of TD_Cf0_2.
Definition exits1_Cf0 : list axst := ltac2:(tb__ "0|0|
S4SeS53S4SeS54S5SeA1A3A3").

Definition CD_Cf0 : axst := CD_of TDr_Cf0_1.
Definition run3_Cf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S28S4S13S26S5S13A1A3A3S4bA3").
Definition Eps_Cf0 : axst := leaf 0 run3_Cf0.
Definition Ebg_Cf0 : axst := leaf 1 run3_Cf0.
Definition C3_Cf0 : axst := C3_of Eps_Cf0.
Definition run4_Cf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S27S5S13A1A3S47A3").
Definition Ems_Cf0 : axst := leaf 0 run4_Cf0.
Definition C4_Cf0 : axst := C4_of Ems_Cf0.
Definition RM_Cf0 : list sobj := RM_of C4_Cf0.
Definition TM0_Cf0 : axst := TM0_of C4_Cf0.
Definition TM_Cf0 : axst := TM_of C4_Cf0.

Definition run5_Cf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S8eS5S13A1A3S55A3").
Definition Erf_Cf0 : axst := leaf 0 run5_Cf0.
Definition XR_Cf0 : list axform := XRC Erf_Cf0.
Definition EC_Cf0 : axst := EC_of Erf_Cf0.
Definition sR_Cf0 : wsub := sR_of (E3_of Erf_Cf0).
Definition RR_Cf0 : list sobj := RR_of EC_Cf0 sR_Cf0.
Definition KEPT_Cf0 : list sobj := KEPT_of EC_Cf0 RR_Cf0.

Definition T0_Cf0 : axst := ltac2:(tb__ "0|0|
Sa5S44S4dS49A3").
Definition XS_Cf0 : list axform := XS_of T0_Cf0.
Definition T1_Cf0 : axst := T1_of T0_Cf0.
Definition KEPT1_Cf0 : list sobj := KEPT1_of T1_Cf0.
Definition T2_Cf0 : axst := T2_of T1_Cf0.
Definition TR_Cf0 : axst := TR_of T1_Cf0.

Definition TRs_Cf0 : axst := TRs_of TR_Cf0.
Definition run5d_Cf0 : list leafA := ltac2:(tb__ "0|0|
S3cS21S4S13S3eS5S13A1A3S56A3").
Definition Erq_Cf0 : axst := leaf 0 run5d_Cf0.
Definition XW_Cf0 : list axform := XW Erq_Cf0.
Definition Erq2_Cf0 : axst := Erq2_of Erq_Cf0.

Definition PMID_Cf0 : axst := ltac2:(tb__ "0|0|
S9bS2S6dS6fS7eS7cS17S7dS74S2A1A4S75S2A1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_Cf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS48A1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_Cf0 : ltac2:(tb__ "0|0|
S0S3S81S40S21S4S13S23S5S13A1A3S3fS4SeS48S5SeA1A3S57A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_Cf0 exits1_Cf0 run1_Cf0); [unfold run1_Cf0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_Cf0 : ltac2:(tb__ "0|2|
S0S3S82S40S21S4S13S23S5S13A1A3S3fS4S7fS80S48Z1S1cZ0M0A1M1A3S5S7fA1A3S7eSeS7fSeS80R1G0G1A3LE;S57A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_Cf0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf0) run1_Cf0); [unfold run1_Cf0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_Cf0_1 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS53A1SfS45A1A2S8G3SaG1G2S4G0SaS16S16S2eS2fA4S5G0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf0_1 : ltac2:(tb__ "0|1|
S1S0S3S19SfS45A1M0A1S2A3S1S0S14S15G0A1S15SfS53A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf0_1 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS45A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf0_1 : ltac2:(tb__ "0|0|
S0SeS11S53SfS45A1A2S45A3"). Proof. vmr. Qed.
Lemma RUN2_Cf0_1 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S24S5S13A1A3S45A3S5dA3"). Proof. unfold run2_Cf0_1; reflexivity. Qed.
Lemma L2_Cf0_1 : ltac2:(tb__ "0|0|
S1S0S3S25S5dS4S13S24S5S13A1A3A2S2A3S0SeS3dU0S5dA2S63A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf0_1; reflexivity]). Qed.
Lemma AXD_Cf0_1 : ltac2:(tb__ "0|0|
S0S7SeA1S79S63S2cA2S8SeS42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf0_1 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S87S42S83Z1M1A1S22S42G1A2A3S8G0S51A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf0_1 : ltac2:(tb__ "0|1|
S0S3S89S42S83Z1M0A1S22S42G0A2S51S4SeS84G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf0_1 : ltac2:(tb__ "0|1|
S0SeS5aS86S88S22S42Z1M0A2S83G0A1S84G0A1S42S51A5S1aSfS42A1A1A2A3").
Proof. unfold TD_Cf0_1, TD_of, RD_Cf0_1; reflexivity. Qed.
Lemma DCHK_Cf0_1 : ltac2:(tb__ "0|2|
S0S3S92U0M0S76S74S2A1G0A2Z1M1S42S5aS22S42G1A2S51A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf0_1 : ltac2:(tb__ "0|0|
S0S7SeA1S79S5aS2dA2S8SeS6bA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf0_1 : ltac2:(tb__ "0|0|
S0S3Sa6S6bS4bA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_Cf0_2 : ltac2:(tb__ "0|4|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS54A1SfS46A1A2S8G3SaG1G2S4G0SaS16S16S2eS2fA4S5G0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_Cf0_2 : ltac2:(tb__ "0|1|
S1S0S3S19SfS46A1M0A1S2A3S1S0S14S15G0A1S15SfS54A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_Cf0_2 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS46A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_Cf0_2 : ltac2:(tb__ "0|0|
S0SeS11S54SfS46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_Cf0_2 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S24S5S13A1A3S46A3S5eA3"). Proof. unfold run2_Cf0_2; reflexivity. Qed.
Lemma L2_Cf0_2 : ltac2:(tb__ "0|0|
S1S0S3S25S5eS4S13S24S5S13A1A3A2S2A3S0SeS3dU0S5eA2S64A3A2"). Proof. Time (split; [vmr | unfold EfD_Cf0_2; reflexivity]). Qed.
Lemma AXD_Cf0_2 : ltac2:(tb__ "0|0|
S0S7SeA1S79S64S2cA2S8SeS43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_Cf0_2 : ltac2:(tb__ "0|2|
S0S7S6S17A1M0A1S87S43S83Z2M1A1S22S43G1A2A3S8G0S52A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_Cf0_2 : ltac2:(tb__ "0|1|
S0S3S89S43S83Z2M0A1S22S43G0A2S52S4SeS84G0A1S5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_Cf0_2 : ltac2:(tb__ "0|1|
S0SeS5bS86S88S22S43Z2M0A2S83G0A1S84G0A1S43S52A5S1aSfS43A1A1A2A3").
Proof. unfold TD_Cf0_2, TD_of, RD_Cf0_2; reflexivity. Qed.
Lemma DCHK_Cf0_2 : ltac2:(tb__ "0|2|
S0S3S92U0M0S76S74S2A1G0A2Z2M1S43S5bS22S43G1A2S52A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_Cf0_2 : ltac2:(tb__ "0|0|
S0S7SeA1S79S5bS2dA2S8SeS6cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_Cf0_2 : ltac2:(tb__ "0|0|
S0S3Sa6S6cS4bA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_Cf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S28S4S13S26S5S13A1A3A3S4bA3S58A3"). Proof. unfold run3_Cf0; reflexivity. Qed.
Lemma L3_Cf0 : ltac2:(tb__ "0|0|
S1S0S3S25S58S4S13S28S4S13S26S5S13A1A3A3A2S2A3S1S0SeS3dU0S58A2S4fA3S0SeS3dU1S58A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_Cf0 | unfold Ebg_Cf0]; reflexivity]). Qed.
Lemma NX3_Cf0 : ltac2:(tb__ "0|1|
S1S0S3S7aS3fS15SfS4bA1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_Cf0 : ltac2:(tb__ "0|0|
S0S3S91S18S20SabA1S1aSfS62A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_Cf0 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S85SfS4fA1SfS47A1A2S8G2SaG0G1S34S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_Cf0 : ltac2:(tb__ "0|0|
S0SeS11S4fSfS47A1A2S47A3"). Proof. vmr. Qed.
Lemma NX3b_Cf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS47A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_Cf0 : ltac2:(tb__ "0|1|
S1S0S3S19SfS47A1M0A1S2A3S1S0S14S15G0A1S15SfS4fA1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_Cf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S27S5S13A1A3S47A3S5fA3"). Proof. unfold run4_Cf0; reflexivity. Qed.
Lemma L4_Cf0 : ltac2:(tb__ "0|0|
S1S0S3S25S5fS4S13S27S5S13A1A3A2S2A3S0SeS3dU0S5fA2S4eA3A2"). Proof. Time (split; [vmr | unfold Ems_Cf0; reflexivity]). Qed.
Lemma D4_Cf0 : ltac2:(tb__ "0|3|
S0S7S9S6S9S16S16A2A1M0S6S18A1M1A2M2A1S85SfS4eA1SfS41A1A2S8G2SaG0G1S35S5S18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_Cf0 : ltac2:(tb__ "0|0|
S0SeS11S4eSfS41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_Cf0 : ltac2:(tb__ "0|1|
S1S0S3S19SfS41A1M0A1S2A3S1S0S14S15G0A1S15SfS4eA1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_Cf0 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S87S41S8bS29S41A1A3S8G0S59A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_Cf0 : ltac2:(tb__ "0|0|
S0S3S8aS41S8bS29S41A1S59S7eS10SeS12S8cA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_Cf0 : ltac2:(tb__ "0|0|
S0SeS88S29S41A1S8bS31S41S59A5S5cA3"). Proof. unfold TM0_Cf0, TM0_of, RM_Cf0; reflexivity. Qed.
Lemma FBM_Cf0 : ltac2:(tb__ "0|3|
S1S0S3S90S18S1dS15SfS41A1M0A1M1A1S1aG0A1M2A3S2A3S1S0S3S90S18S1dS15SfS5cA1A1A1G2A3S2A3S0S3S7aS3fG1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_Cf0 : ltac2:(tb__ "0|0|
S0SeS86S5cS1aSfS41A1A1A2S55A3"). Proof. vmr. Qed.

Lemma NX5_Cf0 : ltac2:(tb__ "0|1|
S1S0S3S7aS3fS15SfS55A1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_Cf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S8eS5S13A1A3S55A3S60A3"). Proof. unfold run5_Cf0; reflexivity. Qed.
Lemma L5_Cf0 : ltac2:(tb__ "0|0|
S1S0S3S25S60S4S13S8eS5S13A1A3A2S2A3S0SeS3dU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erf_Cf0; reflexivity]). Qed.
Lemma AXR_Cf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S65S71A2S8SeS44A2A3"). Proof. Time vmr. Qed.

Lemma HER_Cf0 : ltac2:(tb__ "0|1|
S0S7S6S17A1M0A1S87S44S8dS4dA3S8G0S49A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_Cf0 : ltac2:(tb__ "0|0|
S0S3S89S44S8dS4dS49S4SeS8fS5SeA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_Cf0 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS44A1A1ScS17S70S49A3A3"). Proof. Time vmr. Qed.
Lemma HT0_Cf0 : ltac2:(tb__ "0|0|
S0SeS69S86S88S4dS8dS8fS44S49A5S1aSfS44A1A1A2A3"). Proof. unfold T0_Cf0, T0_of; reflexivity. Qed.
Lemma HXS_Cf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S69S72A2S8SeS4aA2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_Cf0 : ltac2:(tb__ "0|0|
S0S6S17A1S1eSfS4aA1A1ScS17S68S4S17S30S4S17S7dS77A1S4S17S7dS78A1S5S17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_Cf0 : ltac2:(tb__ "0|0|
S0SeS6aS11S4aSa7SfS4aA1S68A2A2A3"). Proof. unfold T2_Cf0, T2_of, KEPT1_Cf0; reflexivity. Qed.
Lemma HTR_Cf0 : ltac2:(tb__ "0|2|
S0SeS4cSa0S6aS4S7cSa1Sa3S15SfS4aA1A1M0S7bG0A1M1A3S5S7cA1A3S7bG1A1A3A3"). Proof. unfold TR_Cf0, TR_of, T2_Cf0; reflexivity. Qed.
Lemma RCHK_Cf0 : ltac2:(tb__ "0|0|
S0S3Sa2U0S2S44S4aS4cS4dS49Sa3A8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_Cf0 : ltac2:(tb__ "0|0|
S0SeS56Sa0S4cSadS15SfS4cA1A1A3A3"). Proof. unfold TRs_Cf0, TRs_of; reflexivity. Qed.
Lemma CCHK_Cf0 : ltac2:(tb__ "0|0|
S0S3SaeU0S3S37L_;S2S33S32X3x2S4cS56A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_Cf0 : ltac2:(tb__ "0|0|
S0S6S10A1S3cS21S4S13S3eS5S13A1A3S56A3S61A3"). Proof. unfold run5d_Cf0; reflexivity. Qed.
Lemma L5d_Cf0 : ltac2:(tb__ "0|0|
S1S0S3S25S61S4S13S3eS5S13A1A3A2S2A3S0SeS3dU0S61A2S67A3A2"). Proof. Time (split; [vmr | unfold Erq_Cf0; reflexivity]). Qed.
Lemma AXW_Cf0 : ltac2:(tb__ "0|0|
S0S7SeA1S79S67S73A2S8SeS66A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_Cf0 : ltac2:(tb__ "0|0|
S0S3S36S66SacA2S2A3"). Proof. Time vmr. Qed.

Lemma Wa_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S94S39U0A1S38A2A1S2A3"). Proof. vmr. Qed.
Lemma Da_Cf0 : ltac2:(tb__ "0|5|
S0S7S9S6S9S16S16A2M0A1M1S6S18A1M2A2M3A1S85SfS3bS3aS39U0A1M4S38A3A1S94G4S38A2A2S8G3SaG1G2S4G0SaS16S16S1fP18A1S1cSaaA1A4S5G0A1A3S5S18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S97S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S98S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S99S39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_Cf0 : ltac2:(tb__ "0|0|
S0S3S90S18S1dSa9A1S95S2S39U0A1S38S75S2A1A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_Cf0 : ltac2:(tb__ "0|4|
S0S7SeA1S79S9aS2S39U0M0A1M1S38S74S2A1M2S75S2A1M3A5S93G0SdS7cG2A2A2A2S8SeS96S2G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_Cf0 : ltac2:(tb__ "0|0|
S0S3S7aS3fS15SfS50A1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_Cf0__runs : ltac2:(tb__ "0|0|
S6S7S6S10A1A1A1") := ltac2:(tb__ "0|0|
Sa8S40S21S4S13S23S5S13A1A3S4SeS50S5SeA1A3A4").
Lemma Cert1m_Cf0 : ltac2:(tb__ "0|0|
S0S3S81S40S21S4S13S23S5S13A1A3S3fS4SeS50S5SeA1A3S57A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_Cf0] exits1_Cf0 Cert1m_Cf0__runs); [unfold Cert1m_Cf0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_Cf0 : ltac2:(tb__ "0|2|
S0S3S82S40S21S4S13S23S5S13A1A3S3fS4S7fS80S50Z1S1cZ0M0A1M1A3S5S7fA1A3S7eSeS7fSeS80R1G0G1A3LE;S57A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_Cf0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_Cf0) Cert1m_Cf0__runs); [unfold Cert1m_Cf0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S9cS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S9dS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_Cf0 : ltac2:(tb__ "0|0|
S0S3S19S9eS39U0A1S38S74S2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_Cf0 : ltac2:(tb__ "0|4|
S0S7SeA1S79S9fS2S39U0M0A1M1S38S74S2A1M2S75S2A1M3A5S93G0SdS7cG2A2A2A2S8SeS9bS2G1S38S7eS7cS17S7dG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cCf0.

(* [comment removed for export] *)
Module F0A_aCf0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCf0"; "ED_Cf0_1"; "ED_Cf0_2"; "TD_Cf0_1"; "TD_Cf0_2"; "P0_Cf0"; "PMID_Cf0"; "TM_Cf0"; "exits1_Cf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_aCf0.ACf0"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lx.F0A_cCf0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACf0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS27Vsegs;Vok;S29Vsegs;S3fU0S1S16R6VKc;R5A6S3bR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbS10SeQ40A1A1S41VA;R3A2S51Vkeep;Vrho1;R3A3SbS26Vsegs;S29Vsegs;S3fU0S1S16R6VKc;R5A6S3bR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6S23SbS42S23R2S3cA3S27Vsegs;R11S29Vsegs;S3fG1S1SfR10RfRdA6R3R2RcA5RbA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_Cf0 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_Cf0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_Cf0 Q BGF_Cf0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_Cf0 C3_Cf0 Ems_Cf0 C4_Cf0 TM0_Cf0 run4_Cf0 RM_Cf0 D3_Cf0 W3_Cf0 EQ3_Cf0 NX3b_Cf0 RUN4_Cf0 L4_Cf0 D4_Cf0 W4_Cf0 EQ4_Cf0
             HeM_Cf0 HchkM_Cf0 HTM_Cf0 FBM_Cf0 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_Cf0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0 UStopLe true S1c_Cf0_1 C2_Cf0_1 EfD_Cf0_1 ED_Cf0_1 run2_Cf0_1 D2_Cf0_1 W2_Cf0_1 NX2_Cf0_1 EQ2_Cf0_1 RUN2_Cf0_1 L2_Cf0_1 AXD_Cf0_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_Cf0_1 TDr_Cf0_1 CD_Cf0 Eps_Cf0 Ebg_Cf0 run3_Cf0 AXDr_Cf0_1 ENTD_Cf0_1 RUN3_Cf0 L3_Cf0 NX3_Cf0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0 UStopLe true S1c_Cf0_2 C2_Cf0_2 EfD_Cf0_2 ED_Cf0_2 run2_Cf0_2 D2_Cf0_2 W2_Cf0_2 NX2_Cf0_2 EQ2_Cf0_2 RUN2_Cf0_2 L2_Cf0_2 AXD_Cf0_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0 UStopLe false TD_Cf0_2 TDr_Cf0_2 CD_Cf0 Eps_Cf0 Ebg_Cf0 run3_Cf0 AXDr_Cf0_2 ENTD_Cf0_2 RUN3_Cf0 L3_Cf0 NX3_Cf0
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5S23SbS42S23R2S3cA3S26Vsegs;S29Vsegs;S3fG1S1SfRfReRcA6R3R2RbA5RaA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_Cf0 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_Cf0 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_Cf0 Q BGF_Cf0 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_Cf0 C3_Cf0 Ems_Cf0 C4_Cf0 TM0_Cf0 run4_Cf0 RM_Cf0 D3_Cf0 W3_Cf0 EQ3_Cf0 NX3b_Cf0 RUN4_Cf0 L4_Cf0 D4_Cf0 W4_Cf0 EQ4_Cf0
             HeM_Cf0 HchkM_Cf0 HTM_Cf0 FBM_Cf0 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_Cf0. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_Cf0 in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0 UStopLe true S1c_Cf0_1 C2_Cf0_1 EfD_Cf0_1 ED_Cf0_1 run2_Cf0_1 D2_Cf0_1 W2_Cf0_1 NX2_Cf0_1 EQ2_Cf0_1 RUN2_Cf0_1 L2_Cf0_1 AXD_Cf0_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_Cf0_1 TDr_Cf0_1 CD_Cf0 Eps_Cf0 Ebg_Cf0 run3_Cf0 AXDr_Cf0_1 ENTD_Cf0_1 RUN3_Cf0 L3_Cf0 NX3_Cf0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0 UStopLe true S1c_Cf0_2 C2_Cf0_2 EfD_Cf0_2 ED_Cf0_2 run2_Cf0_2 D2_Cf0_2 W2_Cf0_2 NX2_Cf0_2 EQ2_Cf0_2 RUN2_Cf0_2 L2_Cf0_2 AXD_Cf0_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0 UStopLe false TD_Cf0_2 TDr_Cf0_2 CD_Cf0 Eps_Cf0 Ebg_Cf0 run3_Cf0 AXDr_Cf0_2 ENTD_Cf0_2 RUN3_Cf0 L3_Cf0 NX3_Cf0
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1SfReRdRbA6S39R1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true P0_Cf0 exits1_Cf0 Cert1_Cf0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1SfRdRcRaA6S39R1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true P0_Cf0 exits1_Cf0 NX0_Cf0 ECert1_Cf0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Theorem free_spine_m_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S24OF_;S17S2SbSbS10SeQ40M0A1A1S25S3R5A1S2aVsegs;R8S28R6A1A3S40R6R5A2S1bSdG0ScR7PdA2A2S32A2S3dU0M1S1RcRbRaR9R7S35S37R5AaS3dG1S1RdRcRbRaR8S36S38R6AaS4bReRdRcRbR9R7A6SbS27Vsegs;RfS29Vsegs;S3fG1S1SfReRdRbA6S3aR1RaA5R9A4FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM.
  apply (f0_s1c 0 UStopLe true PMID_Cf0 exits1_Cf0 Cert1m_Cf0 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_Cf0 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HTM).
Qed.
Theorem efree_spine_m_Cf0 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbS10SeQ40M0A1A1S24OF_;S3R5A1S40R5R4A2S1bSdG0ScR6PdA2A2S32A2S3eU0M1S1RaR9R8R6S35S37R4A9S3eG1S1RbRaR9R7S36S38R5A9S4cRcRbRaR8R6A5SbS26Vsegs;S29Vsegs;S3fG1S1SfRdRcRaA6S3aR1R9A5R8A3FrhoP;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM.
  apply (ef0_s1c 0 UStopLe true PMID_Cf0 exits1_Cf0 NX0m_Cf0 ECert1m_Cf0 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_Cf0 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S22S4aS52R2A2S1fS1bS2eR2A2S1dR2S2fA2A2A2S21F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S54R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S20S53R2A1A1F_;Fa;").

Theorem hdf_Cf0_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S35S37R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC true) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf0_1 TD_Cf0_1 (sD_of ED_Cf0_1 1) RD_Cf0_1 HeD_Cf0_1 HchkD_Cf0_1 HTD_Cf0_1 DCHK_Cf0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf0_1 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S35S37R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC true) 0) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf0_1 TD_Cf0_1 (sD_of ED_Cf0_1 1) RD_Cf0_1 HeD_Cf0_1 HchkD_Cf0_1 HTD_Cf0_1 DCHK_Cf0_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.
Theorem hdf_Cf0_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S25S2aSaR2S28R11A1A3S49SaR3S28R12A1A3S3dU0S1S45VCST;VXGL;R14A3R4R14R13S31R14R12RfReRdRcA6S36S38R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 0 (rd_okG (NVC true) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf0_2 TD_Cf0_2 (sD_of ED_Cf0_2 2) RD_Cf0_2 HeD_Cf0_2 HchkD_Cf0_2 HTD_Cf0_2 DCHK_Cf0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_Cf0_2 : ltac2:(tb__ "0|1|
S17S2SbS10SeQ40M0A1A1S43S0S0S0S47S3R8A1S2dSaRaR8R7R6A5S42S12S0S0A2S11S0S0R6R5A4S19RbA1A3S46R7R6A2S1eS0SdG0ScRbPcA2A2R8A3S4dReRcR9R8R7R6A6S30SfRfA2S24OF_;S3eU0S1S45VCST;VXGL;R11A3R11R10S31R11RfRcRbRaR9A6S36S38R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 0 (rd_okG (NVC true) 0) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_Cf0_2 TD_Cf0_2 (sD_of ED_Cf0_2 2) RD_Cf0_2 HeD_Cf0_2 HchkD_Cf0_2 HTD_Cf0_2 DCHK_Cf0_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.

Lemma tail_Cf0 : ltac2:(tb__ "0|3|
S24OF_;S17S2SbS10SeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S2aSaRcS28RaA1A3S49SaRdS28RbA1A3S4eReRcA2S2dSaReRcR6R5A5S1aRfA1S1eS0SdG0ScRePcA2A2RcA3S1eS0SdG0ScRfPdA2A2RcA3S42S12S0S0A2S11S0S0ReRdA4S19R12A1A3S46RfReA2S1eS13S18R14A1SfA3S30SfR15A2S40R14S31R16R14R12R11R10RfA6A2S1eS0S48R10A1S34A3S4bS45VCST;VXGL;R18A3R19R18R17S31R18R16R14R13R12R11A6S2cSaS44R16R15S14S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R18Z18A2R17A5A4S15G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 true CST XGL HCST HXGL TM_Cf0 Erf_Cf0 EC_Cf0 run5_Cf0 XR_Cf0 NX5_Cf0 RUN5_Cf0 L5_Cf0 AXR_Cf0 T0_Cf0 T1_Cf0 T2_Cf0 TR_Cf0 sR_Cf0 RR_Cf0 KEPT_Cf0 KEPT1_Cf0 XS_Cf0 eFRc HER_Cf0 Hchk_Cf0 OBJS_Cf0 HT0_Cf0 HXS_Cf0 OBJS1_Cf0 HT2_Cf0 HTR_Cf0 RCHK_Cf0 TRs_Cf0 Erq_Cf0 Erq2_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.TQ_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.Edr_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.Xf_0Bf run5d_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.run6_0Bf XW_Cf0 HTRs_Cf0 CCHK_Cf0 RUN5d_Cf0 L5d_Cf0 AXW_Cf0 ENTQ_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.NX6_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.RUN6_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.L6_0Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Bf.f0_drain_0Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi0Bf.f0_exit_0Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Cf0 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S47G1S43S3R9A1S4fRaA1S2dSaRcRaR4R3A5S1aRdA1S1eS0SdG0ScRcPcA2A2RaA3S1eS0SdG0ScRdPdA2A2RaA3S42S12S0S0A2S11S0S0RcRbA4S19R10A1A3S46RdRcA2S1eS13S18R12A1SfA3S30SfR13A2S40R12S31R14R12R10RfReRdA6A2S1eS0S48ReA1S34A3S4cS45VCST;VXGL;R16A3R16R15S31R16R14R12R11R10RfA6S2cSaS44R14R13S14S12S23S2bA2M2S11S23S2bS6S4S7U0A1S1A3S5S2dSaA1VCST;VXGL;S50R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 true CST XGL HCST HXGL TM_Cf0 Erf_Cf0 EC_Cf0 run5_Cf0 XR_Cf0 NX5_Cf0 RUN5_Cf0 L5_Cf0 AXR_Cf0 T0_Cf0 T1_Cf0 T2_Cf0 TR_Cf0 sR_Cf0 RR_Cf0 KEPT_Cf0 KEPT1_Cf0 XS_Cf0 eFRc HER_Cf0 Hchk_Cf0 OBJS_Cf0 HT0_Cf0 HXS_Cf0 OBJS1_Cf0 HT2_Cf0 HTR_Cf0 RCHK_Cf0 TRs_Cf0 Erq_Cf0 Erq2_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.TQ_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.Edr_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.Xf_0Bf run5d_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.run6_0Bf XW_Cf0 HTRs_Cf0 CCHK_Cf0 RUN5d_Cf0 L5d_Cf0 AXW_Cf0 ENTQ_Cf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.NX6_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.RUN6_0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.L6_0Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_q0Bf.ef0_drain_0Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi0Bf.ef0_exit_0Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Cf_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS33S1cR6Z10A2A2S1eS13S18RbA1SfA3S30SfRcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate true 0 UStopLe (NVC true) (VFC true) Wa_Cf0 Da_Cf0 Wb_Cf0 Wc_Cf0 Wd_Cf0 Fb_Cf0 XI_Cf0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_Cf0 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_Cf0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_Cf0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_Cf0 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_Cf_0 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S1bS33S1cR4Z10A2A2S1eS13S18R9A1SfA3S30SfRaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C true _ _ true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate true 0 UStopLe (NVC true) (VFC true) Wa_Cf0 Da_Cf0 Wb_Cf0 Wc_Cf0 Wd_Cf0 Fb_Cf0 XI_Cf0 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_Cf0 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_Cf0_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_Cf0_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_Cf0 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4aVCST;R1A2S1fS20S1fS1bS2eR2A2S1dR2S2fA2A2A1S20S1fS1bZ17db48R2A2S1dR2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_hi_ia0_Cf_0 : ltac2:(tb__ "0|4|
S24OF_;S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S2aSaR9S28R7A1A3S49SaRaS28R8A1A3S1bS33S1cR6Z10A2A2S1eS13S18RbA1S16A3S30SfRcA2S1bR8S32A2S4eRfRdA2S27SaR10S29SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true 0 UStopLe (NVC true) (VFC true) Wbm_Cf0 Wcm_Cf0 Wdm_Cf0 Fb_Cf0 XIm_Cf0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_Cf0 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_Cf0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_Cf0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_Cf0 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_hi_ia0_Cf_0 : ltac2:(tb__ "0|4|
S17S2SbS10SeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S2cSaS44R4R3S14S12S23S2bA2M1S11S23S2bS6S4S7U0A1M2S1A3S5S2dSaA1M3VCST;VXGL;R6R5A5A4S15G1A1A3A5S25S3R6A1S1bS33S1cR4Z10A2A2S1eS13S18R9A1S16A3S30SfRaA2S1bR6S32A2S4fRbA1S26SaS29SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 0 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 0 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true 0 UStopLe (NVC true) (VFC true) Wbm_Cf0 Wcm_Cf0 Wdm_Cf0 Fb_Cf0 XIm_Cf0 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_Cf0 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_Cf0_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_Cf0_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_Cf0 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ACf0.
End F0A_aCf0.

