(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il ix iy.

(* [comment removed for export] *)
Module F0T_cTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "C4_TA"; "EQ_TA"; "q_TA"; "C2_TA"; "C3_TA"; "LT_TA"; "ED_TA"; "S1c_TA"; "l1_TA"; "CD_TA"; "EX_TA"; "Ems_TA"; "Eps_TA"; "P0_TA"; "TM_TA"; "TQ_TA"; "run3_TA"; "run6_TA"; "LH0_TA"; "RM_TA"; "RQ_TA"; "TDr_TA"; "TM0_TA"; "TQ0_TA"; "l2_TA"; "l3_TA"; "l4_TA"; "run2_TA"; "run4_TA"; "run5_TA"; "EfD_TA"; "Eq_TA"; "RD_TA"; "Ebg_TA"; "Edr_TA"; "TD_TA"; "Xf_TA"; "l1okb_TA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_TA : list ulink := Wcan 0.
Definition st_TA : ustop := UStopLe.
Definition q_TA : qvar := QA.
Definition F0_TA : list sprop := FACTS_Tc true q_TA.
Definition P0_TA : axst := P0T_c true q_TA.

Definition l1_TA : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_TA.
Definition LH0_TA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_TA) DUMMY).
Definition l2_TA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_TA.
Definition LH1_TA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_TA) DUMMY).
Definition LT_TA : axst := Eval vm_compute in LT_ofg LH1_TA F0_TA.
Definition EX_TA : axst := Eval vm_compute in EX_ofg LH1_TA F0_TA.
Definition l3_TA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_TA (SVar pFR)).
Definition l4_TA : list leafA := Eval vm_compute in runA FUELF [CASX] EX_TA.
Definition S1c_TA : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_TA DUMMY)) (F0_TA ++ F_ext).

Lemma RUN1_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_TA (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_TA : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_TA : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_TA : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_TA : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_TA : axst := C2_of S1c_TA.
Definition run2_TA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_TA : axst := leaf 0 run2_TA.
Definition ED_TA : axst := ED_of EfD_TA.
Definition RD_TA : list sobj := RDv_of ED_TA.
Definition TD_TA : axst := TDv_of ED_TA.
Definition TDr_TA : axst := TDr_of TD_TA.

Definition CD_TA : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_TA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_TA : axst := leaf 0 run3_TA.
Definition Ebg_TA : axst := leaf 1 run3_TA.
Definition C3_TA : axst := C3_of Eps_TA.
Definition run4_TA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_TA : axst := leaf 0 run4_TA.
Definition C4_TA : axst := C4_of Ems_TA.
Definition RM_TA : list sobj := RM_of C4_TA.
Definition TM0_TA : axst := TM0_of C4_TA.
Definition TM_TA : axst := TM_of C4_TA.
Definition run5_TA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_TA : axst := leaf 0 run5_TA.
Definition EQ_TA : axst := EQ_of Eq_TA.
Definition RQ_TA : list sobj := RQ_of EQ_TA q_TA.
Definition TQ0_TA : axst := TQ0_of EQ_TA q_TA.
Definition TQ_TA : axst := TQ_of EQ_TA q_TA.
Definition run6_TA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_TA : axst := leaf 0 run6_TA.
Definition Xf_TA : axst := leaf 1 run6_TA.

Lemma D2_TA : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_TA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_TA : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_TA : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_TA; reflexivity. Qed.
Lemma L2_TA : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_TA; reflexivity]). Qed.
Lemma AXD_TA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_TA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_TA : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_TA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_TA : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_TA; reflexivity. Qed.
Lemma L3_TA : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_TA | unfold Ebg_TA]; reflexivity]). Qed.
Lemma NX3_TA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_TA : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_TA : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_TA : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_TA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_TA; reflexivity. Qed.
Lemma L4_TA : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_TA; reflexivity]). Qed.
Lemma D4_TA : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_TA : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_TA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_TA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_TA : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_TA : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_TA, TM0_of, RM_TA; reflexivity. Qed.
Lemma FBM_TA : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_TA : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_TA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_TA; reflexivity. Qed.
Lemma L5_TA : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_TA; reflexivity]). Qed.
Lemma AXQ_TA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_TA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_TA : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_TA : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_TA, TQ0_of, RQ_TA; reflexivity. Qed.
Lemma FBQ_TA : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_TA : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_TA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_TA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_TA; reflexivity. Qed.
Lemma L6_TA : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_TA | unfold Xf_TA]; reflexivity]). Qed.
End F0T_cTA.

(* [comment removed for export] *)
Module F0T_cLTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf"; "C4_LTBf"; "EQ_LTBf"; "q_LTBf"; "C2_LTBf"; "C3_LTBf"; "LT_LTBf"; "ED_LTBf"; "S1c_LTBf"; "l1_LTBf"; "CD_LTBf"; "EX_LTBf"; "Ems_LTBf"; "Eps_LTBf"; "P0_LTBf"; "TM_LTBf"; "TQ_LTBf"; "run3_LTBf"; "run6_LTBf"; "LH0_LTBf"; "RM_LTBf"; "RQ_LTBf"; "TDr_LTBf"; "TM0_LTBf"; "TQ0_LTBf"; "l2_LTBf"; "l3_LTBf"; "l4_LTBf"; "run2_LTBf"; "run4_LTBf"; "run5_LTBf"; "EfD_LTBf"; "Eq_LTBf"; "RD_LTBf"; "Ebg_LTBf"; "Edr_LTBf"; "TD_LTBf"; "Xf_LTBf"; "l1okb_LTBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_LTBf : list ulink := Wcan 0.
Definition st_LTBf : ustop := UStopLe.
Definition q_LTBf : qvar := QBf.
Definition F0_LTBf : list sprop := FACTS_Tc false q_LTBf.
Definition P0_LTBf : axst := P0T_c false q_LTBf.

Definition l1_LTBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LTBf.
Definition LH0_LTBf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LTBf) DUMMY).
Definition l2_LTBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LTBf.
Definition LH1_LTBf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LTBf) DUMMY).
Definition LT_LTBf : axst := Eval vm_compute in LT_ofg LH1_LTBf F0_LTBf.
Definition EX_LTBf : axst := Eval vm_compute in EX_ofg LH1_LTBf F0_LTBf.
Definition l3_LTBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LTBf (SVar pFR)).
Definition l4_LTBf : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LTBf.
Definition S1c_LTBf : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LTBf DUMMY)) (F0_LTBf ++ F_ext).

Lemma RUN1_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_LTBf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_LTBf : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_LTBf : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_LTBf : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_LTBf : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LTBf : axst := C2_of S1c_LTBf.
Definition run2_LTBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_LTBf : axst := leaf 0 run2_LTBf.
Definition ED_LTBf : axst := ED_of EfD_LTBf.
Definition RD_LTBf : list sobj := RDv_of ED_LTBf.
Definition TD_LTBf : axst := TDv_of ED_LTBf.
Definition TDr_LTBf : axst := TDr_of TD_LTBf.

Definition CD_LTBf : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_LTBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_LTBf : axst := leaf 0 run3_LTBf.
Definition Ebg_LTBf : axst := leaf 1 run3_LTBf.
Definition C3_LTBf : axst := C3_of Eps_LTBf.
Definition run4_LTBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_LTBf : axst := leaf 0 run4_LTBf.
Definition C4_LTBf : axst := C4_of Ems_LTBf.
Definition RM_LTBf : list sobj := RM_of C4_LTBf.
Definition TM0_LTBf : axst := TM0_of C4_LTBf.
Definition TM_LTBf : axst := TM_of C4_LTBf.
Definition run5_LTBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_LTBf : axst := leaf 0 run5_LTBf.
Definition EQ_LTBf : axst := EQ_of Eq_LTBf.
Definition RQ_LTBf : list sobj := RQ_of EQ_LTBf q_LTBf.
Definition TQ0_LTBf : axst := TQ0_of EQ_LTBf q_LTBf.
Definition TQ_LTBf : axst := TQ_of EQ_LTBf q_LTBf.
Definition run6_LTBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_LTBf : axst := leaf 0 run6_LTBf.
Definition Xf_LTBf : axst := leaf 1 run6_LTBf.

Lemma D2_LTBf : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LTBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LTBf : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_LTBf : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_LTBf; reflexivity. Qed.
Lemma L2_LTBf : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_LTBf; reflexivity]). Qed.
Lemma AXD_LTBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LTBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LTBf : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_LTBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LTBf : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_LTBf; reflexivity. Qed.
Lemma L3_LTBf : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LTBf | unfold Ebg_LTBf]; reflexivity]). Qed.
Lemma NX3_LTBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_LTBf : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LTBf : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_LTBf : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_LTBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_LTBf; reflexivity. Qed.
Lemma L4_LTBf : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_LTBf; reflexivity]). Qed.
Lemma D4_LTBf : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LTBf : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LTBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LTBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LTBf : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_LTBf : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_LTBf, TM0_of, RM_LTBf; reflexivity. Qed.
Lemma FBM_LTBf : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LTBf : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_LTBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_LTBf; reflexivity. Qed.
Lemma L5_LTBf : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_LTBf; reflexivity]). Qed.
Lemma AXQ_LTBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_LTBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_LTBf : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_LTBf : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_LTBf, TQ0_of, RQ_LTBf; reflexivity. Qed.
Lemma FBQ_LTBf : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_LTBf : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_LTBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_LTBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_LTBf; reflexivity. Qed.
Lemma L6_LTBf : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_LTBf | unfold Xf_LTBf]; reflexivity]). Qed.
End F0T_cLTBf.

(* [comment removed for export] *)
Module F0T_cTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "C4_TBe"; "EQ_TBe"; "q_TBe"; "C2_TBe"; "C3_TBe"; "LT_TBe"; "ED_TBe"; "S1c_TBe"; "l1_TBe"; "CD_TBe"; "EX_TBe"; "Ems_TBe"; "Eps_TBe"; "P0_TBe"; "TM_TBe"; "TQ_TBe"; "run3_TBe"; "run6_TBe"; "LH0_TBe"; "RM_TBe"; "RQ_TBe"; "TDr_TBe"; "TM0_TBe"; "TQ0_TBe"; "l2_TBe"; "l3_TBe"; "l4_TBe"; "run2_TBe"; "run4_TBe"; "run5_TBe"; "EfD_TBe"; "Eq_TBe"; "RD_TBe"; "Ebg_TBe"; "Edr_TBe"; "TD_TBe"; "Xf_TBe"; "l1okb_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_TBe : list ulink := Wcan 0.
Definition st_TBe : ustop := UStopLe.
Definition q_TBe : qvar := QBe.
Definition F0_TBe : list sprop := FACTS_Tc true q_TBe.
Definition P0_TBe : axst := P0T_c true q_TBe.

Definition l1_TBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_TBe.
Definition LH0_TBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_TBe) DUMMY).
Definition l2_TBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_TBe.
Definition LH1_TBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_TBe) DUMMY).
Definition LT_TBe : axst := Eval vm_compute in LT_ofg LH1_TBe F0_TBe.
Definition EX_TBe : axst := Eval vm_compute in EX_ofg LH1_TBe F0_TBe.
Definition l3_TBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_TBe (SVar pFR)).
Definition l4_TBe : list leafA := Eval vm_compute in runA FUELF [CASX] EX_TBe.
Definition S1c_TBe : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_TBe DUMMY)) (F0_TBe ++ F_ext).

Lemma RUN1_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_TBe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_TBe : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_TBe : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_TBe : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_TBe : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_TBe : axst := C2_of S1c_TBe.
Definition run2_TBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_TBe : axst := leaf 0 run2_TBe.
Definition ED_TBe : axst := ED_of EfD_TBe.
Definition RD_TBe : list sobj := RDv_of ED_TBe.
Definition TD_TBe : axst := TDv_of ED_TBe.
Definition TDr_TBe : axst := TDr_of TD_TBe.

Definition CD_TBe : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_TBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_TBe : axst := leaf 0 run3_TBe.
Definition Ebg_TBe : axst := leaf 1 run3_TBe.
Definition C3_TBe : axst := C3_of Eps_TBe.
Definition run4_TBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_TBe : axst := leaf 0 run4_TBe.
Definition C4_TBe : axst := C4_of Ems_TBe.
Definition RM_TBe : list sobj := RM_of C4_TBe.
Definition TM0_TBe : axst := TM0_of C4_TBe.
Definition TM_TBe : axst := TM_of C4_TBe.
Definition run5_TBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_TBe : axst := leaf 0 run5_TBe.
Definition EQ_TBe : axst := EQ_of Eq_TBe.
Definition RQ_TBe : list sobj := RQ_of EQ_TBe q_TBe.
Definition TQ0_TBe : axst := TQ0_of EQ_TBe q_TBe.
Definition TQ_TBe : axst := TQ_of EQ_TBe q_TBe.
Definition run6_TBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_TBe : axst := leaf 0 run6_TBe.
Definition Xf_TBe : axst := leaf 1 run6_TBe.

Lemma D2_TBe : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_TBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_TBe : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_TBe : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_TBe; reflexivity. Qed.
Lemma L2_TBe : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_TBe; reflexivity]). Qed.
Lemma AXD_TBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_TBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_TBe : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_TBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_TBe : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_TBe; reflexivity. Qed.
Lemma L3_TBe : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_TBe | unfold Ebg_TBe]; reflexivity]). Qed.
Lemma NX3_TBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_TBe : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_TBe : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_TBe : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_TBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_TBe; reflexivity. Qed.
Lemma L4_TBe : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_TBe; reflexivity]). Qed.
Lemma D4_TBe : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_TBe : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_TBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_TBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_TBe : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_TBe : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_TBe, TM0_of, RM_TBe; reflexivity. Qed.
Lemma FBM_TBe : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_TBe : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_TBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_TBe; reflexivity. Qed.
Lemma L5_TBe : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_TBe; reflexivity]). Qed.
Lemma AXQ_TBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_TBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_TBe : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_TBe : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_TBe, TQ0_of, RQ_TBe; reflexivity. Qed.
Lemma FBQ_TBe : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_TBe : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_TBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_TBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_TBe; reflexivity. Qed.
Lemma L6_TBe : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_TBe | unfold Xf_TBe]; reflexivity]). Qed.
End F0T_cTBe.

(* [comment removed for export] *)
Module F0A_bL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf"; "Ebg_L2Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2Bf.

(* [comment removed for export] *)
Module F0T_cTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "C4_TBf"; "EQ_TBf"; "q_TBf"; "C2_TBf"; "C3_TBf"; "LT_TBf"; "ED_TBf"; "S1c_TBf"; "l1_TBf"; "CD_TBf"; "EX_TBf"; "Ems_TBf"; "Eps_TBf"; "P0_TBf"; "TM_TBf"; "TQ_TBf"; "run3_TBf"; "run6_TBf"; "LH0_TBf"; "RM_TBf"; "RQ_TBf"; "TDr_TBf"; "TM0_TBf"; "TQ0_TBf"; "l2_TBf"; "l3_TBf"; "l4_TBf"; "run2_TBf"; "run4_TBf"; "run5_TBf"; "EfD_TBf"; "Eq_TBf"; "RD_TBf"; "Ebg_TBf"; "Edr_TBf"; "TD_TBf"; "Xf_TBf"; "l1okb_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_TBf : list ulink := Wcan 0.
Definition st_TBf : ustop := UStopLe.
Definition q_TBf : qvar := QBf.
Definition F0_TBf : list sprop := FACTS_Tc true q_TBf.
Definition P0_TBf : axst := P0T_c true q_TBf.

Definition l1_TBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_TBf.
Definition LH0_TBf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_TBf) DUMMY).
Definition l2_TBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_TBf.
Definition LH1_TBf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_TBf) DUMMY).
Definition LT_TBf : axst := Eval vm_compute in LT_ofg LH1_TBf F0_TBf.
Definition EX_TBf : axst := Eval vm_compute in EX_ofg LH1_TBf F0_TBf.
Definition l3_TBf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_TBf (SVar pFR)).
Definition l4_TBf : list leafA := Eval vm_compute in runA FUELF [CASX] EX_TBf.
Definition S1c_TBf : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_TBf DUMMY)) (F0_TBf ++ F_ext).

Lemma RUN1_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_TBf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_TBf : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_TBf : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_TBf : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_TBf : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_TBf : axst := C2_of S1c_TBf.
Definition run2_TBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_TBf : axst := leaf 0 run2_TBf.
Definition ED_TBf : axst := ED_of EfD_TBf.
Definition RD_TBf : list sobj := RDv_of ED_TBf.
Definition TD_TBf : axst := TDv_of ED_TBf.
Definition TDr_TBf : axst := TDr_of TD_TBf.

Definition CD_TBf : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_TBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_TBf : axst := leaf 0 run3_TBf.
Definition Ebg_TBf : axst := leaf 1 run3_TBf.
Definition C3_TBf : axst := C3_of Eps_TBf.
Definition run4_TBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_TBf : axst := leaf 0 run4_TBf.
Definition C4_TBf : axst := C4_of Ems_TBf.
Definition RM_TBf : list sobj := RM_of C4_TBf.
Definition TM0_TBf : axst := TM0_of C4_TBf.
Definition TM_TBf : axst := TM_of C4_TBf.
Definition run5_TBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_TBf : axst := leaf 0 run5_TBf.
Definition EQ_TBf : axst := EQ_of Eq_TBf.
Definition RQ_TBf : list sobj := RQ_of EQ_TBf q_TBf.
Definition TQ0_TBf : axst := TQ0_of EQ_TBf q_TBf.
Definition TQ_TBf : axst := TQ_of EQ_TBf q_TBf.
Definition run6_TBf : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_TBf : axst := leaf 0 run6_TBf.
Definition Xf_TBf : axst := leaf 1 run6_TBf.

Lemma D2_TBf : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_TBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_TBf : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_TBf : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_TBf; reflexivity. Qed.
Lemma L2_TBf : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_TBf; reflexivity]). Qed.
Lemma AXD_TBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_TBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_TBf : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_TBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_TBf : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_TBf; reflexivity. Qed.
Lemma L3_TBf : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_TBf | unfold Ebg_TBf]; reflexivity]). Qed.
Lemma NX3_TBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_TBf : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_TBf : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_TBf : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_TBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_TBf; reflexivity. Qed.
Lemma L4_TBf : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_TBf; reflexivity]). Qed.
Lemma D4_TBf : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_TBf : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_TBf : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_TBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_TBf : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_TBf : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_TBf, TM0_of, RM_TBf; reflexivity. Qed.
Lemma FBM_TBf : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_TBf : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_TBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_TBf; reflexivity. Qed.
Lemma L5_TBf : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_TBf; reflexivity]). Qed.
Lemma AXQ_TBf : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_TBf : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_TBf : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_TBf : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_TBf, TQ0_of, RQ_TBf; reflexivity. Qed.
Lemma FBQ_TBf : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_TBf : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_TBf : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_TBf : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_TBf; reflexivity. Qed.
Lemma L6_TBf : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_TBf | unfold Xf_TBf]; reflexivity]). Qed.
End F0T_cTBf.

(* [comment removed for export] *)
Module F0A_xdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "false"; "bool"; "nil"; "prod"; "list"; "app"; "length"; "true"; "andb"; "fst"; "negb"; "snd"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "cell"; "SLit"; "SVar"; "SAlu"; "mkObj"; "DUnknown"; "ss_objs"; "ob_base"; "ob_dflt"; "ob_lo"; "mkCell"; "ob_hi"; "odefault"; "SExt"; "SPBranch"; "SPNot"; "dflt_writable"; "mkSS"; "ob_cells"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "c8"; "S_qc"; "S_bh"; "idx_where"; "NBX"; "S_nb"; "c4"; "nocellsF"; "S_pc"; "NRTX"; "RSHAPE"; "S_hdr"; "is_lowwin"; "is_winpiece"; "nkeep"; "ITX"; "LCELLS"; "QSX"; "S_it"; "XEX_of"; "exit_perm"; "ins_by"; "is_image"; "is_link"; "memN"; "n_pieces"; "sort_by"; "win_lo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "sobj_eqb"; "ax_setS"; "cell_eqb"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "fold_right"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "qvar"; "O_blkN"; "O_hdr"; "O_sh"; "O_stQ"; "O_stT1"; "O_stT2"; "VOBJ"; "axf"; "cA"; "cQ"; "iam_base"; "vMINq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "nth"; "repeat"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "DPMCELL"; "MLIMCELL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineCacheMax"; "kQuarantineMax"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "snormc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit"; "N_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_free"; "stack_win"; "@Stdlib.Arith.PeanoNat.Nat"; "pred"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Import ListNotations.
Open Scope Z_scope.

Definition nocellsF (o : sobj) : sobj := ltac2:(tb__ "0|0|
S16S19Vo;A1S1bVo;A1S1dVo;A1S5S12A1S1aVo;A1A5").

Definition is_lowwin (o : sobj) : bool :=
  match ob_base o with SAlu ALU_ADD (SVar 10%positive) (SLit _) => true | _ => false end.
Definition is_winpiece (o : sobj) : bool := ltac2:(tb__ "0|7|
S10S4Lx;M0S19Vo;A1S2fS3Lz;S30S30S4Li;R1S30S3Lp;S30S30S4Lp;R1S30S30S4Lp0;R1S30S3Lp1;S30S30S4Lp1;R1S30S3Lp2;M1G1G0S1bVo;A1S2fSaLz;S30S3Li0;S4fS10S10S3Lb;La;M2Lop;M3G3S50G2Lop;M4G4S4S31S10S3La;Lw;Lsgn;M5S30S10S2fS3Lk;M6Li0;Ll;X10x8X30x3Lp1;S3X30x3Lp0;S30S3Lp0;S3X30x3Lp;S3X30x3Li;G3G3G4G4G5S30S10G6Li;Ll;X10x8").
Definition win_lo (o : sobj) : Z := match ob_lo o with SLit z => snormc z | _ => 0 end.
Definition is_link (o : sobj) : bool := ltac2:(tb__ "0|9|
S10S4Lx;M0S19Vo;A1S2fS3Lz;S30G0S1bVo;A1S2fG0S1dVo;A1S2fS2fS4Lz;R1SbSdS8bR3PaA2A1S5cS84R2A1N10A2A2S30S3Lp;M1G1X2fx3Lz;S30S3Li0;M2S4fS10S10S3Lb;La;M3Lop;M4G4S50G3Lop;M5G5S4S31S10S3La;Lw;Lsgn;M6S30S10S2fS3Lk;M7Li0;Ll;M8X10x8Llo;G2G4G4G5G5G6G8X10x8Li;G4G4G5G5G6S30S10G7Li;Ll;X10x8").
Definition is_image (o : sobj) : bool := ltac2:(tb__ "0|1|
S1eS4Lx;S1aVo;A1S3S3SaS30S3Ll;M0G0S2fS10S7S6S2fS2fA2A1S7S2eA1S3Ltmpl;Lflds;Lcnt;Lesz;X1ex6").

Definition idx_where (f : sobj -> bool) (objs : list sobj) : list nat := ltac2:(tb__ "0|2|
S6dS6S2S11A2M0S2ScS2S11A2S7cG0S7G0A1S7eG0A1G0S7bVf;SeS2S11R1A3A1M1A1Lp;G0S7dG1A1Lx;S59S2S11S6eU0S9S11Vobjs;A2A2Vobjs;A4A6A4").

Fixpoint ins_by (key : nat -> Z) (i : nat) (l : list nat) : list nat :=
  match l with [] => [i] | j :: r => if key i <=? key j then i :: l else j :: ins_by key i r end.
Definition sort_by (key : nat -> Z) (l : list nat) : list nat := ltac2:(tb__ "0|0|
S5aS7S2A1S2S47Vkey;A1S5S2A1Vl;A5").
Definition memN (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.

Definition exit_perm (S : sstate) : list nat := ltac2:(tb__ "0|2|
S18VS;A1S7S11A1S2S4dS70S11R1R2S89A4A1Li;S2S2fFi;S35S3eR2A2S7S2A1M0S4cR2S35S3fR3A2A2G0S35S49R4A2G0S35S48R5A2G0S8S2R4S8S2R3S8S2R2R1A3A3A3G0S8S2R1S7cS2G0S7eS2A1S2S7bSdS4aR1R2A2A1M1A1Li;S2S7dG1A1Lx;S6eU0S9S11R7A2A2A6A3Thead;Tim;Tlk;Twp;Tlw;Tkey;Tobjs;").
Definition n_pieces (S : sstate) : nat := ltac2:(tb__ "0|1|
S7fS9S2S35S3eS18VS;A1M0A2A2S9S2S35S3fG0A2A2A2").

Definition XEX_of (Xf : axst) : list axform := ltac2:(tb__ "0|2|
S1S73S76S46S53VXf;A1M0A1A1S1S73S75U0M1A1S71S73S74G1A1S8aS4bG0A1A1A3A3A3").
Definition XM_of (Xf : axst) : axst := ltac2:(tb__ "0|0|
S67VXf;S45VXf;A1A2").

Definition nkeep (nW : nat) : nat := (3 + nW)%nat.
Definition XK_of (nW : nat) (XM : axst) : axst := ltac2:(tb__ "0|1|
S55VXM;S83S53VXM;A1M0S6fS11S40VnW;A1S18G0A1A3A2A2").
Definition REST_of (nW : nat) (XM : axst) : list sobj := ltac2:(tb__ "0|0|
S72S11S40VnW;A1S18S53VXM;A1A1A3").

Definition XR_of (XK : axst) : axst := ltac2:(tb__ "0|1|
S53VXK;A1S2dS55VXK;S23S2aR1A1S81S2bR1A1S1S6S2S10A2M0S0S2S10U4S14P18A1A4S5G0A1A3A2S27R1A1S26R1A1S2cR1A1S18R1A1S25R1A1S29R1A1S28R1A1A9A2TS;").

Definition sX_of (XR : axst) (W : list ulink) (st : ustop) : wsub := ltac2:(tb__ "0|0|
S82S80S53VXR;A1S53S88S87VW;Vst;A3A1A3").

From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import RtCells Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst.

Definition NRTX : list carve_spec := ltac2:(tb__ "0|17|
S1S6S6S6S10S2fA2M0S2fA2M1S7S6S6S2fS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0S2fS0S10S2fS13Z0A1M6Z17db48M7A4Z17db4aA4S1G3S0G2S10S0S2fS2G7U1M8A4S13Z1M9A1A4S1G3S0G2S10S0S2fS2Z17db49G8A4G6A4S5G3A1MaA3A3A4S8S5dS86S1G5S0G1G4S0G0S2fS0S10S2fG6Z17fcd8MbA4Z17fcdcA4S1G3S0G2S10S0S2fS2GbU4McA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z17fbdcMdA4Z17fbe0A4S1G3S0G2S10S0S2fS2GdGcA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S77A4S5bS77G9A2A4S1G3S0G2S10S0S2fS2S77G8A4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S78A4S5bS78Z8A2A4S1G3S0G2S10S0S2fS2S78U8MeA4G6A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z17fb80MfA4Z17fb90A4S1G3S0G2S10S0S2fS2GfGeA4G6A4S1G3S0G2S10S0S2fS2Z17fb88GeA4G6A4GaA3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Ze6780M10A4Ze6788A4S1G3S0G2S10S0S2fS2G10GeA4S13Zdb004A1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Z17fc60M11A4Z17fc68A4S1G3S0G2S10S0S2fS2G11GeA4S13ZffffffffffffffffA1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Zeb8e4M12A4Zeb8f0A4S1G3S0G2S10S0S2fS2G12GcA4S13Z1000A1A4S1G3S0G2S10S0S2fS2Zeb8e8GcA4G6A4S1G3S0G2S10S0S2fS2Zeb8ecGcA4S13ZbeA1A4GaA3A3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S5bS6cZ50A2M13A4S5bS6cZ58A2A4S1G3S0G2S10S0S2fS2G13GeA4S13S79A1A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fG6S5bS6cZ40A2M14A4G13A4S1G3S0G2S10S0S2fS2G14GeA4S13S7aA1A4S1G3S0G2S10S0S2fS2S5bS6cZ48A2GeA4S6bA4GaA3A3A4S1G5S0G1G4S0G0S2fS0S10S2fG6Zeaa78M15A4Zeaa80A4S1G3S0G2S10S0S2fS2G15GeA4S85A4GaA3A4S1G5S0G1G4S0G0S2fS0S10S2fS6aZef2c8M16A4Zef2d0A4S1G3S0G2S10S0S2fS2G16GeA4G6A4GaA3A4S5G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma NRTX_sub : incl NRTX NRT.
Proof. unfold NRTX, NRT. intros k Hk. apply in_inv in Hk as [<-|Hk]; [left; reflexivity | right]. apply in_app_or in Hk as [Hk|Hk]; apply in_or_app; [left; exact Hk | right]. cbn in Hk |- *. tauto. Qed.

Definition RSHAPE (q : qvar) : list sobj := ltac2:(tb__ "0|0|
S6dS11S11S39S8S11S1S11S61S1S11S60S1S11S62S1S11S64S1S11S63S1S11S65S5S11A1A3A3A3A3A3A3S66Vq;A1A3A4").

Definition NBX : sv := ltac2:(tb__ "0|0|
S15S4eS15S51S1fS3Q20S14P82A1A3S13Z4A1A3S15S4eS14P9bA1S13Z1800000000A1A3A3").
Definition ITX : sv := ltac2:(tb__ "0|0|
S15S4eS14P7aA1S15S51S14P7eA1S13Z3A1A3A3").
Definition S_hdr : sobj := nocellsF O_hdr.
Definition S_qc : sobj := ltac2:(tb__ "0|0|
S16S69S13Z0A1S13Z20A1S5S12A1S17A5").
Definition S_bh : sobj := ltac2:(tb__ "0|0|
S16S14P7aA1S13Z0A1S13Z18A1S5S12A1S17A5").
Definition S_it : sobj := ltac2:(tb__ "0|0|
S16S41S13Z18A1S13Z20A1S5S12A1S17A5").
Definition S_pc : sobj := ltac2:(tb__ "0|0|
S16S68S13Z780A1S13Z790A1S5S12A1S17A5").
Definition S_nb : sobj := ltac2:(tb__ "0|0|
S16S36S13Z0A1S13Z2000A1S5S12A1S17A5").
Definition c8 (off : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS13Voff;A1Z8Vv;A3").
Definition c4 (off : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S1cS13Voff;A1Z4Vv;A3").

Definition LCELLS (q : qvar) : list (sobj * cell) := ltac2:(tb__ "0|12|
S8S6S11S12A2M0S1G0S0S11S12S3dS38N10M1S14P6bA1A2A4S1G0S0S11S12S3dS38NcS14P67A1A2A4S5G0A1M2A3A3S5fS7G0A1Lq;Vq;S1G0S0S11S12S33S32Z0M3S14P78A1M4A2A4S1G0S0S11S12S33S32Z8M5S14P79A1A2A4M6S1G0S0S11S12S33S32Z10M7S14P7aA1A2A4S1G0S0S11S12S33S32Z18M8S15S4eS14P7bA1M9S14PdA1MaA3A2A4S1G0S0S11S12S34S32G3S14P7cA1A2A4S1G0S0S11S12S34S32G5S15S4eS14P7dA1MbGaA3A2A4S1G0S0S11S12S34S32G7S15S4eS14P7eA1S13Z1A1McA3A2A4S1G0S0S11S12S44S32G8S15S4eS14PcA1S13G1A1A3A2MdA4G2A3A3A3A3A3A3A3A3S1G0S0S11S12S33S32G3GcA2A4S1G0S0S11S12S33S32G5S36A2A4S1G0S0S11S12S33S32G7S36A2A4MeS1G0S0S11S12S33S32G8S15S4eG9S15S4eGaS13Z2000A1A3MfA3A2A4M10S1G0S0S11S12S3aS38Z780S15S4eS14P7fA1S13N1A1A3A2A4S1G0S0S11S12S3aS38Z784S14P80A1A2A4S1G0S0S11S12S3aS32Z788S14P81A1A2A4S1G0S0S11S12S37S32G3S13G3A1A2A4S1G0S0S11S12S37S32G5GfA2A4S1G0S0S11S12S37S32G7GcA2A4S1G0S0S11S12S37GdA4G2A3A3A3A3A3A3A3M11A3A3A3A3S1G0S0S11S12S33S32G3S15S4eG4GcA3A2A4S1G0G6S1G0GeS1G0G10S1G0S0S11S12S34S32G3S36A2A4S1G0S0S11S12S34S32G5GbA2A4S1G0S0S11S12S34S32G7S13Z3fdA1A2A4G11A3A3A3A3A3A3A3X5fx3A3").

Definition QSX (q : qvar) : sv := ltac2:(tb__ "0|3|
S5fS10Lq;Vq;S15S4eS14P7bA1M0S14PdA1M1A3S15S4eG0S15S4eG1S13Z2000A1A3A3M2G2X5fx3").
Definition FQX (q : qvar) : sprop := ltac2:(tb__ "0|0|
S21S20S52S13S79A1S43Vq;A1A3A1").

Definition rclsb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11SfS57S11S54R1A1S6dS5dS11S5eS3bA4A3S57S11S54S39R1A1A1S3cVq;A1A3A2Lo;VR;A3").
Definition rcivb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S5dS5dS57S11S54S5eR1A1A1VR;A3Lk;S3bA3").
Definition rcellb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S58S6S11S12A2M0G0S57S11S11SbS54S39R1A1ScS11S12R2A3A2S57S12S56SeS11S12R2A3A1S24R1A1A3A2Lo;VR;A3Lsc;S42Vq;A1A3").
Definition rwrb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11S22S1aR1A1A1Lo;VR;A3").
Definition rshpb (q : qvar) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S58S11S11S57S11S11S54S39R1A1R2A2Lo;VR;A3Ls;S3cVq;A1A3").
End F0A_xdefs.

