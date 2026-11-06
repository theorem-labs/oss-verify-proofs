(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From Stdlib Require NArith PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.

(* [comment removed for export] *)
Module F0A_b2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "Ebg_2Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_2Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b2Bf.

(* [comment removed for export] *)
Module F0A_bL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf"; "Ebg_L1Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L1Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL1Bf.

(* [comment removed for export] *)
Module F0T_cLTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA"; "C4_LTA"; "EQ_LTA"; "q_LTA"; "C2_LTA"; "C3_LTA"; "LT_LTA"; "ED_LTA"; "S1c_LTA"; "l1_LTA"; "CD_LTA"; "EX_LTA"; "Ems_LTA"; "Eps_LTA"; "P0_LTA"; "TM_LTA"; "TQ_LTA"; "run3_LTA"; "run6_LTA"; "LH0_LTA"; "RM_LTA"; "RQ_LTA"; "TDr_LTA"; "TM0_LTA"; "TQ0_LTA"; "l2_LTA"; "l3_LTA"; "l4_LTA"; "run2_LTA"; "run4_LTA"; "run5_LTA"; "EfD_LTA"; "Eq_LTA"; "RD_LTA"; "Ebg_LTA"; "Edr_LTA"; "TD_LTA"; "Xf_LTA"; "l1okb_LTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
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

Definition W_LTA : list ulink := Wcan 0.
Definition st_LTA : ustop := UStopLe.
Definition q_LTA : qvar := QA.
Definition F0_LTA : list sprop := FACTS_Tc false q_LTA.
Definition P0_LTA : axst := P0T_c false q_LTA.

Definition l1_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LTA.
Definition LH0_LTA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LTA) DUMMY).
Definition l2_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LTA.
Definition LH1_LTA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LTA) DUMMY).
Definition LT_LTA : axst := Eval vm_compute in LT_ofg LH1_LTA F0_LTA.
Definition EX_LTA : axst := Eval vm_compute in EX_ofg LH1_LTA F0_LTA.
Definition l3_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LTA (SVar pFR)).
Definition l4_LTA : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LTA.
Definition S1c_LTA : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LTA DUMMY)) (F0_LTA ++ F_ext).

Lemma RUN1_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_LTA (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_LTA : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_LTA : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_LTA : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_LTA : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LTA : axst := C2_of S1c_LTA.
Definition run2_LTA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_LTA : axst := leaf 0 run2_LTA.
Definition ED_LTA : axst := ED_of EfD_LTA.
Definition RD_LTA : list sobj := RDv_of ED_LTA.
Definition TD_LTA : axst := TDv_of ED_LTA.
Definition TDr_LTA : axst := TDr_of TD_LTA.

Definition CD_LTA : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_LTA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_LTA : axst := leaf 0 run3_LTA.
Definition Ebg_LTA : axst := leaf 1 run3_LTA.
Definition C3_LTA : axst := C3_of Eps_LTA.
Definition run4_LTA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_LTA : axst := leaf 0 run4_LTA.
Definition C4_LTA : axst := C4_of Ems_LTA.
Definition RM_LTA : list sobj := RM_of C4_LTA.
Definition TM0_LTA : axst := TM0_of C4_LTA.
Definition TM_LTA : axst := TM_of C4_LTA.
Definition run5_LTA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_LTA : axst := leaf 0 run5_LTA.
Definition EQ_LTA : axst := EQ_of Eq_LTA.
Definition RQ_LTA : list sobj := RQ_of EQ_LTA q_LTA.
Definition TQ0_LTA : axst := TQ0_of EQ_LTA q_LTA.
Definition TQ_LTA : axst := TQ_of EQ_LTA q_LTA.
Definition run6_LTA : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_LTA : axst := leaf 0 run6_LTA.
Definition Xf_LTA : axst := leaf 1 run6_LTA.

Lemma D2_LTA : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LTA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LTA : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_LTA : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_LTA; reflexivity. Qed.
Lemma L2_LTA : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_LTA; reflexivity]). Qed.
Lemma AXD_LTA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LTA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LTA : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_LTA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LTA : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_LTA; reflexivity. Qed.
Lemma L3_LTA : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LTA | unfold Ebg_LTA]; reflexivity]). Qed.
Lemma NX3_LTA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_LTA : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LTA : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_LTA : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_LTA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_LTA; reflexivity. Qed.
Lemma L4_LTA : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_LTA; reflexivity]). Qed.
Lemma D4_LTA : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LTA : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LTA : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LTA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LTA : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_LTA : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_LTA, TM0_of, RM_LTA; reflexivity. Qed.
Lemma FBM_LTA : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LTA : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_LTA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_LTA; reflexivity. Qed.
Lemma L5_LTA : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_LTA; reflexivity]). Qed.
Lemma AXQ_LTA : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_LTA : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_LTA : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_LTA : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_LTA, TQ0_of, RQ_LTA; reflexivity. Qed.
Lemma FBQ_LTA : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_LTA : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_LTA : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_LTA : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_LTA; reflexivity. Qed.
Lemma L6_LTA : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_LTA | unfold Xf_LTA]; reflexivity]). Qed.
End F0T_cLTA.

(* [comment removed for export] *)
Module F0T_cLTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "andb"; "Some"; "negb"; "option"; "prod"; "false"; "pair"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "sv"; "ss_lenient"; "sobj"; "ss_facts"; "sprop_below"; "swf"; "SVar"; "ss_objs"; "sprop_eqb"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "entsF"; "BIGX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "CASX"; "PostQ1"; "CD_of"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe"; "C4_LTBe"; "EQ_LTBe"; "q_LTBe"; "C2_LTBe"; "C3_LTBe"; "LT_LTBe"; "ED_LTBe"; "S1c_LTBe"; "l1_LTBe"; "CD_LTBe"; "EX_LTBe"; "Ems_LTBe"; "Eps_LTBe"; "P0_LTBe"; "TM_LTBe"; "TQ_LTBe"; "run3_LTBe"; "run6_LTBe"; "LH0_LTBe"; "RM_LTBe"; "RQ_LTBe"; "TDr_LTBe"; "TM0_LTBe"; "TQ0_LTBe"; "l2_LTBe"; "l3_LTBe"; "l4_LTBe"; "run2_LTBe"; "run4_LTBe"; "run5_LTBe"; "EfD_LTBe"; "Eq_LTBe"; "RD_LTBe"; "Ebg_LTBe"; "Edr_LTBe"; "TD_LTBe"; "Xf_LTBe"; "l1okb_LTBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "LOOPX"; "PreDv"; "atpc"; "sDv_of"; "F_ext"; "PostDv"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
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

Definition W_LTBe : list ulink := Wcan 0.
Definition st_LTBe : ustop := UStopLe.
Definition q_LTBe : qvar := QBe.
Definition F0_LTBe : list sprop := FACTS_Tc false q_LTBe.
Definition P0_LTBe : axst := P0T_c false q_LTBe.

Definition l1_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LTBe.
Definition LH0_LTBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LTBe) DUMMY).
Definition l2_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LTBe.
Definition LH1_LTBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LTBe) DUMMY).
Definition LT_LTBe : axst := Eval vm_compute in LT_ofg LH1_LTBe F0_LTBe.
Definition EX_LTBe : axst := Eval vm_compute in EX_ofg LH1_LTBe F0_LTBe.
Definition l3_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LTBe (SVar pFR)).
Definition l4_LTBe : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LTBe.
Definition S1c_LTBe : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LTBe DUMMY)) (F0_LTBe ++ F_ext).

Lemma RUN1_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S31SdS2A1A3A3S4eA3S49A3"). Proof. Time vmr. Qed.
Lemma RUN2f_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S53A3S59A3"). Proof. Time vmr. Qed.
Lemma RUN3f_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S6cSaS2S6eSdS2A1A3A3S83S46S1fS6dA1A2A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S31SdS2A1A3S4bA3S5bA3"). Proof. Time vmr. Qed.

Definition l1okb_LTBe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S6S6S15S86S22S4S7R1A1M0A1A1S6cA2S26G0S48A2A2LL;Vl;A3").
Lemma chk_LTBe : ltac2:(tb__ "0|a|
S0S9SeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeSeS10ScS6A1M0S9Lx;M1S49SbS6G0S13Ll0;Ll;M2Xcx2A1S10G1S59SbG2Xcx2A1A2S10G1S5aSbG2Xcx2A1A2S10G1S5bSbG2Xcx2A1A2S66S49A1A2S85S16S6S70S6cS49A2A2U1A2A2S69S6S6S15S26S7R1A1M3S46A2S26G3S4bA2A2LL;S59A3A2S1eS4S84S46S1fS6dA1M4A2A1A1A2S23S17S4S46A1M5A1M6G4A2A2S69S6S82S46S4bS6dA3S5aA3A2S69S6S6S26G3S48A2LL;S5bA3A2S68S67S17S4S4eA1M7A1A2A2S68S67S17S4S53A1M8A1A2A2S68S67G6A2A2S68S67S17S4S4bA1M9A1A2A2S10S1aG7A1A1A2S10S1aG8A1A1A2S10S1aG5A1A1A2S10S1aG9A1A1A2SbA3").
Proof. Time vmr. Qed.
Lemma LH0eq_LTBe : ltac2:(tb__ "0|0|
S0S5S7S75S6U0S70S6cS49A2S40A4A1S53A3"). Proof. vmr. Qed.

Lemma SIDE_LTBe : ltac2:(tb__ "0|0|
S0S9S80S4eS46A2SbA3"). Proof. Time vmr. Qed.
Lemma OBND_LTBe : ltac2:(tb__ "0|1|
S0ScS12S12S19S19A2S19A2M0A1S74S1bG0S7fS20S4S46A1A1A4S74S1bG0S7fS20S4S4eA1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LTBe : axst := C2_of S1c_LTBe.
Definition run2_LTBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S28SdS2A1A3S44A3").
Definition EfD_LTBe : axst := leaf 0 run2_LTBe.
Definition ED_LTBe : axst := ED_of EfD_LTBe.
Definition RD_LTBe : list sobj := RDv_of ED_LTBe.
Definition TD_LTBe : axst := TDv_of ED_LTBe.
Definition TDr_LTBe : axst := TDr_of TD_LTBe.

Definition CD_LTBe : axst := ltac2:(tb__ "0|0|
S33S56A1S5S3cR1S6bS18S18S10S6aS18S21R1A1S72A3A1Lf;S1cS4R1A1A1A3A2TC;").
Definition run3_LTBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3").
Definition Eps_LTBe : axst := leaf 0 run3_LTBe.
Definition Ebg_LTBe : axst := leaf 1 run3_LTBe.
Definition C3_LTBe : axst := C3_of Eps_LTBe.
Definition run4_LTBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2bSdS2A1A3S45A3").
Definition Ems_LTBe : axst := leaf 0 run4_LTBe.
Definition C4_LTBe : axst := C4_of Ems_LTBe.
Definition RM_LTBe : list sobj := RM_of C4_LTBe.
Definition TM0_LTBe : axst := TM0_of C4_LTBe.
Definition TM_LTBe : axst := TM_of C4_LTBe.
Definition run5_LTBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S2aSdS2A1A3S4fA3").
Definition Eq_LTBe : axst := leaf 0 run5_LTBe.
Definition EQ_LTBe : axst := EQ_of Eq_LTBe.
Definition RQ_LTBe : list sobj := RQ_of EQ_LTBe q_LTBe.
Definition TQ0_LTBe : axst := TQ0_of EQ_LTBe q_LTBe.
Definition TQ_LTBe : axst := TQ_of EQ_LTBe q_LTBe.
Definition run6_LTBe : list leafA := ltac2:(tb__ "0|0|
S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3").
Definition Edr_LTBe : axst := leaf 0 run6_LTBe.
Definition Xf_LTBe : axst := leaf 1 run6_LTBe.

Lemma D2_LTBe : ltac2:(tb__ "0|4|
S0S11S12ScS12S19S19A2M0A1M1ScS18A1M2A2M3A1S78S4S48A1S4S44A1A2SfG3S14G1G2SaG0S14S19S19S39S3dA4SdG0A1A3S34A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LTBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S44A1M0A1SbA3S1S0S3S17G0A1S17S4S48A1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LTBe : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S44A1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_LTBe : ltac2:(tb__ "0|0|
S0S5S8S48S4S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S28SdS2A1A3S44A3S5cA3"). Proof. unfold run2_LTBe; reflexivity. Qed.
Lemma L2_LTBe : ltac2:(tb__ "0|0|
S1S0S9S25S5cSaS2S28SdS2A1A3A2SbA3S0S5S3fU0S5cA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_LTBe; reflexivity]). Qed.
Lemma AXD_LTBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS5fS36A2SfS5S47A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LTBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S47S6fS71S47A1A3SfG0S61A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LTBe : ltac2:(tb__ "0|0|
S0S9S7cS47S6fS71S47A1S61SaS5S73SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_LTBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS64S37A2SfS5S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LTBe : ltac2:(tb__ "0|0|
S0S9S81S56S4aA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2cSaS2S27SdS2A1A3A3S4aA3S51A3"). Proof. unfold run3_LTBe; reflexivity. Qed.
Lemma L3_LTBe : ltac2:(tb__ "0|0|
S1S0S9S25S51SaS2S2cSaS2S27SdS2A1A3A3A2SbA3S1S0S5S3fU0S51A2S4dA3S0S5S3fU1S51A2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LTBe | unfold Ebg_LTBe]; reflexivity]). Qed.
Lemma NX3_LTBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4aA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma D3_LTBe : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4dA1S4S45A1A2SfG2S14G0G1S3aSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LTBe : ltac2:(tb__ "0|0|
S0S5S8S4dS4S45A1A2S45A3"). Proof. vmr. Qed.
Lemma NX3b_LTBe : ltac2:(tb__ "0|0|
S0S9S68S67S17S4S45A1A1A2SbA3"). Proof. vmr. Qed.
Lemma W3_LTBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S45A1M0A1SbA3S1S0S3S17G0A1S17S4S4dA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2bSdS2A1A3S45A3S5dA3"). Proof. unfold run4_LTBe; reflexivity. Qed.
Lemma L4_LTBe : ltac2:(tb__ "0|0|
S1S0S9S25S5dSaS2S2bSdS2A1A3A2SbA3S0S5S3fU0S5dA2S4cA3A2"). Proof. Time (split; [vmr | unfold Ems_LTBe; reflexivity]). Qed.
Lemma D4_LTBe : ltac2:(tb__ "0|3|
S0S11S12ScS12S19S19A2A1M0ScS18A1M1A2M2A1S78S4S4cA1S4S41A1A2SfG2S14G0G1S3bSdS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LTBe : ltac2:(tb__ "0|0|
S0S5S8S4cS4S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LTBe : ltac2:(tb__ "0|1|
S1S0S9S1eS4S41A1M0A1SbA3S1S0S3S17G0A1S17S4S4cA1A1A3S0S9S1aG0A1S13A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LTBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S41S76S2fS41A1A3SfG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LTBe : ltac2:(tb__ "0|0|
S0S9S7aS41S76S2fS41A1S54S74S6S5S7S77A4A5SbA3"). Proof. Time vmr. Qed.
Lemma HTM_LTBe : ltac2:(tb__ "0|0|
S0S5S7bS2fS41A1S76S35S41S54A5S57A3"). Proof. unfold TM0_LTBe, TM0_of, RM_LTBe; reflexivity. Qed.
Lemma FBM_LTBe : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S41A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S57A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LTBe : ltac2:(tb__ "0|0|
S0S5S7eS57S1cS4S41A1A1A2S4fA3"). Proof. vmr. Qed.
Lemma NX5_LTBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S4fA1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S2aSdS2A1A3S4fA3S5eA3"). Proof. unfold run5_LTBe; reflexivity. Qed.
Lemma L5_LTBe : ltac2:(tb__ "0|0|
S1S0S9S25S5eSaS2S2aSdS2A1A3A2SbA3S0S5S3fU0S5eA2S60A3A2"). Proof. Time (split; [vmr | unfold Eq_LTBe; reflexivity]). Qed.
Lemma AXQ_LTBe : ltac2:(tb__ "0|0|
S0S11S5A1S7dS60S38A2SfS5S42A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_LTBe : ltac2:(tb__ "0|1|
S0S11ScS1bA1M0A1S79S42S2dS43A1S30S42S43A2A3SfG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_LTBe : ltac2:(tb__ "0|0|
S0S9S7aS42S2dS43A1S30S42S43A2S55SaS5S32S43A1SdS5A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTQ_LTBe : ltac2:(tb__ "0|0|
S0S5S7bS30S42S43A2S2dS43A1S32S43A1S42S55A5S58A3"). Proof. unfold TQ0_LTBe, TQ0_of, RQ_LTBe; reflexivity. Qed.
Lemma FBQ_LTBe : ltac2:(tb__ "0|3|
S1S0S9S69S18S1dS17S4S42A1M0A1M1A1S1cG0A1M2A3SbA3S1S0S9S69S18S1dS17S4S58A1A1A1G2A3SbA3S0S9S68S67G1A2SbA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_LTBe : ltac2:(tb__ "0|0|
S0S5S7eS58S1cS4S42A1A1A2S50A3"). Proof. vmr. Qed.
Lemma NX6_LTBe : ltac2:(tb__ "0|1|
S1S0S9S68S67S17S4S50A1M0A1A2SbA3S0S9S1aG0A1S13A3A2"). Proof. split; vmr. Qed.
Lemma RUN6_LTBe : ltac2:(tb__ "0|0|
S0ScS6A1S3eS24SaS2S29SaS2S2eSdS2A1A3A3S50A3S52A3"). Proof. unfold run6_LTBe; reflexivity. Qed.
Lemma L6_LTBe : ltac2:(tb__ "0|0|
S1S0S9S25S52SaS2S29SaS2S2eSdS2A1A3A3A2SbA3S1S0S5S3fU0S52A2S63A3S0S5S3fU1S52A2S65A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_LTBe | unfold Xf_LTBe]; reflexivity]). Qed.
End F0T_cLTBe.

(* [comment removed for export] *)
Module F0A_bL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A"; "Ebg_L2A"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2A : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2A.

(* [comment removed for export] *)
Module F0A_bL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be"; "Ebg_L2Be"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L2Be : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL2Be.

