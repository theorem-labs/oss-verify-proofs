(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lt l5 kz lo ld.

(* [comment removed for export] *)
Module F0T_cLTCe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "false"; "list"; "nil"; "andb"; "Some"; "option"; "prod"; "negb"; "pair"; "length"; "app"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sobj"; "sv"; "sprop"; "swf"; "ss_lenient"; "ss_facts"; "ss_objs"; "SVar"; "sprop_below"; "sprop_eqb"; "SLit"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "leaves_at"; "BIGX"; "DEPE"; "MSE"; "PSE"; "sM_of"; "CASX"; "CD_of"; "F_typ"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "XD"; "XDr"; "casx"; "d3F"; "d4F"; "qvar"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_cLTCe"; "C4_LTCe"; "EC_LTCe"; "C2_LTCe"; "C3_LTCe"; "ED_LTCe"; "LT_LTCe"; "RR_LTCe"; "T1_LTCe"; "S1c_LTCe"; "TR_LTCe"; "l1_LTCe"; "sR_LTCe"; "CD_LTCe"; "EX_LTCe"; "Ems_LTCe"; "Eps_LTCe"; "P0_LTCe"; "TM_LTCe"; "TRs_LTCe"; "run3_LTCe"; "LH0_LTCe"; "RD_LTCe"; "RM_LTCe"; "TDr_LTCe"; "TM0_LTCe"; "l2_LTCe"; "l3_LTCe"; "l4_LTCe"; "run2_LTCe"; "run4_LTCe"; "run5_LTCe"; "run5d_LTCe"; "Ebg_LTCe"; "EfD_LTCe"; "Erf_LTCe"; "Erq2_LTCe"; "Erq_LTCe"; "KEPT1_LTCe"; "T0_LTCe"; "T2_LTCe"; "TD_LTCe"; "KEPT_LTCe"; "XR_LTCe"; "XS_LTCe"; "XW_LTCe"; "l1okb_LTCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "K_i1"; "K_i2"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "P0T_g"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "PostDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe"; "TQ_LTBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_LTCe : list ulink := Wcan 0.
Definition st_LTCe : ustop := UStopLe.
Definition F0_LTCe : list sprop := FACTS_Tg false (VFC false).
Definition P0_LTCe : axst := ltac2:(tb__ "0|0|
S86S7S7cS7aS19S7bS6fS7A1A4S70S7A1A3").

Definition l1_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LTCe.
Definition LH0_LTCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LTCe) DUMMY).
Definition l2_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LTCe.
Definition LH1_LTCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LTCe) DUMMY).
Definition LT_LTCe : axst := Eval vm_compute in LT_ofg LH1_LTCe F0_LTCe.
Definition EX_LTCe : axst := Eval vm_compute in EX_ofg LH1_LTCe F0_LTCe.
Definition l3_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LTCe (SVar pFR)).
Definition l4_LTCe : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LTCe.
Definition S1c_LTCe : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LTCe DUMMY)) (F0_LTCe ++ F_ext).

Lemma RUN1_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S82S6S2S2eS9S2A1A3A3S51A3S4bA3"). Proof. Time vmr. Qed.
Lemma RUN2f_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S82S6S2S85S9S2A1A3A3S55A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN3f_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S82S6S2S85S9S2A1A3A3Sb4S46S20S83A1A2A3S5bA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S2eS9S2A1A3S4eA3S5cA3"). Proof. Time vmr. Qed.

Definition l1okb_LTCe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S7fS15S15S12Sb7S24S13S17R1A1M0A1A1S82A2S27G0S49A2A2LL;Vl;A3").
Lemma chk_LTCe : ltac2:(tb__ "0|a|
S0S4SaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSeS8S15A1M0S4Lx;M1S4bS5S15G0S7Ll0;Ll;M2X8x2A1SeG1S5aS5G2X8x2A1A2SeG1S5bS5G2X8x2A1A2SeG1S5cS5G2X8x2A1A2S6eS4bA1A2Sb6S10S15S88S82S4bA2A2U1A2A2S7fS15S15S12S27S17R1A1M3S46A2S27G3S4eA2A2LL;S5aA3A2S1cS13Sb5S46S20S83A1M4A2A1A1A2S25S18S13S46A1M5A1M6G4A2A2S7fS15Sb3S46S4eS83A3S5bA3A2S7fS15S15S27G3S49A2LL;S5cA3A2S78S77S18S13S51A1M7A1A2A2S78S77S18S13S55A1M8A1A2A2S78S77G6A2A2S78S77S18S13S4eA1M9A1A2A2SeS1dG7A1A1A2SeS1dG8A1A1A2SeS1dG5A1A1A2SeS1dG9A1A1A2S5A3").
Proof. Time vmr. Qed.
Lemma LH0eq_LTCe : ltac2:(tb__ "0|0|
S0S14S17S7dS15U0S88S82S4bA2S40A4A1S55A3"). Proof. vmr. Qed.

Lemma SIDE_LTCe : ltac2:(tb__ "0|0|
S0S4Sa8S51S46A2S5A3"). Proof. Time vmr. Qed.
Lemma OBND_LTCe : ltac2:(tb__ "0|1|
S0S8SdSdS1aS1aA2S1aA2M0A1S7cS19G0Sa7S1fS13S46A1A1A4S7cS19G0Sa7S1fS13S51A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LTCe : axst := C2_of S1c_LTCe.
Definition run2_LTCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S6S2S2aS9S2A1A3S43A3").
Definition EfD_LTCe : axst := leaf 0 run2_LTCe.
Definition ED_LTCe : axst := ED_of EfD_LTCe.
Definition RD_LTCe : list sobj := RDv_of ED_LTCe.
Definition TD_LTCe : axst := TDv_of ED_LTCe.
Definition TDr_LTCe : axst := TDr_of TD_LTCe.

Definition CD_LTCe : axst := ltac2:(tb__ "0|0|
S2fS58A1S14S3bR1S81S1bS1bSeS80S1bS22R1A1S8aA3A1Lf;S1eS13R1A1A1A3A2TC;").
Definition run3_LTCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S6S2S2cS6S2S29S9S2A1A3A3S4dA3").
Definition Eps_LTCe : axst := leaf 0 run3_LTCe.
Definition Ebg_LTCe : axst := leaf 1 run3_LTCe.
Definition C3_LTCe : axst := C3_of Eps_LTCe.
Definition run4_LTCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S6S2S2bS9S2A1A3S44A3").
Definition Ems_LTCe : axst := leaf 0 run4_LTCe.
Definition C4_LTCe : axst := C4_of Ems_LTCe.
Definition RM_LTCe : list sobj := RM_of C4_LTCe.
Definition TM0_LTCe : axst := TM0_of C4_LTCe.
Definition TM_LTCe : axst := TM_of C4_LTCe.

Definition run5_LTCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S6S2S94S9S2A1A3S52A3").
Definition Erf_LTCe : axst := leaf 0 run5_LTCe.
Definition XR_LTCe : list axform := XRC Erf_LTCe.
Definition EC_LTCe : axst := EC_of Erf_LTCe.
Definition sR_LTCe : wsub := sR_of (E3_of Erf_LTCe).
Definition RR_LTCe : list sobj := RR_of EC_LTCe sR_LTCe.
Definition KEPT_LTCe : list sobj := KEPT_of EC_LTCe RR_LTCe.

Definition T0_LTCe : axst := ltac2:(tb__ "0|0|
S9cS42S4cS47A3").
Definition XS_LTCe : list axform := XS_of T0_LTCe.
Definition T1_LTCe : axst := T1_of T0_LTCe.
Definition KEPT1_LTCe : list sobj := KEPT1_of T1_LTCe.
Definition T2_LTCe : axst := T2_of T1_LTCe.
Definition TR_LTCe : axst := TR_of T1_LTCe.

Definition TRs_LTCe : axst := TRs_of TR_LTCe.
Definition run5d_LTCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S6S2S3fS9S2A1A3S53A3").
Definition Erq_LTCe : axst := leaf 0 run5d_LTCe.
Definition XW_LTCe : list axform := XW Erq_LTCe.
Definition Erq2_LTCe : axst := Erq2_of Erq_LTCe.

Lemma D2_LTCe : ltac2:(tb__ "0|4|
S0ScSdS8SdS1aS1aA2M0A1M1S8S1bA1M2A2M3A1S8cS13S49A1S13S43A1A2SbG3SfG1G2S6G0SfS1aS1aS37S3cA4S9G0A1A3S30A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LTCe : ltac2:(tb__ "0|1|
S1S0S4S1cS13S43A1M0A1S5A3S1S0S3S18G0A1S18S13S49A1A1A3S0S4S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LTCe : ltac2:(tb__ "0|0|
S0S4S78S77S18S13S43A1A1A2S5A3"). Proof. vmr. Qed.
Lemma EQ2_LTCe : ltac2:(tb__ "0|0|
S0S14S16S49S13S43A1A2S43A3"). Proof. vmr. Qed.
Lemma RUN2_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S2aS9S2A1A3S43A3S5dA3"). Proof. unfold run2_LTCe; reflexivity. Qed.
Lemma L2_LTCe : ltac2:(tb__ "0|0|
S1S0S4S28S5dS6S2S2aS9S2A1A3A2S5A3S0S14S3eU0S5dA2S62A3A2"). Proof. Time (split; [vmr | unfold EfD_LTCe; reflexivity]). Qed.
Lemma AXD_LTCe : ltac2:(tb__ "0|0|
S0ScS14A1S7eS62S35A2SbS14S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LTCe : ltac2:(tb__ "0|1|
S0ScS8S19A1M0A1S8fS45S87S84S45A1A3SbG0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LTCe : ltac2:(tb__ "0|0|
S0S4S90S45S87S84S45A1S56S6S14S8bS9S14A1A3A5S5A3"). Proof. Time vmr. Qed.
Lemma AXDr_LTCe : ltac2:(tb__ "0|0|
S0ScS14A1S7eS69S36A2SbS14S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LTCe : ltac2:(tb__ "0|0|
S0S4Sb2S58S4dA2S5A3"). Proof. Time vmr. Qed.
Lemma RUN3_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S2cS6S2S29S9S2A1A3A3S4dA3S54A3"). Proof. unfold run3_LTCe; reflexivity. Qed.
Lemma L3_LTCe : ltac2:(tb__ "0|0|
S1S0S4S28S54S6S2S2cS6S2S29S9S2A1A3A3A2S5A3S1S0S14S3eU0S54A2S50A3S0S14S3eU1S54A2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LTCe | unfold Ebg_LTCe]; reflexivity]). Qed.
Lemma NX3_LTCe : ltac2:(tb__ "0|1|
S1S0S4S78S77S18S13S4dA1M0A1A2S5A3S0S4S1dG0A1S7A3A2"). Proof. split; vmr. Qed.

Lemma BGF_LTCe : ltac2:(tb__ "0|0|
S0S4S80S1bS22SacA1S1eS13S61A1A1A3S5A3"). Proof. vmr. Qed.
Lemma D3_LTCe : ltac2:(tb__ "0|3|
S0ScSdS8SdS1aS1aA2A1M0S8S1bA1M1A2M2A1S8cS13S50A1S13S44A1A2SbG2SfG0G1S38S9S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LTCe : ltac2:(tb__ "0|0|
S0S14S16S50S13S44A1A2S44A3"). Proof. vmr. Qed.
Lemma NX3b_LTCe : ltac2:(tb__ "0|0|
S0S4S78S77S18S13S44A1A1A2S5A3"). Proof. vmr. Qed.
Lemma W3_LTCe : ltac2:(tb__ "0|1|
S1S0S4S1cS13S44A1M0A1S5A3S1S0S3S18G0A1S18S13S50A1A1A3S0S4S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S2bS9S2A1A3S44A3S5eA3"). Proof. unfold run4_LTCe; reflexivity. Qed.
Lemma L4_LTCe : ltac2:(tb__ "0|0|
S1S0S4S28S5eS6S2S2bS9S2A1A3A2S5A3S0S14S3eU0S5eA2S4fA3A2"). Proof. Time (split; [vmr | unfold Ems_LTCe; reflexivity]). Qed.
Lemma D4_LTCe : ltac2:(tb__ "0|3|
S0ScSdS8SdS1aS1aA2A1M0S8S1bA1M1A2M2A1S8cS13S4fA1S13S41A1A2SbG2SfG0G1S39S9S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LTCe : ltac2:(tb__ "0|0|
S0S14S16S4fS13S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LTCe : ltac2:(tb__ "0|1|
S1S0S4S1cS13S41A1M0A1S5A3S1S0S3S18G0A1S18S13S4fA1A1A3S0S4S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LTCe : ltac2:(tb__ "0|1|
S0ScS8S19A1M0A1S8fS41S8dS2dS41A1A3SbG0S57A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LTCe : ltac2:(tb__ "0|0|
S0S4S92S41S8dS2dS41A1S57S7cS15S14S17S8eA4A5S5A3"). Proof. Time vmr. Qed.
Lemma HTM_LTCe : ltac2:(tb__ "0|0|
S0S14S91S2dS41A1S8dS32S41S57A5S59A3"). Proof. unfold TM0_LTCe, TM0_of, RM_LTCe; reflexivity. Qed.
Lemma FBM_LTCe : ltac2:(tb__ "0|3|
S1S0S4S7fS1bS21S18S13S41A1M0A1M1A1S1eG0A1M2A3S5A3S1S0S4S7fS1bS21S18S13S59A1A1A1G2A3S5A3S0S4S78S77G1A2S5A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LTCe : ltac2:(tb__ "0|0|
S0S14S96S59S1eS13S41A1A1A2S52A3"). Proof. vmr. Qed.

Lemma NX5_LTCe : ltac2:(tb__ "0|1|
S1S0S4S78S77S18S13S52A1M0A1A2S5A3S0S4S1dG0A1S7A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S94S9S2A1A3S52A3S5fA3"). Proof. unfold run5_LTCe; reflexivity. Qed.
Lemma L5_LTCe : ltac2:(tb__ "0|0|
S1S0S4S28S5fS6S2S94S9S2A1A3A2S5A3S0S14S3eU0S5fA2S63A3A2"). Proof. Time (split; [vmr | unfold Erf_LTCe; reflexivity]). Qed.
Lemma AXR_LTCe : ltac2:(tb__ "0|0|
S0ScS14A1S7eS63S6bA2SbS14S42A2A3"). Proof. Time vmr. Qed.

Lemma HER_LTCe : ltac2:(tb__ "0|1|
S0ScS8S19A1M0A1S8fS42S93S4cA3SbG0S47A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LTCe : ltac2:(tb__ "0|0|
S0S4S90S42S93S4cS47S6S14S95S9S14A1A3A5S5A3"). Proof. Time vmr. Qed.
Lemma OBJS_LTCe : ltac2:(tb__ "0|0|
S0S8S19A1S1fS13S42A1A1S11S19S6aS47A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LTCe : ltac2:(tb__ "0|0|
S0S14S67S96S91S4cS93S95S42S47A5S1eS13S42A1A1A2A3"). Proof. unfold T0_LTCe, T0_of; reflexivity. Qed.
Lemma HXS_LTCe : ltac2:(tb__ "0|0|
S0ScS14A1S7eS67S6cA2SbS14S48A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LTCe : ltac2:(tb__ "0|0|
S0S8S19A1S1fS13S48A1A1S11S19S66S6S19S31S6S19S7bS71A1S6S19S7bS72A1S9S19A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LTCe : ltac2:(tb__ "0|0|
S0S14S68S16S48Sa9S13S48A1S66A2A2A3"). Proof. unfold T2_LTCe, T2_of, KEPT1_LTCe; reflexivity. Qed.
Lemma HTR_LTCe : ltac2:(tb__ "0|2|
S0S14S4aS98S68S6S7aS99S9bS18S13S48A1A1M0S79G0A1M1A3S9S7aA1A3S79G1A1A3A3"). Proof. unfold TR_LTCe, TR_of, T2_LTCe; reflexivity. Qed.
Lemma RCHK_LTCe : ltac2:(tb__ "0|0|
S0S4S9aU0S7S42S48S4aS4cS47S9bA8S5A3"). Proof. Time vmr. Qed.

Lemma HTRs_LTCe : ltac2:(tb__ "0|0|
S0S14S53S98S4aSadS18S13S4aA1A1A3A3"). Proof. unfold TRs_LTCe, TRs_of; reflexivity. Qed.
Lemma CCHK_LTCe : ltac2:(tb__ "0|0|
S0S4SaeU0S4S3aL_;S7S34S33X4x2S4aS53A4S5A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LTCe : ltac2:(tb__ "0|0|
S0S8S15A1S3dS26S6S2S3fS9S2A1A3S53A3S60A3"). Proof. unfold run5d_LTCe; reflexivity. Qed.
Lemma L5d_LTCe : ltac2:(tb__ "0|0|
S1S0S4S28S60S6S2S3fS9S2A1A3A2S5A3S0S14S3eU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erq_LTCe; reflexivity]). Qed.
Lemma AXW_LTCe : ltac2:(tb__ "0|0|
S0ScS14A1S7eS65S6dA2SbS14S64A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LTCe : ltac2:(tb__ "0|0|
S0S4S27S64SafA2S5A3"). Proof. Time vmr. Qed.
Lemma DCHK_LTCe : ltac2:(tb__ "0|1|
S0S4Sb0U0M0S73S6fS7A1G0A2S45S69S84S45A1S56A6S5A3"). Proof. Time vmr. Qed.

Lemma Wa_LTCe : ltac2:(tb__ "0|0|
S0S4S1cS9dS74U0A1A1A1S5A3"). Proof. vmr. Qed.
Lemma Da_LTCe : ltac2:(tb__ "0|4|
S0ScSdS8SdS1aS1aA2M0A1M1S8S1bA1M2A2M3A1S8cS13Sb1S76A1A1S9dS74U0A1A1A2SbG3SfG1G2S6G0SfS1aS1aS20P18A1S23SabA1A4S9G0A1A3S9S1bA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LTCe : ltac2:(tb__ "0|0|
S0S4S1cS9eS74U0A1S6fS7A1A2A1S5A3"). Proof. vmr. Qed.
Lemma Wc_LTCe : ltac2:(tb__ "0|0|
S0S4S1cS9fS74U0A1S6fS7A1A2A1S5A3"). Proof. vmr. Qed.
Lemma Wd_LTCe : ltac2:(tb__ "0|0|
S0S4S1cSa0S74U0A1S6fS7A1A2A1S5A3"). Proof. vmr. Qed.
Lemma Fb_LTCe : ltac2:(tb__ "0|0|
S0S4S7fS1bS21SaaA1S89S7S70S7A1A2A3S5A3"). Proof. vmr. Qed.
Lemma XI_LTCe : ltac2:(tb__ "0|3|
S0ScS14A1S7eSa1S7S74U0M0A1S6fS7A1M1S70S7A1M2A4S97G0S10S7aG1A2A2A2SbS14S86S7S7cS7aS19S7bG1A4G2A3A2A3"). Proof. vmr. Qed.

Definition PMID_LTCe : axst := ltac2:(tb__ "0|0|
Sa2S7S74U0A1S75S7cS7aS19S7bS6fS7A1A4S70S7A1A5").
Lemma Wbm_LTCe : ltac2:(tb__ "0|0|
S0S4S1cSa3S74U0A1S75S6fS7A1A3A1S5A3"). Proof. vmr. Qed.
Lemma Wcm_LTCe : ltac2:(tb__ "0|0|
S0S4S1cSa4S74U0A1S75S6fS7A1A3A1S5A3"). Proof. vmr. Qed.
Lemma Wdm_LTCe : ltac2:(tb__ "0|0|
S0S4S1cSa5S74U0A1S75S6fS7A1A3A1S5A3"). Proof. vmr. Qed.
Lemma XIm_LTCe : ltac2:(tb__ "0|4|
S0ScS14A1S7eSa6S7S74U0M0A1M1S75S6fS7A1M2S70S7A1M3A5S97G0S10S7aG2A2A2A2SbS14Sa2S7G1S75S7cS7aS19S7bG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0T_cLTCe.

(* [comment removed for export] *)
Module F0T_aLTCe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "andb"; "cons"; "nil"; "prod"; "pair"; "negb"; "orb"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "aa_live"; "topG"; "aa_Kf"; "aa_Km"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe"; "MT_LTCe"; "m1_LTCe"; "MX_LTCe"; "MH0_LTCe"; "m2_LTCe"; "m3_LTCe"; "m4_LTCe"; "okbm_LTCe"; "okbp_LTCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_cLTCe"; "ED_LTCe"; "PMID_LTCe"; "TD_LTCe"; "S1c_LTCe"; "P0_LTCe"; "LT_LTCe"; "l1_LTCe"; "EX_LTCe"; "LH0_LTCe"; "TM_LTCe"; "l2_LTCe"; "l3_LTCe"; "l4_LTCe"; "RD_LTCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe.ALTCe"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "J_free_tol_preT"; "objs_le"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_asmC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_cLTCe.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition RUN1p_LTCe := RUN1_LTCe. Definition RUN2p_LTCe := RUN2f_LTCe. Definition RUN3p_LTCe := RUN3f_LTCe. Definition RUN4p_LTCe := RUN4f_LTCe.
Definition okbp_LTCe := l1okb_LTCe. Definition chkp_LTCe := chk_LTCe. Definition H0eqp_LTCe := LH0eq_LTCe. Definition SIDEp_LTCe := SIDE_LTCe. Definition OBNDp_LTCe := OBND_LTCe.
Lemma splitp_LTCe : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S5aScS14A1M1A3A1S1S2S0G0S5eG1A3A1S1S2S0G0S5fG1A3A1S2S0G0S60G1A3A1A2A2A2S1S0S6S53S5aA1S7A3S1S0S6S9aS11S14S73S71S5aA2A2U1A2S7A3S1S0S6S68S14S14S10S44S17R1A1M2S59A2S44G2S5bA2A2LL;S5eA3S7A3S1S0S6S20S15S98S59S21S72A1M3A2A1A1S7A3S1S0S6S22S1dS15S59A1M4A1M5G3A2S7A3S1S0S6S68S14S97S59S5bS72A3S5fA3S7A3S1S0S6S68S14S14S44G2S57A2LL;S60A3S7A3S1S1S78S19S1dS15S58A1M6A1A2S1S78S19S1dS15S5cA1M7A1A2S1S78S19G5A2S78S19S1dS15S5bA1M8A1A2A2A2A2S1S0S6S1cG6A1S9A3S1S0S6S1cG7A1S9A3S1S0S6S1cG4A1S9A3S0S6S1cG8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_LTCe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_LTCe : ltac2:(tb__ "0|1|
S14S69S14R1S5aA3S3S0S16S17R2A1M0S5cA3S0S6S44G0S57A2S7A3A2F_;FL;").
Proof.
  destruct splitp_LTCe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LTCe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_LTCe. destruct (atpc LOOPH l1_LTCe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_LTCe : ltac2:(tb__ "0|0|
S0S6S20S93S34U0A1S2fA2A1S7A3"). Proof. vmr. Qed.
Lemma Dai_LTCe : ltac2:(tb__ "0|4|
S0S12SdS8SdS1eS1eA2M0A1M1S8S25A1M2A2M3A1Sa5S15S7cS32A1A1S93S34U0A1S2fA2A2S13G3SeG1G2SbG0SeS1eS1eS21P18A1S23Sa8A1A4ScG0A1A3ScS25A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_LTCe : ltac2:(tb__ "0|0|
S0S6S20S95S34U0A1S2fA2A1S7A3"). Proof. vmr. Qed.
Lemma Wci_LTCe : ltac2:(tb__ "0|0|
S0S6S20S96S34U0A1S2fA2A1S7A3"). Proof. vmr. Qed.
Definition Certi_LTCe__runs : ltac2:(tb__ "0|0|
S8S12S8S14A1A1A1") := ltac2:(tb__ "0|0|
Sa6S18Ubb8S90S92U0S2fA2A4").
Lemma Certi_LTCe : ltac2:(tb__ "0|1|
S0S6S9eS18Ubb8S90S19S92U0M0S2fA2SbS16S91S34G0A1S2fA2ScS16A1A3A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_LTCe__runs); [unfold Certi_LTCe__runs; reflexivity | vmr]. Qed.
Lemma ECerti_LTCe : ltac2:(tb__ "0|2|
S0S6S9fS18Ubb8S90S19S94U0M0S2fA2SbS9dSa0S91S34G0A1S2fA2Z0M1S23G1A1A3ScS9dA1A3A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_LTCe__runs); [unfold Certi_LTCe__runs; reflexivity | vmr]. Qed.
Definition m1_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_LTCe.
Definition MH0_LTCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_LTCe) DUMMY).
Definition m2_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_LTCe.
Definition MH1_LTCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_LTCe) DUMMY).
Definition MT_LTCe : axst := Eval vm_compute in LT_ofg MH1_LTCe F0_LTCe.
Definition MX_LTCe : axst := Eval vm_compute in EX_ofg MH1_LTCe F0_LTCe.
Definition m3_LTCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_LTCe (SVar pFR)).
Definition m4_LTCe : list leafA := Eval vm_compute in runA FUELF [CASX] MX_LTCe.
Lemma RUN1m_LTCe : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SbS5S71SbS5S46ScS5A1A3A3S55A3S4cA3"). Proof. Time vmr. Qed.
Lemma RUN2m_LTCe : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SbS5S71SbS5S74ScS5A1A3A3S4eA3S4fA3"). Proof. Time vmr. Qed.
Lemma RUN3m_LTCe : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SbS5S71SbS5S74ScS5A1A3A3S99S4bS21S72A1A2A3S50A3"). Proof. Time vmr. Qed.
Lemma RUN4m_LTCe : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SbS5S46ScS5A1A3S4dA3S51A3"). Proof. Time vmr. Qed.
Definition okbm_LTCe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S68S14S14S10S2bS27S15S17R1A1M0A1A1S71A2S44G0S57A2A2LL;Vl;A3").
Lemma chkm_LTCe : ltac2:(tb__ "0|a|
S0S6SaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSfS8S14A1M0S6Lx;M1S4cS7S14G0S9Ll0;Ll;M2X8x2A1SfG1S4fS7G2X8x2A1A2SfG1S50S7G2X8x2A1A2SfG1S51S7G2X8x2A1A2S52S4cA1A2S9aS11S14S73S71S4cA2A2U1A2A2S68S14S14S10S44S17R1A1M3S4bA2S44G3S4dA2A2LL;S4fA3A2S20S15S98S4bS21S72A1M4A2A1A1A2S22S1dS15S4bA1M5A1M6G4A2A2S68S14S97S4bS4dS72A3S50A3A2S68S14S14S44G3S57A2LL;S51A3A2S79S19S1dS15S55A1M7A1A2A2S79S19S1dS15S4eA1M8A1A2A2S79S19G6A2A2S79S19S1dS15S4dA1M9A1A2A2SfS1cG7A1A1A2SfS1cG8A1A1A2SfS1cG5A1A1A2SfS1cG9A1A1A2S7A3").
Proof. Time vmr. Qed.
Lemma H0eqm_LTCe : ltac2:(tb__ "0|0|
S0S16S17S9cS14U0S73S71S4cA2S88A4A1S4eA3"). Proof. vmr. Qed.
Lemma SIDEm_LTCe : ltac2:(tb__ "0|0|
S0S6S8dS55S4bA2S7A3"). Proof. Time vmr. Qed.
Lemma OBNDm_LTCe : ltac2:(tb__ "0|1|
S0S8SdSdS1eS1eA2S1eA2M0A1S9bS24G0S8cS1fS15S4bA1A1A4S9bS24G0S8cS1fS15S55A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_LTCe : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S4cScS14A1M1A3A1S1S2S0G0S4fG1A3A1S1S2S0G0S50G1A3A1S2S0G0S51G1A3A1A2A2A2S1S0S6S52S4cA1S7A3S1S0S6S9aS11S14S73S71S4cA2A2U1A2S7A3S1S0S6S68S14S14S10S44S17R1A1M2S4bA2S44G2S4dA2A2LL;S4fA3S7A3S1S0S6S20S15S98S4bS21S72A1M3A2A1A1S7A3S1S0S6S22S1dS15S4bA1M4A1M5G3A2S7A3S1S0S6S68S14S97S4bS4dS72A3S50A3S7A3S1S0S6S68S14S14S44G2S57A2LL;S51A3S7A3S1S1S78S19S1dS15S55A1M6A1A2S1S78S19S1dS15S4eA1M7A1A2S1S78S19G5A2S78S19S1dS15S4dA1M8A1A2A2A2A2S1S0S6S1cG6A1S9A3S1S0S6S1cG7A1S9A3S1S0S6S1cG4A1S9A3S0S6S1cG8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_LTCe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_LTCe : ltac2:(tb__ "0|1|
S14S69S14R1S4cA3S3S0S16S17R2A1M0S4eA3S0S6S44G0S57A2S7A3A2F_;FL;").
Proof.
  destruct splitm_LTCe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_LTCe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_LTCe. destruct (atpc LOOPH m1_LTCe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ALTCe.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S35S1aS8S2dQ40A1A1S70VA;R3A2Sa4Vkeep;Vrho1;R3A3S1aS4aVsegs;Vok;S3eVsegs;S6fU0S2fS9R6VKc;R5A6S5dR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma spine_tail_LTCe : ltac2:(tb__ "0|2|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S6dU0M1S2fRcRbRaR9R7S54S56R5AaS85RdRcRbRaR8R6A6S1aS4aVsegs;ReS3eVsegs;S6fG1S2fS7RdRcRaA6S57R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LTCe rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LTCe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_LTCe Q BGF_LTCe HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_LTCe C3_LTCe Ems_LTCe C4_LTCe TM0_LTCe run4_LTCe RM_LTCe D3_LTCe W3_LTCe EQ3_LTCe NX3b_LTCe RUN4_LTCe L4_LTCe D4_LTCe W4_LTCe EQ4_LTCe
             HeM_LTCe HchkM_LTCe HTM_LTCe FBM_LTCe ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LTCe. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (f0_s2 0 UStopLe true S1c_LTCe C2_LTCe EfD_LTCe ED_LTCe run2_LTCe D2_LTCe W2_LTCe NX2_LTCe EQ2_LTCe RUN2_LTCe L2_LTCe AXD_LTCe
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0 UStopLe false TD_LTCe TDr_LTCe CD_LTCe Eps_LTCe Ebg_LTCe run3_LTCe AXDr_LTCe ENTD_LTCe RUN3_LTCe L3_LTCe NX3_LTCe
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_LTCe : ltac2:(tb__ "0|4|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S8bR7S2cG0S1bR7PaA2A2S1fS15S58A1A1A3S0G1S1bR8P99A2S2eG0S37S36RbA1A1A2A3S1S28Z1S37S36RcA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6dU0S2fRfReRdRcRaS54S56R8AaS85R10RfReRdRbR9A6S1aS4aVsegs;R11S3eVsegs;S89R10RfRdA3S58R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_LTCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTCe LH0_LTCe LT_LTCe EX_LTCe S1c_LTCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTCe l2_LTCe l3_LTCe l4_LTCe HNX HLEN
           (runT_some _ _ _ _ RUN1p_LTCe NE1) L1okp_LTCe (runT_some _ _ _ _ RUN2p_LTCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LTCe NE3) H3 (runT_some _ _ _ _ RUN4p_LTCe NE4) H4
           (hside_of A Kc rho1 P0_LTCe LT_LTCe tp SIDEp_LTCe OBNDp_LTCe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LTCe keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Theorem free_spine_m_LTCe : ltac2:(tb__ "0|4|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S8bR7S2cG0S1bR7PaA2A2S1fS15S55A1A1A3S0G1S1bR8P99A2S2eG0S37S36RbA1A1A2A3S1S28Z1S37S36RcA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6dU0S2fRfReRdRcRaS54S56R8AaS85R10RfReRdRbR9A6S1aS4aVsegs;R11S3eVsegs;S89R10RfRdA3S55R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_LTCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTCe MH0_LTCe MT_LTCe MX_LTCe S1c_LTCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTCe m2_LTCe m3_LTCe m4_LTCe HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTCe NE1) L1okm_LTCe (runT_some _ _ _ _ RUN2m_LTCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTCe NE3) H3 (runT_some _ _ _ _ RUN4m_LTCe NE4) H4
           (hside_of A Kc rho1 PMID_LTCe MT_LTCe tp SIDEm_LTCe OBNDm_LTCe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LTCe keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S35S1aS8S2dQ40A1A1S70VA;R3A2Sa4Vkeep;Vrho1;R3A3S1aS49Vsegs;S3eVsegs;S6fU0S2fS9R6VKc;R5A6S5dR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma espine_tail_LTCe : ltac2:(tb__ "0|2|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S6eU0M1S2fRaR9R8R6S54S56R4A9S86RbRaR9R7R5A5S1aS49Vsegs;S3eVsegs;S6fG1S2fS7RcRbR9A6S57R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LTCe rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LTCe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_LTCe Q BGF_LTCe HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_LTCe C3_LTCe Ems_LTCe C4_LTCe TM0_LTCe run4_LTCe RM_LTCe D3_LTCe W3_LTCe EQ3_LTCe NX3b_LTCe RUN4_LTCe L4_LTCe D4_LTCe W4_LTCe EQ4_LTCe
             HeM_LTCe HchkM_LTCe HTM_LTCe FBM_LTCe A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LTCe. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (ef0_s2 0 UStopLe true S1c_LTCe C2_LTCe EfD_LTCe ED_LTCe run2_LTCe D2_LTCe W2_LTCe NX2_LTCe EQ2_LTCe RUN2_LTCe L2_LTCe AXD_LTCe
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0 UStopLe false TD_LTCe TDr_LTCe CD_LTCe Eps_LTCe Ebg_LTCe run3_LTCe AXDr_LTCe ENTD_LTCe RUN3_LTCe L3_LTCe NX3_LTCe
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_LTCe : ltac2:(tb__ "0|4|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S8bR6S2cG0S1bR6PaA2A2S1fS15S58A1A1A3S0G1S1bR7P99A2S2eG0S37S36RaA1A1A2A3S1S28Z1S37S36RbA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6eU0S2fRdRcRbR9S54S56R7A9S86ReRdRcRaR8A5S1aS49Vsegs;S3eVsegs;S89RfReRcA3S58R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_LTCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTCe LH0_LTCe LT_LTCe EX_LTCe S1c_LTCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTCe l2_LTCe l3_LTCe l4_LTCe HNX HLEN
           (runT_some _ _ _ _ RUN1p_LTCe NE1) L1okp_LTCe (runT_some _ _ _ _ RUN2p_LTCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LTCe NE3) H3 (runT_some _ _ _ _ RUN4p_LTCe NE4) H4
           (hside_of A Kc rho1 P0_LTCe LT_LTCe tp SIDEp_LTCe OBNDp_LTCe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LTCe keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.
Theorem efree_spine_m_LTCe : ltac2:(tb__ "0|4|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S8bR6S2cG0S1bR6PaA2A2S1fS15S55A1A1A3S0G1S1bR7P99A2S2eG0S37S36RaA1A1A2A3S1S28Z1S37S36RbA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6eU0S2fRdRcRbR9S54S56R7A9S86ReRdRcRaR8A5S1aS49Vsegs;S3eVsegs;S89RfReRcA3S55R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_LTCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTCe MH0_LTCe MT_LTCe MX_LTCe S1c_LTCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTCe m2_LTCe m3_LTCe m4_LTCe HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTCe NE1) L1okm_LTCe (runT_some _ _ _ _ RUN2m_LTCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTCe NE3) H3 (runT_some _ _ _ _ RUN4m_LTCe NE4) H4
           (hside_of A Kc rho1 PMID_LTCe MT_LTCe tp SIDEm_LTCe OBNDm_LTCe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LTCe keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S7eVCST;R1A2S3S7eSa9R2A2S1S28S66R2A2S2aR2S67A2A2A2S4F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S7eVCST;R1A2S2SabR2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S7eVCST;R1A2S2SaaR2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S5S7eVCST;R1A2S1S2S1S28S66R2A2S2aR2S67A2A2A1S2S1S28Z17db48R2A2S2aR2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.
Lemma HTD_LTCe : ltac2:(tb__ "0|0|
S0S16S56Sa7S43S77S54A1S76S75S54S61A5S26S15S54A1A1A2A3").
Proof. unfold TD_LTCe, TDv_of, RD_LTCe; reflexivity. Qed.
Theorem hdf_LTCe : ltac2:(tb__ "0|1|
S35S30S1aS8S2dQ40M0A1A1S7fS5S5S5S83S31R8A1S28S29S3cRaA1S3bRaA1A2Sa1A2S65S18RbR9R8R7A5S69SdS5S5A2SeS5S5R7R6A4S39RcA1A3S82R8R7A2S0S5S2cG0S1bRcPcA2A2R9A3Sa2RfRdRaR9R8R7A6S6aS9R10A2S47OF_;S48S40S18R2S3fR12A1A3S80S18R3S3fR13A1A3S6dU0S2fS81VCST;VXGL;R15A3R4R15R14S6bR15R13R10RfReRdA6S54S56R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG (NVC false) 0) HSEG CST XGL HCST HXGL HCSTD ED_LTCe TD_LTCe (sDv_of ED_LTCe) RD_LTCe HeD_LTCe HchkD_LTCe HTD_LTCe DCHK_LTCe
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LTCe : ltac2:(tb__ "0|1|
S35S30S1aS8S2dQ40M0A1A1S7fS5S5S5S83S31R8A1S28S29S3cRaA1S3bRaA1A2Sa1A2S65S18RbR9R8R7A5S69SdS5S5A2SeS5S5R7R6A4S39RcA1A3S82R8R7A2S0S5S2cG0S1bRcPcA2A2R9A3Sa2RfRdRaR9R8R7A6S6aS9R10A2S47OF_;S6eU0S2fS81VCST;VXGL;R12A3R12R11S6bR12R10RdRcRbRaA6S54S56R1A9FQ;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFET 0 (rd_okG (NVC false) 0) HSEGE CST XGL HCST HXGL HCSTD ED_LTCe TD_LTCe (sDv_of ED_LTCe) RD_LTCe HeD_LTCe HchkD_LTCe HTD_LTCe DCHK_LTCe
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.
Lemma tail_LTCe : ltac2:(tb__ "0|3|
S47OF_;S35S30S1aS8S2dQ40M0A1A1M1S5S5S5S83G1S7fS31R9A1S40S18RcS3fRaA1A3S80S18RdS3fRbA1A3S8eReRcA2S65S18ReRcR6R5A5S3dRfA1S0S5S2cG0S1bRePcA2A2RcA3S0S5S2cG0S1bRfPdA2A2RcA3S69SdS5S5A2SeS5S5ReRdA4S39R12A1A3S82RfReA2S0S6S38R14A1S7A3S6aS9R15A2S6cR14S6bR16R14R12R11R10RfA6A2S0S5S84R10A1S64A3S85S81VCST;VXGL;R18A3R19R18R17S6bR18R16R14R13R12R11A6S42S18S7aR16R15SbSdS16S41A2M2SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;Sa3R18Z18A2R17A5A4ScG2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 false CST XGL HCST HXGL TM_LTCe Erf_LTCe EC_LTCe run5_LTCe XR_LTCe NX5_LTCe RUN5_LTCe L5_LTCe AXR_LTCe T0_LTCe T1_LTCe T2_LTCe TR_LTCe sR_LTCe RR_LTCe KEPT_LTCe KEPT1_LTCe XS_LTCe eFRc HER_LTCe Hchk_LTCe OBJS_LTCe HT0_LTCe HXS_LTCe OBJS1_LTCe HT2_LTCe HTR_LTCe RCHK_LTCe TRs_LTCe Erq_LTCe Erq2_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.TQ_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.Edr_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.Xf_LTBe run5d_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.run6_LTBe XW_LTCe HTRs_LTCe CCHK_LTCe RUN5d_LTCe L5d_LTCe AXW_LTCe ENTQ_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.NX6_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.RUN6_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.L6_LTBe
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBe.f0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBe.f0_exit_LTBe CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LTCe : ltac2:(tb__ "0|3|
S35S30S1aS8S2dQ40M0A1A1M1S5S5S5S83G1S7fS31R9A1S8fRaA1S65S18RcRaR4R3A5S3dRdA1S0S5S2cG0S1bRcPcA2A2RaA3S0S5S2cG0S1bRdPdA2A2RaA3S69SdS5S5A2SeS5S5RcRbA4S39R10A1A3S82RdRcA2S0S6S38R12A1S7A3S6aS9R13A2S6cR12S6bR14R12R10RfReRdA6A2S0S5S84ReA1S64A3S86S81VCST;VXGL;R16A3R16R15S6bR16R14R12R11R10RfA6S42S18S7aR14R13SbSdS16S41A2M2SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;Sa3R16Z18A2R15A5A4ScG2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 false CST XGL HCST HXGL TM_LTCe Erf_LTCe EC_LTCe run5_LTCe XR_LTCe NX5_LTCe RUN5_LTCe L5_LTCe AXR_LTCe T0_LTCe T1_LTCe T2_LTCe TR_LTCe sR_LTCe RR_LTCe KEPT_LTCe KEPT1_LTCe XS_LTCe eFRc HER_LTCe Hchk_LTCe OBJS_LTCe HT0_LTCe HXS_LTCe OBJS1_LTCe HT2_LTCe HTR_LTCe RCHK_LTCe TRs_LTCe Erq_LTCe Erq2_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.TQ_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.Edr_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.Xf_LTBe run5d_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.run6_LTBe XW_LTCe HTRs_LTCe CCHK_LTCe RUN5d_LTCe L5d_LTCe AXW_LTCe ENTQ_LTCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.NX6_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.RUN6_LTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.L6_LTBe
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBe.ef0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBe.ef0_exit_LTBe CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Ce_T : ltac2:(tb__ "0|2|
S47OF_;S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SbSdS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S48S31R6A1S40S18R9S3fR7A1A3S80S18RaS3fR8A1A3S28S29R6R5A2S63A2S0S6S38RbA1S7A3S6aS9RcA2S28R8S62A2S8eRfRdA2S4aS18R10S3eS18S8aRfReA2S7cS32A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C_T false false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (t_instantiate false (NVC false) (VFC false) Wa_LTCe Da_LTCe Wb_LTCe Wc_LTCe Wd_LTCe Fb_LTCe XI_LTCe A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_LTCe (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn HO eq_refl HST
           (hdf_LTCe A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LTCe ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_lo_ia0_Ce_T : ltac2:(tb__ "0|2|
S47OF_;S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SbSdS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S48S31R6A1S40S18R9S3fR7A1A3S80S18RaS3fR8A1A3S28S29R6R5A2S63A2S0S6S38RbA1S9A3S6aS9RcA2S28R8S62A2S8eRfRdA2S4aS18R10S3eS18S8aRfReA2S7cS32A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_LTCe Dai_LTCe Wbi_LTCe Wci_LTCe Certi_LTCe ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false (NVC false) (VFC false) Wbm_LTCe Wcm_LTCe Wdm_LTCe Fb_LTCe XIm_LTCe A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (free_spine_m_LTCe (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2 HO eq_refl HST
           (hdf_LTCe A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LTCe ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_Ce_T : ltac2:(tb__ "0|2|
S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SbSdS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S48S31R6A1S28S29R4R3A2S63A2S0S6S38R9A1S7A3S6aS9RaA2S28R6S62A2S8fRbA1S49S18S3eS18S8aRdRcA2S7cS32A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C_T false false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (t_instantiate false (NVC false) (VFC false) Wa_LTCe Da_LTCe Wb_LTCe Wc_LTCe Wd_LTCe Fb_LTCe XI_LTCe A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_LTCe (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn HO eq_refl HST
           (hdfe_LTCe A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (etail_LTCe A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_lo_ia0_Ce_T : ltac2:(tb__ "0|2|
S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SbSdS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S48S31R6A1S28S29R4R3A2S63A2S0S6S38R9A1S9A3S6aS9RaA2S28R6S62A2S8fRbA1S49S18S3eS18S8aRdRcA2S7cS32A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_LTCe Dai_LTCe Wbi_LTCe Wci_LTCe ECerti_LTCe A Kc rho tp Q p n t jv Hii HKc).
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
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false (NVC false) (VFC false) Wbm_LTCe Wcm_LTCe Wdm_LTCe Fb_LTCe XIm_LTCe A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (efree_spine_m_LTCe (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2 HO eq_refl HST
           (hdfe_LTCe A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 _)
           (etail_LTCe A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALTCe.
End F0T_aLTCe.

(* [comment removed for export] *)
Module F0A_cCf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "false"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "MSE"; "PSE"; "sM_of"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cCf2"; "C4_Cf2"; "ED_Cf2_1"; "ED_Cf2_2"; "ED_Cf2_3"; "ED_Cf2_4"; "EC_Cf2"; "P0_Cf2"; "C2_Cf2_1"; "C2_Cf2_2"; "C2_Cf2_3"; "C2_Cf2_4"; "C3_Cf2"; "CD_Cf2"; "RR_Cf2"; "T1_Cf2"; "TR_Cf2"; "sR_Cf2"; "Ems_Cf2"; "Eps_Cf2"; "PMID_Cf2"; "RD_Cf2_1"; "RD_Cf2_2"; "RD_Cf2_3"; "RD_Cf2_4"; "S1c_Cf2_1"; "S1c_Cf2_2"; "S1c_Cf2_3"; "S1c_Cf2_4"; "TM_Cf2"; "TRs_Cf2"; "exits1_Cf2"; "run1_Cf2"; "run3_Cf2"; "RM_Cf2"; "TD_Cf2_1"; "TD_Cf2_2"; "TD_Cf2_3"; "TD_Cf2_4"; "TM0_Cf2"; "run2_Cf2_1"; "run2_Cf2_2"; "run2_Cf2_3"; "run2_Cf2_4"; "run4_Cf2"; "run5_Cf2"; "run5d_Cf2"; "Ebg_Cf2"; "EfD_Cf2_1"; "EfD_Cf2_2"; "EfD_Cf2_3"; "EfD_Cf2_4"; "Erf_Cf2"; "Erq2_Cf2"; "Erq_Cf2"; "KEPT1_Cf2"; "T0_Cf2"; "T2_Cf2"; "TDr_Cf2_1"; "TDr_Cf2_2"; "TDr_Cf2_3"; "TDr_Cf2_4"; "W_Cf2"; "st_Cf2"; "KEPT_Cf2"; "XR_Cf2"; "XS_Cf2"; "XW_Cf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g";
"se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "TQ_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "true"; "list"; "pair"; "prod"; "bool"; "cons"; "nil"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cCf2"; "ED_Cf2_1"; "ED_Cf2_2"; "ED_Cf2_3"; "ED_Cf2_4"; "TD_Cf2_1"; "TD_Cf2_2"; "TD_Cf2_3"; "TD_Cf2_4"; "P0_Cf2"; "PMID_Cf2"; "TM_Cf2"; "exits1_Cf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_aCf2.ACf2"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cCf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
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
  exact (c_tail 2 true CST XGL HCST HXGL TM_Cf2 Erf_Cf2 EC_Cf2 run5_Cf2 XR_Cf2 NX5_Cf2 RUN5_Cf2 L5_Cf2 AXR_Cf2 T0_Cf2 T1_Cf2 T2_Cf2 TR_Cf2 sR_Cf2 RR_Cf2 KEPT_Cf2 KEPT1_Cf2 XS_Cf2 eFRc HER_Cf2 Hchk_Cf2 OBJS_Cf2 HT0_Cf2 HXS_Cf2 OBJS1_Cf2 HT2_Cf2 HTR_Cf2 RCHK_Cf2 TRs_Cf2 Erq_Cf2 Erq2_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.TQ_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.Edr_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.Xf_2Bf run5d_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.run6_2Bf XW_Cf2 HTRs_Cf2 CCHK_Cf2 RUN5d_Cf2 L5d_Cf2 AXW_Cf2 ENTQ_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.NX6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.RUN6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.L6_2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.F0A_q2Bf.f0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2Bf.f0_exit_2Bf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_Cf2 : ltac2:(tb__ "0|3|
S17S2SbS10SeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S53RaA1S30SaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S37S12S0S0A2S11S0S0RcRbA4S18R10A1A3S3aRdRcA2S1bS13S19R12A1SfA3S33SfR13A2S2eR12S34R14R12R10RfReRdA6A2S1bS0S3cReA1S3fA3S51S39VCST;VXGL;R16A3R16R15S34R16R14R12R11R10RfA6S36SaS4eR14R13S14S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R16Z18A2R15A5A4S15G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 2 true CST XGL HCST HXGL TM_Cf2 Erf_Cf2 EC_Cf2 run5_Cf2 XR_Cf2 NX5_Cf2 RUN5_Cf2 L5_Cf2 AXR_Cf2 T0_Cf2 T1_Cf2 T2_Cf2 TR_Cf2 sR_Cf2 RR_Cf2 KEPT_Cf2 KEPT1_Cf2 XS_Cf2 eFRc HER_Cf2 Hchk_Cf2 OBJS_Cf2 HT0_Cf2 HXS_Cf2 OBJS1_Cf2 HT2_Cf2 HTR_Cf2 RCHK_Cf2 TRs_Cf2 Erq_Cf2 Erq2_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.TQ_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.Edr_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.Xf_2Bf run5d_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.run6_2Bf XW_Cf2 HTRs_Cf2 CCHK_Cf2 RUN5d_Cf2 L5d_Cf2 AXW_Cf2 ENTQ_Cf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.NX6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.RUN6_2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.L6_2Bf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.F0A_q2Bf.ef0_drain_2Bf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2Bf.ef0_exit_2Bf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
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
S0S4fVCST;R1A2S1cS1dS1cS27S31R2A2S29R2S32A2A2A1S1dS1cS27Z17db48R2A2S29R2Z17db4cA2A2A1A2F_;Fa;").
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

(* [comment removed for export] *)
Module F0A_cLCe2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "false"; "list"; "option"; "Some"; "prod"; "pair"; "app"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sobj"; "sprop"; "swf"; "ss_facts"; "ss_lenient"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "leaves_at"; "CASX"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "MSE"; "PSE"; "sM_of"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "d3F"; "d4F"; "entsF"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "rd_okG"; "K_i1"; "K_i2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cLCe2"; "C4_LCe2"; "ED_LCe2_1"; "ED_LCe2_2"; "ED_LCe2_3"; "ED_LCe2_4"; "EC_LCe2"; "P0_LCe2"; "C2_LCe2_1"; "C2_LCe2_2"; "C2_LCe2_3"; "C2_LCe2_4"; "C3_LCe2"; "CD_LCe2"; "RR_LCe2"; "T1_LCe2"; "TR_LCe2"; "sR_LCe2"; "Ems_LCe2"; "Eps_LCe2"; "PMID_LCe2"; "RD_LCe2_1"; "RD_LCe2_2"; "RD_LCe2_3"; "RD_LCe2_4"; "S1c_LCe2_1"; "S1c_LCe2_2"; "S1c_LCe2_3"; "S1c_LCe2_4"; "TM_LCe2"; "TRs_LCe2"; "exits1_LCe2"; "run1_LCe2"; "run3_LCe2"; "RM_LCe2"; "TD_LCe2_1"; "TD_LCe2_2"; "TD_LCe2_3"; "TD_LCe2_4"; "TM0_LCe2"; "run2_LCe2_1"; "run2_LCe2_2"; "run2_LCe2_3"; "run2_LCe2_4"; "run4_LCe2"; "run5_LCe2"; "run5d_LCe2"; "Ebg_LCe2"; "EfD_LCe2_1"; "EfD_LCe2_2"; "EfD_LCe2_3"; "EfD_LCe2_4"; "Erf_LCe2"; "Erq2_LCe2"; "Erq_LCe2"; "KEPT1_LCe2"; "T0_LCe2"; "T2_LCe2"; "TDr_LCe2_1"; "TDr_LCe2_2"; "TDr_LCe2_3"; "TDr_LCe2_4"; "W_LCe2"; "st_LCe2"; "KEPT_LCe2"; "XR_LCe2"; "XS_LCe2"; "XW_LCe2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@Stdlib.Lists.List"; "forallb"; "existsb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "sa_g"; "FACTSg"; "P0_g"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "P0_C"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be"; "TQ_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LCe2 : list ulink := Wcan 2.
Definition st_LCe2 : ustop := UStopLe.
Definition P0_LCe2 : axst := ltac2:(tb__ "0|0|
Sb5SbS84S85SbA4").

Definition run1_LCe2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S25SaS13A1A3S4dA3").

Definition S1c_LCe2_1 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z1A3").
Definition C2_LCe2_1 : axst := C2_of S1c_LCe2_1.
Definition run2_LCe2_1 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S23SaS13A1A3S4eA3").
Definition EfD_LCe2_1 : axst := leaf 0 run2_LCe2_1.
Definition ED_LCe2_1 : axst := ED_of EfD_LCe2_1.
Definition RD_LCe2_1 : list sobj := RD_of ED_LCe2_1 1.
Definition TD_LCe2_1 : axst := TD_of ED_LCe2_1 1.
Definition TDr_LCe2_1 : axst := TDr_of TD_LCe2_1.
Definition S1c_LCe2_2 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z2A3").
Definition C2_LCe2_2 : axst := C2_of S1c_LCe2_2.
Definition run2_LCe2_2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S23SaS13A1A3S4fA3").
Definition EfD_LCe2_2 : axst := leaf 0 run2_LCe2_2.
Definition ED_LCe2_2 : axst := ED_of EfD_LCe2_2.
Definition RD_LCe2_2 : list sobj := RD_of ED_LCe2_2 2.
Definition TD_LCe2_2 : axst := TD_of ED_LCe2_2 2.
Definition TDr_LCe2_2 : axst := TDr_of TD_LCe2_2.
Definition S1c_LCe2_3 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z3A3").
Definition C2_LCe2_3 : axst := C2_of S1c_LCe2_3.
Definition run2_LCe2_3 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S23SaS13A1A3S50A3").
Definition EfD_LCe2_3 : axst := leaf 0 run2_LCe2_3.
Definition ED_LCe2_3 : axst := ED_of EfD_LCe2_3.
Definition RD_LCe2_3 : list sobj := RD_of ED_LCe2_3 3.
Definition TD_LCe2_3 : axst := TD_of ED_LCe2_3 3.
Definition TDr_LCe2_3 : axst := TDr_of TD_LCe2_3.
Definition S1c_LCe2_4 : axst := ltac2:(tb__ "0|0|
S27S39U0S66A2S1aS3S4dA1A1Z4A3").
Definition C2_LCe2_4 : axst := C2_of S1c_LCe2_4.
Definition run2_LCe2_4 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S23SaS13A1A3S51A3").
Definition EfD_LCe2_4 : axst := leaf 0 run2_LCe2_4.
Definition ED_LCe2_4 : axst := ED_of EfD_LCe2_4.
Definition RD_LCe2_4 : list sobj := RD_of ED_LCe2_4 4.
Definition TD_LCe2_4 : axst := TD_of ED_LCe2_4 4.
Definition TDr_LCe2_4 : axst := TDr_of TD_LCe2_4.
Definition exits1_LCe2 : list axst := ltac2:(tb__ "0|0|
S8S2S5fS8S2S60S8S2S61S8S2S62SaS2A1A3A3A3A3").

Definition CD_LCe2 : axst := CD_of TDr_LCe2_1.
Definition run3_LCe2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S2eS8S13S2cSaS13A1A3A3S53A3").
Definition Eps_LCe2 : axst := leaf 0 run3_LCe2.
Definition Ebg_LCe2 : axst := leaf 1 run3_LCe2.
Definition C3_LCe2 : axst := C3_of Eps_LCe2.
Definition run4_LCe2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S2dSaS13A1A3S52A3").
Definition Ems_LCe2 : axst := leaf 0 run4_LCe2.
Definition C4_LCe2 : axst := C4_of Ems_LCe2.
Definition RM_LCe2 : list sobj := RM_of C4_LCe2.
Definition TM0_LCe2 : axst := TM0_of C4_LCe2.
Definition TM_LCe2 : axst := TM_of C4_LCe2.

Definition run5_LCe2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13Sa0SaS13A1A3S63A3").
Definition Erf_LCe2 : axst := leaf 0 run5_LCe2.
Definition XR_LCe2 : list axform := XRC Erf_LCe2.
Definition EC_LCe2 : axst := EC_of Erf_LCe2.
Definition sR_LCe2 : wsub := sR_of (E3_of Erf_LCe2).
Definition RR_LCe2 : list sobj := RR_of EC_LCe2 sR_LCe2.
Definition KEPT_LCe2 : list sobj := KEPT_of EC_LCe2 RR_LCe2.

Definition T0_LCe2 : axst := ltac2:(tb__ "0|0|
Sb6S4cS57S54A3").
Definition XS_LCe2 : list axform := XS_of T0_LCe2.
Definition T1_LCe2 : axst := T1_of T0_LCe2.
Definition KEPT1_LCe2 : list sobj := KEPT1_of T1_LCe2.
Definition T2_LCe2 : axst := T2_of T1_LCe2.
Definition TR_LCe2 : axst := TR_of T1_LCe2.

Definition TRs_LCe2 : axst := TRs_of TR_LCe2.
Definition run5d_LCe2 : list leafA := ltac2:(tb__ "0|0|
S38S21S8S13S3aSaS13A1A3S64A3").
Definition Erq_LCe2 : axst := leaf 0 run5d_LCe2.
Definition XW_LCe2 : list axform := XW Erq_LCe2.
Definition Erq2_LCe2 : axst := Erq2_of Erq_LCe2.

Definition PMID_LCe2 : axst := ltac2:(tb__ "0|0|
SacSbS84S85S91S8fS17S90S42SbA1A4S43SbA1A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LCe2 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S4dA1A1A2S9A3"). Proof. vmr. Qed.
Lemma Cert1_LCe2 : ltac2:(tb__ "0|0|
S0S7S94S3cS21S8S13S25SaS13A1A3S3bS8S2S4dSaS2A1A3S65A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LCe2 exits1_LCe2 run1_LCe2); [unfold run1_LCe2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LCe2 : ltac2:(tb__ "0|2|
S0S7S95S3cS21S8S13S25SaS13A1A3S3bS8S92S93S4dZ1S1cZ0M0A1M1A3SaS92A1A3S91S2S92S2S93R1G0G1A3LE;S65A4A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LCe2 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCe2) run1_LCe2); [unfold run1_LCe2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LCe2_1 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S8eS3S5fA1S3S4eA1A2SeG3S10G1G2S8G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe2_1 : ltac2:(tb__ "0|1|
S1S0S7S19S3S4eA1M0A1S9A3S1S0S14S15G0A1S15S3S5fA1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe2_1 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S4eA1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe2_1 : ltac2:(tb__ "0|0|
S0S2S5S5fS3S4eA1A2S4eA3"). Proof. vmr. Qed.
Lemma RUN2_LCe2_1 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S23SaS13A1A3S4eA3S6eA3"). Proof. unfold run2_LCe2_1; reflexivity. Qed.
Lemma L2_LCe2_1 : ltac2:(tb__ "0|0|
S1S0S7S24S6eS8S13S23SaS13A1A3A2S9A3S0S2S39U0S6eA2S76A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe2_1; reflexivity]). Qed.
Lemma AXD_LCe2_1 : ltac2:(tb__ "0|0|
S0SdS2A1S41S76S28A2SeS2S48A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe2_1 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S97S48S8aZ1M1A1S22S48G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe2_1 : ltac2:(tb__ "0|1|
S0S7S99S48S8aZ1M0A1S22S48G0A2S5bS8S2S8bG0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe2_1 : ltac2:(tb__ "0|1|
S0S2S69S96S98S22S48Z1M0A2S8aG0A1S8bG0A1S48S5bA5S1aS3S48A1A1A2A3").
Proof. unfold TD_LCe2_1, TD_of, RD_LCe2_1; reflexivity. Qed.
Lemma DCHK_LCe2_1 : ltac2:(tb__ "0|2|
S0S7S9bU2M0S44S42SbA1G0A2Z1M1S48S69S22S48G1A2S5bA7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe2_1 : ltac2:(tb__ "0|0|
S0SdS2A1S41S69S29A2SeS2S80A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe2_1 : ltac2:(tb__ "0|0|
S0S7S9cS80S53A2S9A3"). Proof. Time vmr. Qed.
Lemma D2_LCe2_2 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S8eS3S60A1S3S4fA1A2SeG3S10G1G2S8G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe2_2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S4fA1M0A1S9A3S1S0S14S15G0A1S15S3S60A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe2_2 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S4fA1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe2_2 : ltac2:(tb__ "0|0|
S0S2S5S60S3S4fA1A2S4fA3"). Proof. vmr. Qed.
Lemma RUN2_LCe2_2 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S23SaS13A1A3S4fA3S6fA3"). Proof. unfold run2_LCe2_2; reflexivity. Qed.
Lemma L2_LCe2_2 : ltac2:(tb__ "0|0|
S1S0S7S24S6fS8S13S23SaS13A1A3A2S9A3S0S2S39U0S6fA2S77A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe2_2; reflexivity]). Qed.
Lemma AXD_LCe2_2 : ltac2:(tb__ "0|0|
S0SdS2A1S41S77S28A2SeS2S49A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe2_2 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S97S49S8aZ2M1A1S22S49G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe2_2 : ltac2:(tb__ "0|1|
S0S7S99S49S8aZ2M0A1S22S49G0A2S5cS8S2S8bG0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe2_2 : ltac2:(tb__ "0|1|
S0S2S6aS96S98S22S49Z2M0A2S8aG0A1S8bG0A1S49S5cA5S1aS3S49A1A1A2A3").
Proof. unfold TD_LCe2_2, TD_of, RD_LCe2_2; reflexivity. Qed.
Lemma DCHK_LCe2_2 : ltac2:(tb__ "0|2|
S0S7S9bU2M0S44S42SbA1G0A2Z2M1S49S6aS22S49G1A2S5cA7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe2_2 : ltac2:(tb__ "0|0|
S0SdS2A1S41S6aS29A2SeS2S81A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe2_2 : ltac2:(tb__ "0|0|
S0S7S9cS81S53A2S9A3"). Proof. Time vmr. Qed.
Lemma D2_LCe2_3 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S8eS3S61A1S3S50A1A2SeG3S10G1G2S8G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe2_3 : ltac2:(tb__ "0|1|
S1S0S7S19S3S50A1M0A1S9A3S1S0S14S15G0A1S15S3S61A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe2_3 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S50A1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe2_3 : ltac2:(tb__ "0|0|
S0S2S5S61S3S50A1A2S50A3"). Proof. vmr. Qed.
Lemma RUN2_LCe2_3 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S23SaS13A1A3S50A3S70A3"). Proof. unfold run2_LCe2_3; reflexivity. Qed.
Lemma L2_LCe2_3 : ltac2:(tb__ "0|0|
S1S0S7S24S70S8S13S23SaS13A1A3A2S9A3S0S2S39U0S70A2S78A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe2_3; reflexivity]). Qed.
Lemma AXD_LCe2_3 : ltac2:(tb__ "0|0|
S0SdS2A1S41S78S28A2SeS2S4aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe2_3 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S97S4aS8aZ3M1A1S22S4aG1A2A3SeG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe2_3 : ltac2:(tb__ "0|1|
S0S7S99S4aS8aZ3M0A1S22S4aG0A2S5dS8S2S8bG0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe2_3 : ltac2:(tb__ "0|1|
S0S2S6bS96S98S22S4aZ3M0A2S8aG0A1S8bG0A1S4aS5dA5S1aS3S4aA1A1A2A3").
Proof. unfold TD_LCe2_3, TD_of, RD_LCe2_3; reflexivity. Qed.
Lemma DCHK_LCe2_3 : ltac2:(tb__ "0|2|
S0S7S9bU2M0S44S42SbA1G0A2Z3M1S4aS6bS22S4aG1A2S5dA7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe2_3 : ltac2:(tb__ "0|0|
S0SdS2A1S41S6bS29A2SeS2S82A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe2_3 : ltac2:(tb__ "0|0|
S0S7S9cS82S53A2S9A3"). Proof. Time vmr. Qed.
Lemma D2_LCe2_4 : ltac2:(tb__ "0|4|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S8eS3S62A1S3S51A1A2SeG3S10G1G2S8G0S10S16S16S2aS2bA4SaG0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LCe2_4 : ltac2:(tb__ "0|1|
S1S0S7S19S3S51A1M0A1S9A3S1S0S14S15G0A1S15S3S62A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LCe2_4 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S51A1A1A2S9A3"). Proof. vmr. Qed.
Lemma EQ2_LCe2_4 : ltac2:(tb__ "0|0|
S0S2S5S62S3S51A1A2S51A3"). Proof. vmr. Qed.
Lemma RUN2_LCe2_4 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S23SaS13A1A3S51A3S71A3"). Proof. unfold run2_LCe2_4; reflexivity. Qed.
Lemma L2_LCe2_4 : ltac2:(tb__ "0|0|
S1S0S7S24S71S8S13S23SaS13A1A3A2S9A3S0S2S39U0S71A2S79A3A2"). Proof. Time (split; [vmr | unfold EfD_LCe2_4; reflexivity]). Qed.
Lemma AXD_LCe2_4 : ltac2:(tb__ "0|0|
S0SdS2A1S41S79S28A2SeS2S4bA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LCe2_4 : ltac2:(tb__ "0|2|
S0SdScS17A1M0A1S97S4bS8aZ4M1A1S22S4bG1A2A3SeG0S5eA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LCe2_4 : ltac2:(tb__ "0|1|
S0S7S99S4bS8aZ4M0A1S22S4bG0A2S5eS8S2S8bG0A1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma HTD_LCe2_4 : ltac2:(tb__ "0|1|
S0S2S6cS96S98S22S4bZ4M0A2S8aG0A1S8bG0A1S4bS5eA5S1aS3S4bA1A1A2A3").
Proof. unfold TD_LCe2_4, TD_of, RD_LCe2_4; reflexivity. Qed.
Lemma DCHK_LCe2_4 : ltac2:(tb__ "0|2|
S0S7S9bU2M0S44S42SbA1G0A2Z4M1S4bS6cS22S4bG1A2S5eA7S9A3"). Proof. Time vmr. Qed.
Lemma AXDr_LCe2_4 : ltac2:(tb__ "0|0|
S0SdS2A1S41S6cS29A2SeS2S83A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LCe2_4 : ltac2:(tb__ "0|0|
S0S7S9cS83S53A2S9A3"). Proof. Time vmr. Qed.
Lemma RUN3_LCe2 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S2eS8S13S2cSaS13A1A3A3S53A3S67A3"). Proof. unfold run3_LCe2; reflexivity. Qed.
Lemma L3_LCe2 : ltac2:(tb__ "0|0|
S1S0S7S24S67S8S13S2eS8S13S2cSaS13A1A3A3A2S9A3S1S0S2S39U0S67A2S59A3S0S2S39U1S67A2S75A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LCe2 | unfold Ebg_LCe2]; reflexivity]). Qed.
Lemma NX3_LCe2 : ltac2:(tb__ "0|1|
S1S0S7S8cS3bS15S3S53A1M0A1A2S9A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma BGF_LCe2 : ltac2:(tb__ "0|0|
S0S7Sa3S18S20SbbA1S1aS3S75A1A1A3S9A3"). Proof. vmr. Qed.
Lemma D3_LCe2 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S8eS3S59A1S3S52A1A2SeG2S10G0G1S34SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LCe2 : ltac2:(tb__ "0|0|
S0S2S5S59S3S52A1A2S52A3"). Proof. vmr. Qed.
Lemma NX3b_LCe2 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S52A1A1A2S9A3"). Proof. vmr. Qed.
Lemma W3_LCe2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S52A1M0A1S9A3S1S0S14S15G0A1S15S3S59A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LCe2 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S2dSaS13A1A3S52A3S72A3"). Proof. unfold run4_LCe2; reflexivity. Qed.
Lemma L4_LCe2 : ltac2:(tb__ "0|0|
S1S0S7S24S72S8S13S2dSaS13A1A3A2S9A3S0S2S39U0S72A2S58A3A2"). Proof. Time (split; [vmr | unfold Ems_LCe2; reflexivity]). Qed.
Lemma D4_LCe2 : ltac2:(tb__ "0|3|
S0SdSfScSfS16S16A2A1M0ScS18A1M1A2M2A1S8eS3S58A1S3S47A1A2SeG2S10G0G1S35SaS18A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LCe2 : ltac2:(tb__ "0|0|
S0S2S5S58S3S47A1A2S47A3"). Proof. vmr. Qed.
Lemma W4_LCe2 : ltac2:(tb__ "0|1|
S1S0S7S19S3S47A1M0A1S9A3S1S0S14S15G0A1S15S3S58A1A1A3S0S7S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LCe2 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S97S47S9dS2fS47A1A3SeG0S68A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LCe2 : ltac2:(tb__ "0|0|
S0S7S9aS47S9dS2fS47A1S68S91S4S2S6S9eA4A5S9A3"). Proof. Time vmr. Qed.
Lemma HTM_LCe2 : ltac2:(tb__ "0|0|
S0S2S98S2fS47A1S9dS31S47S68A5S6dA3"). Proof. unfold TM0_LCe2, TM0_of, RM_LCe2; reflexivity. Qed.
Lemma FBM_LCe2 : ltac2:(tb__ "0|3|
S1S0S7Sa2S18S1dS15S3S47A1M0A1M1A1S1aG0A1M2A3S9A3S1S0S7Sa2S18S1dS15S3S6dA1A1A1G2A3S9A3S0S7S8cS3bG1A2S9A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LCe2 : ltac2:(tb__ "0|0|
S0S2S96S6dS1aS3S47A1A1A2S63A3"). Proof. vmr. Qed.

Lemma NX5_LCe2 : ltac2:(tb__ "0|1|
S1S0S7S8cS3bS15S3S63A1M0A1A2S9A3S0S7S1bG0A1SbA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LCe2 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13Sa0SaS13A1A3S63A3S73A3"). Proof. unfold run5_LCe2; reflexivity. Qed.
Lemma L5_LCe2 : ltac2:(tb__ "0|0|
S1S0S7S24S73S8S13Sa0SaS13A1A3A2S9A3S0S2S39U0S73A2S7aA3A2"). Proof. Time (split; [vmr | unfold Erf_LCe2; reflexivity]). Qed.
Lemma AXR_LCe2 : ltac2:(tb__ "0|0|
S0SdS2A1S41S7aS87A2SeS2S4cA2A3"). Proof. Time vmr. Qed.

Lemma HER_LCe2 : ltac2:(tb__ "0|1|
S0SdScS17A1M0A1S97S4cS9fS57A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LCe2 : ltac2:(tb__ "0|0|
S0S7S99S4cS9fS57S54S8S2Sa1SaS2A1A3A5S9A3"). Proof. Time vmr. Qed.
Lemma OBJS_LCe2 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S4cA1A1S11S17S86S54A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LCe2 : ltac2:(tb__ "0|0|
S0S2S7eS96S98S57S9fSa1S4cS54A5S1aS3S4cA1A1A2A3"). Proof. unfold T0_LCe2, T0_of; reflexivity. Qed.
Lemma HXS_LCe2 : ltac2:(tb__ "0|0|
S0SdS2A1S41S7eS88A2SeS2S55A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LCe2 : ltac2:(tb__ "0|0|
S0ScS17A1S1eS3S55A1A1S11S17S7dS8S17S30S8S17S90S45A1S8S17S90S46A1SaS17A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LCe2 : ltac2:(tb__ "0|0|
S0S2S7fS5S55Sb7S3S55A1S7dA2A2A3"). Proof. unfold T2_LCe2, T2_of, KEPT1_LCe2; reflexivity. Qed.
Lemma HTR_LCe2 : ltac2:(tb__ "0|2|
S0S2S56Sb1S7fS8S8fSb2Sb4S15S3S55A1A1M0S8dG0A1M1A3SaS8fA1A3S8dG1A1A3A3"). Proof. unfold TR_LCe2, TR_of, T2_LCe2; reflexivity. Qed.
Lemma RCHK_LCe2 : ltac2:(tb__ "0|0|
S0S7Sb3U2SbS4cS55S56S57S54Sb4A8S9A3"). Proof. Time vmr. Qed.

Lemma HTRs_LCe2 : ltac2:(tb__ "0|0|
S0S2S64Sb1S56SbdS15S3S56A1A1A3A3"). Proof. unfold TRs_LCe2, TRs_of; reflexivity. Qed.
Lemma CCHK_LCe2 : ltac2:(tb__ "0|0|
S0S7SbeU2S7S37L_;SbS33S32X7x2S56S64A4S9A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LCe2 : ltac2:(tb__ "0|0|
S0ScS4A1S38S21S8S13S3aSaS13A1A3S64A3S74A3"). Proof. unfold run5d_LCe2; reflexivity. Qed.
Lemma L5d_LCe2 : ltac2:(tb__ "0|0|
S1S0S7S24S74S8S13S3aSaS13A1A3A2S9A3S0S2S39U0S74A2S7cA3A2"). Proof. Time (split; [vmr | unfold Erq_LCe2; reflexivity]). Qed.
Lemma AXW_LCe2 : ltac2:(tb__ "0|0|
S0SdS2A1S41S7cS89A2SeS2S7bA2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LCe2 : ltac2:(tb__ "0|0|
S0S7S36S7bSbcA2S9A3"). Proof. Time vmr. Qed.

Lemma Wa_LCe2 : ltac2:(tb__ "0|0|
S0S7S19Sa5S3eU2A1S3dA2A1S9A3"). Proof. vmr. Qed.
Lemma Da_LCe2 : ltac2:(tb__ "0|5|
S0SdSfScSfS16S16A2M0A1M1ScS18A1M2A2M3A1S8eS3S40S3fS3eU2A1M4S3dA3A1Sa5G4S3dA2A2SeG3S10G1G2S8G0S10S16S16S1fP18A1S1cSbaA1A4SaG0A1A3SaS18A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LCe2 : ltac2:(tb__ "0|0|
S0S7S19Sa8S3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wc_LCe2 : ltac2:(tb__ "0|0|
S0S7S19Sa9S3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wd_LCe2 : ltac2:(tb__ "0|0|
S0S7S19SaaS3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Fb_LCe2 : ltac2:(tb__ "0|0|
S0S7Sa2S18S1dSb9A1Sa6SbS3eU2A1S3dS43SbA1A4A3S9A3"). Proof. vmr. Qed.
Lemma XI_LCe2 : ltac2:(tb__ "0|4|
S0SdS2A1S41SabSbS3eU2M0A1M1S3dS42SbA1M2S43SbA1M3A5Sa4G0S12S8fG2A2A2A2SeS2Sa7SbG1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LCe2 : ltac2:(tb__ "0|0|
S0S7S8cS3bS15S3S5aA1A1A2S9A3"). Proof. vmr. Qed.
Definition Cert1m_LCe2__runs : ltac2:(tb__ "0|0|
ScSdScS4A1A1A1") := ltac2:(tb__ "0|0|
Sb8S3cS21S8S13S25SaS13A1A3S8S2S5aSaS2A1A3A4").
Lemma Cert1m_LCe2 : ltac2:(tb__ "0|0|
S0S7S94S3cS21S8S13S25SaS13A1A3S3bS8S2S5aSaS2A1A3S65A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LCe2] exits1_LCe2 Cert1m_LCe2__runs); [unfold Cert1m_LCe2__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LCe2 : ltac2:(tb__ "0|2|
S0S7S95S3cS21S8S13S25SaS13A1A3S3bS8S92S93S5aZ1S1cZ0M0A1M1A3SaS92A1A3S91S2S92S2S93R1G0G1A3LE;S65A4A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LCe2 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LCe2) Cert1m_LCe2__runs); [unfold Cert1m_LCe2__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LCe2 : ltac2:(tb__ "0|0|
S0S7S19SadS3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wcm_LCe2 : ltac2:(tb__ "0|0|
S0S7S19SaeS3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma Wdm_LCe2 : ltac2:(tb__ "0|0|
S0S7S19SafS3eU2A1S3dS42SbA1A3A1S9A3"). Proof. vmr. Qed.
Lemma XIm_LCe2 : ltac2:(tb__ "0|4|
S0SdS2A1S41Sb0SbS3eU2M0A1M1S3dS42SbA1M2S43SbA1M3A5Sa4G0S12S8fG2A2A2A2SeS2SacSbG1S3dS91S8fS17S90G2A4G3A5A2A3"). Proof. vmr. Qed.
End F0A_cLCe2.

(* [comment removed for export] *)
Module F0A_aLCe2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "L_free"; "Wcan"; "J_free_preT"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "pair"; "prod"; "true"; "bool"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_internal_inited"; "budget_ok_free"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cLCe2"; "ED_LCe2_1"; "ED_LCe2_2"; "ED_LCe2_3"; "ED_LCe2_4"; "TD_LCe2_1"; "TD_LCe2_2"; "TD_LCe2_3"; "TD_LCe2_4"; "P0_LCe2"; "PMID_LCe2"; "TM_LCe2"; "exits1_LCe2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_aLCe2.ALCe2"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0A_cLCe2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ld.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ALCe2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).

Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS23Vsegs;Vok;S25Vsegs;S2dU2S1S10R6VKc;R5A6S4aR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S17SbSfSeQ40A1A1S2fVA;R3A2S55Vkeep;Vrho1;R3A3SbS22Vsegs;S25Vsegs;S2dU2S1S10R6VKc;R5A6S4aR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").

Lemma spine_tail_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbSfSeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6S2aSbS37S2aR2S4bA3S23Vsegs;R13S25Vsegs;S2dG1S1S13R12R11RfA6R3R2ReA5RdA4F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_LCe2 rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_LCe2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 2 UStopLe false keep ok A Kc rho rho1 Ebg_LCe2 Q BGF_LCe2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2 UStopLe false Eps_LCe2 C3_LCe2 Ems_LCe2 C4_LCe2 TM0_LCe2 run4_LCe2 RM_LCe2 D3_LCe2 W3_LCe2 EQ3_LCe2 NX3b_LCe2 RUN4_LCe2 L4_LCe2 D4_LCe2 W4_LCe2 EQ4_LCe2
             HeM_LCe2 HchkM_LCe2 HTM_LCe2 FBM_LCe2 ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LCe2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCe2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2 UStopLe true S1c_LCe2_1 C2_LCe2_1 EfD_LCe2_1 ED_LCe2_1 run2_LCe2_1 D2_LCe2_1 W2_LCe2_1 NX2_LCe2_1 EQ2_LCe2_1 RUN2_LCe2_1 L2_LCe2_1 AXD_LCe2_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCe2_1 TDr_LCe2_1 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_1 ENTD_LCe2_1 RUN3_LCe2 L3_LCe2 NX3_LCe2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCe2_2 C2_LCe2_2 EfD_LCe2_2 ED_LCe2_2 run2_LCe2_2 D2_LCe2_2 W2_LCe2_2 NX2_LCe2_2 EQ2_LCe2_2 RUN2_LCe2_2 L2_LCe2_2 AXD_LCe2_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCe2_2 TDr_LCe2_2 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_2 ENTD_LCe2_2 RUN3_LCe2 L3_LCe2 NX3_LCe2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCe2_3 C2_LCe2_3 EfD_LCe2_3 ED_LCe2_3 run2_LCe2_3 D2_LCe2_3 W2_LCe2_3 NX2_LCe2_3 EQ2_LCe2_3 RUN2_LCe2_3 L2_LCe2_3 AXD_LCe2_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCe2_3 TDr_LCe2_3 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_3 ENTD_LCe2_3 RUN3_LCe2 L3_LCe2 NX3_LCe2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2 UStopLe true S1c_LCe2_4 C2_LCe2_4 EfD_LCe2_4 ED_LCe2_4 run2_LCe2_4 D2_LCe2_4 W2_LCe2_4 NX2_LCe2_4 EQ2_LCe2_4 RUN2_LCe2_4 L2_LCe2_4 AXD_LCe2_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2 UStopLe false TD_LCe2_4 TDr_LCe2_4 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_4 ENTD_LCe2_4 RUN3_LCe2 L3_LCe2 NX3_LCe2
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Lemma espine_tail_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5S2aSbS37S2aR2S4bA3S22Vsegs;S25Vsegs;S2dG1S1S13R11R10ReA6R3R2RdA5RcA3F_;FrhoE;FE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM E rhoE HinE.
  assert (HUS : stopJ_stable (Wcan 2) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Eps_LCe2 rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 2 UStopLe false A' Kc rho1') Ebg_LCe2 rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 2 UStopLe false keep A Kc rho rho1 Ebg_LCe2 Q BGF_LCe2 HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2 UStopLe false Eps_LCe2 C3_LCe2 Ems_LCe2 C4_LCe2 TM0_LCe2 run4_LCe2 RM_LCe2 D3_LCe2 W3_LCe2 EQ3_LCe2 NX3b_LCe2 RUN4_LCe2 L4_LCe2 D4_LCe2 W4_LCe2 EQ4_LCe2
             HeM_LCe2 HchkM_LCe2 HTM_LCe2 FBM_LCe2 A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LCe2. exact (HTM A' rho1' tpM HDO HL rhoM). }
  unfold exits1_LCe2 in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2 UStopLe true S1c_LCe2_1 C2_LCe2_1 EfD_LCe2_1 ED_LCe2_1 run2_LCe2_1 D2_LCe2_1 W2_LCe2_1 NX2_LCe2_1 EQ2_LCe2_1 RUN2_LCe2_1 L2_LCe2_1 AXD_LCe2_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCe2_1 TDr_LCe2_1 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_1 ENTD_LCe2_1 RUN3_LCe2 L3_LCe2 NX3_LCe2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCe2_2 C2_LCe2_2 EfD_LCe2_2 ED_LCe2_2 run2_LCe2_2 D2_LCe2_2 W2_LCe2_2 NX2_LCe2_2 EQ2_LCe2_2 RUN2_LCe2_2 L2_LCe2_2 AXD_LCe2_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCe2_2 TDr_LCe2_2 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_2 ENTD_LCe2_2 RUN3_LCe2 L3_LCe2 NX3_LCe2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCe2_3 C2_LCe2_3 EfD_LCe2_3 ED_LCe2_3 run2_LCe2_3 D2_LCe2_3 W2_LCe2_3 NX2_LCe2_3 EQ2_LCe2_3 RUN2_LCe2_3 L2_LCe2_3 AXD_LCe2_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCe2_3 TDr_LCe2_3 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_3 ENTD_LCe2_3 RUN3_LCe2 L3_LCe2 NX3_LCe2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2 UStopLe true S1c_LCe2_4 C2_LCe2_4 EfD_LCe2_4 ED_LCe2_4 run2_LCe2_4 D2_LCe2_4 W2_LCe2_4 NX2_LCe2_4 EQ2_LCe2_4 RUN2_LCe2_4 L2_LCe2_4 AXD_LCe2_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2 UStopLe false TD_LCe2_4 TDr_LCe2_4 CD_LCe2 Eps_LCe2 Ebg_LCe2 run3_LCe2 AXDr_LCe2_4 ENTD_LCe2_4 RUN3_LCe2 L3_LCe2 NX3_LCe2
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Theorem free_spine_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbSfSeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1S13R10RfRdA6S48R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true P0_LCe2 exits1_LCe2 Cert1_LCe2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCe2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1S13RfReRcA6S48R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true P0_LCe2 exits1_LCe2 NX0_LCe2 ECert1_LCe2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCe2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Theorem free_spine_m_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S20OF_;S17S2SbSbSfSeQ40M0A1A1S21S3R5A1S26Vsegs;R8S24R6A1A3S2eR6R5A2S27SdG0ScR7PdA2A2S3dA2S2bU2M1S1RcRbRaR9R7S40S44R5AaS2bG1S1RdRcRbRaR8S41S45R6AaS2bG1S1ReRdRcRbR9S42S46R7AaS2bG1S1RfReRdRcRaS43S47R8AaS50R10RfReRdRbR9A6SbS23Vsegs;R11S25Vsegs;S2dG1S1S13R10RfRdA6S49R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (f0_s1c 2 UStopLe true PMID_LCe2 exits1_LCe2 Cert1m_LCe2 ok A Kc rho1 tp Q (stopJ_stable_le _) HKc Hok).
  exact (spine_tail_LCe2 keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.
Theorem efree_spine_m_LCe2 : ltac2:(tb__ "0|2|
S0OF_;S17S2SbSbSfSeQ40M0A1A1S20OF_;S3R5A1S2eR5R4A2S27SdG0ScR6PdA2A2S3dA2S2cU2M1S1RaR9R8R6S40S44R4A9S2cG1S1RbRaR9R7S41S45R5A9S2cG1S1RcRbRaR8S42S46R6A9S2cG1S1RdRcRbR9S43S47R7A9S51ReRdRcRaR8A5SbS22Vsegs;S25Vsegs;S2dG1S1S13RfReRcA6S49R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM.
  apply (ef0_s1c 2 UStopLe true PMID_LCe2 exits1_LCe2 NX0m_LCe2 ECert1m_LCe2 A Kc rho1 tp Q (stopJ_stable_le _) HKc).
  exact (espine_tail_LCe2 keep A Kc rho rho1 tp Q HKc HR Hn HD1 HD2 HD3 HD4 HTM).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1fS4fS56R2A2S1cS27S31R2A2S29R2S32A2A2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS58R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1dS57R2A1A1F_;Fa;").

Theorem hdf_LCe2_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S40S44R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC false) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_1 TD_LCe2_1 (sD_of ED_LCe2_1 1) RD_LCe2_1 HeD_LCe2_1 HchkD_LCe2_1 HTD_LCe2_1 DCHK_LCe2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe2_1 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S40S44R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC false) 2) 1 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_1 TD_LCe2_1 (sD_of ED_LCe2_1 1) RD_LCe2_1 HeD_LCe2_1 HchkD_LCe2_1 HTD_LCe2_1 DCHK_LCe2_1
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) Q).
Qed.
Theorem hdf_LCe2_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S41S45R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC false) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_2 TD_LCe2_2 (sD_of ED_LCe2_2 2) RD_LCe2_2 HeD_LCe2_2 HchkD_LCe2_2 HTD_LCe2_2 DCHK_LCe2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe2_2 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S41S45R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC false) 2) 2 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_2 TD_LCe2_2 (sD_of ED_LCe2_2 2) RD_LCe2_2 HeD_LCe2_2 HchkD_LCe2_2 HTD_LCe2_2 DCHK_LCe2_2
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) Q).
Qed.
Theorem hdf_LCe2_3 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S42S46R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC false) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_3 TD_LCe2_3 (sD_of ED_LCe2_3 3) RD_LCe2_3 HeD_LCe2_3 HchkD_LCe2_3 HTD_LCe2_3 DCHK_LCe2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe2_3 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S42S46R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC false) 2) 3 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_3 TD_LCe2_3 (sD_of ED_LCe2_3 3) RD_LCe2_3 HeD_LCe2_3 HchkD_LCe2_3 HTD_LCe2_3 DCHK_LCe2_3
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) Q).
Qed.
Theorem hdf_LCe2_4 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S21S26SaR2S24R11A1A3S4dSaR3S24R12A1A3S2bU2S1S39VCST;VXGL;R14A3R4R14R13S34R14R12RfReRdRcA6S43S47R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFG 2 (rd_okG (NVC false) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_4 TD_LCe2_4 (sD_of ED_LCe2_4 4) RD_LCe2_4 HeD_LCe2_4 HchkD_LCe2_4 HTD_LCe2_4 DCHK_LCe2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) ok Q Hok Hokp).
Qed.
Theorem hdfe_LCe2_4 : ltac2:(tb__ "0|1|
S17S2SbSfSeQ40M0A1A1S38S0S0S0S3bS3R8A1S30SaRaR8R7R6A5S37S12S0S0A2S11S0S0R6R5A4S18RbA1A3S3aR7R6A2S1bS0SdG0ScRbPcA2A2R8A3S4cReRcR9R8R7R6A6S33S10RfA2S20OF_;S2cU2S1S39VCST;VXGL;R11A3R11R10S34R11RfRcRbRaR9A6S43S47R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFEG 2 (rd_okG (NVC false) 2) 4 CST XGL HCST HXGL HCSTD ltac:(unfold SZMAX; lia) ED_LCe2_4 TD_LCe2_4 (sD_of ED_LCe2_4 4) RD_LCe2_4 HeD_LCe2_4 HchkD_LCe2_4 HTD_LCe2_4 DCHK_LCe2_4
           A Kc (rhoC_of A rho p n t jv) HKc (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 2) Q).
Qed.

Lemma tail_LCe2 : ltac2:(tb__ "0|3|
S20OF_;S17S2SbSfSeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S26SaRcS24RaA1A3S4dSaRdS24RbA1A3S52ReRcA2S30SaReRcR6R5A5S1aRfA1S1bS0SdG0ScRePcA2A2RcA3S1bS0SdG0ScRfPdA2A2RcA3S37S12S0S0A2S11S0S0ReRdA4S18R12A1A3S3aRfReA2S1bS14S19R14A1S13A3S33S10R15A2S2eR14S34R16R14R12R11R10RfA6A2S1bS0S3cR10A1S3fA3S50S39VCST;VXGL;R18A3R19R18R17S34R18R16R14R13R12R11A6S36SaS4eR16R15S15S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R18Z18A2R17A5A4S16G2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 2 false CST XGL HCST HXGL TM_LCe2 Erf_LCe2 EC_LCe2 run5_LCe2 XR_LCe2 NX5_LCe2 RUN5_LCe2 L5_LCe2 AXR_LCe2 T0_LCe2 T1_LCe2 T2_LCe2 TR_LCe2 sR_LCe2 RR_LCe2 KEPT_LCe2 KEPT1_LCe2 XS_LCe2 eFRc HER_LCe2 Hchk_LCe2 OBJS_LCe2 HT0_LCe2 HXS_LCe2 OBJS1_LCe2 HT2_LCe2 HTR_LCe2 RCHK_LCe2 TRs_LCe2 Erq_LCe2 Erq2_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.TQ_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.Edr_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.Xf_L2Be run5d_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.run6_L2Be XW_LCe2 HTRs_LCe2 CCHK_LCe2 RUN5d_LCe2 L5d_LCe2 AXW_LCe2 ENTQ_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.NX6_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.RUN6_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.L6_L2Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Be.f0_drain_L2Be CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Be.f0_exit_L2Be CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LCe2 : ltac2:(tb__ "0|3|
S17S2SbSfSeQ40M0A1A1M1S0S0S0S3bG1S38S3R9A1S53RaA1S30SaRcRaR4R3A5S1aRdA1S1bS0SdG0ScRcPcA2A2RaA3S1bS0SdG0ScRdPdA2A2RaA3S37S12S0S0A2S11S0S0RcRbA4S18R10A1A3S3aRdRcA2S1bS14S19R12A1S13A3S33S10R13A2S2eR12S34R14R12R10RfReRdA6A2S1bS0S3cReA1S3fA3S51S39VCST;VXGL;R16A3R16R15S34R16R14R12R11R10RfA6S36SaS4eR14R13S15S12S2aS35A2M2S11S2aS35S6S4S7U2A1S1A3S5S30SaA1VCST;VXGL;S54R16Z18A2R15A5A4S16G2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 2 false CST XGL HCST HXGL TM_LCe2 Erf_LCe2 EC_LCe2 run5_LCe2 XR_LCe2 NX5_LCe2 RUN5_LCe2 L5_LCe2 AXR_LCe2 T0_LCe2 T1_LCe2 T2_LCe2 TR_LCe2 sR_LCe2 RR_LCe2 KEPT_LCe2 KEPT1_LCe2 XS_LCe2 eFRc HER_LCe2 Hchk_LCe2 OBJS_LCe2 HT0_LCe2 HXS_LCe2 OBJS1_LCe2 HT2_LCe2 HTR_LCe2 RCHK_LCe2 TRs_LCe2 Erq_LCe2 Erq2_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.TQ_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.Edr_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.Xf_L2Be run5d_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.run6_L2Be XW_LCe2 HTRs_LCe2 CCHK_LCe2 RUN5d_LCe2 L5d_LCe2 AXW_LCe2 ENTQ_LCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.NX6_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.RUN6_L2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL2Be.L6_L2Be
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lh.F0A_qL2Be.ef0_drain_L2Be CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ld.F0A_xiL2Be.ef0_exit_L2Be CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Ce_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S15S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S28R6R5A2S3eA2S1bS14S19RbA1S13A3S33S10RcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 2) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C false _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (g_instantiate false 2 UStopLe (NVC false) (VFC false) Wa_LCe2 Da_LCe2 Wb_LCe2 Wc_LCe2 Wd_LCe2 Fb_LCe2 XI_LCe2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_LCe2 (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn
           (hdf_LCe2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCe2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCe2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_LCe2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LCe2 ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_Ce_2 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S15S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S21S3R6A1S27S28R4R3A2S3eA2S1bS14S19R9A1S13A3S33S10RaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 2) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C false _ _ false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (g_instantiate false 2 UStopLe (NVC false) (VFC false) Wa_LCe2 Da_LCe2 Wb_LCe2 Wc_LCe2 Wd_LCe2 Fb_LCe2 XI_LCe2 A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_LCe2 (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn
           (hdfe_LCe2_1 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCe2_2 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCe2_3 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_LCe2_4 A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (etail_LCe2 A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2S1cS1dS1cS27S31R2A2S29R2S32A2A2A1S1dS1cS27Z17db48R2A2S29R2Z17db4cA2A2A1A2F_;Fa;").
Theorem free_lo_ia0_Ce_2 : ltac2:(tb__ "0|4|
S20OF_;S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S15S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S21S3R6A1S26SaR9S24R7A1A3S4dSaRaS24R8A1A3S27S28R6R5A2S3eA2S1bS14S19RbA1S10A3S33S10RcA2S27R8S3dA2S52RfRdA2S23SaR10S25SaS8G3G2S1RfReA5S9S4G2S1A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
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
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 2) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false 2 UStopLe (NVC false) (VFC false) Wbm_LCe2 Wcm_LCe2 Wdm_LCe2 Fb_LCe2 XIm_LCe2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (free_spine_m_LCe2 (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2
           (hdf_LCe2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCe2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCe2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp) (hdf_LCe2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LCe2 ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_Ce_2 : ltac2:(tb__ "0|4|
S17S2SbSfSeQ40M0A1A1SdG0ScR2PcA2A2S0SdG0ScR3PdA2A2S0S36SaS4eR4R3S15S12S2aS35A2M1S11S2aS35S6S4S7U2A1M2S1A3S5S30SaA1M3VCST;VXGL;R6R5A5A4S16G1A1A3A5S21S3R6A1S27S28R4R3A2S3eA2S1bS14S19R9A1S10A3S33S10RaA2S27R6S3dA2S53RbA1S22SaS25SaS8G3G2S1RdRcA5S9S4G2S1A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
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
  assert (QC1 : qcondCx false A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (IFF : instG_facts false (Wcan 2) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 false (Wcan 2) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin 2 A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w ltac:(lia) PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill CST XGL 2 A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false 2 UStopLe (NVC false) (VFC false) Wbm_LCe2 Wcm_LCe2 Wdm_LCe2 Fb_LCe2 XIm_LCe2 A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (agree_below_refl _ _) IFF Hw) as [_ Hw1].
  exact (efree_spine_m_LCe2 (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2
           (hdfe_LCe2_1 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCe2_2 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCe2_3 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _) (hdfe_LCe2_4 A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC1 _)
           (etail_LCe2 A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALCe2.
End F0A_aLCe2.

