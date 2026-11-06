(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia NArith PArith.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_top l3 m2.

(* [comment removed for export] *)
Module F0T_hxNT.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@Corelib.Init.Datatypes"; "list"; "prod"; "true"; "@Corelib.Init.Logic"; "False"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT"; "Erc_NT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln"; "HBIGNET_stmt"; "HBIGNT_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells Iface F0A_rebuild InvQ8 F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kx.F0T_hbNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.F0A_hbN_qsz OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_du OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.F0T_hbN_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lu.F0T_hbN_asm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
Import ListNotations.
Open Scope Z_scope.
Ltac vmc := match goal with |- _ = ?b => vm_cast_no_check (eq_refl b) end.
Lemma E_N0_eq : Erc_NT = E_NT. Proof. Time vmc. Qed.
Lemma CF_N0_1 : hbcertF 0 1 E_NT FAM_N0_1.
Proof.
  constructor.
  - rewrite <- E_N0_eq. exact FAM_N0_1_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N0_1L : hbcertV 0 1 true FAM_N0_1 VAR_N0_1L.
Proof.
  constructor.
  - exact VAR_N0_1L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N0_1M : hbcertV 0 1 false FAM_N0_1 VAR_N0_1M.
Proof.
  constructor.
  - exact VAR_N0_1M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CF_N0_2 : hbcertF 0 2 E_NT FAM_N0_2.
Proof.
  constructor.
  - rewrite <- E_N0_eq. exact FAM_N0_2_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N0_2L : hbcertV 0 2 true FAM_N0_2 VAR_N0_2L.
Proof.
  constructor.
  - exact VAR_N0_2L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N0_2M : hbcertV 0 2 false FAM_N0_2 VAR_N0_2M.
Proof.
  constructor.
  - exact VAR_N0_2M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma TAG_N0_ok : hbtag_ok 0 true E_NT.
Proof. intros f FA. cbn [fam_allowed] in FA. destruct FA as [FA|FA]; subst f; [exists FAM_N0_1; split; [exact CF_N0_1 | intros [|]; [exists VAR_N0_1L; exact CV_N0_1L | exists VAR_N0_1M; exact CV_N0_1M]] | exists FAM_N0_2; split; [exact CF_N0_2 | intros [|]; [exists VAR_N0_2L; exact CV_N0_2L | exists VAR_N0_2M; exact CV_N0_2M]]]. Qed.
Theorem HBIGN_NT : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1SbR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S13R6R5S6ScA4F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N0_eq. exact (hb_tag CST XGL H1 H2 H3 H4 true E_NT TAG_N0_ok). Qed.
Theorem HBIGNE_NT : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1SbR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S12R6R5S6ScA4F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N0_eq. exact (hb_tagE CST XGL H1 H2 H3 H4 true E_NT TAG_N0_ok). Qed.
End F0T_hxNT.

(* [comment removed for export] *)
Module F0T_aTCe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "andb"; "cons"; "nil"; "prod"; "pair"; "negb"; "orb"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "add"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "aa_live"; "topG"; "aa_Kf"; "aa_Km"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe"; "MT_TCe"; "m1_TCe"; "MX_TCe"; "MH0_TCe"; "m2_TCe"; "m3_TCe"; "m4_TCe"; "okbm_TCe"; "okbp_TCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCe"; "ED_TCe"; "PMID_TCe"; "TD_TCe"; "S1c_TCe"; "P0_TCe"; "LT_TCe"; "l1_TCe"; "EX_TCe"; "LH0_TCe"; "TM_TCe"; "l2_TCe"; "l3_TCe"; "l4_TCe"; "RD_TCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe.ATCe"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT";
"J_free_tol_preT"; "objs_le"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCe.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition RUN1p_TCe := RUN1_TCe. Definition RUN2p_TCe := RUN2f_TCe. Definition RUN3p_TCe := RUN3f_TCe. Definition RUN4p_TCe := RUN4f_TCe.
Definition okbp_TCe := l1okb_TCe. Definition chkp_TCe := chk_TCe. Definition H0eqp_TCe := LH0eq_TCe. Definition SIDEp_TCe := SIDE_TCe. Definition OBNDp_TCe := OBND_TCe.
Lemma splitp_TCe : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S5bScS14A1M1A3A1S1S2S0G0S5fG1A3A1S1S2S0G0S60G1A3A1S2S0G0S61G1A3A1A2A2A2S1S0S6S54S5bA1S7A3S1S0S6S9bS11S14S74S72S5bA2A2U1A2S7A3S1S0S6S69S14S14S10S45S17R1A1M2S5aA2S45G2S5cA2A2LL;S5fA3S7A3S1S0S6S20S15S99S5aS21S73A1M3A2A1A1S7A3S1S0S6S22S1dS15S5aA1M4A1M5G3A2S7A3S1S0S6S69S14S98S5aS5cS73A3S60A3S7A3S1S0S6S69S14S14S45G2S58A2LL;S61A3S7A3S1S1S79S19S1dS15S59A1M6A1A2S1S79S19S1dS15S5dA1M7A1A2S1S79S19G5A2S79S19S1dS15S5cA1M8A1A2A2A2A2S1S0S6S1cG6A1S9A3S1S0S6S1cG7A1S9A3S1S0S6S1cG4A1S9A3S0S6S1cG8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_TCe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_TCe : ltac2:(tb__ "0|1|
S14S6aS14R1S5bA3S3S0S16S17R2A1M0S5dA3S0S6S45G0S58A2S7A3A2F_;FL;").
Proof.
  destruct splitp_TCe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_TCe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_TCe. destruct (atpc LOOPH l1_TCe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_TCe : ltac2:(tb__ "0|0|
S0S6S20S94S35U0A1S30A2A1S7A3"). Proof. vmr. Qed.
Lemma Dai_TCe : ltac2:(tb__ "0|4|
S0S12SdS8SdS1eS1eA2M0A1M1S8S25A1M2A2M3A1Sa6S15S7dS33A1A1S94S35U0A1S30A2A2S13G3SeG1G2SbG0SeS1eS1eS21P18A1S23Sa9A1A4ScG0A1A3ScS25A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_TCe : ltac2:(tb__ "0|0|
S0S6S20S96S35U0A1S30A2A1S7A3"). Proof. vmr. Qed.
Lemma Wci_TCe : ltac2:(tb__ "0|0|
S0S6S20S97S35U0A1S30A2A1S7A3"). Proof. vmr. Qed.
Definition Certi_TCe__runs : ltac2:(tb__ "0|0|
S8S12S8S14A1A1A1") := ltac2:(tb__ "0|0|
Sa7S18Ubb8S91S93U0S30A2A4").
Lemma Certi_TCe : ltac2:(tb__ "0|1|
S0S6S9fS18Ubb8S91S19S93U0M0S30A2SbS16S92S35G0A1S30A2ScS16A1A3A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_TCe__runs); [unfold Certi_TCe__runs; reflexivity | vmr]. Qed.
Lemma ECerti_TCe : ltac2:(tb__ "0|2|
S0S6Sa0S18Ubb8S91S19S95U0M0S30A2SbS9eSa1S92S35G0A1S30A2Z0M1S23G1A1A3ScS9eA1A3A6S7A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_TCe__runs); [unfold Certi_TCe__runs; reflexivity | vmr]. Qed.
Definition m1_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_TCe.
Definition MH0_TCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_TCe) DUMMY).
Definition m2_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_TCe.
Definition MH1_TCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_TCe) DUMMY).
Definition MT_TCe : axst := Eval vm_compute in LT_ofg MH1_TCe F0_TCe.
Definition MX_TCe : axst := Eval vm_compute in EX_ofg MH1_TCe F0_TCe.
Definition m3_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_TCe (SVar pFR)).
Definition m4_TCe : list leafA := Eval vm_compute in runA FUELF [CASX] MX_TCe.
Lemma RUN1m_TCe : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SbS5S72SbS5S47ScS5A1A3A3S56A3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN2m_TCe : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SbS5S72SbS5S75ScS5A1A3A3S4fA3S50A3"). Proof. Time vmr. Qed.
Lemma RUN3m_TCe : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SbS5S72SbS5S75ScS5A1A3A3S9aS4cS21S73A1A2A3S51A3"). Proof. Time vmr. Qed.
Lemma RUN4m_TCe : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SbS5S47ScS5A1A3S4eA3S52A3"). Proof. Time vmr. Qed.
Definition okbm_TCe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S14S14S10S2cS27S15S17R1A1M0A1A1S72A2S45G0S58A2A2LL;Vl;A3").
Lemma chkm_TCe : ltac2:(tb__ "0|a|
S0S6SaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSaSfS8S14A1M0S6Lx;M1S4dS7S14G0S9Ll0;Ll;M2X8x2A1SfG1S50S7G2X8x2A1A2SfG1S51S7G2X8x2A1A2SfG1S52S7G2X8x2A1A2S53S4dA1A2S9bS11S14S74S72S4dA2A2U1A2A2S69S14S14S10S45S17R1A1M3S4cA2S45G3S4eA2A2LL;S50A3A2S20S15S99S4cS21S73A1M4A2A1A1A2S22S1dS15S4cA1M5A1M6G4A2A2S69S14S98S4cS4eS73A3S51A3A2S69S14S14S45G3S58A2LL;S52A3A2S7aS19S1dS15S56A1M7A1A2A2S7aS19S1dS15S4fA1M8A1A2A2S7aS19G6A2A2S7aS19S1dS15S4eA1M9A1A2A2SfS1cG7A1A1A2SfS1cG8A1A1A2SfS1cG5A1A1A2SfS1cG9A1A1A2S7A3").
Proof. Time vmr. Qed.
Lemma H0eqm_TCe : ltac2:(tb__ "0|0|
S0S16S17S9dS14U0S74S72S4dA2S89A4A1S4fA3"). Proof. vmr. Qed.
Lemma SIDEm_TCe : ltac2:(tb__ "0|0|
S0S6S8eS56S4cA2S7A3"). Proof. Time vmr. Qed.
Lemma OBNDm_TCe : ltac2:(tb__ "0|1|
S0S8SdSdS1eS1eA2S1eA2M0A1S9cS24G0S8dS1fS15S4cA1A1A4S9cS24G0S8dS1fS15S56A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_TCe : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S4dScS14A1M1A3A1S1S2S0G0S50G1A3A1S1S2S0G0S51G1A3A1S2S0G0S52G1A3A1A2A2A2S1S0S6S53S4dA1S7A3S1S0S6S9bS11S14S74S72S4dA2A2U1A2S7A3S1S0S6S69S14S14S10S45S17R1A1M2S4cA2S45G2S4eA2A2LL;S50A3S7A3S1S0S6S20S15S99S4cS21S73A1M3A2A1A1S7A3S1S0S6S22S1dS15S4cA1M4A1M5G3A2S7A3S1S0S6S69S14S98S4cS4eS73A3S51A3S7A3S1S0S6S69S14S14S45G2S58A2LL;S52A3S7A3S1S1S79S19S1dS15S56A1M6A1A2S1S79S19S1dS15S4fA1M7A1A2S1S79S19G5A2S79S19S1dS15S4eA1M8A1A2A2A2A2S1S0S6S1cG6A1S9A3S1S0S6S1cG7A1S9A3S1S0S6S1cG4A1S9A3S0S6S1cG8A1S9A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_TCe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_TCe : ltac2:(tb__ "0|1|
S14S6aS14R1S4dA3S3S0S16S17R2A1M0S4fA3S0S6S45G0S58A2S7A3A2F_;FL;").
Proof.
  destruct splitm_TCe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_TCe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_TCe. destruct (atpc LOOPH m1_TCe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ATCe.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S36S1aS8S2eQ40A1A1S71VA;R3A2Sa5Vkeep;Vrho1;R3A3S1aS4bVsegs;Vok;S3fVsegs;S70U0S30S9R6VKc;R5A6S5eR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma spine_tail_TCe : ltac2:(tb__ "0|2|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S6eU0M1S30RcRbRaR9R7S55S57R5AaS86RdRcRbRaR8R6A6S1aS4bVsegs;ReS3fVsegs;S70G1S30S7RdRcRaA6S58R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_TCe rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_TCe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_TCe Q BGF_TCe HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_TCe C3_TCe Ems_TCe C4_TCe TM0_TCe run4_TCe RM_TCe D3_TCe W3_TCe EQ3_TCe NX3b_TCe RUN4_TCe L4_TCe D4_TCe W4_TCe EQ4_TCe
             HeM_TCe HchkM_TCe HTM_TCe FBM_TCe ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_TCe. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (f0_s2 0 UStopLe true S1c_TCe C2_TCe EfD_TCe ED_TCe run2_TCe D2_TCe W2_TCe NX2_TCe EQ2_TCe RUN2_TCe L2_TCe AXD_TCe
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0 UStopLe false TD_TCe TDr_TCe CD_TCe Eps_TCe Ebg_TCe run3_TCe AXDr_TCe ENTD_TCe RUN3_TCe L3_TCe NX3_TCe
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_TCe : ltac2:(tb__ "0|4|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S8cR7S2dG0S1bR7PaA2A2S1fS15S59A1A1A3S0G1S1bR8P99A2S2fG0S38S37RbA1A1A2A3S1S28Z1S38S37RcA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6eU0S30RfReRdRcRaS55S57R8AaS86R10RfReRdRbR9A6S1aS4bVsegs;R11S3fVsegs;S8aR10RfRdA3S59R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_TCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TCe LH0_TCe LT_TCe EX_TCe S1c_TCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TCe l2_TCe l3_TCe l4_TCe HNX HLEN
           (runT_some _ _ _ _ RUN1p_TCe NE1) L1okp_TCe (runT_some _ _ _ _ RUN2p_TCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_TCe NE3) H3 (runT_some _ _ _ _ RUN4p_TCe NE4) H4
           (hside_of A Kc rho1 P0_TCe LT_TCe tp SIDEp_TCe OBNDp_TCe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_TCe keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Theorem free_spine_m_TCe : ltac2:(tb__ "0|4|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S8cR7S2dG0S1bR7PaA2A2S1fS15S56A1A1A3S0G1S1bR8P99A2S2fG0S38S37RbA1A1A2A3S1S28Z1S38S37RcA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6eU0S30RfReRdRcRaS55S57R8AaS86R10RfReRdRbR9A6S1aS4bVsegs;R11S3fVsegs;S8aR10RfRdA3S56R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_TCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_TCe MH0_TCe MT_TCe MX_TCe S1c_TCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_TCe m2_TCe m3_TCe m4_TCe HNX HLEN
           (runT_some _ _ _ _ RUN1m_TCe NE1) L1okm_TCe (runT_some _ _ _ _ RUN2m_TCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_TCe NE3) H3 (runT_some _ _ _ _ RUN4m_TCe NE4) H4
           (hside_of A Kc rho1 PMID_TCe MT_TCe tp SIDEm_TCe OBNDm_TCe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_TCe keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S36S1aS8S2eQ40A1A1S71VA;R3A2Sa5Vkeep;Vrho1;R3A3S1aS4aVsegs;S3fVsegs;S70U0S30S9R6VKc;R5A6S5eR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma espine_tail_TCe : ltac2:(tb__ "0|2|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S6fU0M1S30RaR9R8R6S55S57R4A9S87RbRaR9R7R5A5S1aS4aVsegs;S3fVsegs;S70G1S30S7RcRbR9A6S58R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_TCe rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_TCe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_TCe Q BGF_TCe HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_TCe C3_TCe Ems_TCe C4_TCe TM0_TCe run4_TCe RM_TCe D3_TCe W3_TCe EQ3_TCe NX3b_TCe RUN4_TCe L4_TCe D4_TCe W4_TCe EQ4_TCe
             HeM_TCe HchkM_TCe HTM_TCe FBM_TCe A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_TCe. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (ef0_s2 0 UStopLe true S1c_TCe C2_TCe EfD_TCe ED_TCe run2_TCe D2_TCe W2_TCe NX2_TCe EQ2_TCe RUN2_TCe L2_TCe AXD_TCe
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0 UStopLe false TD_TCe TDr_TCe CD_TCe Eps_TCe Ebg_TCe run3_TCe AXDr_TCe ENTD_TCe RUN3_TCe L3_TCe NX3_TCe
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_TCe : ltac2:(tb__ "0|4|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S8cR6S2dG0S1bR6PaA2A2S1fS15S59A1A1A3S0G1S1bR7P99A2S2fG0S38S37RaA1A1A2A3S1S28Z1S38S37RbA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6fU0S30RdRcRbR9S55S57R7A9S87ReRdRcRaR8A5S1aS4aVsegs;S3fVsegs;S8aRfReRcA3S59R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_TCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TCe LH0_TCe LT_TCe EX_TCe S1c_TCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TCe l2_TCe l3_TCe l4_TCe HNX HLEN
           (runT_some _ _ _ _ RUN1p_TCe NE1) L1okp_TCe (runT_some _ _ _ _ RUN2p_TCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_TCe NE3) H3 (runT_some _ _ _ _ RUN4p_TCe NE4) H4
           (hside_of A Kc rho1 P0_TCe LT_TCe tp SIDEp_TCe OBNDp_TCe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_TCe keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.
Theorem efree_spine_m_TCe : ltac2:(tb__ "0|4|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S8cR6S2dG0S1bR6PaA2A2S1fS15S56A1A1A3S0G1S1bR7P99A2S2fG0S38S37RaA1A1A2A3S1S28Z1S38S37RbA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6fU0S30RdRcRbR9S55S57R7A9S87ReRdRcRaR8A5S1aS4aVsegs;S3fVsegs;S8aRfReRcA3S56R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_TCe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_TCe MH0_TCe MT_TCe MX_TCe S1c_TCe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_TCe m2_TCe m3_TCe m4_TCe HNX HLEN
           (runT_some _ _ _ _ RUN1m_TCe NE1) L1okm_TCe (runT_some _ _ _ _ RUN2m_TCe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_TCe NE3) H3 (runT_some _ _ _ _ RUN4m_TCe NE4) H4
           (hside_of A Kc rho1 PMID_TCe MT_TCe tp SIDEm_TCe OBNDm_TCe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_TCe keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S3S7fSaaR2A2S1S28S67R2A2S2aR2S68A2A2A2S4F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S2SacR2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S2SabR2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S1S2S1S28S67R2A2S2aR2S68A2A2A1S2S1S28Z17db48R2A2S2aR2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.
Lemma HTD_TCe : ltac2:(tb__ "0|0|
S0S16S57Sa8S44S78S55A1S77S76S55S62A5S26S15S55A1A1A2A3").
Proof. unfold TD_TCe, TDv_of, RD_TCe; reflexivity. Qed.
Theorem hdf_TCe : ltac2:(tb__ "0|1|
S36S31S1aS8S2eQ40M0A1A1S80S5S5S5S84S32R8A1S28S2bS3dRaA1S3cRaA1A2Sa2A2S66S18RbR9R8R7A5S6aSdS5S5A2SeS5S5R7R6A4S3aRcA1A3S83R8R7A2S0S5S2dG0S1bRcPcA2A2R9A3Sa3RfRdRaR9R8R7A6S6bS9R10A2S48OF_;S49S41S18R2S40R12A1A3S81S18R3S40R13A1A3S6eU0S30S82VCST;VXGL;R15A3R4R15R14S6cR15R13R10RfReRdA6S55S57R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG (NVC false) 0) HSEG CST XGL HCST HXGL HCSTD ED_TCe TD_TCe (sDv_of ED_TCe) RD_TCe HeD_TCe HchkD_TCe HTD_TCe DCHK_TCe
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_TCe : ltac2:(tb__ "0|1|
S36S31S1aS8S2eQ40M0A1A1S80S5S5S5S84S32R8A1S28S2bS3dRaA1S3cRaA1A2Sa2A2S66S18RbR9R8R7A5S6aSdS5S5A2SeS5S5R7R6A4S3aRcA1A3S83R8R7A2S0S5S2dG0S1bRcPcA2A2R9A3Sa3RfRdRaR9R8R7A6S6bS9R10A2S48OF_;S6fU0S30S82VCST;VXGL;R12A3R12R11S6cR12R10RdRcRbRaA6S55S57R1A9FQ;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFET 0 (rd_okG (NVC false) 0) HSEGE CST XGL HCST HXGL HCSTD ED_TCe TD_TCe (sDv_of ED_TCe) RD_TCe HeD_TCe HchkD_TCe HTD_TCe DCHK_TCe
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV false QC 0) Q).
Qed.
Lemma tail_TCe : ltac2:(tb__ "0|3|
S48OF_;S36S31S1aS8S2eQ40M0A1A1M1S5S5S5S84G1S80S32R9A1S41S18RcS40RaA1A3S81S18RdS40RbA1A3S8fReRcA2S66S18ReRcR6R5A5S3eRfA1S0S5S2dG0S1bRePcA2A2RcA3S0S5S2dG0S1bRfPdA2A2RcA3S6aSdS5S5A2SeS5S5ReRdA4S3aR12A1A3S83RfReA2S0S6S39R14A1S7A3S6bS9R15A2S6dR14S6cR16R14R12R11R10RfA6A2S0S5S85R10A1S65A3S86S82VCST;VXGL;R18A3R19R18R17S6cR18R16R14R13R12R11A6S43S18S7bR16R15SbSdS16S42A2M2SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;Sa4R18Z18A2R17A5A4ScG2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 false CST XGL HCST HXGL TM_TCe Erf_TCe EC_TCe run5_TCe XR_TCe NX5_TCe RUN5_TCe L5_TCe AXR_TCe T0_TCe T1_TCe T2_TCe TR_TCe sR_TCe RR_TCe KEPT_TCe KEPT1_TCe XS_TCe eFRc HER_TCe Hchk_TCe OBJS_TCe HT0_TCe HXS_TCe OBJS1_TCe HT2_TCe HTR_TCe RCHK_TCe TRs_TCe Erq_TCe Erq2_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.TQ_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.Edr_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.Xf_TBe run5d_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.run6_TBe XW_TCe HTRs_TCe CCHK_TCe RUN5d_TCe L5d_TCe AXW_TCe ENTQ_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.NX6_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.RUN6_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.L6_TBe
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBe.f0_drain_TBe CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBe.f0_exit_TBe CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_TCe : ltac2:(tb__ "0|3|
S36S31S1aS8S2eQ40M0A1A1M1S5S5S5S84G1S80S32R9A1S90RaA1S66S18RcRaR4R3A5S3eRdA1S0S5S2dG0S1bRcPcA2A2RaA3S0S5S2dG0S1bRdPdA2A2RaA3S6aSdS5S5A2SeS5S5RcRbA4S3aR10A1A3S83RdRcA2S0S6S39R12A1S7A3S6bS9R13A2S6dR12S6cR14R12R10RfReRdA6A2S0S5S85ReA1S65A3S87S82VCST;VXGL;R16A3R16R15S6cR16R14R12R11R10RfA6S43S18S7bR14R13SbSdS16S42A2M2SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;Sa4R16Z18A2R15A5A4ScG2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure false A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 false CST XGL HCST HXGL TM_TCe Erf_TCe EC_TCe run5_TCe XR_TCe NX5_TCe RUN5_TCe L5_TCe AXR_TCe T0_TCe T1_TCe T2_TCe TR_TCe sR_TCe RR_TCe KEPT_TCe KEPT1_TCe XS_TCe eFRc HER_TCe Hchk_TCe OBJS_TCe HT0_TCe HXS_TCe OBJS1_TCe HT2_TCe HTR_TCe RCHK_TCe TRs_TCe Erq_TCe Erq2_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.TQ_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.Edr_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.Xf_TBe run5d_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.run6_TBe XW_TCe HTRs_TCe CCHK_TCe RUN5d_TCe L5d_TCe AXW_TCe ENTQ_TCe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.NX6_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.RUN6_TBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.L6_TBe
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBe.ef0_drain_TBe CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBe.ef0_exit_TBe CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Ce_T : ltac2:(tb__ "0|2|
S48OF_;S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SbSdS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S49S32R6A1S41S18R9S40R7A1A3S81S18RaS40R8A1A3S28S64S29R6Z10A2A2S0S6S39RbA1S7A3S6bS9RcA2S28R8S63A2S8fRfRdA2S4bS18R10S3fS18S8bRfReA2S7dS33A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C_T true false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (t_instantiate true (NVC false) (VFC false) Wa_TCe Da_TCe Wb_TCe Wc_TCe Wd_TCe Fb_TCe XI_TCe A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_TCe (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn HO eq_refl HST
           (hdf_TCe A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_TCe ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_hi_ia0_Ce_T : ltac2:(tb__ "0|2|
S48OF_;S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SbSdS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S49S32R6A1S41S18R9S40R7A1A3S81S18RaS40R8A1A3S28S64S29R6Z10A2A2S0S6S39RbA1S9A3S6bS9RcA2S28R8S63A2S8fRfRdA2S4bS18R10S3fS18S8bRfReA2S7dS33A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_TCe Dai_TCe Wbi_TCe Wci_TCe Certi_TCe ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true (NVC false) (VFC false) Wbm_TCe Wcm_TCe Wdm_TCe Fb_TCe XIm_TCe A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (free_spine_m_TCe (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2 HO eq_refl HST
           (hdf_TCe A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_TCe ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_Ce_T : ltac2:(tb__ "0|2|
S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SbSdS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S49S32R6A1S28S64S29R4Z10A2A2S0S6S39R9A1S7A3S6bS9RaA2S28R6S63A2S90RbA1S4aS18S3fS18S8bRdRcA2S7dS33A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 0) UStopLe false A rho)); [intros w Hw; exact (entry_pure_C_T true false A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (t_instantiate true (NVC false) (VFC false) Wa_TCe Da_TCe Wb_TCe Wc_TCe Wd_TCe Fb_TCe XI_TCe A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_TCe (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn HO eq_refl HST
           (hdfe_TCe A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (etail_TCe A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_hi_ia0_Ce_T : ltac2:(tb__ "0|2|
S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SbSdS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4ScG1A1A3A5S49S32R6A1S28S64S29R4Z10A2A2S0S6S39R9A1S9A3S6bS9RaA2S28R6S63A2S90RbA1S4aS18S3fS18S8bRdRcA2S7dS33A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_TCe Dai_TCe Wbi_TCe Wci_TCe ECerti_TCe A Kc rho tp Q p n t jv Hii HKc).
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
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC false) (VFC false) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true (NVC false) (VFC false) Wbm_TCe Wcm_TCe Wdm_TCe Fb_TCe XIm_TCe A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (efree_spine_m_TCe (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2 HO eq_refl HST
           (hdfe_TCe A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 _)
           (etail_TCe A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ATCe.
End F0T_aTCe.

(* [comment removed for export] *)
Module F0T_aLTCf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "andb"; "cons"; "nil"; "prod"; "false"; "pair"; "negb"; "orb"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "aa_live"; "topG"; "aa_Kf"; "aa_Km"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf"; "MT_LTCf"; "m1_LTCf"; "MX_LTCf"; "MH0_LTCf"; "m2_LTCf"; "m3_LTCf"; "m4_LTCf"; "okbm_LTCf"; "okbp_LTCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cLTCf"; "ED_LTCf"; "PMID_LTCf"; "TD_LTCf"; "S1c_LTCf"; "P0_LTCf"; "LT_LTCf"; "l1_LTCf"; "EX_LTCf"; "LH0_LTCf"; "TM_LTCf"; "l2_LTCf"; "l3_LTCf"; "l4_LTCf"; "RD_LTCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf.ALTCf"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY";
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cLTCf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition RUN1p_LTCf := RUN1_LTCf. Definition RUN2p_LTCf := RUN2f_LTCf. Definition RUN3p_LTCf := RUN3f_LTCf. Definition RUN4p_LTCf := RUN4f_LTCf.
Definition okbp_LTCf := l1okb_LTCf. Definition chkp_LTCf := chk_LTCf. Definition H0eqp_LTCf := LH0eq_LTCf. Definition SIDEp_LTCf := SIDE_LTCf. Definition OBNDp_LTCf := OBND_LTCf.
Lemma splitp_LTCf : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S5aSbS14A1M1A3A1S1S2S0G0S5eG1A3A1S1S2S0G0S5fG1A3A1S2S0G0S60G1A3A1A2A2A2S1S0S7S53S5aA1S6A3S1S0S7S9aS11S14S73S71S5aA2A2U1A2S6A3S1S0S7S68S14S14S10S44S17R1A1M2S59A2S44G2S5bA2A2LL;S5eA3S6A3S1S0S7S20S15S98S59S21S72A1M3A2A1A1S6A3S1S0S7S22S1dS15S59A1M4A1M5G3A2S6A3S1S0S7S68S14S97S59S5bS72A3S5fA3S6A3S1S0S7S68S14S14S44G2S57A2LL;S60A3S6A3S1S1S78S19S1dS15S58A1M6A1A2S1S78S19S1dS15S5cA1M7A1A2S1S78S19G5A2S78S19S1dS15S5bA1M8A1A2A2A2A2S1S0S7S1cG6A1SdA3S1S0S7S1cG7A1SdA3S1S0S7S1cG4A1SdA3S0S7S1cG8A1SdA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_LTCf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_LTCf : ltac2:(tb__ "0|1|
S14S69S14R1S5aA3S3S0S16S17R2A1M0S5cA3S0S7S44G0S57A2S6A3A2F_;FL;").
Proof.
  destruct splitp_LTCf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LTCf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_LTCf. destruct (atpc LOOPH l1_LTCf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_LTCf : ltac2:(tb__ "0|0|
S0S7S20S93S34U0A1S2fA2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_LTCf : ltac2:(tb__ "0|4|
S0S12ScS8ScS1eS1eA2M0A1M1S8S25A1M2A2M3A1Sa5S15S7cS32A1A1S93S34U0A1S2fA2A2S13G3SeG1G2SaG0SeS1eS1eS21P18A1S23Sa8A1A4SbG0A1A3SbS25A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_LTCf : ltac2:(tb__ "0|0|
S0S7S20S95S34U0A1S2fA2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_LTCf : ltac2:(tb__ "0|0|
S0S7S20S96S34U0A1S2fA2A1S6A3"). Proof. vmr. Qed.
Definition Certi_LTCf__runs : ltac2:(tb__ "0|0|
S8S12S8S14A1A1A1") := ltac2:(tb__ "0|0|
Sa6S18Ubb8S90S92U0S2fA2A4").
Lemma Certi_LTCf : ltac2:(tb__ "0|1|
S0S7S9eS18Ubb8S90S19S92U0M0S2fA2SaS16S91S34G0A1S2fA2SbS16A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_LTCf__runs); [unfold Certi_LTCf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_LTCf : ltac2:(tb__ "0|2|
S0S7S9fS18Ubb8S90S19S94U0M0S2fA2SaS9dSa0S91S34G0A1S2fA2Z0M1S23G1A1A3SbS9dA1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_LTCf__runs); [unfold Certi_LTCf__runs; reflexivity | vmr]. Qed.
Definition m1_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_LTCf.
Definition MH0_LTCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_LTCf) DUMMY).
Definition m2_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_LTCf.
Definition MH1_LTCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_LTCf) DUMMY).
Definition MT_LTCf : axst := Eval vm_compute in LT_ofg MH1_LTCf F0_LTCf.
Definition MX_LTCf : axst := Eval vm_compute in EX_ofg MH1_LTCf F0_LTCf.
Definition m3_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_LTCf (SVar pFR)).
Definition m4_LTCf : list leafA := Eval vm_compute in runA FUELF [CASX] MX_LTCf.
Lemma RUN1m_LTCf : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SaS5S71SaS5S46SbS5A1A3A3S55A3S4cA3"). Proof. Time vmr. Qed.
Lemma RUN2m_LTCf : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SaS5S71SaS5S74SbS5A1A3A3S4eA3S4fA3"). Proof. Time vmr. Qed.
Lemma RUN3m_LTCf : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SaS5S71SaS5S74SbS5A1A3A3S99S4bS21S72A1A2A3S50A3"). Proof. Time vmr. Qed.
Lemma RUN4m_LTCf : ltac2:(tb__ "0|0|
S0S8S14A1S87S45SaS5S46SbS5A1A3S4dA3S51A3"). Proof. Time vmr. Qed.
Definition okbm_LTCf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S68S14S14S10S2bS27S15S17R1A1M0A1A1S71A2S44G0S57A2A2LL;Vl;A3").
Lemma chkm_LTCf : ltac2:(tb__ "0|a|
S0S7S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9SfS8S14A1M0S7Lx;M1S4cS6S14G0SdLl0;Ll;M2X8x2A1SfG1S4fS6G2X8x2A1A2SfG1S50S6G2X8x2A1A2SfG1S51S6G2X8x2A1A2S52S4cA1A2S9aS11S14S73S71S4cA2A2U1A2A2S68S14S14S10S44S17R1A1M3S4bA2S44G3S4dA2A2LL;S4fA3A2S20S15S98S4bS21S72A1M4A2A1A1A2S22S1dS15S4bA1M5A1M6G4A2A2S68S14S97S4bS4dS72A3S50A3A2S68S14S14S44G3S57A2LL;S51A3A2S79S19S1dS15S55A1M7A1A2A2S79S19S1dS15S4eA1M8A1A2A2S79S19G6A2A2S79S19S1dS15S4dA1M9A1A2A2SfS1cG7A1A1A2SfS1cG8A1A1A2SfS1cG5A1A1A2SfS1cG9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma H0eqm_LTCf : ltac2:(tb__ "0|0|
S0S16S17S9cS14U0S73S71S4cA2S88A4A1S4eA3"). Proof. vmr. Qed.
Lemma SIDEm_LTCf : ltac2:(tb__ "0|0|
S0S7S8dS55S4bA2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_LTCf : ltac2:(tb__ "0|1|
S0S8ScScS1eS1eA2S1eA2M0A1S9bS24G0S8cS1fS15S4bA1A1A4S9bS24G0S8cS1fS15S55A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_LTCf : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S4cSbS14A1M1A3A1S1S2S0G0S4fG1A3A1S1S2S0G0S50G1A3A1S2S0G0S51G1A3A1A2A2A2S1S0S7S52S4cA1S6A3S1S0S7S9aS11S14S73S71S4cA2A2U1A2S6A3S1S0S7S68S14S14S10S44S17R1A1M2S4bA2S44G2S4dA2A2LL;S4fA3S6A3S1S0S7S20S15S98S4bS21S72A1M3A2A1A1S6A3S1S0S7S22S1dS15S4bA1M4A1M5G3A2S6A3S1S0S7S68S14S97S4bS4dS72A3S50A3S6A3S1S0S7S68S14S14S44G2S57A2LL;S51A3S6A3S1S1S78S19S1dS15S55A1M6A1A2S1S78S19S1dS15S4eA1M7A1A2S1S78S19G5A2S78S19S1dS15S4dA1M8A1A2A2A2A2S1S0S7S1cG6A1SdA3S1S0S7S1cG7A1SdA3S1S0S7S1cG4A1SdA3S0S7S1cG8A1SdA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_LTCf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_LTCf : ltac2:(tb__ "0|1|
S14S69S14R1S4cA3S3S0S16S17R2A1M0S4eA3S0S7S44G0S57A2S6A3A2F_;FL;").
Proof.
  destruct splitm_LTCf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_LTCf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_LTCf. destruct (atpc LOOPH m1_LTCf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ALTCf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S35S1aS8S2dQ40A1A1S70VA;R3A2Sa4Vkeep;Vrho1;R3A3S1aS4aVsegs;Vok;S3eVsegs;S6fU0S2fSdR6VKc;R5A6S5dR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma spine_tail_LTCf : ltac2:(tb__ "0|2|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S6dU0M1S2fRcRbRaR9R7S54S56R5AaS85RdRcRbRaR8R6A6S1aS4aVsegs;ReS3eVsegs;S6fG1S2fS6RdRcRaA6S57R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LTCf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LTCf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_LTCf Q BGF_LTCf HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_LTCf C3_LTCf Ems_LTCf C4_LTCf TM0_LTCf run4_LTCf RM_LTCf D3_LTCf W3_LTCf EQ3_LTCf NX3b_LTCf RUN4_LTCf L4_LTCf D4_LTCf W4_LTCf EQ4_LTCf
             HeM_LTCf HchkM_LTCf HTM_LTCf FBM_LTCf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LTCf. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (f0_s2 0 UStopLe true S1c_LTCf C2_LTCf EfD_LTCf ED_LTCf run2_LTCf D2_LTCf W2_LTCf NX2_LTCf EQ2_LTCf RUN2_LTCf L2_LTCf AXD_LTCf
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0 UStopLe false TD_LTCf TDr_LTCf CD_LTCf Eps_LTCf Ebg_LTCf run3_LTCf AXDr_LTCf ENTD_LTCf RUN3_LTCf L3_LTCf NX3_LTCf
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_LTCf : ltac2:(tb__ "0|4|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S8bR7S2cG0S1bR7PaA2A2S1fS15S58A1A1A3S0G1S1bR8P99A2S2eG0S37S36RbA1A1A2A3S1S28Z1S37S36RcA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6dU0S2fRfReRdRcRaS54S56R8AaS85R10RfReRdRbR9A6S1aS4aVsegs;R11S3eVsegs;S89R10RfRdA3S58R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_LTCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTCf LH0_LTCf LT_LTCf EX_LTCf S1c_LTCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTCf l2_LTCf l3_LTCf l4_LTCf HNX HLEN
           (runT_some _ _ _ _ RUN1p_LTCf NE1) L1okp_LTCf (runT_some _ _ _ _ RUN2p_LTCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LTCf NE3) H3 (runT_some _ _ _ _ RUN4p_LTCf NE4) H4
           (hside_of A Kc rho1 P0_LTCf LT_LTCf tp SIDEp_LTCf OBNDp_LTCf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LTCf keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Theorem free_spine_m_LTCf : ltac2:(tb__ "0|4|
S5OF_;S47OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S48S31R5A1S40Vsegs;R8S3fR6A1A3S6cR6R5A2S28S2cG0S1bR7PdA2A2S62A2S8bR7S2cG0S1bR7PaA2A2S1fS15S55A1A1A3S0G1S1bR8P99A2S2eG0S37S36RbA1A1A2A3S1S28Z1S37S36RcA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6dU0S2fRfReRdRcRaS54S56R8AaS85R10RfReRdRbR9A6S1aS4aVsegs;R11S3eVsegs;S89R10RfRdA3S55R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_LTCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTCf MH0_LTCf MT_LTCf MX_LTCf S1c_LTCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTCf m2_LTCf m3_LTCf m4_LTCf HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTCf NE1) L1okm_LTCf (runT_some _ _ _ _ RUN2m_LTCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTCf NE3) H3 (runT_some _ _ _ _ RUN4m_LTCf NE4) H4
           (hside_of A Kc rho1 PMID_LTCf MT_LTCf tp SIDEm_LTCf OBNDm_LTCf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_LTCf keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S35S1aS8S2dQ40A1A1S70VA;R3A2Sa4Vkeep;Vrho1;R3A3S1aS49Vsegs;S3eVsegs;S6fU0S2fSdR6VKc;R5A6S5dR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma espine_tail_LTCf : ltac2:(tb__ "0|2|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S6eU0M1S2fRaR9R8R6S54S56R4A9S86RbRaR9R7R5A5S1aS49Vsegs;S3eVsegs;S6fG1S2fS6RcRbR9A6S57R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_LTCf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_LTCf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_LTCf Q BGF_LTCf HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_LTCf C3_LTCf Ems_LTCf C4_LTCf TM0_LTCf run4_LTCf RM_LTCf D3_LTCf W3_LTCf EQ3_LTCf NX3b_LTCf RUN4_LTCf L4_LTCf D4_LTCf W4_LTCf EQ4_LTCf
             HeM_LTCf HchkM_LTCf HTM_LTCf FBM_LTCf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LTCf. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (ef0_s2 0 UStopLe true S1c_LTCf C2_LTCf EfD_LTCf ED_LTCf run2_LTCf D2_LTCf W2_LTCf NX2_LTCf EQ2_LTCf RUN2_LTCf L2_LTCf AXD_LTCf
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0 UStopLe false TD_LTCf TDr_LTCf CD_LTCf Eps_LTCf Ebg_LTCf run3_LTCf AXDr_LTCf ENTD_LTCf RUN3_LTCf L3_LTCf NX3_LTCf
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_LTCf : ltac2:(tb__ "0|4|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S8bR6S2cG0S1bR6PaA2A2S1fS15S58A1A1A3S0G1S1bR7P99A2S2eG0S37S36RaA1A1A2A3S1S28Z1S37S36RbA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6eU0S2fRdRcRbR9S54S56R7A9S86ReRdRcRaR8A5S1aS49Vsegs;S3eVsegs;S89RfReRcA3S58R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_LTCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTCf LH0_LTCf LT_LTCf EX_LTCf S1c_LTCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTCf l2_LTCf l3_LTCf l4_LTCf HNX HLEN
           (runT_some _ _ _ _ RUN1p_LTCf NE1) L1okp_LTCf (runT_some _ _ _ _ RUN2p_LTCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_LTCf NE3) H3 (runT_some _ _ _ _ RUN4p_LTCf NE4) H4
           (hside_of A Kc rho1 P0_LTCf LT_LTCf tp SIDEp_LTCf OBNDp_LTCf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LTCf keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.
Theorem efree_spine_m_LTCf : ltac2:(tb__ "0|4|
S5OF_;S35S30S1aS1aS8S2dQ40M0A1M1A1S47OF_;S31R5A1S6cR5R4A2S28S2cG0S1bR6PdA2A2S62A2S8bR6S2cG0S1bR6PaA2A2S1fS15S55A1A1A3S0G1S1bR7P99A2S2eG0S37S36RaA1A1A2A3S1S28Z1S37S36RbA1M2A1M3A2S28G3S7dS3aG2A1A1A2A2S6eU0S2fRdRcRbR9S54S56R7A9S86ReRdRcRaR8A5S1aS49Vsegs;S3eVsegs;S89RfReRcA3S55R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_LTCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTCf MH0_LTCf MT_LTCf MX_LTCf S1c_LTCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTCf m2_LTCf m3_LTCf m4_LTCf HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTCf NE1) L1okm_LTCf (runT_some _ _ _ _ RUN2m_LTCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTCf NE3) H3 (runT_some _ _ _ _ RUN4m_LTCf NE4) H4
           (hside_of A Kc rho1 PMID_LTCf MT_LTCf tp SIDEm_LTCf OBNDm_LTCf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_LTCf keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
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
Lemma HTD_LTCf : ltac2:(tb__ "0|0|
S0S16S56Sa7S43S77S54A1S76S75S54S61A5S26S15S54A1A1A2A3").
Proof. unfold TD_LTCf, TDv_of, RD_LTCf; reflexivity. Qed.
Theorem hdf_LTCf : ltac2:(tb__ "0|1|
S35S30S1aS8S2dQ40M0A1A1S7fS5S5S5S83S31R8A1S28S29S3cRaA1S3bRaA1A2Sa1A2S65S18RbR9R8R7A5S69ScS5S5A2SeS5S5R7R6A4S39RcA1A3S82R8R7A2S0S5S2cG0S1bRcPcA2A2R9A3Sa2RfRdRaR9R8R7A6S6aS6R10A2S47OF_;S48S40S18R2S3fR12A1A3S80S18R3S3fR13A1A3S6dU0S2fS81VCST;VXGL;R15A3R4R15R14S6bR15R13R10RfReRdA6S54S56R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG (NVC true) 0) HSEG CST XGL HCST HXGL HCSTD ED_LTCf TD_LTCf (sDv_of ED_LTCf) RD_LTCf HeD_LTCf HchkD_LTCf HTD_LTCf DCHK_LTCf
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_LTCf : ltac2:(tb__ "0|1|
S35S30S1aS8S2dQ40M0A1A1S7fS5S5S5S83S31R8A1S28S29S3cRaA1S3bRaA1A2Sa1A2S65S18RbR9R8R7A5S69ScS5S5A2SeS5S5R7R6A4S39RcA1A3S82R8R7A2S0S5S2cG0S1bRcPcA2A2R9A3Sa2RfRdRaR9R8R7A6S6aS6R10A2S47OF_;S6eU0S2fS81VCST;VXGL;R12A3R12R11S6bR12R10RdRcRbRaA6S54S56R1A9FQ;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFET 0 (rd_okG (NVC true) 0) HSEGE CST XGL HCST HXGL HCSTD ED_LTCf TD_LTCf (sDv_of ED_LTCf) RD_LTCf HeD_LTCf HchkD_LTCf HTD_LTCf DCHK_LTCf
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.
Lemma tail_LTCf : ltac2:(tb__ "0|3|
S47OF_;S35S30S1aS8S2dQ40M0A1A1M1S5S5S5S83G1S7fS31R9A1S40S18RcS3fRaA1A3S80S18RdS3fRbA1A3S8eReRcA2S65S18ReRcR6R5A5S3dRfA1S0S5S2cG0S1bRePcA2A2RcA3S0S5S2cG0S1bRfPdA2A2RcA3S69ScS5S5A2SeS5S5ReRdA4S39R12A1A3S82RfReA2S0S7S38R14A1S6A3S6aS6R15A2S6cR14S6bR16R14R12R11R10RfA6A2S0S5S84R10A1S64A3S85S81VCST;VXGL;R18A3R19R18R17S6bR18R16R14R13R12R11A6S42S18S7aR16R15SaScS16S41A2M2SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;Sa3R18Z18A2R17A5A4SbG2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 true CST XGL HCST HXGL TM_LTCf Erf_LTCf EC_LTCf run5_LTCf XR_LTCf NX5_LTCf RUN5_LTCf L5_LTCf AXR_LTCf T0_LTCf T1_LTCf T2_LTCf TR_LTCf sR_LTCf RR_LTCf KEPT_LTCf KEPT1_LTCf XS_LTCf eFRc HER_LTCf Hchk_LTCf OBJS_LTCf HT0_LTCf HXS_LTCf OBJS1_LTCf HT2_LTCf HTR_LTCf RCHK_LTCf TRs_LTCf Erq_LTCf Erq2_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.TQ_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.Edr_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.Xf_LTBf run5d_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.run6_LTBf XW_LTCf HTRs_LTCf CCHK_LTCf RUN5d_LTCf L5d_LTCf AXW_LTCf ENTQ_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.NX6_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.RUN6_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.L6_LTBf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBf.f0_drain_LTBf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBf.f0_exit_LTBf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_LTCf : ltac2:(tb__ "0|3|
S35S30S1aS8S2dQ40M0A1A1M1S5S5S5S83G1S7fS31R9A1S8fRaA1S65S18RcRaR4R3A5S3dRdA1S0S5S2cG0S1bRcPcA2A2RaA3S0S5S2cG0S1bRdPdA2A2RaA3S69ScS5S5A2SeS5S5RcRbA4S39R10A1A3S82RdRcA2S0S7S38R12A1S6A3S6aS6R13A2S6cR12S6bR14R12R10RfReRdA6A2S0S5S84ReA1S64A3S86S81VCST;VXGL;R16A3R16R15S6bR16R14R12R11R10RfA6S42S18S7aR14R13SaScS16S41A2M2SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;Sa3R16Z18A2R15A5A4SbG2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 true CST XGL HCST HXGL TM_LTCf Erf_LTCf EC_LTCf run5_LTCf XR_LTCf NX5_LTCf RUN5_LTCf L5_LTCf AXR_LTCf T0_LTCf T1_LTCf T2_LTCf TR_LTCf sR_LTCf RR_LTCf KEPT_LTCf KEPT1_LTCf XS_LTCf eFRc HER_LTCf Hchk_LTCf OBJS_LTCf HT0_LTCf HXS_LTCf OBJS1_LTCf HT2_LTCf HTR_LTCf RCHK_LTCf TRs_LTCf Erq_LTCf Erq2_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.TQ_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.Edr_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.Xf_LTBf run5d_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.run6_LTBf XW_LTCf HTRs_LTCf CCHK_LTCf RUN5d_LTCf L5d_LTCf AXW_LTCf ENTQ_LTCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.NX6_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.RUN6_LTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.L6_LTBf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBf.ef0_drain_LTBf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBf.ef0_exit_LTBf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_lo_Cf_T : ltac2:(tb__ "0|2|
S47OF_;S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SaScS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S48S31R6A1S40S18R9S3fR7A1A3S80S18RaS3fR8A1A3S28S29R6R5A2S63A2S0S7S38RbA1S6A3S6aS6RcA2S28R8S62A2S8eRfRdA2S4aS18R10S3eS18S8aRfReA2S7cS32A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC false (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C_T false true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (t_instantiate false (NVC true) (VFC true) Wa_LTCf Da_LTCf Wb_LTCf Wc_LTCf Wd_LTCf Fb_LTCf XI_LTCf A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_LTCf (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn HO eq_refl HST
           (hdf_LTCf A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_LTCf ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_lo_ia0_Cf_T : ltac2:(tb__ "0|2|
S47OF_;S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SaScS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S48S31R6A1S40S18R9S3fR7A1A3S80S18RaS3fR8A1A3S28S29R6R5A2S63A2S0S7S38RbA1SdA3S6aS6RcA2S28R8S62A2S8eRfRdA2S4aS18R10S3eS18S8aRfReA2S7cS32A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
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
  apply (fi_prefix Wai_LTCf Dai_LTCf Wbi_LTCf Wci_LTCf Certi_LTCf ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid false (NVC true) (VFC true) Wbm_LTCf Wcm_LTCf Wdm_LTCf Fb_LTCf XIm_LTCf A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (free_spine_m_LTCf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2 HO eq_refl HST
           (hdf_LTCf A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_LTCf ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_Cf_T : ltac2:(tb__ "0|2|
S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SaScS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S48S31R6A1S28S29R4R3A2S63A2S0S7S38R9A1S6A3S6aS6RaA2S28R6S62A2S8fRbA1S49S18S3eS18S8aRdRcA2S7cS32A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureC false (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C_T false true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (t_instantiate false (NVC true) (VFC true) Wa_LTCf Da_LTCf Wb_LTCf Wc_LTCf Wd_LTCf Fb_LTCf XI_LTCf A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_LTCf (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn HO eq_refl HST
           (hdfe_LTCf A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (etail_LTCf A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_lo_ia0_Cf_T : ltac2:(tb__ "0|2|
S35S30S1aS8S2dQ40M0A1A1S2cG0S1bR2PcA2A2S5S2cG0S1bR3PdA2A2S5S42S18S7aR4R3SaScS16S41A2M1SeS16S41S7bS32A1S33S65S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S48S31R6A1S28S29R4R3A2S63A2S0S7S38R9A1SdA3S6aS6RaA2S28R6S62A2S8fRbA1S49S18S3eS18S8aRdRcA2S7cS32A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
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
  apply (efi_prefix Wai_LTCf Dai_LTCf Wbi_LTCf Wci_LTCf ECerti_LTCf A Kc rho tp Q p n t jv Hii HKc).
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
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts false (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 false (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid false (NVC true) (VFC true) Wbm_LTCf Wcm_LTCf Wdm_LTCf Fb_LTCf XIm_LTCf A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (efree_spine_m_LTCf (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2 HO eq_refl HST
           (hdfe_LTCf A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 _)
           (etail_LTCf A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ALTCf.
End F0T_aLTCf.

(* [comment removed for export] *)
Module F0T_aTCf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "andb"; "cons"; "nil"; "prod"; "false"; "pair"; "negb"; "orb"; "length"; "option"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_lenient"; "ss_next"; "sv"; "ss_objs"; "swf"; "SVar"; "sv_below"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_pc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "add"; "eqb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "AE_A"; "JL_free"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "aa_internal_inited"; "aa_live"; "topG"; "aa_Kf"; "aa_Km"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf"; "MT_TCf"; "m1_TCf"; "MX_TCf"; "MH0_TCf"; "m2_TCf"; "m3_TCf"; "m4_TCf"; "okbm_TCf"; "okbp_TCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCf"; "ED_TCf"; "PMID_TCf"; "TD_TCf"; "S1c_TCf"; "P0_TCf"; "LT_TCf"; "l1_TCf"; "EX_TCf"; "LH0_TCf"; "TM_TCf"; "l2_TCf"; "l3_TCf"; "l4_TCf"; "RD_TCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "qcondCx"; "rhoC_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "PostDv"; "PreDv"; "sDv_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "Pre_free_tolI"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf.ATCf"; "contTM"; "econtTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT";
"J_free_tol_preT"; "objs_le"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition RUN1p_TCf := RUN1_TCf. Definition RUN2p_TCf := RUN2f_TCf. Definition RUN3p_TCf := RUN3f_TCf. Definition RUN4p_TCf := RUN4f_TCf.
Definition okbp_TCf := l1okb_TCf. Definition chkp_TCf := chk_TCf. Definition H0eqp_TCf := LH0eq_TCf. Definition SIDEp_TCf := SIDE_TCf. Definition OBNDp_TCf := OBND_TCf.
Lemma splitp_TCf : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S5bSbS14A1M1A3A1S1S2S0G0S5fG1A3A1S1S2S0G0S60G1A3A1S2S0G0S61G1A3A1A2A2A2S1S0S7S54S5bA1S6A3S1S0S7S9bS11S14S74S72S5bA2A2U1A2S6A3S1S0S7S69S14S14S10S45S17R1A1M2S5aA2S45G2S5cA2A2LL;S5fA3S6A3S1S0S7S20S15S99S5aS21S73A1M3A2A1A1S6A3S1S0S7S22S1dS15S5aA1M4A1M5G3A2S6A3S1S0S7S69S14S98S5aS5cS73A3S60A3S6A3S1S0S7S69S14S14S45G2S58A2LL;S61A3S6A3S1S1S79S19S1dS15S59A1M6A1A2S1S79S19S1dS15S5dA1M7A1A2S1S79S19G5A2S79S19S1dS15S5cA1M8A1A2A2A2A2S1S0S7S1cG6A1SdA3S1S0S7S1cG7A1SdA3S1S0S7S1cG4A1SdA3S0S7S1cG8A1SdA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkp_TCf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okp_TCf : ltac2:(tb__ "0|1|
S14S6aS14R1S5bA3S3S0S16S17R2A1M0S5dA3S0S7S45G0S58A2S6A3A2F_;FL;").
Proof.
  destruct splitp_TCf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_TCf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqp_TCf. destruct (atpc LOOPH l1_TCf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.
Lemma Wai_TCf : ltac2:(tb__ "0|0|
S0S7S20S94S35U0A1S30A2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_TCf : ltac2:(tb__ "0|4|
S0S12ScS8ScS1eS1eA2M0A1M1S8S25A1M2A2M3A1Sa6S15S7dS33A1A1S94S35U0A1S30A2A2S13G3SeG1G2SaG0SeS1eS1eS21P18A1S23Sa9A1A4SbG0A1A3SbS25A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_TCf : ltac2:(tb__ "0|0|
S0S7S20S96S35U0A1S30A2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_TCf : ltac2:(tb__ "0|0|
S0S7S20S97S35U0A1S30A2A1S6A3"). Proof. vmr. Qed.
Definition Certi_TCf__runs : ltac2:(tb__ "0|0|
S8S12S8S14A1A1A1") := ltac2:(tb__ "0|0|
Sa7S18Ubb8S91S93U0S30A2A4").
Lemma Certi_TCf : ltac2:(tb__ "0|1|
S0S7S9fS18Ubb8S91S19S93U0M0S30A2SaS16S92S35G0A1S30A2SbS16A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_TCf__runs); [unfold Certi_TCf__runs; reflexivity | vmr]. Qed.
Lemma ECerti_TCf : ltac2:(tb__ "0|2|
S0S7Sa0S18Ubb8S91S19S95U0M0S30A2SaS9eSa1S92S35G0A1S30A2Z0M1S23G1A1A3SbS9eA1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_TCf__runs); [unfold Certi_TCf__runs; reflexivity | vmr]. Qed.
Definition m1_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_TCf.
Definition MH0_TCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_TCf) DUMMY).
Definition m2_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_TCf.
Definition MH1_TCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_TCf) DUMMY).
Definition MT_TCf : axst := Eval vm_compute in LT_ofg MH1_TCf F0_TCf.
Definition MX_TCf : axst := Eval vm_compute in EX_ofg MH1_TCf F0_TCf.
Definition m3_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_TCf (SVar pFR)).
Definition m4_TCf : list leafA := Eval vm_compute in runA FUELF [CASX] MX_TCf.
Lemma RUN1m_TCf : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SaS5S72SaS5S47SbS5A1A3A3S56A3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN2m_TCf : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SaS5S72SaS5S75SbS5A1A3A3S4fA3S50A3"). Proof. Time vmr. Qed.
Lemma RUN3m_TCf : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SaS5S72SaS5S75SbS5A1A3A3S9aS4cS21S73A1A2A3S51A3"). Proof. Time vmr. Qed.
Lemma RUN4m_TCf : ltac2:(tb__ "0|0|
S0S8S14A1S88S46SaS5S47SbS5A1A3S4eA3S52A3"). Proof. Time vmr. Qed.
Definition okbm_TCf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S69S14S14S10S2cS27S15S17R1A1M0A1A1S72A2S45G0S58A2A2LL;Vl;A3").
Lemma chkm_TCf : ltac2:(tb__ "0|a|
S0S7S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9S9SfS8S14A1M0S7Lx;M1S4dS6S14G0SdLl0;Ll;M2X8x2A1SfG1S50S6G2X8x2A1A2SfG1S51S6G2X8x2A1A2SfG1S52S6G2X8x2A1A2S53S4dA1A2S9bS11S14S74S72S4dA2A2U1A2A2S69S14S14S10S45S17R1A1M3S4cA2S45G3S4eA2A2LL;S50A3A2S20S15S99S4cS21S73A1M4A2A1A1A2S22S1dS15S4cA1M5A1M6G4A2A2S69S14S98S4cS4eS73A3S51A3A2S69S14S14S45G3S58A2LL;S52A3A2S7aS19S1dS15S56A1M7A1A2A2S7aS19S1dS15S4fA1M8A1A2A2S7aS19G6A2A2S7aS19S1dS15S4eA1M9A1A2A2SfS1cG7A1A1A2SfS1cG8A1A1A2SfS1cG5A1A1A2SfS1cG9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma H0eqm_TCf : ltac2:(tb__ "0|0|
S0S16S17S9dS14U0S74S72S4dA2S89A4A1S4fA3"). Proof. vmr. Qed.
Lemma SIDEm_TCf : ltac2:(tb__ "0|0|
S0S7S8eS56S4cA2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_TCf : ltac2:(tb__ "0|1|
S0S8ScScS1eS1eA2S1eA2M0A1S9cS24G0S8dS1fS15S4cA1A1A4S9cS24G0S8dS1fS15S56A1A1A4A3"). Proof. Time vmr. Qed.
Lemma splitm_TCf : ltac2:(tb__ "0|9|
S1S1S2S0S8S14A1M0S4dSbS14A1M1A3A1S1S2S0G0S50G1A3A1S1S2S0G0S51G1A3A1S2S0G0S52G1A3A1A2A2A2S1S0S7S53S4dA1S6A3S1S0S7S9bS11S14S74S72S4dA2A2U1A2S6A3S1S0S7S69S14S14S10S45S17R1A1M2S4cA2S45G2S4eA2A2LL;S50A3S6A3S1S0S7S20S15S99S4cS21S73A1M3A2A1A1S6A3S1S0S7S22S1dS15S4cA1M4A1M5G3A2S6A3S1S0S7S69S14S98S4cS4eS73A3S51A3S6A3S1S0S7S69S14S14S45G2S58A2LL;S52A3S6A3S1S1S79S19S1dS15S56A1M6A1A2S1S79S19S1dS15S4fA1M7A1A2S1S79S19G5A2S79S19S1dS15S4eA1M8A1A2A2A2A2S1S0S7S1cG6A1SdA3S1S0S7S1cG7A1SdA3S1S0S7S1cG4A1SdA3S0S7S1cG8A1SdA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_TCf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1okm_TCf : ltac2:(tb__ "0|1|
S14S6aS14R1S4dA3S3S0S16S17R2A1M0S4fA3S0S7S45G0S58A2S6A3A2F_;FL;").
Proof.
  destruct splitm_TCf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_TCf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- H0eqm_TCf. destruct (atpc LOOPH m1_TCf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ATCf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition contTM (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S36S1aS8S2eQ40A1A1S71VA;R3A2Sa5Vkeep;Vrho1;R3A3S1aS4bVsegs;Vok;S3fVsegs;S70U0S30SdR6VKc;R5A6S5eR1R4A5VQ;A4FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma spine_tail_TCf : ltac2:(tb__ "0|2|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S6eU0M1S30RcRbRaR9R7S55S57R5AaS86RdRcRbRaR8R6A6S1aS4bVsegs;ReS3fVsegs;S70G1S30S6RdRcRaA6S58R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_TCf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_TCf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (contF_small 0 UStopLe false keep ok A Kc rho rho1 Ebg_TCf Q BGF_TCf HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0 UStopLe false Eps_TCf C3_TCf Ems_TCf C4_TCf TM0_TCf run4_TCf RM_TCf D3_TCf W3_TCf EQ3_TCf NX3b_TCf RUN4_TCf L4_TCf D4_TCf W4_TCf EQ4_TCf
             HeM_TCf HchkM_TCf HTM_TCf FBM_TCf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_TCf. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (f0_s2 0 UStopLe true S1c_TCf C2_TCf EfD_TCf ED_TCf run2_TCf D2_TCf W2_TCf NX2_TCf EQ2_TCf RUN2_TCf L2_TCf AXD_TCf
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0 UStopLe false TD_TCf TDr_TCf CD_TCf Eps_TCf Ebg_TCf run3_TCf AXDr_TCf ENTD_TCf RUN3_TCf L3_TCf NX3_TCf
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_TCf : ltac2:(tb__ "0|4|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S8cR7S2dG0S1bR7PaA2A2S1fS15S59A1A1A3S0G1S1bR8P99A2S2fG0S38S37RbA1A1A2A3S1S28Z1S38S37RcA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6eU0S30RfReRdRcRaS55S57R8AaS86R10RfReRdRbR9A6S1aS4bVsegs;R11S3fVsegs;S8aR10RfRdA3S59R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_TCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TCf LH0_TCf LT_TCf EX_TCf S1c_TCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TCf l2_TCf l3_TCf l4_TCf HNX HLEN
           (runT_some _ _ _ _ RUN1p_TCf NE1) L1okp_TCf (runT_some _ _ _ _ RUN2p_TCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_TCf NE3) H3 (runT_some _ _ _ _ RUN4p_TCf NE4) H4
           (hside_of A Kc rho1 P0_TCf LT_TCf tp SIDEp_TCf OBNDp_TCf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_TCf keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Theorem free_spine_m_TCf : ltac2:(tb__ "0|4|
S5OF_;S48OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S49S32R5A1S41Vsegs;R8S40R6A1A3S6dR6R5A2S28S2dG0S1bR7PdA2A2S63A2S8cR7S2dG0S1bR7PaA2A2S1fS15S56A1A1A3S0G1S1bR8P99A2S2fG0S38S37RbA1A1A2A3S1S28Z1S38S37RcA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6eU0S30RfReRdRcRaS55S57R8AaS86R10RfReRdRbR9A6S1aS4bVsegs;R11S3fVsegs;S8aR10RfRdA3S56R1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_TCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_TCf MH0_TCf MT_TCf MX_TCf S1c_TCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_TCf m2_TCf m3_TCf m4_TCf HNX HLEN
           (runT_some _ _ _ _ RUN1m_TCf NE1) L1okm_TCf (runT_some _ _ _ _ RUN2m_TCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_TCf NE3) H3 (runT_some _ _ _ _ RUN4m_TCf NE4) H4
           (hside_of A Kc rho1 PMID_TCf MT_TCf tp SIDEm_TCf OBNDm_TCf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_tail_TCf keep ok A Kc rho rho1 tp Q HKc Hok HR Hn HD1 HTM rhoE).
Qed.
Definition econtTM (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S36S1aS8S2eQ40A1A1S71VA;R3A2Sa5Vkeep;Vrho1;R3A3S1aS4aVsegs;S3fVsegs;S70U0S30SdR6VKc;R5A6S5eR1R4A5VQ;A3FrhoM;F_;F_;FtpM;Frho1';FA';").
Lemma espine_tail_TCf : ltac2:(tb__ "0|2|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S6fU0M1S30RaR9R8R6S55S57R4A9S87RbRaR9R7R5A5S1aS4aVsegs;S3fVsegs;S70G1S30S6RcRbR9A6S58R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Eps_TCf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JF 0 UStopLe false A' Kc rho1') Ebg_TCf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'.
    split; [|intros rhoX; exact (econtF_small 0 UStopLe false keep A Kc rho rho1 Ebg_TCf Q BGF_TCf HR Hn A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0 UStopLe false Eps_TCf C3_TCf Ems_TCf C4_TCf TM0_TCf run4_TCf RM_TCf D3_TCf W3_TCf EQ3_TCf NX3b_TCf RUN4_TCf L4_TCf D4_TCf W4_TCf EQ4_TCf
             HeM_TCf HchkM_TCf HTM_TCf FBM_TCf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_TCf. exact (HTM A' rho1' tpM HDO HL rhoM). }
  apply (ef0_s2 0 UStopLe true S1c_TCf C2_TCf EfD_TCf ED_TCf run2_TCf D2_TCf W2_TCf NX2_TCf EQ2_TCf RUN2_TCf L2_TCf AXD_TCf
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0 UStopLe false TD_TCf TDr_TCf CD_TCf Eps_TCf Ebg_TCf run3_TCf AXDr_TCf ENTD_TCf RUN3_TCf L3_TCf NX3_TCf
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_TCf : ltac2:(tb__ "0|4|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S8cR6S2dG0S1bR6PaA2A2S1fS15S59A1A1A3S0G1S1bR7P99A2S2fG0S38S37RaA1A1A2A3S1S28Z1S38S37RbA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6fU0S30RdRcRbR9S55S57R7A9S87ReRdRcRaR8A5S1aS4aVsegs;S3fVsegs;S8aRfReRcA3S59R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitp_TCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TCf LH0_TCf LT_TCf EX_TCf S1c_TCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TCf l2_TCf l3_TCf l4_TCf HNX HLEN
           (runT_some _ _ _ _ RUN1p_TCf NE1) L1okp_TCf (runT_some _ _ _ _ RUN2p_TCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3p_TCf NE3) H3 (runT_some _ _ _ _ RUN4p_TCf NE4) H4
           (hside_of A Kc rho1 P0_TCf LT_TCf tp SIDEp_TCf OBNDp_TCf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_TCf keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.
Theorem efree_spine_m_TCf : ltac2:(tb__ "0|4|
S5OF_;S36S31S1aS1aS8S2eQ40M0A1M1A1S48OF_;S32R5A1S6dR5R4A2S28S2dG0S1bR6PdA2A2S63A2S8cR6S2dG0S1bR6PaA2A2S1fS15S56A1A1A3S0G1S1bR7P99A2S2fG0S38S37RaA1A1A2A3S1S28Z1S38S37RbA1M2A1M3A2S28G3S7eS3bG2A1A1A2A2S6fU0S30RdRcRbR9S55S57R7A9S87ReRdRcRaR8A5S1aS4aVsegs;S3fVsegs;S8aRfReRcA3S56R1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR Hn HOB E153 HST HD1 HTM rhoP.
  destruct splitm_TCf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_TCf MH0_TCf MT_TCf MX_TCf S1c_TCf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_TCf m2_TCf m3_TCf m4_TCf HNX HLEN
           (runT_some _ _ _ _ RUN1m_TCf NE1) L1okm_TCf (runT_some _ _ _ _ RUN2m_TCf NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_TCf NE3) H3 (runT_some _ _ _ _ RUN4m_TCf NE4) H4
           (hside_of A Kc rho1 PMID_TCf MT_TCf tp SIDEm_TCf OBNDm_TCf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_tail_TCf keep A Kc rho rho1 tp Q HKc HR Hn HD1 HTM rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S3S7fSaaR2A2S1S28S67R2A2S2aR2S68A2A2A2S4F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S2SacR2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S2SabR2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S5S7fVCST;R1A2S1S2S1S28S67R2A2S2aR2S68A2A2A1S2S1S28Z17db48R2A2S2aR2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.
Lemma HTD_TCf : ltac2:(tb__ "0|0|
S0S16S57Sa8S44S78S55A1S77S76S55S62A5S26S15S55A1A1A2A3").
Proof. unfold TD_TCf, TDv_of, RD_TCf; reflexivity. Qed.
Theorem hdf_TCf : ltac2:(tb__ "0|1|
S36S31S1aS8S2eQ40M0A1A1S80S5S5S5S84S32R8A1S28S2bS3dRaA1S3cRaA1A2Sa2A2S66S18RbR9R8R7A5S6aScS5S5A2SeS5S5R7R6A4S3aRcA1A3S83R8R7A2S0S5S2dG0S1bRcPcA2A2R9A3Sa3RfRdRaR9R8R7A6S6bS6R10A2S48OF_;S49S41S18R2S40R12A1A3S81S18R3S40R13A1A3S6eU0S30S82VCST;VXGL;R15A3R4R15R14S6cR15R13R10RfReRdA6S55S57R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC ok Q Hok Hokp.
  exact (depot_call_HDFT 0 (rd_okG (NVC true) 0) HSEG CST XGL HCST HXGL HCSTD ED_TCf TD_TCf (sDv_of ED_TCf) RD_TCf HeD_TCf HchkD_TCf HTD_TCf DCHK_TCf
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) ok Q Hok Hokp).
Qed.
Theorem hdfe_TCf : ltac2:(tb__ "0|1|
S36S31S1aS8S2eQ40M0A1A1S80S5S5S5S84S32R8A1S28S2bS3dRaA1S3cRaA1A2Sa2A2S66S18RbR9R8R7A5S6aScS5S5A2SeS5S5R7R6A4S3aRcA1A3S83R8R7A2S0S5S2dG0S1bRcPcA2A2R9A3Sa3RfRdRaR9R8R7A6S6bS6R10A2S48OF_;S6fU0S30S82VCST;VXGL;R12A3R12R11S6cR12R10RdRcRbRaA6S55S57R1A9FQ;F_;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp0 md0 p n t jv HKc HKM HA HL HCL Hp [HT HJV] QC Q.
  exact (depot_call_HDFET 0 (rd_okG (NVC true) 0) HSEGE CST XGL HCST HXGL HCSTD ED_TCf TD_TCf (sDv_of ED_TCf) RD_TCf HeD_TCf HchkD_TCf HTD_TCf DCHK_TCf
           A Kc (rhoC_of A rho p n t jv) HKc HKM (rd_zone_C A rho tp0 md0 p n HA HL HCL Hp t HT jv HJV true QC 0) Q).
Qed.
Lemma tail_TCf : ltac2:(tb__ "0|3|
S48OF_;S36S31S1aS8S2eQ40M0A1A1M1S5S5S5S84G1S80S32R9A1S41S18RcS40RaA1A3S81S18RdS40RbA1A3S8fReRcA2S66S18ReRcR6R5A5S3eRfA1S0S5S2dG0S1bRePcA2A2RcA3S0S5S2dG0S1bRfPdA2A2RcA3S6aScS5S5A2SeS5S5ReRdA4S3aR12A1A3S83RfReA2S0S7S39R14A1S6A3S6bS6R15A2S6dR14S6cR16R14R12R11R10RfA6A2S0S5S85R10A1S65A3S86S82VCST;VXGL;R18A3R19R18R17S6cR18R16R14R13R12R11A6S43S18S7bR16R15SaScS16S42A2M2SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;Sa4R18Z18A2R17A5A4SbG2A1A3A5A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (c_tail 0 true CST XGL HCST HXGL TM_TCf Erf_TCf EC_TCf run5_TCf XR_TCf NX5_TCf RUN5_TCf L5_TCf AXR_TCf T0_TCf T1_TCf T2_TCf TR_TCf sR_TCf RR_TCf KEPT_TCf KEPT1_TCf XS_TCf eFRc HER_TCf Hchk_TCf OBJS_TCf HT0_TCf HXS_TCf OBJS1_TCf HT2_TCf HTR_TCf RCHK_TCf TRs_TCf Erq_TCf Erq2_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.TQ_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.Edr_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.Xf_TBf run5d_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.run6_TBf XW_TCf HTRs_TCf CCHK_TCf RUN5d_TCf L5d_TCf AXW_TCf ENTQ_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.NX6_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.RUN6_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.L6_TBf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM ok _ Hok Hokp
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBf.f0_drain_TBf CST XGL HCST HXGL HCSTQ HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBf.f0_exit_TBf CST XGL HCST HXGL HCSTF ok (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.
Lemma etail_TCf : ltac2:(tb__ "0|3|
S36S31S1aS8S2eQ40M0A1A1M1S5S5S5S84G1S80S32R9A1S90RaA1S66S18RcRaR4R3A5S3eRdA1S0S5S2dG0S1bRcPcA2A2RaA3S0S5S2dG0S1bRdPdA2A2RaA3S6aScS5S5A2SeS5S5RcRbA4S3aR10A1A3S83RdRcA2S0S7S39R12A1S6A3S6bS6R13A2S6dR12S6cR14R12R10RfReRdA6A2S0S5S85ReA1S65A3S87S82VCST;VXGL;R16A3R16R15S6cR16R14R12R11R10RfA6S43S18S7bR14R13SaScS16S42A2M2SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;Sa4R16Z18A2R15A5A4SbG2A1A3A5A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd0;Ftp0;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB Hp Hn HL HCL Hii QC HR HJM.
  destruct (virt_pure true A rho p n tp0 md0 HA0 HL Hii QC) as (HLV & HiiV & QCV).
  exact (ec_tail 0 true CST XGL HCST HXGL TM_TCf Erf_TCf EC_TCf run5_TCf XR_TCf NX5_TCf RUN5_TCf L5_TCf AXR_TCf T0_TCf T1_TCf T2_TCf TR_TCf sR_TCf RR_TCf KEPT_TCf KEPT1_TCf XS_TCf eFRc HER_TCf Hchk_TCf OBJS_TCf HT0_TCf HXS_TCf OBJS1_TCf HT2_TCf HTR_TCf RCHK_TCf TRs_TCf Erq_TCf Erq2_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.TQ_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.Edr_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.Xf_TBf run5d_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.run6_TBf XW_TCf HTRs_TCf CCHK_TCf RUN5d_TCf L5d_TCf AXW_TCf ENTQ_TCf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.NX6_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.RUN6_TBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.L6_TBf
           A Kc rho p n t jv tp0 md0 HKc HA0 HB Hp Hn HL HCL Hii QC HR HJM _
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBf.ef0_drain_TBf CST XGL HCST HXGL HCSTQ HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HB Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))
           (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBf.ef0_exit_TBf CST XGL HCST HXGL HCSTF (refillA A 24) Kc rho tp p n t jv (KEEPD CST XGL A) Hp Hn HLV HCL HiiV QCV HR HJM (fun a H => H))).
Qed.

Theorem free_hi_Cf_T : ltac2:(tb__ "0|2|
S48OF_;S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SaScS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S49S32R6A1S41S18R9S40R7A1A3S81S18RaS40R8A1A3S28S64S29R6Z10A2A2S0S7S39RbA1S6A3S6bS6RcA2S28R8S63A2S8fRfRdA2S4bS18R10S3fS18S8bRfReA2S7dS33A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureC true (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C_T true true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros k Hg w Hw.
  destruct (t_instantiate true (NVC true) (VFC true) Wa_TCf Da_TCf Wb_TCf Wc_TCf Wd_TCf Fb_TCf XI_TCf A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_TCf (KEEPD CST XGL A) ok A Kc rho (rhoC_of A rho p n t jv) tp _ HKc Hok HR Hn HO eq_refl HST
           (hdf_TCf A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (tail_TCf ok A Kc rho tp p n t jv tp0 md0 HKc Hok Hokp HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) k Hg w Hw1).
Qed.
Theorem free_hi_ia0_Cf_T : ltac2:(tb__ "0|2|
S48OF_;S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SaScS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S49S32R6A1S41S18R9S40R7A1A3S81S18RaS40R8A1A3S28S64S29R6Z10A2A2S0S7S39RbA1SdA3S6bS6RcA2S28R8S63A2S8fRfRdA2S4bS18R10S3fS18S8bRfReA2S7dS33A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_TCf Dai_TCf Wbi_TCf Wci_TCf Certi_TCf ok A Kc rho tp Q p n t jv Hii HKc Hok).
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
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply triple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros k Hg w Hw.
  destruct (g_instantiate_mid true (NVC true) (VFC true) Wbm_TCf Wcm_TCf Wdm_TCf Fb_TCf XIm_TCf A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (free_spine_m_TCf (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc Hok HR Hn2 HO eq_refl HST
           (hdf_TCf A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 ok _ Hok Hokp)
           (tail_TCf ok A1 Kc rho2 tp p n t jv tp1 md1 HKc Hok Hokp HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_Cf_T : ltac2:(tb__ "0|2|
S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SaScS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S49S32R6A1S28S64S29R4Z10A2A2S0S7S39R9A1S6A3S6bS6RaA2S28R6S63A2S90RbA1S4aS18S3fS18S8bRdRcA2S7dS33A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureC true (Wcan 0) UStopLe true A rho)); [intros w Hw; exact (entry_pure_C_T true true A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & HB & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A Kc rho tp w Hw) |].
  intros w Hw.
  destruct (t_instantiate true (NVC true) (VFC true) Wa_TCf Da_TCf Wb_TCf Wc_TCf Wd_TCf Fb_TCf XI_TCf A Kc rho (rhoC_of A rho p n t jv) tp w p n (N8 n)
              (rhoF_agree (refillA A 24) rho p n t jv) IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_TCf (KEEPD CST XGL A) A Kc rho (rhoC_of A rho p n t jv) tp _ HKc HR Hn HO eq_refl HST
           (hdfe_TCf A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (etail_TCf A Kc rho tp p n t jv tp0 md0 HKc HDS HA0 HB eq_refl eq_refl HL HCL Hii QC HR HJM)
           (rhoC_of A rho p n t jv) w Hw1).
Qed.
Theorem efree_hi_ia0_Cf_T : ltac2:(tb__ "0|2|
S36S31S1aS8S2eQ40M0A1A1S2dG0S1bR2PcA2A2S5S2dG0S1bR3PdA2A2S5S43S18S7bR4R3SaScS16S42A2M1SeS16S42S7cS33A1S34S66S18A1VCST;VXGL;R6R5A5A4SbG1A1A3A5S49S32R6A1S28S64S29R4Z10A2A2S0S7S39R9A1SdA3S6bS6RaA2S28R6S63A2S90RbA1S4aS18S3fS18S8bRdRcA2S7dS33A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC Hn HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ budget_ok_free A /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _). split; [exact HL | split; [exact HB | exists tp, (cfg_model (w_cfg w)); exact HA]]. }
  intros (HL & HB & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_TCf Dai_TCf Wbi_TCf Wci_TCf ECerti_TCf A Kc rho tp Q p n t jv Hii HKc).
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
  assert (QC1 : qcondCx true A1) by exact QC.
  assert (HB1 : budget_ok_free A1) by exact HB.
  assert (HKM1 : aa_Km A1 + aa_Kf A1 <= KMAX) by exact HKM.
  assert (IFF : instG_facts true (Wcan 0) UStopLe (NVC true) (VFC true) (rhoC_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instG_here_C A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV true QC1 true (Wcan 0) UStopLe HHI). }
  destruct (repin_eqs A1 rho2 p n t jv EID) as (PW & PL & PM).
  eapply etriple_conseq; [intros w Hw; exact (mid_repin_T A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp w PW PL PM Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_refill_T CST XGL A1 Kc rho2 tp w Hw) |].
  pose proof (ig_rig _ _ _ _ _ _ _ _ _ _ IFF rho2 (agree_below_vals _ _ _ (rhoF_agree (refillA A1 24) rho2 p n t jv))) as HR.
  assert (Hn2 : bv_unsigned (rw rho2 13%positive) <= kQuarantineMax) by (rewrite E13; exact Hn).
  intros w Hw.
  destruct (g_instantiate_mid true (NVC true) (VFC true) Wbm_TCf Wcm_TCf Wdm_TCf Fb_TCf XIm_TCf A1 Kc (rhoC_of A1 rho2 p n t jv) (rhoC_of A1 rho2 p n t jv) tp w p n (N8 n)
              (agree_below_refl _ _) IFF Hw) as (_ & Hw1 & HO).
  exact (efree_spine_m_TCf (KEEPD CST XGL A1) A1 Kc rho2 (rhoC_of A1 rho2 p n t jv) tp _ HKc HR Hn2 HO eq_refl HST
           (hdfe_TCf A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM1 HA1 HL HCL E12 HTJ QC1 _)
           (etail_TCf A1 Kc rho2 tp p n t jv tp1 md1 HKc HDS HA1 HB1 E12 E13 HL HCL eq_refl QC1 HR JM)
           (rhoC_of A1 rho2 p n t jv) w Hw1).
Qed.
End ATCf.
End F0T_aTCf.

(* [comment removed for export] *)
Module F0T_top.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "JL_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "J_free_tol_pre"; "L_free_tol"; "Pre_free_tol"; "free_tol_contract"; "free_tol_contract_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_top"; "QFTT"; "C_q1c"; "armTE_stmt"; "armT_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_top"; "qcondC"; "top_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall TopGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_top.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_top.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ll.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.F0T_aTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_bTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0T_mTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.F0T_aLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_bLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_aTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_bTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lm.F0T_mTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.F0T_aLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_bLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_aTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_bTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lm.F0T_mTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l3.F0T_aLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_bLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0T_mLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ll.F0T_mLTBf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.F0T_aNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_hxNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.F0T_aLNT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m2.F0T_hxLNT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QFTT (CST XGL : list (Z * Z)) (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|1|
S2dS0S30Vrho;Vtp;S9ScS2bS2cA2M0SbS2bS2cS11S1A1S4S26S0A1VCST;VXGL;VA;VKc;A5A4SaG0A1A3A5").

Definition armT_stmt (CST XGL : list (Z * Z)) (C : AA -> valuation -> Prop) : Prop := ltac2:(tb__ "0|0|
S1fOF_;S15S2SdS8S17Q40A1A1S3R3A1S7S0R6S6R4A1A3S2eS0R7S6R5A1A3VC;R7R5A2S21S0R9S5S0S16R8R7A2SfS1A1R6R5A5S22VCST;VXGL;R8R7R6R5A6A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition armTE_stmt (CST XGL : list (Z * Z)) (C : AA -> valuation -> Prop) : Prop := ltac2:(tb__ "0|0|
S15S2SdS8S17Q40A1A1S3R3A1VC;R5R3A2S20S0S5S0S16R6R5A2SfS1A1R4R3A5S22VCST;VXGL;R6R5R4R3A6A3F_;F_;Ftp;Frho;FKc;FA;").
Definition C_q1c (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S19S29S18Q40SeVrho;PdA2A2S2fA2S32VA;A1A2").
Definition C_big (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S2aS2fS18Q40SeVrho;PdA2A2A2").

Lemma top_pure_T : ltac2:(tb__ "0|0|
S15S2SdS8S17Q40A1A1S1fS5S0S16R5R4A2SfS1A1R3R2R1A6S33R6R4A2F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). unfold top_pure. cbn zeta.
  assert (HC : blk_cls (bv_unsigned (rw rho 12%positive)) (bv_unsigned (rw rho 13%positive))).
  { pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (Hsep & _). destruct (Hsep _ _ HL) as (_ & _ & _ & _ & _ & _ & _ & S8). exact S8. }
  split; [exact HL|]. split; [exact HC|]. exact (qcond_cases A rho tp _ _ _ HA HL HC).
Qed.

Lemma SPA_free_tol_T : ltac2:(tb__ "0|0|
S15S2SdS8S17Q40A1A1S1fS5S0S10S0S26S0A1R5R4A4S12S1A1R3R2R1A6S5S0S16R6R5A2SfS1A1R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w [Hsm ((HA & HU & HIn & HK & HT & HBud & HV) & HKM & HP)].
  destruct (pub_window segsA rho tp free_depth (Pre_free_tol AE_A) w ([mkObj (SVar 12) (SLit 0) (SVar 13) [] DUnknown] ++ A_globals) tol_facts
              ltac:(unfold free_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity |].
    intros p Hp. unfold Pre_free_tol, Pre_free_tolI in Hp |- *. cbn [ax_S mkA ss_facts] in Hp |- *. unfold pub_facts in *.
    rewrite ?in_app_iff in Hp. rewrite ?in_app_iff. tauto.
  - split; [|split; [exact HKM|]].
    + split; [exact HA|]. split; [exact HU|]. split; [exact HIn|]. split; [exact HK|]. split; [exact HT|]. split; [exact HBud|].
      exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
    + unfold HB in HP. unfold top_var in HV. rewrite HV in HP. exact HP.
Qed.

Section FTopT.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S1eS1dVCST;R1A2S1cS1dS31R2A2S19S29S27R2A2S2aR2S28A2A2A2S1bF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S1eS1dVCST;R1A2S1aS35R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S1eS1dVCST;R1A2S1aS34R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S1eS1dVCST;R1A2S19S1aS19S29S27R2A2S2aR2S28A2A2A1S1aS19S29Z17db48R2A2S2aR2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.     Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Lemma HQ1C_T : ltac2:(tb__ "0|0|
S25VCST;VXGL;S23A3").
Proof.
  intros ok A Kc rho tp HK HF HP [Hn QC].
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_T A Kc rho tp w Hw)|]. destruct Hw as [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC.qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe.free_lo_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe.free_hi_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe.free_lo_ia0_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe.free_hi_ia0_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf.free_lo_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf.free_hi_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf.free_lo_ia0_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf.free_hi_ia0_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
Qed.
Lemma HQ1CE_T : ltac2:(tb__ "0|0|
S24VCST;VXGL;S23A3").
Proof.
  intros A Kc rho tp HK [Hn QC].
  apply (etriple_pre_pure segsA _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_T A Kc rho tp w Hw)|]. destruct Hw as [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC.qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe.efree_lo_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe.efree_hi_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m3.F0T_aLTCe.efree_lo_ia0_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCe.efree_hi_ia0_Ce_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf.efree_lo_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf.efree_hi_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aLTCf.efree_lo_ia0_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_aTCf.efree_hi_ia0_Cf_T CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
Qed.

Lemma free_tol_top : ltac2:(tb__ "0|0|
S1fOF_;S15S2SdS8S17Q40A1A1S3R3A1S7S0R6S6R4A1A3S2eS0R7S6R5A1A3S21S0R8S5S0S16R7R6A2SfS1A1R5R4A5S22VCST;VXGL;R7R6R5R4A6A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HK HF HP.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_T A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_LTA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_LTA _ big_fact_LTA HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_TA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_TA _ big_fact_TA HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_LTA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_LTA _ big_fact_LTA HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_TA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_TA _ big_fact_TA HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_LTBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_LTBe _ big_fact_LTBe HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_TBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_TBe _ big_fact_TBe HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_LTBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_LTBe _ big_fact_LTBe HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_TBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_TBe _ big_fact_TBe HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_LTBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_LTBf _ big_fact_LTBf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_TBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_TBf _ big_fact_TBf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_LTBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_LTBf _ big_fact_LTBf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_TBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_TBf _ big_fact_TBf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (HQ1C_T ok A Kc rho tp HK HF HP (conj Hn QC)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (free_lo_N_T CST XGL HCST HXGL HCSTD HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGN_LNT CST XGL HCST HXGL HCSTF HCSTQ ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_N_T CST XGL HCST HXGL HCSTD HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGN_NT CST XGL HCST HXGL HCSTF HCSTQ ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_lo_ia0_N_T CST XGL HCST HXGL HCSTD HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_LNT CST XGL HCST HXGL HCSTF HCSTQ ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_ia0_N_T CST XGL HCST HXGL HCSTD HCST2 HSEG HGEO ok A Kc rho tp HK HF HP HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_NT CST XGL HCST HXGL HCSTF HCSTQ ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.
Lemma efree_tol_top : ltac2:(tb__ "0|0|
S15S2SdS8S17Q40A1A1S3R3A1S20S0S5S0S16R5R4A2SfS1A1R3R2A5S22VCST;VXGL;R5R4R3R2A6A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HK.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_T A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_LTA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_LTA _ big_fact_LTA HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_TA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_TA _ big_fact_TA HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_LTA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_LTA _ big_fact_LTA HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_TA CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_TA _ big_fact_TA HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_LTBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_LTBe _ big_fact_LTBe HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_TBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_TBe _ big_fact_TBe HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_LTBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_LTBe _ big_fact_LTBe HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_TBe CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_TBe _ big_fact_TBe HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_LTBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_LTBf _ big_fact_LTBf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_TBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_TBf _ big_fact_TBf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_LTBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_LTBf _ big_fact_LTBf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_TBf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_TBf _ big_fact_TBf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m5.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (HQ1CE_T A Kc rho tp HK (conj Hn QC)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (efree_lo_N_T CST XGL HCST HXGL HCSTD HSEGE HGEO A Kc rho tp HK HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_LNT CST XGL HCST HXGL HCSTF HCSTQ A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_N_T CST XGL HCST HXGL HCSTD HSEGE HGEO A Kc rho tp HK HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_NT CST XGL HCST HXGL HCSTF HCSTQ A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_lo_ia0_N_T CST XGL HCST HXGL HCSTD HCST2 HSEGE HGEO A Kc rho tp HK HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_LNT CST XGL HCST HXGL HCSTF HCSTQ (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_ia0_N_T CST XGL HCST HXGL HCSTD HCST2 HSEGE HGEO A Kc rho tp HK HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_NT CST XGL HCST HXGL HCSTF HCSTQ (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Theorem free_tol_contract_B : ltac2:(tb__ "0|0|
S13S0S1S26S0A1VCST;VXGL;A5").
Proof.
  intros ok A Kc rho tp HK HF HP.
  eapply triple_conseq; [intros w Hw; exact (SPA_free_tol_T A Kc rho tp w Hw) | intros w Hw; exact Hw | exact (free_tol_top ok A Kc rho tp HK HF HP)].
Qed.
Theorem free_tol_contract_ex_B : ltac2:(tb__ "0|0|
S14S0S1S26S0A1VCST;VXGL;A5").
Proof. intros A Kc rho tp HK w Hw. exact (efree_tol_top A Kc rho tp HK w (SPA_free_tol_T A Kc rho tp w Hw)). Qed.
End FTopT.
End F0T_top.

