(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.

(* [comment removed for export] *)
Module Lib_handle_l_chk3.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_13 : CC 13 T_fail0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 T_mck = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_15 : CC 15 T_mcg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_16 : CC 16 C_mk = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_17 : CC 17 C_mg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_18 : CC 18 C_rlk = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_19 : CC 19 C_rlg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk3.

(* [comment removed for export] *)
Module Lib_handle_l_chk4.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_20 : CC 20 C_fa0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 C_fa1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_22 : CC 22 XN = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_23 : CC 23 C_few = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_24 : CC 24 C_ok = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_25 : CC 25 T_keep2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_26 : CC 26 T_grown2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_27 : CC 27 T_fail2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 T_m2k = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_29 : CC 29 T_m2g = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_30 : CC 30 C_e8k = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_31 : CC 31 C_e8g = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_32 : CC 32 C_f2a = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_33 : CC 33 C_f2b = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_34 : CC 34 C_epf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_35 : CC 35 C_epo = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_36 : CC 36 C_rlf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_37 : CC 37 C_rlo = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk4.

(* [comment removed for export] *)
Module Lib_handle_l_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2"; "cutsL"; "exitsL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l"; "FUEL_hl"; "cutpcs_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA"; "ejcert_hdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_handle_l_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_handle_l_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_chk4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.

Lemma hdr_ok : ltac2:(tb__ "0|0|
S3S1S9S0S4A2S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ejcertL_ok : ltac2:(tb__ "0|0|
S3S1SaS6S0S7S8S0S4S5A7S2A3").
Proof.
  apply ejcertA_of_cuts; [exact hdr_ok|].
  change (cuts_okE segs FUEL_hl cutpcs_hl NPH PE 0 [Pre_hl; C_pro; C_pre; H; L1; L2; K; C_unp; T_pc; T_da; J; T_keep; T_grown; T_fail0; T_mck; T_mcg; C_mk; C_mg; C_rlk; C_rlg; C_fa0; C_fa1; XN; C_few; C_ok; T_keep2; T_grown2; T_fail2; T_m2k; T_m2g; C_e8k; C_e8g; C_f2a; C_f2b; C_epf; C_epo; C_rlf; C_rlo] TG = true).
  simple apply cuts_okE_cons; [exact cc_0|].
  simple apply cuts_okE_cons; [exact cc_1|].
  simple apply cuts_okE_cons; [exact cc_2|].
  simple apply cuts_okE_cons; [exact cc_3|].
  simple apply cuts_okE_cons; [exact cc_4|].
  simple apply cuts_okE_cons; [exact cc_5|].
  simple apply cuts_okE_cons; [exact cc_6|].
  simple apply cuts_okE_cons; [exact cc_7|].
  simple apply cuts_okE_cons; [exact cc_8|].
  simple apply cuts_okE_cons; [exact cc_9|].
  simple apply cuts_okE_cons; [exact cc_10|].
  simple apply cuts_okE_cons; [exact cc_11|].
  simple apply cuts_okE_cons; [exact cc_12|].
  simple apply cuts_okE_cons; [exact cc_13|].
  simple apply cuts_okE_cons; [exact cc_14|].
  simple apply cuts_okE_cons; [exact cc_15|].
  simple apply cuts_okE_cons; [exact cc_16|].
  simple apply cuts_okE_cons; [exact cc_17|].
  simple apply cuts_okE_cons; [exact cc_18|].
  simple apply cuts_okE_cons; [exact cc_19|].
  simple apply cuts_okE_cons; [exact cc_20|].
  simple apply cuts_okE_cons; [exact cc_21|].
  simple apply cuts_okE_cons; [exact cc_22|].
  simple apply cuts_okE_cons; [exact cc_23|].
  simple apply cuts_okE_cons; [exact cc_24|].
  simple apply cuts_okE_cons; [exact cc_25|].
  simple apply cuts_okE_cons; [exact cc_26|].
  simple apply cuts_okE_cons; [exact cc_27|].
  simple apply cuts_okE_cons; [exact cc_28|].
  simple apply cuts_okE_cons; [exact cc_29|].
  simple apply cuts_okE_cons; [exact cc_30|].
  simple apply cuts_okE_cons; [exact cc_31|].
  simple apply cuts_okE_cons; [exact cc_32|].
  simple apply cuts_okE_cons; [exact cc_33|].
  simple apply cuts_okE_cons; [exact cc_34|].
  simple apply cuts_okE_cons; [exact cc_35|].
  simple apply cuts_okE_cons; [exact cc_36|].
  simple apply cuts_okE_cons; [exact cc_37|].
  apply cuts_okE_nil.
Qed.
End Lib_handle_l_chk.

(* [comment removed for export] *)
Module Lib_handle_l_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "True"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "g8"; "has_facts"; "ax_base"; "leafA"; "la_state"; "ax_setS"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "SLit"; "sobj"; "SPUle"; "ss_next"; "ss_objs"; "sprop_eqb"; "holds"; "swf"; "eval"; "SPEq"; "SVar"; "SAlu"; "DUnknown"; "cell"; "mkObj"; "sv_below"; "obj_wf"; "obj_range"; "soff"; "sprop_below"; "agree_below"; "dflt_writable"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "pair"; "cons"; "nil"; "nat"; "Some"; "option"; "None"; "fst"; "andb"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "emeasA"; "PTrue"; "nd_below"; "TPA"; "frinA"; "tvinA"; "fbinA"; "ffinA"; "JA_pre"; "nd_bd"; "nd_tv"; "JA"; "JLA"; "amode"; "fr_sub_eqb"; "frozen"; "nd_am"; "nd_fr"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "mul"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l"; "fr_hl"; "pQ"; "pK"; "pD"; "X_hl"; "L_mc1"; "Pre_mc"; "tv_hl"; "nd0"; "E_da0"; "E_mg0"; "E_mk0"; "E_pc0"; "E_unp0"; "E_vr0"; "Pre_hl"; "R_v"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "pC"; "E_sm0"; "E_vr"; "L_sm"; "PD_vn"; "Pre_sm"; "X_pro"; "Xk_v"; "cmul12"; "mid_dst"; "pC1"; "pT0"; "reshapeA"; "s_v"; "slot_facts"; "xf_cm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "hG"; "hF"; "tE"; "kb"; "lc_d"; "lc_k"; "tL"; "lc_c"; "PROG"; "tB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf"; "P0_hl"; "bF"; "P0_hl_b"; "fF"; "vrF"; "DW_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2"; "VR"; "cutsL"; "epi_state"; "ndJ"; "tvN"; "ndG"; "ndK"; "z0"; "ndT"; "tvL"; "C_epf"; "P_fail"; "P_ok"; "R_v2"; "ndN"; "ndO"; "ndOg"; "ndX"; "ndX2"; "nd_fail"; "nd_ok"; "E_da2"; "E_m2g0"; "E_m2k0"; "E_vc"; "E_vc0"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_f7a"; "X_f7b"; "X_fp0"; "X_fp1"; "X_ok0"; "X_rlf"; "X_rlo"; "Xk_v2"; "bdL"; "cmul4"; "exitsL"; "lcc1"; "mid4_dst"; "ndEf"; "ndEo"; "ndF"; "ndNs"; "ndP"; "s_v2"; "sel_rel"; "slot4_facts"; "tvY"; "xf_e8"; "yCUR"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "BXok_d"; "bd_below"; "bd_subst"; "bud_le"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "J_ofPA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.HLAddr"; "DW"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "shadow_reopen_stateA"; "release_objs_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvd"; "tvz"; "T_ok"; "FBx"; "remove_nth"; "tv_sub_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf.Sum"; "HNPH"; "Posts_hlJ"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "baseF"; "P0_builder"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "xrs_inclb"; "robjs_okF"; "xrs_okF"; "PostsC"; "xrs_okL"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "T_afterA"; "call_checkTA"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "JL_stack_malloc"; "J_memcpy_pre"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_eqs"; "cm1"; "cm2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf.Sum.X"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf.VN"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN. End VN.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf. End VNP.

Definition P0_hl (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S116VCST;VFB;VFF;Vr;A4S0S35S12aZ1Sd1S31S31S6S6A2M0S6A2G0S39G0S6A2VFF;A4A2U0A3A2").
Lemma P0_hl_b : ltac2:(tb__ "0|2|
S2eS31S6S6A2M0A1M1G1S2eS31G0S6A2A1S14S90R4R3R2R1A4S116R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 128 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 128 < 2 ^ 40. Proof. lia. Qed.

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S3aS3aSccS15S1cS19Vq;S88A2A1VF;A3SccS15S1cS19S88S8cA2A1VF;A3A2SccS15S1cS19S8cS17S141A1A2A1VF;A3A2").
Lemma VR_val : ltac2:(tb__ "0|3|
S14S2eS15A1S13S6Sd0S15S1dR4A1R3A3S0S2fS94R3R4A2S30A3S1S56Z0M0R3A2S58R3Z40M1A2A2S1S0S6Sd4R7S96R5R4A2A2S5bS59G1S5aSd4R7S88A2Sd4R7R5A2A2M2A2R4A2A3S1S56G0G2A2S56G2S57Z2Z1aA2A2A2A2F_;F_;F_;Fa;Fq;FF;Frho;").
Proof.
  intros rho F q a HF HV Ha. unfold vrF in HV. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. unfold two26 in F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho q) as Rq. pose proof (uval_range rho tE) as RE.
  assert (ES : uval rho (SAlu ALU_SUB tE q) = uval rho tE - uval rho q).
  { destruct (U_sub_q rho tE q) as [k Hk]. unfold U in Hk. unfold uval in *.
    pose proof (bv_urange (eval rho (SAlu ALU_SUB tE q))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia. }
  assert (EM : uval rho (kb 64 (SAlu ALU_SUB tE q)) = 64 * (uval rho tE - uval rho q)).
  { unfold kb. rewrite uval_mul_lit by lia. rewrite ES. reflexivity. }
  unfold VR. rewrite uval_add_litZ by (rewrite ?EM; lia). rewrite EM. lia.
Qed.
Lemma VR_meas : ltac2:(tb__ "0|3|
S14S14S2eS15A1S13S6S6Sd0S15S1dR6A1R4A3S0S2fS94R4R5A2S30A3S0S55Q40A1M0S1fR7S88A2S1fR8S88A2A3S0G0S1fR8R6A2S1fR9R6A2A3S56Z0M1R6A2S58R7R6A2S58R7Z40A2S1S56G1Sd4RcS96RaR9A2A2M2A2S58G2Sd4RdS96RaR8A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fb;Fa;Fq;FF;Frho';Frho;").
Proof.
  intros rho rho' F q a b HF HV H1 H2 Ha Hab Hb.
  assert (EQ : uval rho' (VR q a) = uval rho (VR q a)).
  { unfold uval, VR, kb. cbn [eval]. rewrite H1, H2. reflexivity. }
  rewrite EQ. destruct (VR_val rho F q a HF HV ltac:(lia)) as [-> R1]. destruct (VR_val rho F q b HF HV ltac:(lia)) as [-> _]. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
SfcS14S2eS55Q40A1A1SeeOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S6S139VCST;R1A2S1S56Z0R2A2S58R2S100A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S6S139VXGL;R1A2S1S56Z0R2A2S58R2S100A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2eS31S31S6S6A2S6A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S4cVAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41Vnd;Aa").
Definition Posts_hlJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S33S31S8Se6A2M0S32S8Se6Sa1S110Sa9A1A4S33G0S32S8Se6Sa2S110SaaA1A4S34G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S4bVAInv;VCST;VXGL;S85VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S31S8S3dA2S127Fn;") := ltac2:(tb__ "0|0|
S52VAInv;VCST;VXGL;S85VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Se7S54S85Vrho0;Vtp0;S10fA5").

Let siteP : ltac2:(tb__ "0|0|
SfcS14S2eS15A1S2eS31S13S13A2A1S2eS31S31S13S6A2S13A2A1S37S35A1S2eS18A1S14S2eS55Q40A1A1SeeVAInv;RaR3R2R1A4Sd0S15S1dRaA1R9A3S0S2fS115SedRaA2S30A3Sf0S85Vrho0;RcA3S90VCST;VFB;VFF;Vrho0;A4S43Vrho0;RfA2S109RfSfeSfdR10A1A1A2S46VFB;R11A2S47VFF;R12A2S45VFB;R13R12R10A4S107R13R11A2S108R14R12A2S44VFF;R16R15R12A4S0S2fS125R15R14R13R12SdcR11A6S30A3S12fVCST;R18S38S6A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Se3VAInv;VCST;VALA;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedS95Ac").
Let siteF : ltac2:(tb__ "0|0|
SfcS14S2eS15A1S2eS31S13S13A2A1S2eS31S31S13S6A2S13A2A1S2eS18A1S14S2eS55Q40A1A1SeeVAInv;R9R3R2R1A4Sd0S15S1dR9A1R8A3S0S2fS115SedR9A2S30A3Sf0S85Vrho0;RbA3S90VCST;VFB;VFF;Vrho0;A4S43Vrho0;ReA2S109ReSfeSfdRfA1A1A2S45VFB;R10RfRdA4S107R10ReA2S108R11RfA2S44VFF;R13R12RfA4S0S2fSf6R12R11R10S38S35A1SdcRfA6S30A3S147VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Se1VAInv;VCST;VALA;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedS95Ac").
Let siteH : ltac2:(tb__ "0|1|
SfcS14S2eS15A1S2eS31S13S13A2A1S2eS31S31S13S6A2S13A2A1S2eS18A1S14S2eS55Q40A1A1SeeVAInv;R9R3R2R1A4Sd0S15S1dR9A1R8A3S0S2fS115SedR9A2S30A3Sf0S85Vrho0;RbA3S90VCST;VFB;VFF;Vrho0;A4S43Vrho0;ReA2S109ReSfeSfdRfA1A1A2S45VFB;R10RfRdA4S107R10ReA2S108R11RfA2S44VFF;R13R12RfA4S0S2fSf6R12R11R10S38S35A1SdcRfA6S30A3S18S6ScdS18R2R12A3S1S56S39S6S6S28R17R3A2M0A3R2A2S58R2S3bS6S6G0A3A2A2S3S11aVCST;Vrho0;S10aVFB;R18R16A3S119VFF;R18R15A3R3A5S3S1S56Z0R3A2S58R3S100A2A2S12dR3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Se2VAInv;VCST;VALA;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedS95Ac").
Let siteX : ltac2:(tb__ "0|4|
SfcS14S2eS15A1S2eS31S13S13A2A1M0S2eS31S31S13S6A2S13A2M1A1M2S37S35A1M3S2eS18A1G0S14S2eS55Q40A1A1SeeVAInv;RbR3R2R1A4Sd0S15S1dRbA1RaA3S0S2fS115SedRbA2S30A3Sf0S85Vrho0;RdA3S90VCST;VFB;VFF;Vrho0;A4S43Vrho0;R10A2S109R10SfeSfdR11A1A1A2S46VFB;R12A2S47VFF;R13A2S45VFB;R14R13R11A4S107R14R12A2S108R15R13A2S44VFF;R17R16R13A4S0S2fSf7VXGL;R16R15R14R13R12SddR11A8S30A3S1S11fVCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S35S10bG1R1R16A3Li;R15X37x2R12A9S1S131VCST;VXGL;R19S38S6A1R18R12A6S148R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Se4VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedS95Af").
Let site_pure : ltac2:(tb__ "0|2|
S8S103S2eS18A1S14S2eS31S13S13A2A1S2eS31S31S13S6A2S13A2A1S2eSd5A1S0S2fS115SedS16S9R7A1A1A2S30A3S0S2fS125S16S9R8A1A1R4R3S38S35A1M0SdcR6A6S30A3S0S2fSf7VXGL;S16S9R9A1M1A1R5R4G0S1bG1A1SddSaR9A1A8S30A3S130VAInv;VCST;VXGL;S85Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S3fR6R5R4S3eA4S38S6A1SfcS10dS4L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
Se5VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedS95Af").
Let payA_same : ltac2:(tb__ "0|1|
S2eS15A1S2eSd5A1S0S2fSd6R1A1S30A3S12eS85Vrho0;S90VCST;VFB;VFF;A3R3S17Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
Se0S85Vrho0;S90VCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S7S7S3dS14S121S85R3A2S0S2fS42R4R3A2S30A3S5fS54R6S4fVAInv;VCST;VXGL;S85VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
SdfVAInv;VCST;VXGL;VALA;S85VKc;VHKc;VFB;VFF;VBX;Vrho0;S90VCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S14S18S6S2eS31S13S13A2A1S2eS31S31S13S6A2S13A2A1S117SedR5A2Sf0S85Vrho0;R6A3S90VCST;VFB;VFF;Vrho0;A4S0S2fSdcR7A1S30A3S1S56S39S6S6S28R9R8A2M0A3R7A2S58R7S3bS6S6G0A3A2A2S11aVCST;Vrho0;S10aVFB;RaR7A3S119VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
SdeVCST;S85S10eVFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S92VCST;VFB;VFF;A3SedA9").

Lemma P0_now : ltac2:(tb__ "0|2|
S14Sf0S85Vrho0;R1A3S90VCST;VFB;VFF;Vrho0;A4S1S6S1S56Sd4R4S8fA2M0R1A2S58R1S5bG0Sd4R4S8cA2A2A2A2S11aVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1S129VFF;Sd4R3S13bA2Z518A3S1S129VFF;Sd4R3S13aA2Z30A3S0S35S12aZ1Sd1S31S31S6S6A2M1S6A2G1S39G1S6A2VFF;A4A2U0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hl CST FB FF) (P0_hl_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as [_ D]. auto.
Qed.

Lemma JA_tv_swap2 : ltac2:(tb__ "0|1|
S31S13S13A2M0G0S2eG0A1S2eS31S31S13S6A2S13A2A1S2eSd5A1S14S2eS55Q40A1A1S2eSefA1SeeVJAv;S3fS33G0R9S33G0R8R7A3A3R6R5S3eA4R4R3R2R1A5VJAv;S3fS33G0R9S33G0RaR8A3A3R7R6S3eA4R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;Fbd;Ffr;Fr;Fb;Fa;").
Proof.
  intros a b r fr bd rho tp tr md (Ai & kc & HJ).
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  assert (HCNT : cntS rho (a :: b :: r) <= cntS rho (b :: a :: r)) by (rewrite !cntS_cons; lia).
  exists Ai, kc. unfold JAi. cbn [nd_tv nd_fr nd_bd nd_am].
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split.
  - split; [|split].
    + inversion HN as [|x l Ha HN1]; subst. inversion HN1 as [|y l' Hb HN2]; subst. constructor; [exact Hb|]. constructor; [exact Ha | exact HN2].
    + cbn [tvd] in HD |- *. destruct HD as (Da & Db & Dr). split; [|split; [|exact Dr]].
      * intros t' Ht' Hzb Hzt. destruct Ht' as [<-|Ht'].
        -- intros E. apply (Da b (or_introl eq_refl) Hzt Hzb). symmetry. exact E.
        -- exact (Db t' Ht' Hzb Hzt).
      * intros t' Ht' Hza Hzt. exact (Da t' (or_intror Ht') Hza Hzt).
    + inversion HZ as [|x l Ha HZ1]; subst. inversion HZ1 as [|y l' Hb HZ2]; subst. constructor; [exact Hb|]. constructor; [exact Ha | exact HZ2].
  - split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [|split; [exact HBU | exact (JA_tail_le _ _ _ rho rho _ _ HCNT HPA)]].

    unfold XA in HXA |- *. destruct HXA as [HX0 HCEN]. split; [exact HX0|].
    intros bn L1 L2 L3 L4. apply (HCEN bn L1 L2 L3). intros v Hv. apply L4. unfold tvals in *. cbn [map In] in Hv |- *. tauto.
Qed.
Lemma SPA_swap2 : ltac2:(tb__ "0|1|
S31S13S13A2M0G0S2eG0A1S2eS31S31S13S6A2S13A2A1S2eSd5A1S8S14S2eS55Q40A1A1Sf3S5cS54VJAv;S3fS33G0R9S33G0R8R7A3A3R6R5S3eA4A1R4R3R2R1A6S5cS54VJAv;S3fS33G0R9S33G0RaR8A3A3R7R6S3eA4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FS;Fbd;Ffr;Fr;Fb;Fa;").
Proof. intros a b r fr bd S rho tp w [Hsm HJ]. split; [exact Hsm | apply JA_tv_swap2; exact HJ]. Qed.

Lemma tvz_kd : ltac2:(tb__ "0|2|
S14S6S13S13S2eS31S13S13A2M0A1S108R5S33G0S32S13S13R3S89R4R2A2A4R1A3A2S1S58Z0M1R5A2S56R5ZcA2A2S56Sd4R7R4A2S102A2S2S0S6Sd4R8R5A2G1A3A1S2S0S6Sd4R9R7A2G1A3A1F_;F_;F_;F_;Fr;Fk;Fd;Fe;Frho;").
Proof.
  intros rho e d k r HZ He HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E12. unfold uval, kb in E12. unfold kb in HZ. rewrite E12 in HZ. nia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S14S2eS15A1S13Sd0S15S1dR3A1R2A3S0S2fSccS15S1cS19S7fR2A2A1R3A3S30A3S0S2fSccS15S1cS19R3S17S102A1M0A2A1R4A3S30A3S0S2fSccS15S1cS19S75R4A2A1R5A3S30A3S0S2fSccS15S1cS19S89ZcR5A2G0A2A1R6A3S30A3Sd0S15S1dR8A1S83R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho pC) as RC. pose proof (uval_range rho k) as Rk.
  unfold pC1 in F1. rewrite uval_add_litZ in F1 by lia.
  assert (E12k : uval rho (kb 12 k) = 12 * uval rho k) by (unfold kb; apply uval_mul_lit; lia). rewrite E12k in F5.
  assert (E12c : uval rho (cmul12 pC) = 12 * uval rho pC) by (unfold cmul12; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot_facts.
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E12c; lia). rewrite E12c, E12k. lia.
  - rewrite E12c, E12k. lia.
  - unfold B32. rewrite E12c, uval_lit by lia. lia.
Qed.
Lemma slot4_holds : ltac2:(tb__ "0|1|
S14S2eS15A1S13Sd0S15S1dR3A1R2A3S0S2fSccS15S1cS19SbfR2A2A1R3A3S30A3S0S2fSccS15S1cS19R3S17S102A1M0A2A1R4A3S30A3S0S2fSccS15S1cS19S8dR4A2A1R5A3S30A3S0S2fSccS15S1cS19S89Z4R5A2G0A2A1R6A3S30A3Sd0S15S1dR8A1Sc8R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho lc_c) as RC. pose proof (uval_range rho k) as Rk.
  unfold lcc1 in F1. rewrite uval_add_litZ in F1 by lia.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia). rewrite E4k in F5.
  assert (E4c : uval rho (cmul4 lc_c) = 4 * uval rho lc_c) by (unfold cmul4; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot4_facts.
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E4c; lia). rewrite E4c, E4k. lia.
  - rewrite E4c, E4k. lia.
  - unfold B32. rewrite E4c, uval_lit by lia. lia.
Qed.

Lemma foff_rng : ltac2:(tb__ "0|0|
S14S2eS15A1S6Sd0S15S1dR3A1R2A3S0S2fS93R3A1S30A3S1S56Z0R3A2S56R3Z80A2A2S0S6Sd4R6S22S101S87S17R4A1A3A2S5bSd4R6S87A2R4A2A3F_;F_;F_;Foff;FF;Fr;").
Proof. intros r F off HF HFR Ho. unfold hF. apply (frame_off_rng hG 160 128 off r F sz_rng Ho HF HFR). Qed.
Lemma slot_rng : ltac2:(tb__ "0|1|
S14S2eS15A1S13S13S6S1S56Z0R1A2S56R1ZcA2A2Sd0S15S1dR6A1R5A3S0S2fSccS15S1cS19R5S17Z800000000000A1A2A1R6A3S30A3S0S2fSccS15S1cS19R5S17S102A1A2A1R7A3S30A3S1S0S6Sd4R9S22S101R7R6A3A2S5bSd4R9R7A2Sd4R9R6A2M0A2A3S1S0S6S29R9R6A2G0A3S0S6S29R9S22S101R6S17R5A1A3A2S5bG0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm;Fd;FF;Fr;").
Proof.
  intros r F d cm w Hw HF Hd Hs.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S6S2eS55Q40A1A1Sf2F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S5dS8S14S2eS55Q40A1A1Sf2Sd0S15S1dR3A1S16S9R4A1A1A3VTR;S5cS54R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sf2Sf2Sf2Sf3R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
Sf2OSf2Sf3R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S5dS5dS8S8S103S2eS18A1M0S2eS31S8Se6A2M1A1S2eS31S13S13A2M2A1Sf2S14S2eS55Q40A1A1M3G2ScdG2R1R5A3ScdG2R2SaRbA1A3F_;Fr;S0S37G0A1Se8RaR9R8A3S36G0R7A2A3S0S2fSeaRbRaR9R8Sd1G1S8S39S8Se6A2R7A4A5S30A3S14G3VTR;S5cS54RfRdR2R1A5Se7S54S1aS9RdA1A1R2R1RaA5A2Ftp1;Frho1;S2eSefA1M4S10dSeeS5eS54R9R8R10S32G4S122R3S123R2R1A2A4A5R13RaR9R4R2A4R13S105S104RbRfS111R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S8Se6G4S10dSeeS14G3G4S10dSeeScdG1S32S8Se6RaR9A4R14A3S5eS54R12R11R19S32G4S122R9S123R8R7A2A4A5R1cR13R12RaR8A4Sf0S1aS9R1aA1A1S105S104R14R18S111R9R13RaA3A3R19A2R8A3S5eS54R9R8ReS32G4S122R7S123R6R5A2A4A5ReS105S104R16R1aS111RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S145R17S111RcR16RdA3R1bR1cR1dR10R1eR19RbA9S14Sf1R18S111RdR17ReA3R1cR1dS9R1eA1S9R1fA1S9R11A1R1RcA9VTR;S5cS54SecR11S105S104R19R1dS111ReR18RfA3A3R1eA2R18RdRcA5S146R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S5cS54R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRESN : ltac2:(tb__ "0|1|
S2eS31S6S6A2M0A1S2eS31G0S6A2A1SdbS14S2eS55Q40A1A1Sd7Z3R3A2VTR;S5cS54S48VAInv;VCST;VXGL;VKc;S118R6R5A2R6R5R4S41S140AaS13fR3R2A5Se7S54S124R3R2S11eVAInv;VCST;VXGL;VKc;S118S41S79R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
SfcS14S2eS55Q40A1A1VTR;S5cS54S136VAInv;Z1M0R3VKc;A4S7aR2R1A5Se7S54S124R2R1S33S31S8Se6A2M1S32S8Se6S78S134VAInv;VCST;VXGL;G0R3VKc;A6A4S34G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
SfcS14S2eS55Q40A1A1VTR;S5cS54S135VAInv;R3VKc;A3S66R2R1A5Se7S54S124R2R1S33S31S8Se6A2M0S32S8Se6S65S133VAInv;VCST;VXGL;R3VKc;A5A4M1S33G0G1S34G0A1A3A3A5A2Ftp1;Frho1;FAi;").

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S8S103S2eS18A1M0S14S2eS55Q40A1A1S3dSf2S0S37G0A1Se8R7VPre;R6A3S36G0R5A2A3S0S2fSe9R8VPre;R7R6Sd1SeS8SfVPosts;A4A5S30A3S0S2fS120S85S1aS9R9A1A1A2S30A3S0S2fS42S1aS9RaA1A1R5A2S30A3S0S2fScfS15S2aS1aS9RbA1M1A1A1S16G1A1A3S30A3SeS14ScdSeR2VPosts;A3S2bS1aS9RfA1A1RcR2A3VTR;S5cS54VJAv;RbA1S126S16S9R10A1A1SebRfVPre;SfR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S5cS54VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_pc : pure_rule Pre_pc Posts_pc.
Hypothesis CALL_da : pure_rule Pre_da Posts_da.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S8S3dS31S6S13A2M0S14S2eS55Q40A1A1M1S6G1ScdS31S31S8S3dA2M2G0A2S32G2G0S32S8S3dR7R6A4R5A4S97A3S1S56Z0S40S32G2G0S32S8S3dR8R7A4R6A4R5A2M3A2S58G3R3A2A2VTR;S5cS54VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S8S3dS14S2eS55Q40A1A1M0S6G0ScdS31S8Se6A2S32S8Se6R6S110R5A1A4S10fA3VTR;S5cS54VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsL exitsL Posts_hlJ PD_vr PD_vn]; do n right; left; reflexivity.

Lemma loop_meas : ltac2:(tb__ "0|5|
S14S14S2eS15A1S7S6S6S8S8S3dS3dSd0S15S1dRaA1R8A3S0S2fS94S61R9A2S30A3Sf0R9RcRbA3S0S2fS26RaS88A2S30A3S0S2fS26RbS61A2S30A3S56Z0M0RbA2S58RcRbA2S58RcZ40A2S1S56G0S40S32S31S8S3dA2M1S31S6S13A2M2S32S8S3dRbR9A4S32S6S13Z50M3S96S61ReA2A4A4R11A2M4A2S58G4S40S32G1G2S32S8S3dRcRaA4S32S6S13G3S96S61RdA2A4A4R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;Fn;FF;Frho';Frho;").
Proof.
  intros rho rho' F n a b X T ndX ndT HF HV Hag HbE HbQ Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho' F pQ a b HF HV (eq_sym (eval_agree_vals n rho rho' tE Hag HbE)) (eq_sym (eval_agree_vals n rho rho' pQ Hag HbQ)) Ha Hab Hb) as M.
  unfold uval in M. lia.
Qed.
Lemma loop_meas_same : ltac2:(tb__ "0|5|
S14S2eS15A1S6S6S8S8S3dS3dSd0S15S1dR8A1R7A3S0S2fS94S61R8A2S30A3S56Z0M0R8A2S58R9R8A2S58R9Z40A2S1S56G0S40S32S31S8S3dA2M1S31S6S13A2M2S32S8S3dR8R6A4S32S6S13Z50M3S96S61RbA2A4A4RdA2M4A2S58G4S40S32G1G2S32S8S3dR9R7A4S32S6S13G3S96S61RaA2A4A4RdA2A2A2F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;FF;Frho;").
Proof.
  intros rho F a b X T ndX ndT HF HV Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho F pQ a b HF HV eq_refl eq_refl Ha Hab Hb) as M. unfold uval in M. lia.
Qed.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S8S3dS6S14S0S6S40S32S31S8S3dA2S31S6S13A2S32S8S3dR4R3A4S32S6S13R2S9dA4A4R1A2S59R2S57Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S8S3dS6S13S14S14S13S0S55Q40A1S1fR2R1A2S1fR3R1A2A3Fe;S0S6S40S32S31S8S3dA2S31S6S13A2S32S8S3dR7R6A4S32S6S13R5R4A4A4M0R2A2S40G0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.

Lemma X_reopen : ltac2:(tb__ "0|7|
S8S8S2eS31S13S13A2A1S2eSd5A1S6S6S14S2eS55Q40A1A1M0S6G0S31S6S13A2M1S0S13SdRbA1S17SffA1A3S56Z0M2R8A2S1S56R9R8A2S56R8Z10A2A2S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2Z3dA2Z1A2A1A2S34S15A1A3A3S16S9ReA1A1A2S30A3S0S2fS1eS9Sf8RfSaRfA1S86RbRaA5A1A1S30A3S0S2fS91S16S9R10A1A1A1S30A3S0S2fSf6S16S9R11A1M3A1RfS60S38S35A1SdcS1bG3A1A6S30A3S0S2fSf7VXGL;S16S9R12A1M4A1R10S60S36S35U0A2S1bG4A1SddSaR12A1A8S30A3S0S8Sf8R13SaR13A1S86RfReA5R12A3ScdS31S31S8S3dA2M5G1A2S32G5G1S32S8S3dR13S3fR12S60R11S3eA4A4RaA4S97A3S1S56G2S40S32G5G1S32S8S3dR14S3fR13S60R12S3eA4A4RbA4RfA2M6A2S58G6RdA2A2VTR;S5cS54VJAv;S3fR14S60R13S3eA4A1R16R10RfA5VFAM;ReRdA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FC;FA;").
Proof.
  intros A C tv bd k1 k2 rho tp b tp0 rv Hbase Hk1 Hk2 Hfe Hwf HB HRO HXL HC HinC Hm.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) rv); [exact HinC | exact Hm]].
  intros w Hw. rewrite <- HC.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG k1 k2 A (ax_X A) rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_E_unp : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S99A1S6dR3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS6dS99A4S32S6S13Z50S96S61Z3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_reopen E_unp0 C_unp tvL (bdL pK pQ) 4 6 rho tp _ tp0 (80, VR pQ 58) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_unp_eq | innth 7 | exact (loop_meas_same rho _ 58 59 E_unp0 C_unp _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))].
Qed.

Lemma XH_X_ok0 : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z26S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa4A1Sb8R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF, tvL, tvI.
  eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_reopen X_ok0 C_ok tvN (bdL pK pX) 8 9 rho tp b tp0 (36, z0) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_ok_eq | innth 24 | rewrite emeas_z0; lia].
Qed.

Lemma reenter_abs : ltac2:(tb__ "0|6|
S8S3dS31S6S13A2M0S14S2eS55Q40A1M1A1M2S6G2Sf2ScdS31S31S8S3dA2M3G0A2S32G3G0S32S8S3dR8R7A4R6A4S97A3Sf3R3R1A1S5S14S14S1S13S0G1S1fR2R1A2M4S1fRaR1A2A3Fe;S5cS54VJAv;RbA1RcR1R8R3A6A2Lrho';A2F_;Fw;S14S13S0G1G4S1fR9R1A2A3Fe;S1S56Z0S40S32G3G0S32S8S3dRcRbA4RaA4R2A2M5A2S58G5R7A2A2F_;Frho';VTR;R4VFAM;R6R5A2A2F_;F_;F_;FP;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FC;").
Proof.
  intros C nd rv rho tp b tp0 P HinC HP Hm. eapply TR_pre; [exact HP|]. apply TR_exw. intros rho'.
  apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. apply (REENTER C nd rv); [exact HinC | exact (Hm rho' HE)].
Qed.
Lemma X_release : ltac2:(tb__ "0|7|
S8S8S2eS18A1M0S6S6S2eS24A1S2dS2eS31S13S13A2A1S2eSd5A1S14S2eS55Q40A1M1A1M2S6G2S31S6S13A2M3S0S13SdReA1S17SffA1A3S56Z0M4RcA2S1S56RdRcA2S56RcZ10A2A2S0S2fS2cRbA1S30A3S0G0S1bS9R12A1A1S3cS18R10S33S18SfbS86RfReRdRcA5S34S18A1A3A3A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2Z3dA2Z1A2A1A2S34S15A1A3A3S16S9R13A1A1A2S30A3S0S2fS42S1aS9R14A1A1S3fRdS60RcS3eA4A2S30A3S0S2fS91S16S9R15A1A1A1S30A3S0S2fSf6S16S9R16A1A1RfS60S38S35A1SdcR14A6S30A3S0S8SfaR17R15Pa0S34S31S6S6A2A1A4R16A3ScdS31S31S8S3dA2M5G3A2S32G5G3S32S8S3dR17S3fR11S60R10S3eA4A4RbA4S97A3S14S13S0G1S1fR2R1A2S1fR12R1A2A3Fe;S1S56G4S40S32G5G3S32S8S3dR1aS3fR14S60R13S3eA4A4ReA4R2A2M6A2S58G6R10A2A2F_;Frho';VTR;S5cS54VJAv;S3fR13S60R12S3eA4A1R1aR11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FC;FA;").
Proof.
  intros A C objs k1 k2 cells d tv bd rho tp b tp0 rv Hbase Hk1 Hk2 Hdw Ho Hfe Hnb HB HRO HC HinC Hm.
  apply (reenter_abs C (NDA tv fr_hl bd ANone) rv rho tp b tp0); [exact HinC | | exact Hm].
  intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG k1 k2 cells d] (vms md tp ms)). split; [intros e; apply eval_absorb|].
  rewrite <- HC.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG k1 k2 cells d A objs [] rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 1) with 128; lia) Hdw Hfe eq_refl Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hl objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.
Lemma XH_X_pro : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z5eS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sc5A1S7bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndP, ndF.
  apply (X_release X_pro C_pre objs_pro 0 16 cells_pro DZero _ _ rho tp b tp0 (92, z0) eq_refl ltac:(lia) ltac:(lia) eq_refl X_pro_objs);
    [vmr|vmr|vmr|vmr| exact C_pre_eq | innth 2 | intros rho' _; rewrite emeas_z0; lia].
Qed.
Lemma XH_X_r2k : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9cA1S72R3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS72S9cA4S32S6S13Z50S96S61Z2eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndK, ndF.
  apply (X_release X_r2k C_rlk objs_r2k 4 6 cells_r2k DUnknown _ _ rho tp _ tp0 (80, VR pQ 45) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2k_objs);
    [vmr|vmr|vmr|vmr| exact C_rlk_eq | innth 18 |].
  intros rho' HE. rewrite (emeas_eq C_rlk _ 80 (VR pQ 45) rho rho' HE).
  exact (loop_meas_same rho _ 45 46 X_r2k C_rlk _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_r2g : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9bA1S71R3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS71S9bA4S32S6S13Z50S96S61Z2eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndG, ndF.
  apply (X_release X_r2g C_rlg objs_r2g 4 6 cells_r2g DUnknown _ _ rho tp _ tp0 (80, VR pQ 45) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2g_objs);
    [vmr|vmr|vmr|vmr| exact C_rlg_eq | innth 19 |].
  intros rho' HE. rewrite (emeas_eq C_rlg _ 80 (VR pQ 45) rho rho' HE).
  exact (loop_meas_same rho _ 45 46 X_r2g C_rlg _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma X_pure : ltac2:(tb__ "0|6|
S8S8S8S8S8S8S3dS2eS113A1S103S2eS18A1M0S14S2eS55Q40A1A1M1G1S6S6S13eRfS33SeS12ReS143A2S34SeA1A3A2S0S37G0A1Se8ReR10R8A3S36G0R7A2A3S0S2fSe9RfR11R9R8S33S8R10S34S8A1A3A5S30A3S0S2fS120S85S1aS9R10A1A1A2S30A3S0S2fS42S1aS9R11A1A1RdA2S30A3S0S2fScfS15S2aS1aS9R12A1M2A1A1S16G2A1A3S30A3S0S8S126S16S9R13A1A1SebRdR15R14R13RcA5A2R12A3S0S37S8A1S112R13RfA2S36S8R12A2A3ScdS31S31S8S3dA2M3S31S6S13A2M4A2S32G3G4S32S8S3dR13R11A4S32S6S13Z50M5S96S61RaA2A4A4S97A3S0S2fS94S61S16S9R16A1A1A2S30A3S0S2fS26S1aS9R17A1A1S88A2S30A3S0S2fS26S1aS9R18A1A1S61A2S30A3S56Z0ReA2S58RfReA2S58RfZ40A2VTR;S5cS54VJAv;R18A1R1cR14R13A5VFAM;S40S32G3G4S32S8S3dR19R18A4S32S6S13G5S96S61R10A2A4A4R14A2R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbpos;Fa;Ftp0;Ftp;Frho;FR;Fs;Fxf2;Fndx;FX0;FT;FT0;FE;FP;FPre;").
Proof.
  intros Pre P E T0 T X0 ndx xf2 s R rho tp tp0 a bpos CALL He Hchk Hnf Hnb Hfb HT0 HT HinT HV HbE HbQ Ha Hab Hb.
  apply TR_facts. intros HF.
  apply (CALL E s R rho tp ndx _ He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [In] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite HT0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf2 rho' T0 T tp w HT Hw)|].
  apply (REENTER T ndx (80, VR pQ a)); [exact HinT|].
  exact (loop_meas rho rho' _ _ a bpos X0 T ndx ndx HF HV (agree_below_vals _ _ _ Hag) HbE HbQ Ha Hab Hb).
Qed.

Lemma XH_E_pc : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S99A1S6cR3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS6cS99A4S32S6S13Z50S96S61Z39A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndJ) E_pc1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 4 6 cells_unp DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_pc1_eq. unfold ndJ, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvL fr_hl (bdL pK pQ) ANone 0%nat 160%positive 1 170%positive hG 4 6 cells_unp DUnknown E_pc0 objs_pc0 [(32, 12)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl E_pc0_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvL fr_hl objs_pc0 rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact (SPA_axforms segs _ xf_pc rho' E_pc1 E_pc tp w E_pc_eq Hw)|].
  rewrite <- (emeas_eq E_pc0 ndJ 80 (VR pQ 57) rho rho' HE).
  apply (X_pure Pre_pc P_ret E_pc T_pc0 T_pc E_pc0 ndJ xf_tpc s_pc R_pc rho' tp tp0 56 57 CALL_pc);
    [vmr|vmr|vmr|vmr|vmr| exact T_pc0_eq | exact T_pc_eq | innth 8 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S99A1S69R3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS69S99A4S32S6S13Z50S96S61Z37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pure Pre_da P_da E_da T_da0 T_da E_da0 ndJ xf_tda s_da R_da rho tp tp0 54 55 CALL_da);
    [vmr|vmr|vmr|vmr|vmr| exact T_da0_eq | exact T_da_eq | innth 9 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma X_epi : ltac2:(tb__ "0|8|
S8S8S2eS31S13S13A2A1S2eSd5A1S14S2eS55Q40A1A1M0S6G0S6S0S13SdR9A1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2M1Z3dA2Z1M2A2A1A2S34S15A1A3A3S16S9RaA1A1A2S30A3S0S2fS1eS9Sf8RbSaRbA1S86Z0M3Z10A5A1A1S30A3S0S2fS1eS9S98RcA1A1A1S30A3S0S2fS91S16S9RdA1A1A1S30A3S0S2fS93S16S9ReA1A1A1S30A3S0S2fSf6S16S9RfA1M4A1RdS60S38S35A1SdcS1bG4A1A6S30A3S0S2fSf7VXGL;S16S9R10A1M5A1ReS60S36S35U0A2S1bG5A1SddSaR10A1A8S30A3S0S8S98R11A1R10A3ScdS31S31S8S3dA2M6S31S6S13A2M7A2S32G6G7S32S8S3dR11S3fR10S60RfS3eA4A4S32S6S13RaS9dA4A4S97A3S56G3RbA2S56S59S5bRcG2A2S57G1Z40A2A2ReA2VTR;S5cS54VJAv;S3fR13S60R12S3eA4A1R15R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FY;").
Proof.
  intros Y C tv bd rho tp b tp0 rk Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia]].
  intros w Hw. rewrite <- HC. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_E_da2 : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z26S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa4A1SabR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da2 E_da2x tp w E_da2x_eq Hw)|].
  apply (CALL_da E_da2x s_da2 R_da2 rho tp ndN _); [vmr|vmr|vmr|vmr|vmr|].
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite T_da2_eq.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_tda2 rho' T_da2 Y_few tp w Y_few_eq Hw)|].
  unfold ndN, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_epi Y_few C_few tvN (bdL pK pX) rho' tp b tp0 30); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_few_eq | innth 23 | lia | lia].
Qed.

Lemma Forall_single : forall {A} (P : A -> Prop) a l, Forall P (a :: l) -> Forall P [a].
Proof. intros A P a l H. constructor; [exact (Forall_inv H) | constructor]. Qed.
Lemma tvd_single : ltac2:(tb__ "0|1|
S14S31S13S13A2M0S107R2S33G0R1S34G0A1A3A2Ft;Frho;"). Proof. intros rho t. cbn. split; [intros t' [] | exact I]. Qed.

Lemma HIN_v : ltac2:(tb__ "0|2|
S14S10dSfcS14S2eS55Q40A1A1SeeSd0S15S1dR6A1S16S9S77A1A1A3S90VCST;VFB;VFF;Vrho0;A4Sf0S85Vrho0;R8A3VAInv;R7R6R5R4A4S43Vrho0;R8A2S109RbSfeSfdR9A1A1A2S46VFB;RaA2S47VFF;RbA2S45VFB;RcReS9fA4S107RfS9fA2S108R10S9fA2S44VFF;RfR11S60A4S1S11cVCST;Vrho0;VFB;VFF;R12S33S31S13S13A2M0S32S13S13S8aS89Z4S8bA2A4S34G0A1A3M1S60S70A8S1S11dVCST;VXGL;Vrho0;VFB;VFF;R12G1S60S7cA9S118S10aVFB;R12G1A3S119VFF;R12S60A3S105S104R12S70R11A3S82A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (lc_d, kb 4 lc_k)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(lc_d, kb 4 lc_k)] fr_hl None extraOH R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(lc_d, kb 4 lc_k)] fr_hl None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR ltac:(vmr))).
  - unfold VNP.P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with pK. change (wsub_get s_v 15) with pD. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with (xbo 624).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply Forall_inv_tail in HZ. apply (tvz_kd rho 12 pD pK [] HZ); [lia | unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E624 : uval rho (xbo 624) = uval rho vb + 624) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E624, H1, H2. rewrite E624. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S99A1S6eR3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS6eS99A4S32S6S13Z50S96S61Z34A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndJ) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndJ, ndF, tvL, tvI.
  change [(lc_d, kb 4 lc_k); (pD, kb 12 pK)] with ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E_vr s_v R_v Xk_v rho tp [(lc_d, kb 4 lc_k)] [(pD, kb 12 pK)] fr_hl (bdL pK pQ) bdX ANone (FAM (emeasA (E_vr0, ndJ, (80, VR pQ 52)) rho) tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. change ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]) with tvL. change ([PHIN pQ pK; KLG pK] ++ bdX) with (bdJK pK).
      eapply TR_pre; [|apply (REENTER T_keep ndK (80, VR pQ 51)); [innth 11 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_keep ndJ ndK HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ pK HF2); vmr.
      * assert (TNZ : tnz rho' (pD, kb 12 pK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle pC1 pK) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle pC pK) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' pC) as RC.
          unfold pC1 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. cbn [nd_tv] in HZ'. apply Forall_inv_tail in HZ'.
          apply (tvz_kd rho' 12 pD pK [] HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (pD, kb 12 pK) eq_refl HJ (or_intror (or_introl eq_refl)) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]) with tvL. change (bd_subst _ [] ++ bdX) with bdX.
      apply (REENTER T_fail0 ndX (30, z0)); [innth 13|]. rewrite emeas_z0. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho (VR pQ 52))). lia.
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. change ([(lc_d, kb 4 lc_k)] ++ [(vDg, kb 12 vKg)]) with tvG. change ([PHIN pQ vKg; KLG vKg] ++ bdX) with (bdJK vKg).
      eapply TR_pre; [|apply (REENTER T_grown ndG (80, VR pQ 51)); [innth 12 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_grown ndJ ndG HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma HIN_v2 : ltac2:(tb__ "0|2|
S14S10dSfcS14S2eS55Q40A1A1SeeSd0S15S1dR6A1S16S9SaeA1A1A3S90VCST;VFB;VFF;Vrho0;A4Sf0S85Vrho0;R8A3VAInv;R7R6R5R4A4S43Vrho0;R8A2S109RbSfeSfdR9A1A1A2S46VFB;RaA2S47VFF;RbA2S45VFB;RcReS9aA4S107RfS9aA2S108R10S9aA2S44VFF;RfR11S60A4S1S11cVCST;Vrho0;VFB;VFF;R12S33S31S13S13A2M0S32S13S13S63S89ZcS62A2A4S34G0A1A3M1S60Sa3A8S1S11dVCST;VXGL;Vrho0;VFB;VFF;R12G1S60SbbA9S118S10aVFB;R12G1A3S119VFF;R12S60A3S105S104R12Sa3R11A3Sc6A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vc)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (pD, kb 12 pK)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(pD, kb 12 pK)] fr_hl None extraOH R_v2 rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(pD, kb 12 pK)] fr_hl None (ss_objs (ax_S E_vc)) Xk_v2 rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR ltac:(vmr))).
  - unfold VNP.P0_vr. rewrite !rw_call'.
    change (wsub_get s_v2 17) with lc_k. change (wsub_get s_v2 15) with lc_d. change (wsub_get s_v2 14) with vAL. change (wsub_get s_v2 12) with (xbo 656).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle lc_k (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply Forall_inv_tail in HZ. apply (tvz_kd rho 4 lc_d lc_k [] HZ); [lia | unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E656 : uval rho (xbo 656) = uval rho vb + 656) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E656, H1, H2. rewrite E656. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vc : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z22S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sc4A1SafR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndNs) E_vc1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 8 9 cells_vc DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_vc1_eq. unfold ndNs, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvN fr_hl (bdL pK pX) ANone 0%nat 160%positive 1 170%positive hG 8 9 cells_vc DUnknown E_vc0 objs_vc0 [(64, 4)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl E_vc0_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvN fr_hl objs_vc0 rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact (SPA_axforms segs _ xf_vc rho' E_vc1 E_vc tp w E_vc_eq Hw)|].
  clear HE. apply TR_facts. intros HF. unfold ndNs, ndF, tvN, tv_hl.
  change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E_vc s_v2 R_v2 Xk_v2 rho' tp [(pD, kb 12 pK)] [(lc_d, kb 4 lc_k)] fr_hl (bdL pK pX) bdX2 ANone (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v2 rho' ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [Ld ndL] rho2 tp' Hd Hag. cbn [PD_vr PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    +
      rewrite T_keep2_0_eq, imp_keep2_tv, imp_keep2_bd. change ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]) with tvN. change (bd_vec 4 lcn1 lc_k ++ bdX2) with (bdO lc_k).
      eapply TR_pre; [|apply (REENTER T_keep2 ndO (32, z0)); [innth 25 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_keep2_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot4_holds rho2 _ lc_k HF2); vmr.
      * assert (TNZ : tnz rho2 (lc_d, kb 4 lc_k)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle lcc1 lc_k) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle lc_k (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle lc_c lc_k) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho2 lc_c) as RC.
          unfold lcc1 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. cbn [nd_tv] in HZ'. apply Forall_inv_tail in HZ'.
          apply (tvz_kd rho2 4 lc_d lc_k [] HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (lc_d, kb 4 lc_k) eq_refl HJ (or_intror (or_introl eq_refl)) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail2_eq, imp_fail2_tv. change ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]) with tvN. change (bd_subst _ [] ++ bdX2) with bdX2.
      apply (REENTER T_fail2 ndX2 (32, z0)); [innth 27 | rewrite emeas_z0; lia].
    +
      rewrite T_grown2_0_eq, imp_grown2_tv, imp_grown2_bd. change ([(pD, kb 12 pK)] ++ [(vDg, kb 4 vKg)]) with tvN2. change (bd_vec 4 lcn1 vKg ++ bdX2) with (bdO vKg).
      eapply TR_pre; [|apply (REENTER T_grown2 ndOg (32, z0)); [innth 26 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_grown2_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot4_holds rho2 _ vKg HF2); vmr.
Qed.

Lemma X_E_mc : ltac2:(tb__ "0|a|
S8S8S8S8S2eS113A1S18S13S13S6S3dS103S2eS18A1M0S14S2eS55Q40A1A1M1S6G1S31S6S13A2M2S1S56Z0M3R9A2S56R9ZcA2A2S0S4dS50R9A1S3eA3S0S2eS31S31S13S6A2S13A2A1S51RaA1S60A3S0S37S8A1S112R14R10A2S36S8R13A2A3S0S37S18A1SceS18S1bS9R14A1A1U4M4A3S36S18S25RfReS22S101ReS17RdA1A3S34S24A1M5S23A5A2A3S0S18R11S25S22S101R10RfA3S17G3A1S17ReA1G5S23A5A3S0S2fS27S1aS9R16A1A1R12A2S30A3S0S2fSccS15S1cS19R12S17Z800000000000A1A2A1S16S9R17A1A1A3S30A3S0S2fSccS15S1cS19R12S17S102A1A2A1S16S9R18A1A1A3S30A3S0S8S81R19G4R15A3R18A3S0S37G0A1Se8R19S66R11A3S36G0R10A2A3S0S2fSeaR1aS66R12R11S33S8S65S33S8S65S34S8A1A3A3A5S30A3S0S2fS12cS85R13A2S30A3S0S2fS120S85S1aS9R1cA1A1A2S30A3S0S2fS42S1aS9R1dA1A1R16A2S30A3S0S2fSd8S1aS9R1eA1A1S49R17A1A2S30A3S0S2fSd6S49R18A1A1S30A3S0S2fS91S16S9R20A1A1A1S30A3S0S2fS125S16S9R21A1A1S4aR1aA1S60S38S35A1M6SdcR18A6S30A3S0S2fSf7VXGL;S16S9R22A1M7A1S4aR1bA1S60G6S1bG7A1SddSaR22A1A8S30A3S0S8S12bS66R23R1bR1aS65A5R22A3ScdS31S31S8S3dA2M8G2A2S32G8G2S32S8S3dR23R1dA4R16A4S97A3Sd0S15S1dR1bA1S16S9R25A1A1A3S14Sf0S1aS9R27A1A1R1dR1A3S1S56G3S40S32G8G2S32S8S3dR27R21A4R1aA4R2A2M9A2S58G9R1cA2A2F_;Frho';F_;VTR;S5cS54VJAv;R1fA1R28R1cR1bA5VFAM;R1aR19A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;FR;Fs;Fnd;Fw;Fcm;Fd;Fdob;Fxf;FT;FE;FE1;FE0;").
Proof.
  intros E0 E1 E T xf dob d cm w nd s R rho tp b tp0 rv Hw Ham Hfr HE1 H4 Hdob Hwf4 Hd Hs HE He Hchk Htp Hnf Hnb Hbb Hwp HB HR HX HT HinT Hm.
  destruct nd as [tv fr bd am]. cbn [nd_tv nd_fr nd_bd nd_am] in *. subst am fr. subst dob.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hl bd ANone)) E rho tp).
  { intros w0 Hw0. pose proof (SPA_axforms segs _ xf rho E0 E1 tp w0 HE1 Hw0) as Hw1. rewrite <- HE. unfold reshapeA.
    apply (SPA_reshape segs _ rho E1 4 _ _ tp w0 H4); [reflexivity | reflexivity | reflexivity | exact Hwf4 | | exact Hw1].
    intros HF. destruct (slot_rng rho _ d cm w Hw HF Hd Hs) as (A1 & A2 & A3).
    unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d cm))) with (uval rho (SAlu ALU_ADD d cm)). rewrite A1. unfold uval. lia. }
  apply TR_facts. intros HF.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E s R rho tp (NDA tv fr_hl bd ANone) bd (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMCPY Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnf.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact (site_pure E s R rho tv fr_hl bd HB HR HX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc s R rho tp tr ms md Hsm HM HX' ltac:(first [assumption | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])).
  - intros L rho' tp' HL Hag. cbn [In] in HL. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HT.
    apply (REENTER T (NDA tv fr_hl bd ANone) rv); [exact HinT|]. exact (Hm HF rho' Hag).
Qed.
Lemma XH_E_mk : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9cA1S6bR3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS6bS9cA4S32S6S13Z50S96S61Z32A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (X_E_mc E_mk0 (E_mc1 E_mk0) E_mk T_mck xf_mc (dst_obj pD) pD (cmul12 pC) 12 ndK (s_mc E_mk pD pK) R_mk rho tp _ tp0 (80, VR pQ 49) ltac:(lia) eq_refl eq_refl E_mk1_eq);
    [vmr| reflexivity |vmr|vmr|vmr| exact E_mk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mck_eq | innth 14 |].
  intros HF rho' Hag. exact (loop_meas rho rho' _ _ 49 50 E_mk0 T_mck _ _ HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_E_mg : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9bA1S6aR3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS6aS9bA4S32S6S13Z50S96S61Z32A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (X_E_mc E_mg0 (E_mc1 E_mg0) E_mg T_mcg xf_mc (dst_obj vDg) vDg (cmul12 pC) 12 ndG (s_mc E_mg vDg vKg) R_mg rho tp _ tp0 (80, VR pQ 49) ltac:(lia) eq_refl eq_refl E_mg1_eq);
    [vmr| reflexivity |vmr|vmr|vmr| exact E_mg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mcg_eq | innth 15 |].
  intros HF rho' Hag. exact (loop_meas rho rho' _ _ 49 50 E_mg0 T_mcg _ _ HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_E_m2k : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1eS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa5A1SadR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_mc E_m2k0 (E_mc21 E_m2k0) E_m2k T_m2k xf_mc2 (dst4_obj lc_d) lc_d (cmul4 lc_c) 4 ndO (s_mc2 E_m2k lc_d lc_k) R_m2k rho tp b tp0 (28, z0) ltac:(lia) eq_refl eq_refl E_m2k1_eq);
    [vmr| reflexivity |vmr|vmr|vmr| exact E_m2k_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_m2k_eq | innth 28 |].
  intros _ rho' _. rewrite emeas_z0. lia.
Qed.
Lemma XH_E_m2g : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1eS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa6A1SacR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_mc E_m2g0 (E_mc21 E_m2g0) E_m2g T_m2g xf_mc2 (dst4_obj vDg) vDg (cmul4 lc_c) 4 ndOg (s_mc2 E_m2g vDg vKg) R_m2g rho tp b tp0 (28, z0) ltac:(lia) eq_refl eq_refl E_m2g1_eq);
    [vmr| reflexivity |vmr|vmr|vmr| exact E_m2g_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_m2g_eq | innth 29 |].
  intros _ rho' _. rewrite emeas_z0. lia.
Qed.

Lemma X_cm : ltac2:(tb__ "0|a|
S8S8S8S13S13S2eS31S13S13A2A1S2eSd5A1S14S2eS55Q40A1A1M0G0S0S37S18A1SceS18S1bS9RaA1A1U1A3S36S18S25S22S101R7S7dS75A1M1A3S17Z0A1S17ZcA1S34S24A1S23A5A2A3S0S2fS27S1aS9RbA1A1S7eR8A1A2S30A3S0S2fSccS15S1cS19R9S17Z800000000000A1A2A1S16S9RcA1A1A3S30A3S0S2fSccS15S1cS19G1S17S102A1A2A1S16S9RdA1A1A3S30A3S0S37S8A1S112S13cReRbA2S84A2S36S8RdA2A3S0S13SdReA1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2Z3dA2Z1A2A1A2S34S15A1A3A3S16S9RfA1A1A2S30A3S0S2fS11bS64ReRdS8aS8bA4SaR10A1A2S30A3S0S2fS1eS9Sf8R11S64RfReS8aS8bA4S86Z4M2Z6M3A5A1A1S30A3S0S2fS91S16S9R12A1A1A1S30A3S0S2fSf6S16S9R13A1M4A1RfS60S38S35A1SdcS1bG4A1A6S30A3S0S2fSf7VXGL;S16S9R14A1M5A1R10S60S36S35U0A2S1bG5A1SddS64R12R11S8aS8bA4A8S30A3S0S8Sf8R15S64R13R12S8aS8bA4S86G2G3A5R14A3ScdS31S31S8S3dA2M6S31S6S13A2M7A2S32G6G7S32S8S3dR15S3fR12S60R11S3eA4A4S32S6S13Z50M8S96S61Z2fA2A4A4S97A3S0S2fS94S61S16S9R18A1A1A2S30A3VTR;S5cS54VJAv;S3fR14S60R13S3eA4M9A1R19R12R11A5VFAM;S40S32G6G7S32S8S3dR19G9A4S32S6S13G8S96S61Z30A2A4A4R12A2R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Ftp;Frho;Fbd;Ftv;Fk;Fd;FC;FY;FX;").
Proof.
  intros X Y C d k tv bd rho tp tp0 H1 Hwf1 Hd Hs HY Hbase Hfe HXi Hwf HB HRO HXL HC HinC HV.
  apply TR_facts. intros HF.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) (80, VR pQ 47)); [exact HinC | exact (loop_meas_same rho _ 47 48 X C _ _ HF HV ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. rewrite <- HC.
  assert (Hw1 : SPA segs (JAv (NDA tv fr_hl bd ANone)) (cm1 X d) rho tp w).
  { unfold cm1, reshapeA. apply (SPA_reshape segs _ rho X 1 _ _ tp w H1); [reflexivity | reflexivity | reflexivity | exact Hwf1 | | exact Hw].
    intros HF'. destruct (slot_rng rho _ d (cmul12 pC) 12 ltac:(lia) HF' Hd Hs) as (A1 & A2 & A3).
    unfold mid_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (cmul12 pC)))) with (uval rho (SAlu ALU_ADD d (cmul12 pC))). rewrite A1. unfold uval. lia. }
  pose proof (SPA_axforms segs _ xf_cm rho (cm1 X d) Y tp w HY Hw1) as Hw2.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 4 6 Y (X_hl d k lc_d lc_k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
           ltac:(change (fs_frame_size 1) with 128; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw2].
  intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_X_rpk : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9cA1S74R3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS74S9cA4S32S6S13Z50S96S61Z30A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndK, ndF.
  apply (X_cm X_rpk Y_rpk C_mk pD pK _ _ rho tp tp0); [vmr|vmr|vmr|vmr| exact Y_rpk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mk_eq | innth 16 | vmr].
Qed.
Lemma XH_X_rpg : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0G0VTR;S5cS54VJAv;S9bA1S73R3R2A5VFAM;S40S32S31S8S3dA2S31S6S13A2S32S8S3dS73S9bA4S32S6S13Z50S96S61Z30A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndG, ndF.
  apply (X_cm X_rpg Y_rpg C_mg vDg vKg _ _ rho tp tp0); [vmr|vmr|vmr|vmr| exact Y_rpg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mg_eq | innth 17 | vmr].
Qed.

Lemma X_arr : ltac2:(tb__ "0|9|
S8S8S8S8S2eS113A1S2eS31S13S13A2A1M0G0S2eSd5A1S14S2eS55Q40A1A1M1S6G1S6S0S37S8A1S112RdR9A2S36S8RcA2A3S0S2fS11bR9SaRdA1A2S30A3S0S8S128ReRaA2RdA3S0G0SaReA1RbA3S0S13SdRfA1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2M2Z3dA2Z1M3A2A1A2S34S15A1A3A3S16S9R10A1A1A2S30A3S0S2fS1eS9Sf8R11SaR11A1S86Z0M4Z10A5A1A1S30A3S0S2fS1eS9S98R12A1A1A1S30A3S0S2fS91S16S9R13A1A1A1S30A3S0S2fS93S16S9R14A1A1A1S30A3S0S2fSf6S16S9R15A1M5A1R11S60S38S35A1SdcS1bG5A1A6S30A3S0S2fSf7VXGL;S16S9R16A1M6A1R12S60S36S35U0A2S1bG6A1SddSaR16A1A8S30A3S0S8S98R17A1R16A3ScdS31S31S8S3dA2M7S31S6S13A2M8A2S32G7G8S32S8S3dR17S3fR14S60R13S3eA4A4S32S6S13ReS9dA4A4S97A3S56G4RfA2S56S59S5bR10G3A2S57G2Z40A2A2R12A2VTR;S5cS54VJAv;S3fR17S60R16S3eA4A1R1dR15R14A5VFAM;R13R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FXc;Fxf;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C xf Xc tv bd rho tp b tp0 rk HZ HXZ HY HXY Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hl bd ANone)) Y rho tp).
  { intros w Hw. rewrite <- HY. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ HXZ)|]. exact (SPA_axforms segs _ xf rho X Z tp w HZ Hw). }
  apply (X_epi Y C tv bd rho tp b tp0 rk Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb).
Qed.
Lemma XH_X_fp0 : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1cS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa7A1Sb6R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_arr X_fp0 Z_fp0 Y_fp0 C_fa0 xf_f (X_hl pD pK lc_d lc_k) tvN bdX rho tp b tp0 26 Z_fp0_eq); [vmr| exact Y_fp0_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fa0_eq | innth 20 | lia | lia].
Qed.
Lemma XH_X_fp1 : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1cS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa7A1Sb7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_arr X_fp1 Z_fp1 Y_fp1 C_fa1 xf_f (X_hl pD pK lc_d lc_k) tvN bdX rho tp b tp0 26 Z_fp1_eq); [vmr| exact Y_fp1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fa1_eq | innth 21 | lia | lia].
Qed.

Lemma X_e8 : ltac2:(tb__ "0|8|
S8S8S8S8S13S13S2eSd5A1S14S2eS55Q40A1A1M0S6G0S0S37S18A1SceS18S1bS9RbA1A1U1A3S36S18S25S22S101R7SbdS8dA1M1A3S17Z0M2A1S17Z4A1S34S24A1S23A5A2A3S0S2fS27S1aS9RcA1A1Sc0R8A1A2S30A3S0S2fSccS15S1cS19R9S17Z800000000000A1A2A1S16S9RdA1A1A3S30A3S0S2fSccS15S1cS19G1S17S102A1A2A1S16S9ReA1A1A3S30A3S0S37S8A1S112S13dRfRbA2ScaA2S36S8ReA2A3S0S2fS11bS64S63S62RcRbA4SaRfA1A2S30A3S0S8S128R10S64S63S62RdRcA4A2RfA3S0S2eS31S13S13A2A1SaR10A1S64S63S62ReRdA4A3S0S13SdR11A1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2M3Z3dA2Z1A2A1A2S34S15A1A3A3S16S9R12A1A1A2S30A3S0S2fS1eS9Sf8R13SaR13A1S86G2Z10A5A1A1S30A3S0S2fS1eS9S98R14A1A1A1S30A3S0S2fS91S16S9R15A1A1A1S30A3S0S2fS93S16S9R16A1A1A1S30A3S0S2fSf6S16S9R17A1M4A1S67S63S62R15R14A4S60S38S35A1SdcS1bG4A1A6S30A3S0S2fSf7VXGL;S16S9R18A1M5A1S67S63S62R16R15A4S60S36S35U0A2S1bG5A1SddSaR18A1A8S30A3S0S8S98R19A1R18A3ScdS31S31S8S3dA2M6S31S6S13A2M7A2S32G6G7S32S8S3dR19S3fS67S63S62R18R17A4S60R16S3eA4A4S32S6S13Z18S9dA4A4S97A3S56S59Z1aS57G3Z40A2A2R14A2VTR;S5cS54VJAv;S3fS67S63S62R1aR19A4S60R18S3eA4A1R1eR17R16A5VFAM;R15R14A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fbd;Fk2;Fd2;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C d2 k2 bd rho tp b tp0 H1 Hwf1 Hd Hs HZ HXZ HY HXY Hbase Hfe Hwf2 Hwf3 HB HFRF HRO HXL HC HinC Hb.
  apply TR_facts. intros HF.
  eapply TR_pre with (P := SPA segs (JAv (NDA (tv_hl pD pK d2 k2) fr_hl bd ANone)) (cm2 X d2) rho tp).
  { intros w Hw. unfold cm2, reshapeA. apply (SPA_reshape segs _ rho X 1 _ _ tp w H1); [reflexivity | reflexivity | reflexivity | exact Hwf1 | | exact Hw].
    intros HF'. destruct (slot_rng rho _ d2 (cmul4 lc_c) 4 ltac:(lia) HF' Hd Hs) as (A1 & A2 & A3).
    unfold mid4_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d2 (cmul4 lc_c)))) with (uval rho (SAlu ALU_ADD d2 (cmul4 lc_c))). rewrite A1. unfold uval. lia. }
  apply (X_arr (cm2 X d2) Z Y C xf_e8 (X_hl pD pK d2 k2) (tv_hl pD pK d2 k2) bd rho tp b tp0 24 HZ HXZ HY HXY Hbase Hfe Hwf2 Hwf3 HB HFRF HRO HXL HC HinC ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_e8k : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1aS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa5A1Sb1R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndO, ndF, tvN.
  apply (X_e8 X_e8k Z_e8k Y_e8k C_e8k lc_d lc_k (bdO lc_k) rho tp b tp0); [vmr|vmr|vmr|vmr| exact Z_e8k_eq |vmr| exact Y_e8k_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_e8k_eq | innth 30 | exact Hb].
Qed.
Lemma XH_X_e8g : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1aS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa6A1Sb0R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndOg, ndF, tvN2.
  apply (X_e8 X_e8g Z_e8g Y_e8g C_e8g vDg vKg (bdO vKg) rho tp b tp0); [vmr|vmr|vmr|vmr| exact Z_e8g_eq |vmr| exact Y_e8g_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_e8g_eq | innth 31 | exact Hb].
Qed.
Lemma XH_X_f2a : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1aS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa8A1Sb2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX2, ndF.
  apply (X_arr X_f2a Z_f2a Y_f2a C_f2a xf_f2 (X_hl pD pK lc_d lc_k) tvN bdX2 rho tp b tp0 24 Z_f2a_eq); [vmr| exact Y_f2a_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_f2a_eq | innth 32 | lia | lia].
Qed.
Lemma XH_X_f2b : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z1aS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sa8A1Sb3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX2, ndF.
  apply (X_arr X_f2b Z_f2b Y_f2b C_f2b xf_f2 (X_hl pD pK lc_d lc_k) tvN bdX2 rho tp b tp0 24 Z_f2b_eq); [vmr| exact Y_f2b_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_f2b_eq | innth 33 | lia | lia].
Qed.

Lemma epi_glue : ltac2:(tb__ "0|2|
S8S2eS31S13S13A2A1S2eSd5A1S14S2eS55Q40A1A1Sf3S0S13SdR6A1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2Z3dA2Z1A2A1A2S34S15A1A3A3S16S9R7A1A1A2S30A3S0S2fS1eS9Sf8R8SaR8A1S86Z0Z10A5A1A1S30A3S0S2fS1eS9S98R9A1A1A1S30A3S0S2fS91S16S9RaA1A1A1S30A3S0S2fS93S16S9RbA1A1A1S30A3S0S2fSf6S16S9RcA1M0A1RbS60S38S35A1SdcS1bG0A1A6S30A3S0S2fSf7VXGL;S16S9RdA1M1A1RcS60S36S35U0A2S1bG1A1SddSaRdA1A8S30A3S5cS54VJAv;S3fRdS60RcS3eA4A1ReRbRaR9A6S5cS54VJAv;S3fReS60RdS3eA4A1S98RfA1RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fbd;Ftv;FY;").
Proof.
  intros Y tv bd rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL Hw. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma X_f7 : ltac2:(tb__ "0|6|
S8S8S103S14S2eS55Q40A1A1M0S6G0S0S13SdR7A1S17SffA1A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2M1Z3dA2Z1A2A1A2S34S15A1A3A3S16S9R8A1A1A2S30A3S0S2fS1eS9Sf8R9SaR9A1S86Z0Z10M2A5A1A1S30A3S0S2fS1eS9S98RaA1A1A1S30A3S0S2fS91S16S9RbA1A1A1S30A3S0S2fS93S16S9RcA1A1A1S30A3S0S2fSf6S16S9RdA1M3A1S9aS60S38S35A1SdcS1bG3A1A6S30A3S0S2fSf7VXGL;S16S9ReA1M4A1S9aS60S36S35U0A2S1bG4A1SddSaReA1A8S30A3S0S8S98RfA1ReA3S0S103S142S85S9RfA1S9Sa0A1A3ReA3S0S2fS11R10Sa0RfA3S30A3S0S2fS106R10S85A2S30A3S0S2fS120S85S1aS9R12A1A1A2S30A3S0S2fS42S1aS9R13A1A1Sc3S9aSbcS62S80A2M5A2A2S30A3S0S2fS10cR13S9aSc9A3S30A3S0S2fS4eR14S60S60A3S30A3S0S2fSdaS16S9R16A1A1Sd9R15S33Sd5S8eZ48ScbA2S34Sd5A1A3A2G5A3S30A3S56S59G2S57G1Z40A2A2R13A2VTR;S5cS54VJAv;S9eA1R19R16R15A5VFAM;R14R13A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FZ;FX;").
Proof.
  intros X Z s rho tp b tp0 Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HZ Hs He Hid Hnp Hnb Htv Hfr Hbd Hb.
  unfold ndT, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  eapply TR_pre; [|apply (REENTER C_epf ndEf (14, z0) (rho_sub rho s)); [innth 34 | rewrite emeas_z0; lia]].
  intros w Hw. unfold ndEf, ndF.
  apply (SPA_entails_JA segs AInv CST XGL ALA NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc Z C_epf s (NDA tvN fr_hl (bdL pK pT0) ANone) (NDA tvY fr_hl [PROG 72 yCUR] ANone) rho tp w
           He Hid Hnp Hnb Htv Hfr Hbd eq_refl).
  rewrite <- HZ. exact (epi_glue X tvN (bdL pK pT0) rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL Hw).
Qed.
Definition s_f7a : wsub := Eval vm_compute in infer_sub NPH (ax_S Z_f7a) (ax_S C_epf).
Definition s_f7b : wsub := Eval vm_compute in infer_sub NPH (ax_S Z_f7b) (ax_S C_epf).
Lemma XH_X_f7a : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z10S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;S9eA1Sb4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_f7 X_f7a Z_f7a s_f7a rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Z_f7a_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Hb].
Qed.
Lemma XH_X_f7b : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z10S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;S9eA1Sb5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_f7 X_f7b Z_f7b s_f7b rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Z_f7b_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|7|
S8S8S8S2eS31S13S13A2A1S2eSd5A1S14S2eS55Q40A1A1M0S6G0S6S0S37S8A1S112RaS33S113S114Sc7A1S34S113A1A3A2S36S8R9A2A3S0S8S10RaS144S9RaA1M1Sd2S18U15M2S1bG1A1A3A2A2R9A3S0S2fSf9Pa0PaaS86Z1M3Sd3S18G2S1bS9RbA1A1A3A5S30A3S0S2fScS33S15S20SbS86A1S87A2S33S15S19S21S86A1S17S5aS57Z2M4Z3dA2G3A2A1A2S34S15A1A3A3S16S9RcA1A1A2S30A3S0S2fS42S1aS9RdA1A1S3fRbS60RaS3eA4A2S30A3ScdS31S31S8S3dA2M5S31S6S13A2M6A2S32G5G6S32S8S3dRdS3fRcS34S31S31S13S6A2S13A2A1RbS3eA4A4S32S6S13R6S9dA4A4S97A3S56Z0R7A2S56S59S5bR8G3A2S57G4Z40A2A2RaA2VTR;S5cS54VJAv;S3fRfS60ReS3eA4A1R12RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 21 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 21 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 21 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hl).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG X1 (firstn 21 (ss_objs (ax_S X1))) (skipn 21 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rlo : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59ZcS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sc2A1SbaR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEo, ndF. apply (X_X_rl X_rlo _ C_rlo _ _ rho tp b tp0 10 X_rlo_eq); [vmr|vmr|vmr|vmr| innth 37 | lia | lia].
Qed.
Lemma XH_X_rlf : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59ZcS57Z2Z40A2A2R2A2VTR;S5cS54VJAv;Sc1A1Sb9R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEf, ndF. apply (X_X_rl X_rlf _ C_rlf _ _ rho tp b tp0 10 X_rlf_eq); [vmr|vmr|vmr|vmr| innth 36 | lia | lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0S56S59Z62S57Z2Z40A2A2R2A2VTR;S5cS54VJAv;S68A1S76R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd0, ND, tv_hl. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|].
  change (NDA [(lc_d, kb 4 lc_k); (li_d, kb 12 li_k)] [] (bd_hl li_n li_k lc_n lc_k tI) ANone) with nd0'.
  apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           1 E_sm0 s_sm R_sm rho tp nd0' 160 170 (FAM b tp0) CSM).
  - lia.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - intros A A' _; exact I.
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & HC0).
    cbn [nd_tv nd_fr nd0' ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tvI li_d li_k lc_d lc_k) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tvI li_d li_k lc_d lc_k) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 96); rewrite uval_lit by lia; change (fs_frame_size 1) with 128; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tvI li_d li_k lc_d lc_k) fr_hl (bd_hl li_n li_k lc_n lc_k tI) ANone 0%nat 160 1 170
                  T_sm1 objs_sm1 (X_hl li_d li_k lc_d lc_k) [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tvI li_d li_k lc_d lc_k) fr_hl (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hl li_d li_k lc_d lc_k) rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0VTR;S5cS54VJAv;SaaA1Sa2R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S14S2eS55Q40A1A1M0S6G0VTR;S5cS54VJAv;Sa9A1Sa1R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S8S3dS31S6S13A2M0S14S2eS55Q40A1A1M1G1ScdS31S31S8S3dA2M2G0A2S32G2G0S32S8S3dR6R5A4R4A4SbeA3VTR;S5cS54VJAv;R6A1R7R4R3A5VFAM;S40S32G2G0S32S8S3dR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsL] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_unp.
  - apply XH_E_pc.
  - apply XH_E_da.
  - apply XH_E_vr.
  - apply XH_E_mk.
  - apply XH_E_mg.
  - apply XH_X_rpk.
  - apply XH_X_rpg.
  - apply XH_X_r2k.
  - apply XH_X_r2g.
  - apply XH_X_fp0. rewrite emeas_z0. lia.
  - apply XH_X_fp1. rewrite emeas_z0. lia.
  - apply XH_X_f7a. rewrite emeas_z0. lia.
  - apply XH_X_f7b. rewrite emeas_z0. lia.
  - apply XH_X_ok0. rewrite emeas_z0. lia.
  - apply XH_E_da2. rewrite emeas_z0. lia.
  - apply XH_E_vc. rewrite emeas_z0. lia.
  - apply XH_E_m2k. rewrite emeas_z0. lia.
  - apply XH_E_m2g. rewrite emeas_z0. lia.
  - apply XH_X_e8k. rewrite emeas_z0. lia.
  - apply XH_X_e8g. rewrite emeas_z0. lia.
  - apply XH_X_f2a. rewrite emeas_z0. lia.
  - apply XH_X_f2b. rewrite emeas_z0. lia.
  - apply XH_X_rlf. rewrite emeas_z0. lia.
  - apply XH_X_rlo. rewrite emeas_z0. lia.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S53S54VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S137S54S132VAInv;VCST;VXGL;A5").

Theorem handle_l_sum : ltac2:(tb__ "0|0|
S2eS55Q40A1A1Sf5S54Vok;S5cS54S48VAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41S68AaS6fVrho0;R1A5Se7S54S85Vrho0;R1S10fA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA FUEL_hl cutpcs_hl NPH
                (map edropA cutsL) (map edropA exitsL) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertL_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsL)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 1 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ok (map edropA cutsL) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_hl CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S138S54S132VAInv;VCST;VXGL;A5").

Theorem handle_l_sum_ex : ltac2:(tb__ "0|0|
S2eS55Q40A1A1Sf4S54S5cS54S48VAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S41S68AaS6fVrho0;R1A5Se7S54S85Vrho0;R1S10fA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA FUEL_hl cutpcs_hl NPH cutsL exitsL (Q tp0) ejcertL_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue) cutsL) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 1 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue cutsL T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_hl CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

End Lib_handle_l_pf.

(* [comment removed for export] *)
Module Lib_load_obj_al_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "bitem"; "ASv"; "BI"; "AMin"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "ss_facts"; "ss_next"; "SLit"; "SAlu"; "SPUle"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_load_obj_al_eqs"; "s_latch_l"; "Lok_l"; "nd_l_okX"; "Ys_l"; "bdX_l"; "Xf_l"; "Xs_l"; "Yf_l"; "bd_l_fX"; "comm_l"; "commf_l"; "nd_l_fX"; "cutsQ"; "exitsQ"; "extra_l"; "ndXE_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al"; "tv_l"; "kept_l"; "tv_l_ok"; "LAr"; "T_l_f"; "T_l_okR"; "qCURl"; "tv_l_f"; "E_l"; "R_l"; "Xk_l"; "bd_l_f"; "bd_l_ok"; "gLC'"; "gLI'"; "k_li"; "qC2l"; "qCl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.

Definition Lok_l : axst := Eval vm_compute in leafL (runL 200 cps_arm T_l_okR) pc_latch 0.
Definition s_latch_l : wsub := ltac2:(tb__ "0|1|
S0S4ScS14A2M0S1ScS14P248S50A4S0G0S1ScS14P249S4fA4S6bS3bS31S1eA1S31S3dA1A3A3A3").
Definition bdX_l : list bitem := Eval vm_compute in bd_subst s_latch_l (bdX 0).
Definition nd_l_okX : ndesc := ltac2:(tb__ "0|0|
S36S44S2dS21S35S3cS2A2A4").
Definition ndX_l : ndesc := ltac2:(tb__ "0|0|
S36S42S2dS5cZ0A1S35S3cS2A2A4").
Definition comm_l : list bitem := Eval vm_compute in bd_common bd_l_ok bdX_l.
Definition Xs_l : list bitem := Eval vm_compute in bd_minus bd_l_ok bdX_l.
Definition Ys_l : list bitem := Eval vm_compute in bd_minus bdX_l bd_l_ok.

Lemma al_checks_pay : ltac2:(tb__ "0|29|
SaS9S3S54S4eS7SeS26S23A3A2S2A3SaS9S3S54S7SeS26S20A3S21A2S2A3SaS9S3S13S20A1S2A3SaS9S8SeA1M0S23S0SeS10Z48Z0M1S0S4SbSdA2M2S1SbSdZ1M3SfS19S60S3eS3fA3A1A4S0G2S1SbSdN1SfS48A1A4S5G2A1M4A3A3G1A4S0SeS45S0SeS59S58A1S0SeS10G3G1S0G2S1SbSdZ18SfS15P1a6A1M5A1M6A4M7S0G2S1SbSdZ60M8S11G5G3G1G3A4A4M9S0G2S1SbSdZ8MaSfS15P1a9A1MbA1McA4MdS0G2S1SbSdG8S11GbG3G1G3A4A4MeS0G2S1SbSdGaSfS15P1acA1MfA1M10A4M11S0G2S1SbSdG8S11GfG3G1G3A4A4M12S0G2S1SbSdGaSfS15P1afA1M13A1M14A4M15S0G2S1SbSdG8S11G13G3G1G3A4A4M16S0G2S1SbSdZ78M17SfS15P1b2A1A1M18A4S0G2S1SbSdZ68M19SfS15P1b5A1A1M1aA4S0G2S1SbSdG17SfS15P1b8A1A1M1bA4G4A3M1cA3A3A3A3A3A3A3A3A3A3G1A4S0SeS10G1G3S0G2S1SbSdZ70M1dG6A4M1eS0G2S1SbSdZ50M1fGcA4M20S0G2S1SbSdG1fG10A4M21S0G2S1SbSdG1fG14A4M22S0G2S1SbSdG1dG18A4S0G2S1SbSdG1fG1aA4S0G2S1SbSdG1dG1bA4G4A3M23A3A3A3A3A3A3G1A4S5SeA1M24A3A3A3A3A3A3SaS9G0S20S0SeS56G1A1S0SeS57G1A1S0SeS10G3G1S0G2G7S0G2G9S0G2GdS0G2GeS0G2G11S0G2G12S0G2G15S0G2G16S0G2S1SbSdG17SfS15P2faA1M25A1M26A4S0G2S1SbSdG19SfS15P2ffA1M27A1M28A4G1cA3A3A3A3A3A3A3A3A3A3G1A4S0SeS10G1G3S0G2G1eS0G2G20S0G2G21S0G2G22S0G2S1SbSdG1dG26A4S0G2S1SbSdG1fG28A4G23A3A3A3A3A3A3G1A4G24A3A3A3A3A3SaS9S14S48S15P2f8A1A3SaS9S14S53G25A3SaS9S14S52G27A3S9S3S37S17S31S47A1A1S1fA2S2A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma al_checks_exit : ltac2:(tb__ "0|5|
SaS9S3S33S1eS3dS1dA3S2A3SaS9S3S5fS1dS3bA2S2A3SaS9S3S73S3bS17S31S1eA1M0A1M1A2S2A3SaS9S3S37G1S1fA2S2A3SaS9S3S6cS1dS44S42A3S2A3SaS9S3S3aS1dS2dS2dA3S2A3SaS9S3S6dS16G0A1S12S1dS5cZ0A1A2S21A3S2A3SaS9S3S38S39S1dS35S3cS2A2M2A2G2A2S2A3SaS9S3S70S2eS1dA2S2A3SaS9S14S5eS1dP1ccM3A2S15G3A1A3SaS9S14S5eS1dP1d3M4A2S15G4A1A3S9S3S55S42S30A2S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xf_l : list bitem := ltac2:(tb__ "0|0|
S0SeS45S0SeS59S58A1S5SeA1A3A3").
Definition Yf_l : list bitem := ltac2:(tb__ "0|1|
S0SeS56Z0M0A1S0SeS57G0A1S5SeA1A3A3").
Definition commf_l : list bitem := Eval vm_compute in bd_minus bd_l_f Xf_l.
Definition bd_l_fX : list bitem := Yf_l ++ commf_l.
Definition nd_l_fX : ndesc := ltac2:(tb__ "0|0|
S36S49S2dS25S35S3cS2A2A4").
Definition ndXE_l : ndesc := ltac2:(tb__ "0|1|
S36S42S2dS0SeS56Z0M0A1S0SeS57G0A1S5SeA1A3A3S35S3cS2A2A4").
Lemma al_checks_payf : ltac2:(tb__ "0|2|
SaS9S3S54S4dS7SeS27S22A3A2S2A3SaS9S3S54S7SeS27S24A3S25A2S2A3SaS9S3S6eS16S31S46A1M0A1S18Z0M1A1G1S22S24A5S2A3SaS9S3S37S17G0A1S28A2S2A3S9S8S4S14S14A2A1S49S44A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S47S1fA4U1M4A4S1SbS14S5aS5bZaS5dA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S46S28A4G4A4G5A4S5G3A1A3A3").
Definition exitsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S1eS1fA4U1M4A4S1SbS14S5aS5bZ1S5dA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S6aS2cA4G4A4G5A4S5G3A1A3A3").
Lemma ecertQ_ok : ltac2:(tb__ "0|0|
S9S3S6fS61S3bS68Uc8S69S3bS29S2aA8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_l (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S2fVo;A1S2S64Vo;A1X3x2").
Lemma al_checks2 : ltac2:(tb__ "0|1|
SaS9S3S65S16S31S4aA1A1M0S43S2dS2bS4bA5S2A3SaS9S3S67G0S43S2dS66S4cA5S2A3SaS9S3S63G0A1S2A3S9S3S72S1bS1cS1aS51S18ZffffffffA1A2A1G0A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_l : ltac2:(tb__ "0|0|
S71S4S14S14A2S1S14S14S40S62Z10S41A2A4S43A3").
Proof. cbn. do 16 right. left. reflexivity. Qed.
End Lib_load_obj_al_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_al_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf"; "P0_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al"; "kept_l"; "PDk_l"; "R_l"; "T_l_ok"; "E_l"; "Xk_l"; "passed_l"; "rates_l"; "s_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al.HL"; "Pre_hl"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_load_obj_al_eqs"; "Xs_l"; "Ys_l"; "cutsQ"; "Lok_l"; "nd_l_okX"; "s_latch_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "bd_nn"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al.HL2"; "Posts_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_handle_l_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_load_obj_al_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S36S1S3SdA1M0S11OF_;M1A2M2G2S3bS6G0G1R1A3S7G0G1R1A3A2Lp;S53A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_l : nd_am HL.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_l : ltac2:(tb__ "0|1|
S36S1SeS18A2M0G0S2aS1eS22S7SeS18R1A3A1S1bA3Ld;S7bA3"). Proof. repeat constructor. Qed.
Lemma P0_hl_mono : ltac2:(tb__ "0|2|
S3S1ScScA2M0A1M1G1G1S3S1G0ScA2A1S11G0S33G0R1R5A3S33G0R2R5A3F_;Fbn;S2fR6R5R3R2A4S2fR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma pay_l : ltac2:(tb__ "0|0|
S11S36S14S13R1A1S15SfS4dA1A1A3S6aS60R2A2S29S34S6cS61R3A2S6cS60R3A2A2S29S34S6bS61R3A2S6bS60R3A2A2S6aS61R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof al_checks_pay as (_ & _ & _ & EX & EY & EQ & _). rewrite EX, EY. rewrite EQ.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 434) (SVar 760))) F7.
  fact HF (SPUle (SVar 434) (SLit 4294967295)) F8. fact HF (SPUle (SVar 762) (SVar 763)) F9. fact HF (SPUle (SVar 763) (SLit 4294967295)) F10.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 481) (SVar 480))) F11.
  fact HF (SPUle (SVar 767) (SAlu ALU_ADD (SVar 437) (SLit 1))) F13. fact HF (SPUle (SVar 437) (SVar 585)) F14.
  fact HF (SPUle (SVar 585) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 480) (SVar 481)) (SLit 1))) F15.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F13, F14, F15. rewrite uval_lit in F1, F3, F8, F10 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428.
  pose proof (uval_range r (SVar 431)) as R431. pose proof (uval_range r (SVar 440)) as R440. pose proof (uval_range r (SVar 437)) as R437.
  pose proof (uval_range r (SVar 767)) as R767. pose proof (uval_range r (SVar 585)) as R585.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F12. rewrite h_ule, uval_lit in F12 by lia.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia).
  rewrite E2 in F6, F11.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 434) (SVar 760)) = uval r (SVar 434) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F7.
  assert (E5 : uval r (SAlu ALU_ADD (SAlu ALU_ADD (SVar 480) (SVar 481)) (SLit 1)) = uval r (SVar 480) + uval r (SVar 481) + 1) by (rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia); rewrite E1, uval_lit by lia; lia).
  rewrite E5 in F15.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 437) (SLit 1)) = uval r (SVar 437) + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite E6 in F13.
  unfold LAr, LAX, LAK, LAXK, A1, AK1, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma rates_l_holds : ltac2:(tb__ "0|0|
S11S36S14S13R1A1S15SfS4dA1A1A3S36S14S13R2A1S51A3F_;Fr;").
Proof.
  intros r HF. pose proof al_checks_pay as (_ & _ & _ & _ & _ & EQ & EQ1 & EQ2 & _).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SVar 584) (SVar 490)) F7. fact HF (SPUle (SVar 476) (SVar 760)) F8.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F9. fact HF (SPUle (SVar 585) (SVar 490)) F10.
  fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 434) (SVar 760))) F11. fact HF (SPUle (SVar 434) (SVar 584)) F12.
  fact HF (SPUle (SVar 767) (SAlu ALU_ADD (SVar 437) (SLit 1))) F13. fact HF (SPUle (SVar 437) (SVar 585)) F14.
  fact HF (SPUle (SVar 434) (SLit 4294967295)) F15. fact HF (SPUle (SVar 762) (SVar 763)) F16. fact HF (SPUle (SVar 763) (SLit 4294967295)) F17.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17. rewrite uval_lit in F1, F3, F9, F15, F17 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 584)) as R584. pose proof (uval_range r (SVar 585)) as R585. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 767)) as R767. pose proof (uval_range r (SVar 437)) as R437.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 434) (SVar 760)) = uval r (SVar 434) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F11.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 437) (SLit 1)) = uval r (SVar 437) + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite E6 in F13.
  assert (ES : uval r (SAlu ALU_SUB qCURl pCP) = uval r (SVar 760) - uval r (SVar 476)) by (rewrite EQ; unfold pCP; apply uval_sub_le; exact F8).
  assert (EG1 : uval r gLI' = uval r (SVar 584) + (uval r (SVar 760) - uval r (SVar 476))) by (unfold gLI', gLI; rewrite <- ES; apply uval_add_small; rewrite ES; lia).
  assert (EG2 : uval r gLC' = uval r (SVar 585) + 1) by (unfold gLC', gLC; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (EE : uval r (SAlu ALU_ADD pE0 (SLit 1)) = uval r (SVar 480) + uval r (SVar 481) + 1).
  { unfold pE0, pPOS, pLNL. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
  unfold rates_l, rate_gli, rate_glc, cg_li, cg_lc. rewrite EQ1, EQ2.
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG1, EE; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG2, EE; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG1; lia|].
  constructor; [apply (proj2 (h_ule _ _ _)); rewrite EG2; lia|]. constructor.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S77S11S3S25Q40A1A1S40OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S76S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
ScS6fVCST;R1A2S29S34Z0R2A2S35R2S72A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
ScS6fVXGL;R1A2S29S34Z0R2A2S35R2S72A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
ScS7aR1A1S6fVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1ScScA2ScA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S2aS4S85Z1S37S1S1ScScA2M0ScA2G0S6G0ScA2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S32VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1cVAInv;VCST;VXGL;S66VKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;S66VKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma HIN_l : ltac2:(tb__ "0|1|
S11S49S77S11S3S25Q40A1A1S40S36S14S13R6A1S15SfS4eA1A1A3VP0;Vrho0;A1S70S66Vrho0;R8A3VAInv;R7R6R5R4A4S1dVrho0;R8A2S7dRbS79S78R9A1A1A2S1fVFB;RaA2S20VFF;RbA2S24VFB;RcReS9S1S12S12A2S4aS50A3M0A4S7eRfG0A2S7fR10G0A2S21VFF;RfR11S31A4S29S83VCST;Vrho0;VFB;VFF;R12S4aS31S4cA8S29S84VCST;VXGL;Vrho0;VFB;VFF;R12S4aS31S4fA9S2fVCST;S7cVFB;R12S4aA3S82VFF;R12S31A3S3cS3dR12S4cR11A3S52A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof al_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_l) by (apply (tvinA_sublist FB Ai rho (kept_l ++ passed_l)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_l) by (exact (tvd_app_l rho kept_l passed_l HD)).
  assert (HZk : tvz rho kept_l) by (apply (tvz_sublist rho (kept_l ++ passed_l)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_l frL extra_l R_l rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_l in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_l frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_l frL o a HF CLN HT0 HZk lines_in_kept_l HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_l frL xextraLO Xk_l rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_l frL r a Hav HP0 HE Ha).
  - pose proof al_checks as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hl, P0_builder. rewrite !rw_call'.
    change (wsub_get s_l 15) with vBUF. change (wsub_get s_l 18) with vLEN. change (wsub_get s_l 12) with bA. change (wsub_get s_l 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_l rho R_l ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_l) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_l) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
ScS3S25Q40A1A1S2bF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27SeS11S3S25Q40A1A1S2bS36S14S13R3A1S15SfR4A1A1A3VTR;S26S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2bS2bS2bS2eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2bOS2bS2eR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27SeSeS3eS3S17A1M0S3S1SeS57A2M1A1S3S1S12S12A2M2A1S2bS11S3S25Q40A1A1M3G2S33G2R1R5A3S33G2R2S10RbA1A3F_;Fr;S2aSbG0A1S5aRaR9R8A3S8G0R7A2A3S2aSaS59RbRaR9R8S37G1SeS6SeS57A2R7A4A5S5A3S11G3VTR;S26S0RfRdR2R1A5S56S0S16SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S41A1M4S49S40S28S0R9R8R10S2G4S5bR3S5cR2R1A2A4A5R13RaR9R4R2A4R13S3cS3dRbRfS3fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS57G4S49S40S11G3G4S49S40S33G1S2SeS57RaR9A4R14A3S28S0R12R11R19S2G4S5bR9S5cR8R7A2A4A5R1cR13R12RaR8A4S70S16SfR1aA1A1S3cS3dR14R18S3fR9R13RaA3A3R19A2R8A3S28S0R9R8ReS2G4S5bR7S5cR6R5A2A4A5ReS3cS3dR16R1aS3fRbR15RcA3A3R1bA2R15RaR9R8R6A6S29S80R17S3fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S71R18S3fRdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S26S0S58R11S3cS3dR19R1dS3fReR18RfA3A3R1eA2R18RdRcA5S81R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S18SeS11S3S25Q40A1A1S2bR6R3A1VTR;S26S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S26S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHL : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S69S11S3S25Q40A1A1S68Z5R3A2VTR;S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6dS54S5S5fA3AaS5eR3R2A5S56S0S5dR3R2S6eVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4bR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S33S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S62A3S39S53R7R5A3S29S34Z0S38S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S35G4R4A2A2VTR;S26S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_l : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0VTR;S26S0VJAFv;S30S42A2S48R3R2A5VFAM;S38S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S48S42A4U1A4S2ScS12S43S44Z11S46A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof al_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof al_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_l frL bd_l (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_l rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_l rho E_hl E_l tp w Cxf).
    unfold ndv, tv_l. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_l _ E_hl rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hl rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_l HF CLN HTK HZ). unfold tv_l. apply in_or_app. left. exact lines_in_kept_l. }
  intros Hdnz.

  unfold ndv, tv_l.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hl CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HL.Pre_hl (ndh h0 true HL.nd0) PDk_l NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHL eq_refl
           E_l s_l R_l Xk_l rho tp kept_l passed_l frL bd_l brest_l (AHead pH true) (FAM (efmeasA (E_hl, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    unfold payA. apply (pay_okF_split _ _ _ _ bd_l _ payC_l payX_l payY_l PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_l rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_l frL rho' HK lines_in_kept_l Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof al_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & RT & Rfb).
    cbn [PDk_l liftPD PDh HL2.Posts_hl map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_l_f) T_l_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_l_f) (xfb_l T_l_f0) rho' T_l_f0 B_l_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof al_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_l_fX) T_l_f rho' tp')).
      { intros w Hw. unfold nd_l_fX, nd_l_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l_f frL (AHead pH true) bd_l_f commf_l Xf_l Yf_l bd_l_fX _ T_l_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_l_f nd_l_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hl T_l_f ndA1 nd_l_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_l_ok) T_l_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_l_ok) (xfb_l T_l_ok0) rho' T_l_ok0 B_l_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof al_checks_pay as (PQ1 & PQ2 & PWy & _).

      apply (TR_pre (SPA segs (JAv nd_l_okX) T_l_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rates_l_holds rho' HFo) | exact HFo]].
        unfold nd_l_okX, nd_l_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l_ok frL (AHead pH true) bd_l_ok comm_l Xs_l Ys_l bdX_l _ T_l_ok rho' tp' w PQ1 PQ2 PWy HFo (pay_l rho') Hw). }
      apply (CUTV T_l_okR nd_l_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hl T_l_okR ndA1 nd_l_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_l_latch : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1S2eS30R3A1S26S0VJAv;S64A1S63R4R3R2A6S29S30S3cR5S65A2M0A1S26S0VJAv;S45A1S55G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof al_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_l X_latch s_latch_l nd_l_okX tv_l (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_l tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S23S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S74S0S73VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S45A2S55R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S47A2S67R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHL_T : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S69S11S3S25Q40A1A1S68Z5R3A2S2dS0Vok;S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6dS54S5S5fA3AaS5eR3R2A5S56S0S5dR3R2S6eVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4bR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_l.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hl CST) PTrue HL.Pre_hl (ndh h0 true HL.nd0) (PDh HL2.Posts_hl h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hl CST) PTrue HL.Pre_hl HL.nd0 HL2.Posts_hl NPH h0 true h0_ltH HamC_l HamPD_l (P0_hl_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_l_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S33S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S62A3S39S53R7R5A3S29S34Z0S38S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S35G4R4A2A2S2dS0Vok;S26S0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsQ) (map efdrop exitsQ) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertQ_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_l) tp1 tp0')].
    intros w Hw. destruct (Lok_l_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_l tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 al_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_l_T : ltac2:(tb__ "0|1|
S11S3S25Q40A1A1M0G0S2dS0Vok;S26S0VJAFv;S30S42A2S48R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_l (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHL_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S75S0S73VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
ScS3S25Q40A1A1S2bF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
ScScS3S25Q40A1A1S2eS34R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S45A2S55R3R2A5VFAM;S38S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S55S45A4U1A4S2ScS12S43S44Z1S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S47A2S67R3R2A5VFAM;S38S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S67S47A4U1A4S2ScS12S43S44Z1S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHL_E : ltac2:(tb__ "0|1|
S3S1ScScA2M0A1S3S1G0ScA2A1S69S11S3S25Q40A1A1S68Z5R3A2S2cS0S26S0S1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S6dS54S5S5fA3AaS5eR3R2A5S56S0S5dR3R2S6eVAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4bR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_l.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hl CST) PTrue HL.Pre_hl (ndh h0 true HL.nd0) (PDh HL2.Posts_hl h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hl CST) PTrue HL.Pre_hl HL.nd0 HL2.Posts_hl NPH h0 true h0_ltH HamC_l HamPD_l (P0_hl_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_l_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS18S4S1ScS12A2M0S11S3S25Q40A1A1M1ScG1S33S1S1S1SeS18A2M2S4A2M3G0A2S2G3G0S2G2S4S2SeS18R8R7A4R6A4R5A4S62A3S39S53R7R5A3S29S34Z0S38S2G3G0S2G2S4S2SeS18RaR9A4R8A4R7A4R6A2M4A2S35G4R4A2A2S2cS0S26S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsQ exitsQ (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertQ_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof al_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_l ndX0 nd_l_okX 1%nat 1%nat RL 1 s_latch_l rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_l) tp1 tp0'). }
    intros w Hw. destruct (Lok_l_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_l tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 al_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_l_E : ltac2:(tb__ "0|2|
S11S3S25Q40A1A1M0G0S2cS0S26S0VJAFv;S30S42A2S48R3R2A5VFAM;S38S2S1S1SeS18A2M1S4A2S1ScS12A2S2G1S4S2SeS18S48S42A4U1A4S2ScS12S43S44Z11S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_l (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHL_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_al_pf.

