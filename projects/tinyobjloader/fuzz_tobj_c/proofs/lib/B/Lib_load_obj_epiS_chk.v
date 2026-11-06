(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "Some"; "app"; "option"; "pair"; "false"; "prod"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "sobj"; "SVar"; "sprop_eqb"; "sv"; "SPEq"; "sprop_below"; "ss_objs"; "DUnknown"; "ss_facts"; "ss_next"; "swf"; "SAlu"; "ss_pc"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "axwf"; "ax_base"; "ax_X"; "g8"; "has_facts"; "leafA"; "la_state"; "entailsA"; "la_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "g5"; "vF"; "objs_butlast"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "wsub_id_on"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "E_wm"; "K_rp"; "E_wm0"; "L_rpx"; "B_1"; "L_w"; "PreR"; "ent_chk2"; "wK1"; "wK2"; "L_rpc"; "E_wmr"; "L_rp0"; "L_v0a"; "T_wm0"; "bdAt"; "ndAt"; "T_rp"; "T_wm"; "T_wmb"; "T_wr"; "bnds"; "nd_rp"; "nd_succP"; "LR"; "R_w"; "T_wc"; "bd_succP"; "brestAt"; "cps_b"; "s_w"; "wLen"; "wOff"; "xf_w"; "xfb_w"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS4"; "E_fu"; "land_chk"; "R_fu"; "T_fu0"; "s_fu"; "B_fu"; "E_fu0"; "L_d6f"; "L_d6y"; "L_d6z"; "L_d7"; "L_land"; "T_fu"; "B_8"; "B_9"; "C_9v"; "bd9"; "bd_land"; "comOf"; "ekOf"; "nd_d0"; "xf_fu"; "xfb_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "alA"; "bA"; "pNX"; "t_c"; "t_k"; "v_sh"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "AHead"; "NDA"; "fr_sub_eqb"; "nd_bd"; "nd_am"; "nd_fr"; "nd_tv"; "ndesc"; "am_eqb"; "am_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "BIc"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "V_ldR"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "bd_succ"; "L_dz"; "s_fs2"; "E_fs2"; "bd_fz2"; "kept_fs2"; "qHz2"; "s_kn"; "s_nn"; "E_fs21"; "L_sk"; "L_sn"; "R_fs2"; "Xk_fs2"; "bd_nop2"; "bd_ok2"; "bd_s0"; "hand_fs2"; "nd_succ"; "qHk2"; "qHn2"; "tvL_k"; "tv_fz2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_defs"; "ldef_facts"; "nx500"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_chk.FU"; "Pre_fu"; "P_fu"; "Posts_fu";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_chk"; "Lb_rp0"; "Lb_v0a"; "cc_facts"; "wcells"; "f_len"; "f_nx"; "pcells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "bd_disp"; "pc_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS3"; "L_d1"; "B_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "local_ok"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "PHIe"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1.FS"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_chk.FU.FinUnkAddr"; "fu_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiS1 Lib_load_obj_epiS2 Lib_load_obj_epiS3 Lib_load_obj_epiS_st2 Lib_load_obj_epiS4 Lib_load_obj_epiS_defs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module FU. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_unknowns. End FU.

Lemma ent_chk2_unf : ltac2:(tb__ "0|3|
S20S20S85S85S0S3S40R4R3R2R1A4S2A3S1S0S3S28R5R4S35S2aS1fR5A1M0S1fR4A1A3M1A3S2A3S1S0S3Sc8G1S2aA2S2A3S1S0S3S8fS2aS1aG0A1M2A2S2A3S1S0S3S7dG2R3A2S2A3S1S0S3SdbG1S84R3A1S84R2A1A3S2A3S1S0S3S80G1S83R3A1S83R2A1A3S2A3S1S0S3S33S19G0A1S8aG1S81R2A1A2S81R3A1A3S2A3S0S3S86S87G1S82R2A1A2S82R3A1A2S2A3A2A2A2A2A2A2A2F_;Fndj;Fndi;FT;FL;").
Proof.
  intros L T ndi ndj H. unfold ent_chk2 in H. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.
Lemma land_chk_unf : ltac2:(tb__ "0|4|
S20S6S89A1S14S0S3S5fR3R2R1A3S2A3S1S0S3SbaR3S8S89S70R3A1M0S71R3A1M1A3A2S2A3S1S0S3SbaS8S89G0Sc2A3S6fR3A1M2A2S2A3S1S0S3S34S19S1fR4A1A1SfZ0M3A1G3G1Sc2A5S2A3S0S3S40R4Sc1S7fS30S2fG2S7eR2SbA2A4S72A4S2A3A2A2A2F_;Fhd;Fbd;FL;").
Proof.
  intros L bd hd H. unfold land_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H4]. repeat split; assumption.
Qed.

Lemma epiS_chk_fs : ltac2:(tb__ "0|8|
S1S0S3SbeS37S93A1M0S95S2fS31S9cA5S2A3S1S0S3Sc0G0S95S2fSbfS9dA5S2A3S1S0S3S5cSeS13S10S2cSfZ7fffff7ff800A1A2A1G0A3S2A3S1S0S3Sa7G0A1S2A3S1S0S3Sa8S93A1S2A3S1S0S14Sc7S92PcA2S77A3S1S0S14Sc7S92P64A2S76A3S1S0S89SbdS89UeSa0S8bZ0M1G1G1A3A4Sd4Z80M2S79S7bS7cA1M3A1M4S7aG3A1M5A3A3S1S0S3S5cSeS13S10Sd5G2G5A2SfZffffffffA1M6A2A1S37S99A1M7A3S2A3S1S0S3S5cSeS13S10G4G5A2A1G7A3S2A3S1S0S3S5cSeS13S10G5G6A2A1G7A3S2A3S0S6S89A1S8aS92S81Sd6A1A2Sa1A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_succ : ltac2:(tb__ "0|2|
S1S0S3S8fS2aS38S9bA1M0A2S2A3S1S0S3S7dG0S7fS30S2fS9eS7eSa4S2A2A4A2S2A3S1S0S3S80S98S2fS2fA3S2A3S1S0S3S32S8eS98A2S2A3S1S0S3S8fS2aS38S9aA1M1A2S2A3S1S0S3S7dG1S7fSa5S2fS9fS7eSa3S2A2A4A2S2A3S1S0S3S80S97S2fS2fA3S2A3S1S0S3S32S8eS97A2S2A3S0S3SbbSa6S30A2S2A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition Lb_v0a : axst := Eval vm_compute in ax_add_facts bnds L_v0a.
Definition Lb_rp0 : axst := Eval vm_compute in ax_add_facts bnds L_rp0.
Definition f_nx : sprop := ltac2:(tb__ "0|0|
S10S78S1cSd3S2eSfZ1A1A3A2").
Definition f_len : sprop := SPUle vLEN (SLit 67108864).

Definition cc_facts : list sprop := ltac2:(tb__ "0|3|
S4SeS10S12P197A1S12P198A1M0A2S4SeS10G0SfZffffffffA1M1A2S4SeS10S12P1a3A1S12P1a4A1M2A2S4SeS10G2G1A2S5SeA1A3A3A3A3").
Lemma epiS_chk_v0 : ltac2:(tb__ "0|7|
S1S0S3S5dSeS16S38S46A1A1S8SeS4eS37S46A1M0A3M1A3S2A3S1S0S20Sc9S46G1A2Sb4A3S1S0S3S5cSeS13Sb8A1M2G0A3S2A3S1S0S3S5cSeS13Sb7A1M3G0A3S2A3S1S0S3S5dSeSeS5cSeS13R1A1M4G0A3Lf;Sb5A3S2A3S1S0S3SbaS90S54A2S2A3S1S0S3S40Sb4S3dS50S49U1A1A4S2A3S1S0S3S32S8eS35S2aS1fSb4A1S1fS3dA1A3A2S2A3S1S0S3S5dSeS16S38S45A1A1S8SeS4eS37S45A1M5A3M6A3S2A3S1S0S20Sc9S45G6A2Sb3A3S1S0S3S5cSeG2G5A3S2A3S1S0S3S5cSeG3G5A3S2A3S1S0S3S5dSeSeS5cSeG4G5A3Lf;Sb5A3S2A3S1S0S3S40Sb3S3aS50S4fA4S2A3S0S3S32S8eS35S2aS1fSb3A1S1fS3aA1A3A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS_chk_w : ltac2:(tb__ "0|2|
S1S0S14S22S3eA1SfSadA1A3S1S0S3S25S4SeS15S24S2bA1S2cA2S4SeS10S12S2bA1SfSafSaeZ2Z3dA2Z1A2A1A2S5SeA1A3A3S37S3eA1M0A2S2A3S1S0S3S1bS1fSd0S3eS23S3eA1S2bS41S42A5M1A1A1S2A3S1S0S20G1S4dA3S1S0S3Sa9G0S30S2fS31S17S1fS3eA1A1A5S2A3S0S3S21S4dA1S2A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition wcells : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_wm0)) (shobj g5 0 0 [] DUnknown)).
Definition pcells : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S L_rpx)) (shobj g5 0 0 [] DUnknown)).

Lemma epiS_chk_wm : ltac2:(tb__ "0|b|
S1S0S14S22S3bA1SfSadA1A3S1S0S6S11A1M0S17S1fS3bA1A1S8S11S2dS3bA1M1S4S11Sd1S2bS41S42Sb6S18A5S5S11A1A3A3A3S1S0S3S25S4SeS15S24S2bA1S2cA2S4SeS10S12S2bA1SfSafSaeZ2Z3dA2Z1A2A1A2S5SeA1A3A3S37S3bA1M2A2S2A3S1S0S3S5dScS36S36A2M3Sd2Sb6S18S41S42A4S4G3SaS36S36S59S58A4S5G3A1A3M4A3S2A3S1S0S3S7dS38S3bA1S7fS30S2fS90S7eS75S2A2A4A2S2A3S1S0S3Sa9G2S30S2fS31G1A5S2A3S1S0S3Sa7G2A1S2A3S1S0S20ScfS3bG1P6eG4A4S44A3S1S0S9S20A1M5SacS44S5aS44A1A2S7S20S39A2A3S1S0S9G0A1ScaS39S3fS57S39A1M6A3S7G0S52S39A1M7A2A3S1S0S3SccS39S3fG6G7S4S20S51S5S20A1A3M8A5S2A3S1S0S3SddS2aG6A2S2A3S1S0S3S8fS2aS38S39A1M9A2S2A3S1S0S3S7dG9Sa2A2S2A3S1S0S3S8cG9S90A2S2A3S1S0S3S8dS90A1S2A3S1S0S3S5dS20S20SdSdG0S3Lx;Sd9S1fS3fA1S1fR1A1A2S2S11G0SbLl;Ls;X6x2SceS3fR1A2A2S1eS22R1A1S22S3fA1A2A2LL;G8A3S2A3S1S0S3SbeS37S39A1MaS30S2fS31G7A5S2A3S1S0S3Sc0GaS30S2fSbfS23S39A1A5S2A3S1S0S3Sa7GaA1S2A3S1S0S3Sa8S39A1S2A3S1S0S20S53S39A1S47A3S1S0G5SacS47S5bS47A1A2S7S20S4cA2A3S1S0S20Sc6S4cA1S4bA3S0S3S21S4bA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS_chk_rp : ltac2:(tb__ "0|3|
S1S0S14S22S3aA1SfSadA1A3S1S0S3S25S4SeS15S24S2bA1S2cA2S4SeS10S12S2bA1SfSafSaeZ2Z3dA2Z1A2A1A2S5SeA1A3A3S37S3aA1M0A2S2A3S1S0S3SdcS23S3dA1M1S23S3aA1A2S2A3S1S0S3S1bS1fSd0S3aG1S2bS41S42A5M2A1A1S2A3S1S0S20G2S4aA3S1S0S3Sa9G0S30S2fS31S17S1fS3aA1A1A5S2A3S1S0S3S21S3aA1S2A3S0S3S21S4aA1S2A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_rpx : ltac2:(tb__ "0|3|
S1S0S14S22S3cA1SfSadA1A3S1S0S6S11A1S17S1fS3cA1A1S8S11S2dS3cA1M0S4S11Sd1S2bS41S42Sb9S18A5S5S11A1A3A3A3S1S0S3S25S4SeS15S24S2bA1S2cA2S4SeS10S12S2bA1SfSafSaeZ2Z3dA2Z1A2A1A2S5SeA1A3A3S37S3cA1M1A2S2A3S1S0S3S7dS38S3cA1S7fS30S2fS48U1M2A1S7eS75S2A2A4A2S2A3S1S0S3Sa9G1S30S2fS31G0A5S2A3S1S0S3Sa7G1A1S2A3S1S0S20ScfS3cG0P6eS5ScS36S36A2A1A4S43A3S1S0S3S40S43S3dS4fS49G2A1A4S2A3S1S0S3S32S8eS35S2aS1fS43A1S1fS3dA1A3A2S2A3S0S3S21S43A1S2A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS4_chk_fu : ltac2:(tb__ "0|6|
S1S0S6ScS36SaaA2M0A1SbcS26G0S26SaS36SaaS1dS1fS27R1A1A1A1S29R1A1A4LL;Sd8U12cS56Sc5A3A4S4G0SaS36SaaSc3SabA4S4G0SaS36SaaSd7SabA4S5G0A1A3A3A3S1S0S9S20A1M1SacS64S73S64A1A2S7S20S5eA2A3S1S0S9S6S11A1M2A1ScaS5eSb0S62A3S7G2S60A2A3S1S0S3ScbS5eSb0S62S60SbcS26S20S27Sb2A4A5S2A3S1S0S3S8fS2aS1aS1fS5eA1M3A1M4A2S2A3S1S0S3S7dG4S49U7A1A2S2A3S1S0S3S5dSeS16G4A1S19G3A1M5A3S2A3S1S0S20SdaG5ScdS62Sb0Sb1S5eS60A5A2S61A3S1S0G1SacS61S74S61A1A2S7S20S63A2A3S1S0S20Sc6S63A1S6aA3S1S0S3S21S6aA1S2A3S1S0S3S21S6bA1S2A3S1S0S3S21S6cA1S2A3S0S3S21S6dA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_fu : ltac2:(tb__ "0|0|
S1S0S3Sa8S5eA1S2A3S0S3S5dSeS16S38S5eA1A1S37S5eA1A3S2A3A2").
Proof. conj_vmc. Qed.
Lemma epiS4_chk_land : ltac2:(tb__ "0|2|
S1S0S3S5fS69S6eS75A3S2A3S1S0S3S5fS68S48U7A1M0S75A3S2A3S1S0S3S5fSc4S48U1A1S75A3S2A3S1S0S3S5fS67S55U6A1M1S75A3S2A3S1S0S3S5fS66G1S75A3S2A3S1S0S3S5fS65G0S75A3S2A3S0S3S5fS91S94S96A3S2A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_landphi : ltac2:(tb__ "0|1|
S1S0S3S32S88S35S2aS1fS69A1S1fSc1A1M0A3A2S2A3S1S0S3S32S88S35S2aS1fS68A1G0A3A2S2A3S1S0S3S32S88S35S2aS1fSc4A1G0A3A2S2A3S1S0S3S32S88S35S2aS1fS67A1G0A3A2S2A3S1S0S3S32S88S35S2aS1fS66A1G0A3A2S2A3S1S0S3S32S88S35S2aS1fS65A1G0A3A2S2A3S1S0S3S32S88S35S2aS1fS91A1G0A3A2S2A3S0S3S7dS38S91A1S7fS30S2fS94S7eS96SbA2A4A2S2A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
