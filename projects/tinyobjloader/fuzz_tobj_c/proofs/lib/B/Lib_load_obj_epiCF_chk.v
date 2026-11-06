(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "prod"; "cons"; "pair"; "false"; "nil"; "Some"; "andb"; "list"; "option"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sprop_eqb"; "SPUle"; "ss_next"; "SLit"; "ss_facts"; "sprop_below"; "SAlu"; "SPUlt"; "SVar"; "valuation"; "sobj"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "entailsA"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF"; "s_c"; "E_c"; "R_c"; "brest_vr"; "kept_vr"; "Xk_vr"; "nd_cf"; "pcsOf"; "s_gk"; "C_cf"; "E_c1"; "L_cfZ"; "T_grown"; "T_grownS"; "T_keep"; "bd_vr"; "k_ac"; "s_ent"; "tv_vr"; "L_cfE"; "L_x"; "Lf0"; "Lf1"; "T_fail0"; "T_grown0"; "T_keep0"; "bd_cf"; "xfb_vr"; "B_fail"; "B_grown"; "B_keep"; "E_c0"; "K_w"; "L_xF"; "Lf0F"; "Lf1F"; "PDk_vr"; "T_fail"; "T_keepS"; "d_ac"; "nd_grown"; "s_bk"; "vI"; "C_bl"; "L_bk"; "Ls_b"; "Ls_c"; "Ls_f"; "Ls_w"; "Ls_x"; "Wt"; "X_bl"; "bnd_nt"; "cnt0_src"; "ent_facts"; "hand_vr"; "inj_grown"; "inj_keep"; "nd_fail"; "nv_src"; "passed_vr"; "pc_bl"; "pc_blx"; "room_vr"; "vKg"; "vcf"; "vr_pc"; "xf_vr"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF.VRN"; "Pre_vr"; "P_fail"; "P_grown"; "P_keep"; "nd0"; "bdP"; "tv0"; "tvP"; "vKn"; "vN"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF_chk"; "Fx"; "len_src"; "ent_chkS"; "rp_chk"; "bd_xe"; "nx"; "slot_src"; "s_f0"; "s_f1"; "s_x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_am"; "nd_bd"; "nd_tv"; "ndesc"; "am_subst"; "NDA"; "nd_fr"; "AHead"; "am_eqb"; "nd_below"; "ND"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "V_ldR"; "vNV"; "fact_nv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "alA"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA";
"pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "wsub_id_on"; "bud_le2"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "L_cf0"; "K_rp"; "nd_rp"; "pc_cf"; "pc_rp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame Glue3.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD_eqs Lib_load_obj_epiS1 Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiCF.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).

Definition ent_chkS (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S20VL;VT;Vs;A3G0S99Vs;S6aA2G0Sb9S6aS7eVL;A1M1A2G0S8cG1Vndi;A2G0SafVs;S85Vndi;A1S85Vndj;A1A3G0S8eVs;S89Vndi;A1S89Vndj;A1A3G0Sb5S79VL;A1S95Vs;S84Vndj;A1A2S84Vndi;A1A3S8bS87Vs;S83Vndj;A1A2S83Vndi;A1A2S8X2x2S8X2x2S8X2x2S8X2x2S8X2x2S8X2x2S8X2x2").
Lemma ent_chkS_unf : ltac2:(tb__ "0|2|
S1dS1dS9cS86S86S0S2S7bR5R4R3R2R1A5S3A3S1S0S2S20R6R5R4A3S3A3S1S0S2S99R4S6aA2S3A3S1S0S2Sb9S6aS13S1eR6A1M0A1M1A2S3A3S1S0S2S8cG1R3A2S3A3S1S0S2SafR4S85R3A1S85R2A1A3S3A3S1S0S2S8eR4S89R3A1S89R2A1A3S3A3S1S0S2Sb5S15G0A1S95R4S84R2A1A2S84R3A1A3S3A3S0S2S8bS87R4S83R2A1A2S83R3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chkS in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Lemma epiCF_checks_ent : ltac2:(tb__ "0|a|
S1S0S1dS94SbaS4SfS59S15S1eSbaA1M0A1M1A3M2A2S36A3S1S0S2S68SfS16S13G0A1A1G2A3S3A3S1S0S2S67SfS11S5eA1G1A3S3A3S1S0S2S67SfS11S58A1S15S1eS36A1M3A1A3S3A3S1S0S2S1cS1eS2eA1M4A1S3A3S1S0SdS5ScS5S10S10A2M5A1M6ScSfA1M7A2M8A1Sc5G3G4A2SaG8S7G6G7S6G5S7S10S10S19P1a0A1S14Z0A1A4S9G5A1A3S9SfA1A4A2A3S1S0S78S13G4A1S13G3A1A3S1S0S1dS22S36G4A2S2eA3S1S0S2S1fS2cA1S3A3S1S0S2S20S2eS2cS34A3S3A3S1S0S2S99S34S6aA2S3A3S0ScS5S77S92A2M9A1S2aS51A1S6G9S7S77S92S65S93A4S9G9A1A3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_vr : ltac2:(tb__ "0|9|
S1S0SdS1dA1Sa2S42S66S42A1A2SaS1dS2dA2A3S1S0S1dS94S2dS4SfS62S15S1eS2dA1M0A1A3M1A2S24A3S1S0S2S68SfS16S13G0A1A1G1A3S3A3S1S0SdScS1bA1M2A1SadS24S6dS23A3SaG2S25A2A3S1S0S2SacS24S6dS23S25Sc0S5S5S1dS86A2M3S1aS1aOF_;F_;M4A2M5S1dG5SeS1dS86SeG3G4R1A3A3Ld;S47A4A5S3A3S1S0S2Sc7S6aS23A2S3A3S1S0S2Sc6S23SbfA2S3A3S1S0S2SafS23S5fS85Sa3S9eS3S71A3M6A1A3S3A3S1S0S2S8bS87S23S83G6A1A2S8aSa5S3A2A2S3A3S1S0S2S68S5Sb1G4A2M7G7Sb2S6dSbfS23S13S1eS24A1A1M8SeSb1G4R1A3A5Ld;S47A3S3A3S1S0S2Sb8S90S35A2S3A3S1S0S2Sb7S3dS32A2S3A3S1S0S2Sb3S28S21S24A1A2S3A3S1S0ScS96A1S95S23S84G6A1A2S5aA3S1S0S2S8cG8S29A2S3A3S1S0S2S97G8S26A2S3A3S1S0S2Sb9S6aG8A2S3A3S0S2S98S32A1S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_vr_nd : ltac2:(tb__ "0|d|
S1S0S86S88S4S5S10S10A2M0S27SaeSabS23S6dS70S24A4M1S85Sa3S9eS3S71A3M2A1A2A3S8fS4S96S95G1S84G2A1A2S26A3S87G1S83G2A1A2A4S29A3S1S0S86S88S4G0S27SaeSabS23S6dS6fS24A4M3S85Sa3S9eS3S8dS74S9S5S5S10S77A2S10A2A1M4S72S76S75A2A3A3M5A1A2A3S8fS4S96S95G3S84G5A1A2S26A3S87G3S83G5A1A2A4S4bA3S1S0S86S88S4G0S27SaeSabS23S6dS6eS24A4M6S85Sa3S9eS3S8dS73G4S9S96A1A3A3M7A1A2A3S8fS4S96S95G6S84G7A1A2S26A3S87G6S83G7A1A2A4S5dA3S1S0S1dSb0S6dS24S23S25S70S28A6S3cA3S1S0S1dSb0S6dS24S23S25S6fS28A6S3bA3S1S0S1dSb0S6dS24S23S25S6eS28A6S3aA3S1S0SdS1dA1M8Sa2S3cS3eS3cA1A2SaS1dS41A2A3S1S0G8Sa2S3bS3eS3bA1A2SaS1dS40A2A3S1S0G8Sa2S3aS3eS3aA1A2SaS1dS3fA2A3S1S0S1dSaaS41A1S31A3S1S0S1dSaaS40A1S2fA3S1S0S1dSaaS3fA1S48A3S1S0S1dS94S31S4SfS5cS15S1eS31A1M9A1A3MaA2S49A3S1S0S1dS94S2fS4SfS5bS15S1eS2fA1MbA1A3McA2S30A3S1S0S2S68SfS16S13G9A1A1GaA3S3A3S1S0S2S68SfS16S13GbA1A1GcA3S3A3S1S0S2S1fS49A1S3A3S1S0S2S1fS30A1S3A3S1S0S2S1fS48A1S3A3S1S0S2S20S30S43S2bA3S3A3S0S2S99S2bS6aA2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_run : ltac2:(tb__ "0|7|
S1S0ScS5S77S92A2M0A1M1S2aS53A1S6G0S7S77S92S60S93A4M2S9G0A1M3A3A3S1S0G1S2aS50A1S6G0G2S6G0S7S77S92S61S93A4M4S6G0G2S6G0G4G3A3A3A3A3A3S1S0G1S2aS54A1S6G0S7S77S92SbdS93A4S6G0S7S77S92SbeS93A4M5G3A3M6A3A3S1S0G1S2aS52A1S6G0G5G6A3A3S1S0S2S1fS4eA1S3A3S1S0S2S1fS56A1S3A3S1S0S2S20S4fS2cS4cA3S3A3S0S2S99S4cS6aA2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiCF_checks_inj : ltac2:(tb__ "0|7|
S1S0S1dS94S37S4SfS6SfS57S9SfA1A3M0S15S1eS37A1M1A1A3M2A2S44A3S1S0S2S68SfS16S13G1A1A1G2A3S3A3S1S0S1dS94S38S4SfG0S15S1eS38A1M3A1A3M4A2S45A3S1S0S2S68SfS16S13G3A1A1G4A3S3A3S1S0S1dS94S39S4SfG0S15S1eS39A1M5A1A3M6A2S46A3S0S2S68SfS16S13G5A1A1G6A3S3A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition len_src (F : list sprop) : bool := ltac2:(tb__ "0|0|
SbSbS67SfS11Sa1A1VF;A3S67SfS11S12Sa9S17Sa4S6cS14Z1A1A3A2A1VF;A3A2S67SfS11S12S6cS14Z4000000A1A2A1VF;A3A2").
Definition slot_src (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
SbSbSbSbS67SfS11S12S55Vk;A2A1VF;A3S67SfS11S12Vk;S14ZffffffffA1M0A2A1VF;A3A2S67SfS11S12S9dZ4Vk;A2G0A2A1VF;A3A2S67SfS11S18S4dSa0A2A1VF;A3A2S7aVF;A1A2").

Lemma epiCF_chk_ent : ltac2:(tb__ "0|0|
S1S0S86Sc4S88S90S8fS3dS8aSa5S3A2A4A3S1S0S2Sb8S90S35A2S3A3S1S0S2Sb7S3dS32A2S3A3S1S0S2S7bS2eS2cS34S29S29A5S3A3S0S2Sb4S9fS34A2S3A3A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_chk_site : ltac2:(tb__ "0|5|
S1S0S2Sc1S79S24A1M0S27S8fS91S25A5S3A3S1S0S2Sc3G0S27S8fSc2S28A5S3A3S1S0S2S67SfS11S18S4dSa0A2A1S79S2dA1M1A3S3A3S1S0S2S7aG1A1S3A3S1S0S2S67SfS11S12S33S14ZffffffffA1M2A2A1G0A3S3A3S1S0S2S67SfS11S12S6bS14Z7fffff7ff800A1A2A1G0A3S3A3S1S0S2S67SfS11S12S9dZ10Sa7A2M3G2A2A1G0A3S3A3S1S0S2S67SfS11S12Sa7G2A2A1G0A3S3A3S1S0S2S67SfS11S12Sa6S14Z800000000000A1A2A1G0A3S3A3S1S0S2S67SfS11S12S17Sa4Sa6G3A3S19P1eA1M4A2A1G0A3S3A3S1S0S2S67SfS11S12G4S14Z7fffff800000A1A2A1G0A3S3A3S1S0S2Sb6S7eS24A1S9fA2S3A3S1S0S10S9aS23P11A2S33A3S1S0S10S9aS23PfA2S4aA3S1S0S10S9aS23PcA2S17Sa4S6bS14Z2d8A1A3A3S0S10S9aS23PeA2Sa8A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma lines_in_kept_vr : ltac2:(tb__ "0|0|
S69S5S10S10A2S7S10S10Sa6S9dZ10Sa7A2A4S27A3").
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma acol_in_tv_vr : ltac2:(tb__ "0|0|
S69S5S10S10A2S7S10S10S4aS9dZ4S33A2A4S35A3").
Proof. unfold tv_vr. apply in_or_app. right. left. reflexivity. Qed.

Lemma epiCF_chk_cont : ltac2:(tb__ "0|1|
S1S0S2S7fS33S79S31A1A2S3A3S1S0S2S7fS63S79S2fA1A2S3A3S1S0S2S7bS30S43S2bS4bS29A5S3A3S1S0S2Sb4S9fS2bA2S3A3S0S10S9bS2bS64Z1dA1M0A2G0A3A2A2A2A2").
Proof. conj_vmc. Qed.

Definition bd_xe : list bitem := brest_vr ++ hand_vr.
Definition s_x : wsub := Eval vm_compute in infer_sub NP (ax_S L_xF) (ax_S K_rp).
Definition s_f0 : wsub := Eval vm_compute in infer_sub NP (ax_S Lf0F) (ax_S K_rp).
Definition s_f1 : wsub := Eval vm_compute in infer_sub NP (ax_S Lf1F) (ax_S K_rp).
Definition rp_chk (L : axst) (s : wsub) (bd : list bitem) : bool := ltac2:(tb__ "0|0|
S2S2L_;S7bVL;SbbVs;S88S90S8fVbd;S8aSa5S3A2A4SbcA5Sb4S9fVs;A2S8X2x2").
Lemma epiCF_chk_exit : ltac2:(tb__ "0|0|
S1S0S2S7aS79S37A1A1S3A3S1S0S2S7aS79S38A1A1S3A3S1S0S2S7aS79S39A1A1S3A3S1S0S2Sb8S35S90A2S3A3S1S0S2Sb7S32S7dA2S3A3S1S0S2S7cS44S82S7dA3S3A3S1S0S2S7cS45S80S26A3S3A3S0S2S7cS46S81S26A3S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
