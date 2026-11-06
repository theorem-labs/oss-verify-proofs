(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "false"; "prod"; "list"; "app"; "andb"; "pair"; "Some"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sprop_eqb"; "SLit"; "SPUle"; "SVar"; "sobj"; "ss_objs"; "swf"; "SAlu"; "SPBranch"; "SPEq"; "SPNot"; "dflt_writable"; "ob_cells"; "ob_dflt"; "ss_facts"; "ss_next"; "sv_below"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "has_facts"; "entailsA"; "g8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "ent_chk"; "g5_facts"; "Te_sf0"; "shape_ok"; "she"; "two52"; "ndA1p"; "nd_d1n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "tvA"; "KU1"; "nd_d2"; "nd_fa"; "nd_d1"; "nd_e"; "gp"; "nd_CL"; "V_ld"; "nd_A2"; "nd_B2"; "ndT"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "g5"; "objs_butlast"; "L_ms"; "Pre_ms"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "ndesc"; "AHeadN"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "Ee_sfA"; "Ee_sf"; "Ee_sfD"; "Te_s81"; "Te_s82"; "Ee_zf"; "Ee_s8"; "Ee_sfB"; "Re_sf"; "Ee_s8a"; "L_sf"; "Pre_sf"; "Re_s8"; "Te_s8r"; "Te_sf"; "X_sx"; "s_s8"; "s_sf"; "sx_sfB"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "KU"; "bd_below"; "bud_pay"; "BIc"; "bd_subst"; "bud_le"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "E_fl"; "kept_bd"; "E_flF"; "E_flG"; "L_fr"; "Pre_fr"; "dropX"; "E_bd"; "E_flC"; "K_j1"; "R_fl"; "L_fl0"; "L_fl1"; "L_j1s"; "Lb_j1"; "R_bd"; "T_fl0"; "Xk_bd"; "bd_disp"; "brest_bd"; "dnz"; "fact_sz"; "s_fl"; "s_j1b"; "s_j1s"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "E_fa"; "E_fd"; "vG"; "E_ml"; "X_A1"; "X_B"; "C_L"; "K_fa"; "L_L3"; "R_fa"; "R_fd"; "R_ml"; "s_L3"; "s_ml"; "vNd"; "vNx"; "E_fa0"; "E_fd1"; "L_L1"; "T_fa0"; "T_fd0"; "T_ml0"; "X_A"; "X_fa0"; "X_fa1"; "gA"; "nB"; "s_L1"; "s_fa"; "s_fa0"; "s_fa1"; "s_fd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "xrs47_chk"; "V_below"; "carve_site_chk"; "wsub_id_on"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "L_f8"; "Pre_f8"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "sv_subst"; "wsub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "flag_carve_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_FL"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs.

Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).

Definition ent_chk (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S29VL;VT;Vs;A3G0Sc1Vs;S43A2G0S68S43S2cVL;A1M1A2G0S4aG1Vndi;A2G0Sc5Vs;S4eVndi;A1S4eVndj;A1A3G0S54Vs;S4dVndi;A1S4dVndj;A1A3G0S71S2bVL;A1S70Vs;S4cVndj;A1A2S4cVndi;A1A3S52S53Vs;S4bVndj;A1A2S4bVndi;A1A2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2").
Lemma ent_chk_unf : ltac2:(tb__ "0|2|
S24S24Sc3S4fS4fS0S2S2dR5R4R3R2R1A5S3A3S1S0S2S29R6R5R4A3S3A3S1S0S2Sc1R4S43A2S3A3S1S0S2S68S43S1fS25R6A1M0A1M1A2S3A3S1S0S2S4aG1R3A2S3A3S1S0S2Sc5R4S4eR3A1S4eR2A1A3S3A3S1S0S2S54R4S4dR3A1S4dR2A1A3S3A3S1S0S2S71S1eG0A1S70R4S4cR2A1A2S4cR3A1A3S3A3S0S2S52S53R4S4bR2A1A2S4bR3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Definition nd_d1n : ndesc := ndEp tvA brest_bd.

Lemma epiD_chk_bd : ltac2:(tb__ "0|4|
S1S0S2S73S2bS7dA1M0S77S22S23S85A5S3A3S1S0S2S75G0S77S22S74S87A5S3A3S1S0S2S72S88A1S3A3S1S0S2S41SfS10S12SbbZ10Sb1A2M1S11ZffffffffA1M2A2A1G0A3S3A3S1S0S2S41SfS10S12Sb1G2A2A1G0A3S3A3S1S0S2S41SfS10S12Sb0S11Z800000000000A1A2A1G0A3S3A3S1S0S2S41SfS10S12S17ScdSb0G1A3S13P1eA1M3A2A1G0A3S3A3S1S0S2S41SfS10S12S48S11Z7fffff7ff800A1A2A1G0A3S3A3S1S0S2S41SfS10S12G3S11Z7fffff800000A1A2A1G0A3S3A3S0S2Sb6S2cS7dA1S3dA2S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_fl : ltac2:(tb__ "0|6|
S1S0S2S2dS81S79S4S7SbaSeA2A1M0S39S39A5S3A3S1S0S2S2dS82S79G0S39S39A5S3A3S1S0S2Sb8S3dG0A2S3A3S1S0S2S41SfS10S12SbbZ10Sb1A2S11ZffffffffA1M1A2A1S2bS79A1M2A3S3A3S1S0S2S41SfS10S12Sb1G1A2A1G2A3S3A3S1S0S2Sb7S78S77S22U0M3S23A5S3A3S1S0S24Sc7S78Sb0S8fA3S7eA3S1S0S24S7cSb0S7eA2S76A3S1S0S2S41SfS10S8bA1S2bS78A1A3S3A3S1S0S2S73S2bS76A1M4S35S22S23S80A5S3A3S1S0S2S75G4S35S22S74S26S76A1A5S3A3S1S0S2S41SfS10S8aA1G4A3S3A3S1S0S2S6eG4S11Z0A1S6cS89S36A5S3A3S1S0S2S6dS2cS76A1S36A2S3A3S1S0S24Sb3S7bS76S8cS80S7aA5S86A3S0S8S7SeSeA2M5A1Sc4G5G3S77A3S35A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_j1 : ltac2:(tb__ "0|1|
S1S0S2S2dS83S7fS8eS34S37A5S3A3S1S0S2S2dS84S7fS8dS37S37A5S3A3S0S8S7SeSeA2M0A1Sc4G0U0S77A3S35A3A2A2").
Proof. conj_vmc. Qed.

Definition ndA1p : ndesc := ltac2:(tb__ "0|0|
S51S35S22S36S50Sb2Sa9A2A4").
Definition two52 : Z := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.two52.
Lemma epiD_chk_loop : ltac2:(tb__ "0|e|
S1S0S2S2dSa7S97SadS38S38A5S3A3S1S0S2S2dSa8S97SaeS38S38A5S3A3S1S0S2S2dSa2S96SabS3eS3cA5S3A3S1S0S2S2dS98S96S9cS3fS3cA5S3A3S1S0S2S68S43S2cSa6A1M0A2S3A3S1S0S2S4aG0S37A2S3A3S1S0S2S68S43S2cS94A1M1A2S3A3S1S0S2S4aG1S33A2S3A3S1S0S2S6aS2bS94A1M2S35S22S23S15S25S94A1A1A5S3A3S1S0S2Sb5G2S35S26S94A1A3S3A3S1S0S4fS51S5S7SeSeA2M3SbSeSeSb2Sc6S13S69G1P1M4A2A1A1A4S35A3S22S9S6bS36S5S6bS6fZ0Z1S6cA3S4S6bA1A3A3M5S50S13G1A1S13S69G1P3M6A2A1A2A4S3eA3S1S0S2S68S43S2cS95A1M7A2S3A3S1S0S2S4aG7S40S9fS92A2A2S3A3S1S0S2S6aS2bS95A1M8S35S22S23S15S25S95A1A1A5S3A3S1S0S2Sb5G8S35S26S95A1A3S3A3S1S0S4fS51S5G3SbSeSeS9fSc6S13S69G7G4A2A1A1A4S35A3S22G5S50S13G7A1S13S69G7G6A2M9A1A2A4S3fA3S1S0SbaG9S69SaaG6A2MaA3S1S0S2S41SfS10S12S92S11S32A1MbA2A1G8A3S3A3S1S0S2S41SfS10S12S13GaA1McGbA2A1S2bS98A1A3S3A3S0SeSc2S9cS3bS92Z8MdA2A2S3bGcGdA2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_fd : ltac2:(tb__ "0|4|
S1S0S24S7cS9eSa1A2S91A3S1S0S2S73S2bS91A1M0S35S22S23S9aA5S3A3S1S0S2S75G0S35S22S74S26S91A1A5S3A3S1S0S2S41SfS10S1aS18SceS9eS11Z0M1A1M2A3A1A1G0A3S3A3S1S0S2S6eG0G2S6cS9S6bS36S5S6bS6fG1Z1S6cA3S4S6bA1A3A3S36A5S3A3S1S0S2S6dS2cS91A1M3S36A2S3A3S1S0S2S4aG3S3cA2S3A3S1S0S24Sb3S7bS91SafS9aS7aA5Sa4A3S1S0S2S41SfS10S12S92S11S32A1A2A1G0A3S3A3S0S2S20G3S3bS92Z6A2A2S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition shape_ok (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
S42S24S24SaSaS8S14A1M0S2Lx;ScfS25VPre;A1S25R1A1A2S3S14G0S6Ll;Ls;X8x2Sd0VPre;R1A2A2S21S27R1A1S27VPre;A1A2A2LL;VLs;A3").
Definition g5_facts : list sprop := ltac2:(tb__ "0|0|
S5SfS19S2aS44A1S13P6eA1A2S5SfS12S13S44A1S11Sd5Sd4Z2Z3dA2Z1A2A1A2S4SfA1A3A3").
Lemma epiD_chk_fa : ltac2:(tb__ "0|2|
S1S0S24S7cSbcSa0A2S90A3S1S0S2S73S2bS90A1M0S4S7SeSeA2A1M1S22S23S99A5S3A3S1S0S2S75G0G1S22S74S26S90A1A5S3A3S1S0S2S41SfS10S12S11Z1000A1SbcA2A1G0A3S3A3S1S0S2S6eG0S11Z0A1S6cS36S4S6bA1A5S3A3S1S0S2S4aS2cS90A1S38A2S3A3S0S24Sb3S7bS90SacS99S7aA5Sa3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_ml : ltac2:(tb__ "0|2|
S1S0S2Sb4S43S9dA2S3A3S1S0S2S68S43S2cS93A1M0A2S3A3S1S0S2S4aG0S37A2S3A3S1S0S2S30S47S5S24S46S4S24A1A3A2S3A3S1S0S2S73S2bS93A1M1S35S22S23S9bA5S3A3S1S0S2S75G1S35S22S74S26S93A1A5S3A3S1S0S24Sb3S47S93S9dS9bS46A5Sa5A3S0S2S6dG0S36A2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiD_chk_s8 : ltac2:(tb__ "0|7|
S1S0SeS27S5aA1S11SccA1M0A3S1S0S2S28S2eS2bS5aA1M1A2S3A3S1S0S2S6aG1S4S7SeSeA2A1M2S22S23S15S25S5aA1A1A5S3A3S1S0S2Sb4S43S65S5bA1A2S3A3S1S0S2S68S43S2cS5bA1M3A2S3A3S1S0S2S4aG3S3aA2S3A3S1S0S2S30SbeS5S24SbdS4S24A1A3A2S3A3S1S0S2S73S2bS5bA1M4G2S22S23S61A5S3A3S1S0S2S75G4G2S22S74S26S5bA1A5S3A3S1S0SeS27S58A1G0A3S1S0S2S28S2eS2bS58A1M5A2S3A3S1S0S2S4aS2cS58A1S3aA2S3A3S1S0S2S6aG5G2S22S23S45S58A1A5S3A3S1S0SeS27S59A1G0A3S1S0S2S28S2eS2bS59A1M6A2S3A3S0S2S6aG6G2S22S23S15S25S59A1A1A5S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Definition she : sobj := Eval vm_compute in last (ss_objs (ax_S Ee_sfA)) dflt_obj.
Definition Te_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf Ee_sf (s_sf Ee_sf) Re_sf L_sf (ax_X Ee_sf).
Lemma epiD_chk_sf : ltac2:(tb__ "0|8|
S1S0SeS27S55A1S11SccA1M0A3S1S0S8S14A1S15S25S55A1A1S9S14S45S55A1M1S5S14ScbS44Z14Z34S1cS31A1S1dS31A1M2A5S4S14A1A3A3A3S1S0S2S1bG2A1S3A3S1S0S2S28S2eS2bS55A1M3A2S3A3S1S0S2S4aS2cS55A1S3aA2S3A3S1S0S2S6aG3S4S7SeSeA2A1M4S22S23G1A5S3A3S1S0S24S67S55A1S5cA3S1S0SeS27S57A1G0A3S1S0S24Sc8S57P78A2S56A3S1S0S2S16S25S56A1A1S3A3S1S0S2S6aS2bS57A1M5G4S22S23S15S25S57A1A1A5S3A3S1S0S2Sb5G5G4S26S57A1A3S3A3S1S0S2Sb4S43S66S56A1M6A2S3A3S1S0S2S68S43S2cS56A1M7A2S3A3S1S0S2S4aG7S3aA2S3A3S1S0SeSc0G6PcA2S48A3S1S0SeSc0G6Sd3A2S49A3S1S0S2Sd2S2bS56A1G4S22ScSdU0A2S23S5dA6S3A3S1S0S24Sd1S60S56G6S5dS5fS26S56A1A6S2fA3S0S24SbfS2fA1S63A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_sx : ltac2:(tb__ "0|4|
S1S0S24ScaS5aS64S5aA1S44Z38ZdbA5M0S5eA3S1S0S2S16S25G0A1A1S3A3S1S0S24Sc9S58S45S58A1P6eM1S4S7Sb9Sb9A2A1M2A4S59A3S1S0S24ScaS59S26S59A1S44Z14Z34A5M3S62A3S1S0S2S16S25G3A1A1S3A3S1S0S24Sc9S55S45S55A1G1G2A4S5cA3S0S2S16S25Sc8S57P78A2A1A1S3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
