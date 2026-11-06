(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "Some"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_objs"; "swf"; "sprop"; "ss_next"; "ss_facts"; "SPUle"; "dflt_writable"; "ob_cells"; "ob_dflt"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "tvA"; "nd_d2"; "nd_z"; "KU1"; "PhisD"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "g5_facts"; "shape_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5"; "Es_sfA"; "Es_sf"; "Es_s80"; "Es_sfD"; "Ts_s81"; "Ts_s82"; "Es_s8"; "s_perr"; "Es_mc"; "Es_sfB"; "P_okM"; "Rs_sf"; "Ts_sf"; "nd_okL"; "Es_s8a"; "Es_sf0"; "P_errM"; "P_okF"; "P_okL"; "Rs_mc"; "Rs_s8"; "Ts_mc"; "Ts_s8"; "Ts_s8r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "objs_butlast"; "g5"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5.IF"; "nd_lo_err"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "Pre_mc48"; "vARn"; "L_f8"; "L_mc48"; "Pre_f8"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5_chk"; "Ts_sf0"; "shs"; "cutsS5"; "exitsS5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "flag_carve_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "cps_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "L_sf"; "Pre_sf"; "X_sx"; "s_s8"; "s_sf"; "sx_sfB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "ejcertAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_FL"; "@Stdlib.Lists.List";
"existsb"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs Lib_load_obj_epiD_chk Lib_load_obj_epiS5.

Definition cutsS5 : list efnode := ltac2:(tb__ "0|5|
S5S7S7S7ScS44A2M0S6A2M1S7S24S11A2M2A2M3S4G1G2S4G0S6S4ScS44S41S20A4U1M4A4S4S24S11Z163S53A4A4S5G3S4G1G2S4G0S6S4ScS44S42S20A4G4A4S4S24S11Z15eS53A4A4S5G3S4G1G2S4G0S6S4ScS44S38S39A4G4A4S4S24S11Z159S53A4A4S8G3A1A3A3A3").
Definition exitsS5 : list efnode := ltac2:(tb__ "0|5|
S5S7S7S7ScS44A2M0S6A2M1S7S24S11A2M2A2M3S4G1G2S4G0S6S4ScS44S2eS20A4U1M4A4S4S24S11Z162S53A4A4S5G3S4G1G2S4G0S6S4ScS44S3bS20A4G4A4S4S24S11Z15dS53A4A4S5G3S4G1G2S4G0S6S4ScS44S3eS39A4G4A4S4S24S11Z158S53A4A4S8G3A1A3A3A3").
Lemma ecertS5_ok : ltac2:(tb__ "0|0|
S0S2S7bS6eS4eS23U12cS6fS4eS63S64A8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma epiS5_chk_mc : ltac2:(tb__ "0|2|
S1S0S2S5dS4eS29S34A1M0A2S3A3S1S0S2S45G0S20A2S3A3S1S0S2S66G0S22A2S3A3S1S0S2S68S22A1S3A3S1S0S2S2bS56S5ScS59S8ScA1A3A2S3A3S1S0S25S17SdS56A1A1S77A3S1S0S11SeS56A1S12S5cA1A3S1S0S2S5eS28S34A1M1S1fS26S27S3fA5S3A3S0S2S60G1S1fS26S5fSfS34A1A5S3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_chk_s8 : ltac2:(tb__ "0|6|
S1S0S11SeS2eA1S12S5cA1M0A3S1S0S2S10S2aS28S2eA1M1A2S3A3S1S0S2S54G1S1fS26S27S14SdS2eA1A1A5S3A3S1S0S2S69S4eS73S32A1A2S3A3S1S0S2S5dS4eS29S32A1M2A2S3A3S1S0S2S45G2S20A2S3A3S1S0S2S2bS5aS5ScS58S8ScA1A3A2S3A3S1S0S2S5eS28S32A1M3S1fS26S27S40A5S3A3S1S0S2S60G3S1fS26S5fSfS32A1A5S3A3S1S0S11SeS30A1G0A3S1S0S2S10S2aS28S30A1M4A2S3A3S1S0S2S45S29S30A1S20A2S3A3S1S0S2S54G4S1fS26S27S4fS30A1A5S3A3S1S0S11SeS31A1G0A3S1S0S2S10S2aS28S31A1M5A2S3A3S1S0S2S54G5S1fS26S27S14SdS31A1A1A5S3A3S0S2S66G2S22A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Definition shs : sobj := Eval vm_compute in last (ss_objs (ax_S Es_sfA)) dflt_obj.
Definition Ts_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf Es_sf (s_sf Es_sf) Rs_sf L_sf (ax_X Es_sf).
Lemma epiS5_chk_sf : ltac2:(tb__ "0|7|
S1S0S11SeS2cA1S12S5cA1M0A3S1S0SbS13A1S14SdS2cA1A1S9S13S4fS2cA1M1S5S13S6dS50Z14Z34S1bS62A1S1cS62A1M2A5S8S13A1A3A3A3S1S0S2S1aG2A1S3A3S1S0S2S10S2aS28S2cA1M3A2S3A3S1S0S2S45S29S2cA1S20A2S3A3S1S0S2S54G3S1fS26S27G1A5S3A3S1S0ScS75S2cA1S35A3S1S0S11SeS2fA1G0A3S1S0ScS6aS2fP78A2S2dA3S1S0S2S15SdS2dA1A1S3A3S1S0S2S54S28S2fA1M4S1fS26S27S14SdS2fA1A1A5S3A3S1S0S2S7cG4S1fSfS2fA1A3S3A3S1S0S2S69S4eS74S2dA1M5A2S3A3S1S0S2S5dS4eS29S2dA1M6A2S3A3S1S0S2S45G6S20A2S3A3S1S0S11S65G5PcA2S51A3S1S0S11S65G5S7eA2S52A3S1S0S2S7dS28S2dA1S1fS26SaS6U0A2S27S37A6S3A3S1S0ScS79S71S2dG5S37S70SfS2dA1A6S61A3S0ScS5bS61A1S38A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS5_chk_sx : ltac2:(tb__ "0|4|
S1S0ScS6cS2eS72S2eA1S50Z38ZdbA5M0S3aA3S1S0S2S15SdG0A1A1S3A3S1S0ScS6bS30S4fS30A1P6eM1S8S7S24S24A2A1M2A4S31A3S1S0ScS6cS31SfS31A1S50Z14Z34A5M3S43A3S1S0S2S15SdG3A1A1S3A3S1S0ScS6bS2cS4fS2cA1G1G2A4S35A3S0S2S15SdS6aS2fP78A2A1A1S3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_chk_post : ltac2:(tb__ "0|4|
S1S0S2S80S16S1dS17SdS36A1M0A1A1S9S16S4dS4S11S11S57S12Z40A1A4A1S18G0A1M1A3M2A3S3A3S1S0ScS76S36G2A2S3dA3S1S0S2S7fS16S1eS19S12Z1000A1S57A2A1G1A3S3A3S1S0S2S45S17SdS3cA1M3A1S21A2S3A3S1S0S2S78S33S49S21A1S49S55A1A3S3A3S1S0S2S4cS33S48S21A1S48S55A1A3S3A3S1S0S2S7aS18G3A1S67S33S47S55A1A2S47S21A1A3S3A3S0S2S4aS4bS33S46S55A1A2S46S21A1A2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
