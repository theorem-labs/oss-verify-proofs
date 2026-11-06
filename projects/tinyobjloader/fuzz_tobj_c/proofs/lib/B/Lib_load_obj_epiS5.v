(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "swf"; "ss_objs"; "ss_pc"; "ob_base"; "ob_lo"; "ss_next"; "DUnknown"; "cell"; "ss_facts"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "false"; "true"; "nat"; "Some"; "nil"; "pair"; "option"; "list"; "prod"; "app"; "negb"; "orb"; "None"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "la_reason"; "la_state"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "AXSplit"; "AXUnbase"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vOUT"; "idxB"; "g5"; "objs_butlast"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5"; "s_pok"; "Es_mc"; "Es_s8"; "nd_okL"; "Es_s8a"; "Es_sf"; "P_errM"; "P_okF"; "Ts_s81"; "s_mcS"; "Es_mc1"; "Es_mc2"; "Es_sfB"; "Es_sfC"; "P_errR"; "P_okR"; "Rs_mc"; "Rs_s8"; "Ts_mc"; "Ts_mc0"; "Ts_s8"; "Ts_s80"; "Ts_s82"; "Ts_s8r"; "Bs_mc"; "Es_sf0"; "P_okL"; "P_okM"; "Rs_sf"; "Ts_sf"; "s_perr"; "xf_mergeR"; "xf_rebaseR"; "Es_s80"; "Es_sfA"; "Es_sfD"; "fr_offR"; "frame_idxR"; "needs_rebaseR"; "xfb_mcS"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "nobj"; "cps_ad"; "L_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5.IF"; "nd_lo_ok"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "Pre_mc48"; "Pre_f8"; "L_f8"; "L_mc48"; "ax_tidy"; "vARn"; "vALo"; "xf_shback"; "xf_shcall"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "filter"; "existsb"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "P_errL"; "Pre_sf"; "dflt_obj"; "L_sf"; "insert_by"; "s_s8"; "s_sf"; "sx_T82"; "sx_T8r"; "sx_s8a"; "xf_merge"; "xf_rebase"; "xf_sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "AHead"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_below"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "lo_ret"; "sf5_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_iface.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3.
Module IF. Include Lib_load_obj_iface. End IF.

Definition Es_mc1 : axst := Eval vm_compute in optL (apply_axforms L_ok [AXSplit (idxB L_ok vOUT 0) (SLit 144)]).
Definition Es_mc2 : axst := Eval vm_compute in optL (apply_axforms Es_mc1 [AXSplit (idxB Es_mc1 vOUT 144) (SLit 192)]).
Definition Es_mc : axst := Eval vm_compute in optL (apply_axforms Es_mc2 [AXUnbase (idxB Es_mc2 vOUT 144) 144]).
Definition s_mcS : wsub := ltac2:(tb__ "0|1|
S12S1bS0S5A2M0S18S0S5P35S35A4S12G0S18S0S5P36S7Zd0A1A4S12G0S18S0S5P37S72A4S12G0S18S0S5P38S7Z30A1A4S12G0S18S0S5Sa6S39A4S77PaS23S3bA1S23S6cA1A3A3A3A3A3A3").
Definition Rs_mc : list sobj := Eval vm_compute in optR (entails_frA Es_mc Pre_mc48 s_mcS).
Definition Ts_mc0 : axst := Eval vm_compute in T_afterA Pre_mc48 Es_mc s_mcS Rs_mc L_mc48.

Definition xfb_mcS (T : axst) : list axform := ltac2:(tb__ "0|3|
S36VT;S35Z0A3S15S36VT;S35Zc0A3S15S12S2aS2cU1M0A1S12S2aS2dS12S15R2S12S15G0S12S15R1S7aS15S15S1dS1eS1eS75R1R3A2S75R1G0A2A2S75R1R2A2A2A1Li;S63U0M1S66VT;A1A2A3A3A3A3A1S12S2aS2bG1A1M2S12S2aG2S17S2aA1A3A3A3A3TiB;TiA;").
Definition Bs_mc : axst := Eval vm_compute in optL (apply_axforms Ts_mc0 (xfb_mcS Ts_mc0)).
Definition Ts_mc : axst := Eval vm_compute in ax_tidy Bs_mc.

Definition Es_s80 : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_mc) ssf8_pc 0.
Definition Es_s8a : axst := Eval vm_compute in sx_s8a Es_s80.
Definition Es_s8 : axst := Eval vm_compute in sx_s8 Es_s80.
Definition Rs_s8 : list sobj := Eval vm_compute in optR (entails_frA Es_s8 Pre_f8 (s_s8 Es_s8)).
Definition Ts_s80 : axst := Eval vm_compute in sx_T80 Es_s8.
Definition Ts_s81 : axst := Eval vm_compute in sx_T81 Ts_s80.
Definition Ts_s82 : axst := Eval vm_compute in sx_T82 Ts_s81.
Definition Ts_s8r : axst := Eval vm_compute in sx_T8r Ts_s82.
Definition Ts_s8 : axst := Eval vm_compute in ax_tidy Ts_s8r.
Definition Es_sf0 : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_s8) sf5_pc 0.
Definition Es_sfA : axst := Eval vm_compute in sx_sfA Es_sf0.
Definition Es_sfB : axst := Eval vm_compute in sx_sfB Es_sfA.
Definition Es_sfC : axst := Eval vm_compute in sx_sfC Es_sfB.
Definition Es_sfD : axst := Eval vm_compute in sx_sfD Es_sfC.
Definition Es_sf : axst := Eval vm_compute in sx_sf Es_sfD.
Definition Rs_sf : list sobj := Eval vm_compute in optR (entails_frA Es_sf Pre_sf (s_sf Es_sf)).
Definition Ts_sf : axst := Eval vm_compute in sx_Tsf Es_sf.
Definition P_okL : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_sf) lo_ret 0.

Definition fr_offR (o : sobj) : option Z := ltac2:(tb__ "0|19|
S5S19S1A1M0Lx;M1SbVo;A1S1S1fS1A1M2Lz;M3S0S0G0Li;M4R1S0G2Lp;M5S0S0G0Lp;M6R1S0S0G0Lp0;M7R1S0G2Lp1;M8S0S0G0Lp1;M9R1S0G2Lp2;MaGaG1ScVo;A1MbS1S16S1R1A2Llo;S0G2Li0;McS30S5S5G2Lb;La;MdLop;MeGeS31GdLop;MfGfS11S2S5G2La;Lw;Lsgn;M10S0S5S1G2Lk;M11Li0;Ll;M12X5x8X0x3Lp1;G2X0x3Lp0;S0G2Lp0;M13G2X0x3Lp;G2X0x3Li;S30S5S5S30G0Lop;R3S5G0La;R2G3S0G4R1G5S0G6R1S0G7R1G8S0G9R1GaGaS5G0Lb;R5S1G1GbS1S16S1Sa7R2R1A2A2Llo;GcS30S5S5G2Lb0;La0;M14Lop0;M15G15S31G14Lop0;M16G16S11S2S5G2La0;Lw;Lsgn;M17G12X5x8Lc;GcG15G15G16G16G17G12X5x8X0x3Lp1;G2X0x3Lp0;G13G2X0x3Lp;G2X0x3Li;G15G15G16G16G17S0S5G11Li;Ll;M18X5x8G2G2G2G2G2G2G2G2G2X30xaLb;La;Lop;GeGfGfG10G18X5x8").

Definition needs_rebaseR (o : sobj) : bool := ltac2:(tb__ "0|d|
S5S11Lx;M0SbVo;A1S1S13Lz;M1S0S13Li;S30S5S5S30S11Lop;R3S5S11La;R2G1S0S0S11Li;R1S0S13Lp;S0S0S11Lp;R1S0S0S11Lp0;R1S0S13Lp1;S0S0S11Lp1;R1S0S13Lp2;M2G2S5S11Lb;R5S1G0ScVo;A1S1S14Lz0;S0S13Li0;M3S30S5S5S13Lb0;La0;M4Lop0;M5G5S31G4Lop0;M6G6S11S2S5S13La0;Lw;Lsgn;M7S0S5S1S13Lk;M8Li0;Ll;M9X5x8Lz;G3G5G5G6G6G7G9X5x8X0x3Lp1;S13X0x3Lp0;S0S13Lp0;S13X0x3Lp;S13X0x3Li;G5G5G6G6G7S0S5G8Li;Ll;MaX5x8S13S13S13S13S13S13S13S13S13X30xaLb;La;Lop;S30S5S5S13Lb;La;MbLop;S31GbLop;McGcS11S2S5S13La;Lw;Lsgn;GaX5x8").
Definition xf_rebaseR (A : axst) : list axform := ltac2:(tb__ "0|0|
S62S15S2aS15S2cR1A1Li;S7aS15S15S60S64S6R1S9S23VA;A1A1S7fA4A1Li;S63U0S66VA;A1A2A3A4").
Definition frame_idxR (A : axst) : list nat := ltac2:(tb__ "0|2|
S62S1bS1S15A2M0S15S21S1S15A2S7cS1aG0A1M1S15S15G1S19S1A1G1Lx;S5eS64S6R2S9S23VA;A1A1S7fA4A1S1S81R1R3R2A3Lk;R1X19x2Lacc;Li;S17G0A1S63U0S66VA;A1A2A5A4").
Definition xf_mergeR (A : axst) : list axform := ltac2:(tb__ "0|1|
S5fVA;A1S1aS15A1S12S2aS2dS1cS15R1S7aS15S15S1dS7bS15S75R1A1R2A3A1Li;S63U0M0S66VA;A1A2A3A3A1S65S2aS2bG0A1S9dS20S15R1A2U1A2A3A3Tfi;").
Definition P_okR : axst := Eval vm_compute in optL (apply_axforms P_okL (xf_rebaseR P_okL)).
Definition P_okM : axst := Eval vm_compute in optL (apply_axforms P_okR (xf_mergeR P_okR)).
Definition P_okF : axst := Eval vm_compute in ax_add_facts (tv_factsA (vARn, SLit 64)) P_okM.
Definition s_pok : wsub := ltac2:(tb__ "0|0|
S77S34S23S41A1S23S6bA1A3").
Definition P_errR : axst := Eval vm_compute in optL (apply_axforms P_errL (xf_rebaseR P_errL)).
Definition P_errM : axst := Eval vm_compute in optL (apply_axforms P_errR (xf_mergeR P_errR)).
Definition s_perr : wsub := ltac2:(tb__ "0|0|
S77S34S23S40A1S23S6aA1A3").

Definition nd_okL : ndesc := ltac2:(tb__ "0|1|
S94S12S1bS5S5A2M0S18S5S5S71S7Z40A1A4S17G0A1A3S17S1bS1bS5S1A2S5A2A1S12S8bS8cZ0S8dZ1A3S17S8bA1A3S93Sa1S13A2A4").

Lemma epiS5_checks_mc : ltac2:(tb__ "0|5|
S4S3S19S22A1M0S29S68S12S2aS2eS36S68S35Z0A3S7Z90M1A1A2S17S2aA1M2A3A2S16S22S44A2A3S4S3G0S29S44S12S2aS2eS36S44S35G1A3S7Zc0A1A2G2A3A2S16S22S45A2A3S4S3G0S29S45S12S2aS2fS36S45S35G1A3G1A2G2A3A2S16S22S3bA2A3S4S3S19S1aS6A1M3A1S79S3bS6cS43A3S16G3S4aA2A3S4S3S11S78S3bS6cS43S4aS12S22S6fS17S22A1A3A5S14A3S4S3S11S9bS34S43A2S14A3S4S3S22S9aS6cS3bS43S4aS6fA5S4dA3S4S3G0S29S4dS61S4dA1A2S16S22S52A2A3S4S3S22S70S52A1S4cA3S4S3S11S25S4cA1S14A3S3S1aS1bS1S32A2M4A1S62S24G4S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS67S4cA3A4S12G4S18S1S32Sa0S33A4S17G4A1A3A3A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_s8 : ltac2:(tb__ "0|5|
S4S3S11S8S23S3eA1A1S14A3S4S3S22S86S5bA1S3eA3S4S3S19S22A1M0S29S3eS74S3eZ38M1A2A2S16S22S3cA2A3S4S3S19S1aS6A1M2A1S79S3cS6dS82S3cA1M3A3S16G2S4bA2A3S4S3S11S78S3cS6dG3S4bS12S22S6eS17S22A1A3A5S14A3S4S3S22S9aS6dS3cG3S4bS6eA5S4fA3S4S3G0S29S4fS73S4fA1A2S16S22S42A2A3S4S3G2S9S23S42A1A1S1cS6S38S42A1S12S6Sa5S37G1ZdbS17SfA1SeA5S17S6A1A3A3A3S4S3S22S84S42A1S50A3S4S3S11S8S23S50A1A1S14A3S4S3S22S85S50A1S51A3S4S3S11S8S23S51A1A1S14A3S4S3S22S70S51A1S4eA3S4S3S11S25S4eA1S14A3S3S1aS1bS1S32A2M4A1S62S24G4S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS67S4eA3A4S12G4S18S1S32S9fS33A4S17G4A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_sf : ltac2:(tb__ "0|4|
S4S3S19S22A1M0S29S53S89S53A1A2S16S22S5cA2A3S4S3S11S8S23S46A1A1S14A3S4S3G0S29S46S88S46A1A2S16S22S47A2A3S4S3G0S29S47S87S47A1A2S16S22S5dA2A3S4S3S11S25S3fA1S14A3S4S3S19S1aS6A1M1A1S79S3fS7eS83S3fA1M2A3S16G1S56A2A3S4S3S11S78S3fS7eG2S56S12S22S80S17S22A1A3A5S14A3S4S3S11S25S57A1S14A3S3S1aS1bS1S32A2M3A1S62S24G3S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS67S57A3A4S12G3S18S1S32S9eS33A4S17G3A1A3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_post : ltac2:(tb__ "0|3|
S4S3S19S22A1M0S29S54S5aS54A1A2S16S22S49A2A3S4S3G0S29S49S59S49A1A2S16S22S55A2A3S4S3S22Sa2S99S18S5S5S71S7Z40A1A4A1S55A2S41A3S4S3S11S28S41S6bS3aA3S14A3S4S3S11S8aS3aS34A2S14A3S4S3S11S9cS34SdS23S41A1M1A1M2A2S14A3S4S3S11S98G2S3dA2S14A3S4S3S11Sa3S3aS92S3dA1S92S69A1A3S14A3S4S3S11S97S3aS91S3dA1S91S69A1A3S14A3S4S3S11Sa4S10G1A1S8eS3aS90S69A1A2S90S3dA1A3S14A3S4S3S11S95S96S3aS8fS69A1A2S8fS3dA1A2S14A3S4S3G0S29S7dS5aS7dA1A2S16S22S48A2A3S4S3G0S29S48S59S48A1A2S16S22S40A2A3S4S3S11S28S40S6aS58A3S14A3S4S3S11S8aS58S34A2S14A3S3S11S9cS34SdS23S40A1A1A2S14A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
