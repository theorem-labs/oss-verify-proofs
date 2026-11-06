(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "app"; "prod"; "Some"; "nat"; "nil"; "option"; "fst"; "list"; "length"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SLit"; "SVar"; "sprop_eqb"; "sv"; "ss_facts"; "ss_next"; "SAlu"; "SMd"; "SPUlt"; "sobj"; "valuation"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "s_vn"; "E_vn"; "R_vn"; "kept_vn"; "Xk_vn"; "brest_vn"; "T_vn_f0"; "T_vn_ok0"; "bd_vn"; "h0"; "tv_vn"; "PDk_vn"; "cutsV"; "exitsV"; "hand_vn"; "room_vn"; "PhisV"; "T_vn_f"; "T_vn_ok"; "c_avn"; "cps_arm"; "k_avn"; "nd_vn_f"; "nd_vn_ok"; "passed_vn"; "xf_vn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn.HVN"; "Pre_hvn"; "P_fail"; "P_ok"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "A1"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "bud_pay2"; "ejcertAF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn_eqs"; "E_vn1"; "xfb"; "B_vn_f"; "B_vn_ok"; "H_ecertV_ok"; "extra_vn"; "keep_ecertV_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "AHead"; "am_eqb"; "nd_below"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "HNEXT"; "xLC"; "pNX"; "pH"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "bd_permb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition keep_ecertV_ok : list sprop := ltac2:(tb__ "0|a|
S4SfS19S12P1ccA1S12P1d3A1M0A2S4SfS10S12P1eaA1S12P1e0A1M1A2S4SfS10S12P197A1M2S18S4eS11Z3A1S17S4dS17S4dG1S12P1e1A1A3M3S11Z1A1A3A3A2S4SfS10G0S12PeA1M4A2S4SfS10G3G4A2S4SfS10G4S11Z4000000A1A2S4SfS10S12P196A1M5S12P1eA1M6A2S4SfS10S17S4dG5S18S4eS11Z4A1S12P198A1M7A3M8A3G6A2S4SfS10G5S11Z800000000000A1A2S4SfS10G2G7A2S4SfS10G7S11ZffffffffA1M9A2S4SfS10G8G9A2S9SfA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition H_ecertV_ok : list sprop := ltac2:(tb__ "0|0|
S8cS55S5S4aS2aS2bA3A2").
Lemma ecertV_ok : ltac2:(tb__ "0|1|
S0S3S4cS85S45S2eUc8S32S45S67S4aS4aS8bS53A1M0S2aA4S67S4aS4aG0S2bA4A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma avn_checks : ltac2:(tb__ "0|a|
S1S0SaScS1aA1M0A1S79S1fS3eS1eA3S7G0S20A2A3S1S0S3S78S1fS3eS1eS20S67S6S6S38S5eA2M1S1bS1bOF_;F_;M2A2M3S38G3SbS38S5eSbG1G2R1A3A3Ld;S29A4A5S2A3S1S0S3S8dS45S1eA2S2A3S1S0S3S89S1eS7aA2S2A3S1S0S3S7cS1eS36S63S75S27S2S41A3M4A1A3S2A3S1S0S3S65S60S1eS61G4A1A2S64S71S2A2M5A2S2A3S1S0S3S3cS6S7eG2A2M6G6S7fS3eS7aS1eS16S39S1fA1M7A1M8SbS7eG2R1A3A5Ld;S29A3S2A3S1S0S3S81S47S28A2S2A3S1S0S3S82S87S48A1S26A2S2A3S1S0S3S80S22S3aS1fA1A2S2A3S1S0ScS5bA1S5cS1eS62G4A1A2S2cA3S1S0S3S4bS15G7A1S11Z0M9A1G9S26S5S5bS2cS23A3A5S2A3S1S0S3S66G8S5fS28S46S26G5A4A2S2A3S0S3S5dG8S23A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition extra_vn (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S49Vo;A1S2S6aVo;A1X3x2").

Definition E_vn1 : axst := Eval vm_compute in optL (apply_axforms E_hvn xf_vn).
Lemma E_vn1_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S88S37A2S7S38S4fA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vn_eq : ltac2:(tb__ "0|0|
S0S38S8aS4fS5SfS4SfS2dS9SfA1A3S15S39S4fA1A1A3A2S1fA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma avn_checks2 : ltac2:(tb__ "0|5|
S1S0S3S6bS15S39S1fA1M0A1M1S21S46S54S20A5S2A3S1S0S3S6dG1S21S46S6cS22A5S2A3S1S0S3S69G1A1S2A3S1S0S3S81S28S47A2S2A3S1S0S3S76S45S16G0A1M2A2S2A3S1S0S84G2S6eA3S1S0S3S3bSfS13S10S6fS44A2A1S15S39S4fA1M3A1M4A3S2A3S1S0S3S3bSfS13S10S44S11Z4000000A1A2A1G4A3S2A3S1S0S3S3bSfS13S19S72S6fA2A1G4A3S2A3S1S0S3S3bSfS13S10S33S11ZffffffffA1A2A1G1A3S2A3S1S0S3S3bSfS13S10S31S18S4eS11Z3A1S70A3A2A1G4A3S2A3S1S0S3S3bSfS13S10S70S17S4dS44S11Z1A1A3A2A1G4A3S2A3S0S3S3cSfS1cS16G3A1A1S5SfS4SfS2dS9SfA1A3G4A3A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept : ltac2:(tb__ "0|0|
S3dS6S14S14A2SeS14S14S73S86Z10S74A2A4S21A3").
Proof. cbn. do 17 right. left. reflexivity. Qed.

Lemma T_vn_ok0_eq : ltac2:(tb__ "0|0|
S0S38S7dS3eS1fS1eS20S40S22A6S25A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_f0_eq : ltac2:(tb__ "0|0|
S0S38S7dS3eS1fS1eS20S3fS22A6S24A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition xfb (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S56S5aU0M0Z80A2S4S56S59S4S8G0S4S8U3S4S8U1S4S8U2S68U4M1S83SdS1aS1dS39VT;A1A1A2G1A2A2A3A3A3A3A1S4S56S58G0A1S9S56A1A3A3A3").
Definition B_vn_ok : axst := Eval vm_compute in optL (apply_axforms T_vn_ok0 (xfb T_vn_ok0)).
Definition B_vn_f : axst := Eval vm_compute in optL (apply_axforms T_vn_f0 (xfb T_vn_f0)).
Lemma B_vn_ok_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S25S50S25A1A2S7S38S52A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma B_vn_f_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S24S50S24A1A2S7S38S51A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_ok_eq : ax_tidy B_vn_ok = T_vn_ok.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_f_eq : ax_tidy B_vn_f = T_vn_f.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma nd_vn_ok_eq : ltac2:(tb__ "0|2|
S0S5eS5fS5S6S14S14A2S21S7bS77S1eS3eS40S1fA4M0S63S75S27S2S43A3M1A1A2A3S46S5S5bS5cG0S62G1A1A2S23A3S60G0S61G1A1A2A4S35A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nd_vn_f_eq : ltac2:(tb__ "0|2|
S0S5eS5fS5S6S14S14A2S21S7bS77S1eS3eS3fS1fA4M0S63S75S27S2S42A3M1A1A2A3S46S5S5bS5cG0S62G1A1A2S23A3S60G0S61G1A1A2A4S34A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma avn_checks3 : ltac2:(tb__ "0|6|
S1S0S3S69S15S39S30A1M0A1M1A1S2A3S1S0S3S69S15S39S2fA1M2A1M3A1S2A3S1S0S3S3bSfS13S10S6fS44A2A1M4G1A3S2A3S1S0S3S3bSfS13S10S44S11Z4000000A1A2A1M5G1A3S2A3S1S0S3S3bSfG4G3A3S2A3S1S0S3S3bSfG5G3A3S2A3S1S0S3S76S6eS16G0A1A2S2A3S0S3S76S6eS16G2A1A2S2A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
