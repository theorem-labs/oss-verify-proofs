(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "pair"; "cons"; "prod"; "nat"; "nil"; "app"; "Some"; "fst"; "option"; "list"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "SAlu"; "ss_facts"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aml"; "s_ml"; "E_ml"; "R_ml"; "Xk_ml"; "T_ml_f0"; "T_ml_ok0"; "B_ml_f"; "B_ml_ok"; "PDk_ml"; "T_ml_f"; "T_ml_ok"; "xfb_ml"; "cutsM"; "exitsM"; "extra_ml"; "xf_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "am_subst"; "AHead"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aml.HML"; "Pre_ml"; "P_fail"; "P_ok"; "nd0"; "Posts_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tvL"; "frL"; "A1"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "HNEXT"; "X_latch"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "bdA"; "ndA1"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_handle_mtllib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_handle_mtllib_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HMLAddr.
Module HML. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_handle_mtllib. End HML.

Definition xf_ml : list axform := ltac2:(tb__ "0|2|
S5S3cS41U7M0S13N100M1A1A2S5S3cS3eG0G1A2S8S3cA1A3A3").
Definition E_ml : axst := Eval vm_compute in optL (apply_axforms E_hm xf_ml).
Definition s_ml : wsub := ltac2:(tb__ "0|1|
S5S6S43S12A2M0S4S43S12S44S4cA4S5G0S4S43S12P13S16S69S48S13Z100A1A3A4S72PaS10S1bA1S10S33A1A3A3A3").
Definition R_ml : list sobj := Eval vm_compute in optR (entails_frA E_ml HML.Pre_ml s_ml).
Definition PDk_ml : list pdescK := ltac2:(tb__ "0|0|
S76S65S37S44S2A3A1").
Definition Xk_ml : list (sv * sv) := Eval vm_compute in ax_X E_ml.
Definition extra_ml (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S3bVo;A1S2S6cVo;A1X3x2").

Lemma aml_checks : ltac2:(tb__ "0|e|
S1S0ScSfA1S3dS70S29A2SaSfS1bA2A3S1S0ScSdS14A1M0A1S5dS1bS33S1aA3SaG0S1cA2A3S1S0S3S5cS1bS33S1aS1cS67S6S6SfS2aA2M1S15S15OF_;F_;M2A2M3SfG3SbSfS2aSbG1G2R1A3A3Ld;S22A4A5S2A3S1S0S3S77S47S1aA2S2A3S1S0S3S73S1aS51A2S2A3S1S0S3S5fS1aS8S6S12S12A2M4A1M5S30S64S44S2S36A3M6A1A3S2A3S1S0S3S31S2cS1aS2eG6A1A2S2dS4cS2A2M7A2S2A3S1S0S3S79S6S61G2A2M8G8S62S33S51S1aS18S10S1bA1M9A1MaSbS61G2R1A3A5Ld;S22A3S2A3S1S0S3S63S1dS11S1bA1A2S2A3S1S0SdS49A1S4aS1aS2fG6A1A2S8S49A1A3S1S0S3S74S17G9A1MbS13Z0McA1GcS55S3aA1MdGdA5S2A3S1S0S3S32GaS2bS9G4S38G5A3S39GdG7A4A2S2A3S1S0S3S4bGaGdA2S2A3S1S0S3S7aS47GaA2S2A3S1S0S43GaS4dA3S1S0S3S6dGbS38S39S28S1cA5S2A3S1S0S3S6fGbS38S39S6eS1dA5S2A3S0S3S6bGbA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_tvL : ltac2:(tb__ "0|0|
S78S6S12S12A2S4S12S12S4fS52Z10S50A2A4S38A3").
Proof. cbn. do 18 right. left. reflexivity. Qed.

Definition T_ml_ok0 : axst := Eval vm_compute in T_afterA3 HML.Pre_ml E_ml s_ml R_ml HML.P_ok Xk_ml.
Definition T_ml_f0 : axst := Eval vm_compute in T_afterA3 HML.Pre_ml E_ml s_ml R_ml HML.P_fail Xk_ml.
Definition xfb_ml (T : axst) : list axform := ltac2:(tb__ "0|2|
S5S3cS3eU0M0Z100A2S5S3cS40S5S7G0S5S7U3S5S7U1S5S7U2S68U4M1S66SeS14S19S10VT;A1A1A2G1A2A2A3A3A3A3A1S5S3cS3fG0A1S8S3cA1A3A3A3").
Definition B_ml_ok : axst := Eval vm_compute in optL (apply_axforms T_ml_ok0 (xfb_ml T_ml_ok0)).
Definition B_ml_f : axst := Eval vm_compute in optL (apply_axforms T_ml_f0 (xfb_ml T_ml_f0)).
Definition T_ml_ok : axst := Eval vm_compute in ax_tidy B_ml_ok.
Definition T_ml_f : axst := Eval vm_compute in ax_tidy B_ml_f.
Lemma aml_checks_nd : ltac2:(tb__ "0|a|
S1S0S2aS2bS9S6S12S12A2M0S38S5eS5bS1aS33S35S1bA4M1S30S64S44S2S36A3M2A1M3A2A3S39S9S49S4aG1S2fG2A1M4A2S55S3aA1M5A3S2cG1S2eG2A1M6A2A4S2bS9G0S38S8G0A1A3S39G5S2dS4cS2A2A4M7A3S1S0S2aS2bS9G0S38S5eS5bS1aS33S34S1bA4M8G3A2A3S39S9S49S4aG8G4A2G5A3S2cG8G6A2A4G7A3S1S0SfS60S33S1bS1aS1cS35S1dA6S1fA3S1S0SfS60S33S1bS1aS1cS34S1dA6S1eA3S1S0ScSfA1M9S3dS1fS25S1fA1A2SaSfS21A2A3S1S0G9S3dS1eS25S1eA1A2SaSfS20A2A3S1S0SfS5aS21A1S24A3S0SfS5aS20A1S23A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsM : list efnode := ltac2:(tb__ "0|6|
S5S6S6S6SfS2aA2M0S7A2M1S6S42S12A2M2A2M3S4G1G2S4G0S7S4SfS2aS24S56A4U1M4A4S4S42S12S53S54ZaS57A2A4M5A4S5G3S4G1G2S4G0S7S4SfS2aS23S56A4G4A4G5A4S8G3A1A3A3").
Definition exitsM : list efnode := ltac2:(tb__ "0|6|
S5S6S6S6SfS2aA2M0S7A2M1S6S42S12A2M2A2M3S4G1G2S4G0S7S4SfS2aS4eS58A4U1M4A4S4S42S12S53S54Z1S57A2A4M5A4S5G3S4G1G2S4G0S7S4SfS2aS71S59A4G4A4G5A4S8G3A1A3A3").
Lemma ecertM_ok : ltac2:(tb__ "0|0|
S0S3S75S6aS47S45Uc8S46S47S26S27A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
