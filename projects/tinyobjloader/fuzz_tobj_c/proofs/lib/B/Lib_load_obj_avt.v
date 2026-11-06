(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "prod"; "pair"; "nat"; "nil"; "app"; "Some"; "list"; "option"; "fst"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "sobj"; "ss_next"; "SPUle"; "cell"; "ss_facts"; "sprop_below"; "ss_objs"; "valuation"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt"; "s_vt"; "E_vt"; "S_vt_okR"; "brest_vt"; "R_vt"; "tv_vt"; "E_vt1"; "T_vt_f0"; "T_vt_ok0"; "T_vt_ok1"; "Xk_vt"; "bd_vt"; "c_avt"; "B_vt_f"; "B_vt_ok"; "PDk_vt"; "T_vt_ok"; "hand_vt"; "kept_vt"; "nd_vt_ok"; "xfb_vt"; "T_vt_f"; "avt_cell_new"; "avt_cell_old"; "bd_vt_ok"; "bdrest_vt"; "d_avt"; "d_aw"; "k_avt"; "k_aw"; "ndX_vt"; "nd_vt_f"; "passed_vt"; "rate_t1"; "room_vt"; "t1"; "tv_vt_f"; "tv_vt_ok"; "upd_cellv"; "upd_objv"; "xf_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt.HVT"; "Pre_vt"; "P_fail"; "P_ok"; "Posts_vt"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "HNEXT"; "X_latch"; "pE0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "AK1"; "LAK"; "bdA"; "bdX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "bd_permb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hvt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HVTAddr.
Module HVT. Include Lib_handle_vt. End HVT.

Definition c_avt : sv := t_c (v_avt vsP).  Definition d_avt : sv := t_d (v_avt vsP).  Definition k_avt : sv := t_k (v_avt vsP).
Definition c_aw : sv := t_c (v_avtw vsP).  Definition d_aw : sv := t_d (v_avtw vsP).  Definition k_aw : sv := t_k (v_avtw vsP).

Definition room_vt : list sprop := ltac2:(tb__ "0|1|
S3S11S15S37S10Sa2Z2M0Z1bA2A1A2S3S11S15S7cZ4S12S78S12S79S37S10Z1A1A3S10G0A1A3A2S10S99A1A2S8S11A1A3A3").

Definition xf_vt : list axform := ltac2:(tb__ "0|2|
S3S64S69U7M0S10Na0M1A1A2S3S64S66G0G1A2S8S64A1A3A3").
Definition E_vt1 : axst := Eval vm_compute in optL (apply_axforms E_hvt xf_vt).
Definition E_vt : axst := Eval vm_compute in ax_add_facts room_vt E_vt1.
Definition s_vt : wsub := ltac2:(tb__ "0|1|
S3S5S71SfA2M0S6S71SfS73S74A4S3G0S6S71SfP13S12S78S89S10Za0A1A3A4S9bPaS28S2cA1S28S54A1A3A3A3").
Definition R_vt : list sobj := Eval vm_compute in optR (entails_frA E_vt HVT.Pre_vt s_vt).
Definition PDk_vt : list pdescK := ltac2:(tb__ "0|0|
S9fS7fS57S73S2A3A1").

Definition passed_vt : list (sv * sv) := ltac2:(tb__ "0|2|
S3S5SfSfA2M0S6SfSfS45S7cZ4M1S47A2A4S3G0S6SfSfS46S7cG1S48A2A4S8G0A1A3A3").
Definition kept_vt : list (sv * sv) := Eval vm_compute in (firstn 3 tvL ++ skipn 5 tvL).
Definition tv_vt : list (sv * sv) := kept_vt ++ passed_vt.

Definition bdrest_vt : list bitem := Eval vm_compute in (firstn 6 bd_rest ++ skipn 10 bd_rest).
Definition brest_vt : list bitem := ltac2:(tb__ "0|0|
S3S6eS6dSa3S6bZ48A2A1S3S6eS85S84A1S44A3A3").
Definition hand_vt : list bitem := Eval vm_compute in bd_subst s_vt (nd_bd (ndh h0 true HVT.nd0)).
Definition bd_vt : list bitem := Eval vm_compute in (firstn 4 (skipn 6 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_vt).

Definition Xk_vt : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_avt ||| sv_eqb (fst r) d_aw)) (ax_X E_vt).

Lemma avt_checks : ltac2:(tb__ "0|c|
S1S0ScS27A1S65S98S53A2SaS27S31A2A3S1S0S27S8bS31S9S11S4dS17S28S31A1M0A1A3M1A2S2cA3S1S0ScSbS13A1M2A1S8eS2cS54S2bA3SaG2S2fA2A3S1S0S4S8dS2cS54S2bS2fS7aS5S5S27S5bA2M3S1aS1aOF_;F_;M4A2M5S27G5SdS27S5bSdG3G4R1A3A3Ld;S3aA4A5S2A3S1S0S4Sa0S88S2bA2S2A3S1S0S4S9dS2bS7dA2S2A3S1S0S4S90S2bS4bS61S7eS73S2S58A3M6A1A3S2A3S1S0S4S62S5eS2bS5fG6A1A2S5dS74S2A2M7A2S2A3S1S0S4S80S5S92G4A2M8G8S93S54S7dS2bS14S28S2cA1M9A1MaSdS92G4R1A3A5Ld;S3aA3S2A3S1S0S4S95S6cS30A2S2A3S1S0S4S95S30S6cA2S2A3S1S0S4S96S86S6bA1S36A2S2A3S1S0S4S94S35S2aS2cA1A2S2A3S1S0SbS6eA1S6fS2bS60G6A1A2S3cA3S1S0S4S9eS17G9A1S10Z0MbA1GbS36S9S6eS3cS2eA3A5S2A3S1S0S4S63GaS5cS30S6aS36G7A4A2S2A3S1S0S4S70GaS2eA2S2A3S1S0S4Sa1S88GaA2S2A3S1S0S71GaS75A3S0S4S80S11S18S14G0A1A1G1A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_vt_ok0 : axst := Eval vm_compute in T_afterA3 HVT.Pre_vt E_vt s_vt R_vt HVT.P_ok Xk_vt.
Definition T_vt_f0 : axst := Eval vm_compute in T_afterA3 HVT.Pre_vt E_vt s_vt R_vt HVT.P_fail Xk_vt.
Definition isub_ok : wsub := Eval vm_compute in import_subA s_vt HVT.Pre_vt HVT.P_ok E_vt.
Definition isub_f : wsub := Eval vm_compute in import_subA s_vt HVT.Pre_vt HVT.P_fail E_vt.
Definition tv_vt_ok : list (sv * sv) := Eval vm_compute in (kept_vt ++ import_tv isub_ok (nd_tv HVT.nd_ok)).
Definition bd_vt_ok : list bitem := Eval vm_compute in (bd_subst isub_ok (nd_bd HVT.nd_ok) ++ brest_vt).
Definition tv_vt_f : list (sv * sv) := Eval vm_compute in (kept_vt ++ import_tv isub_f (nd_tv HVT.nd_fail)).
Definition nd_vt_ok : ndesc := ltac2:(tb__ "0|0|
S5cS50S6aS43S5dS74S2A2A4").
Definition nd_vt_f : ndesc := ltac2:(tb__ "0|0|
S5cS4fS6aS2eS5dS74S2A2A4").
Lemma avt_checks_nd : ltac2:(tb__ "0|5|
S1S0S5bS5cS9S5SfSfA2M0S3dS8fS8cS2bS54S56S2cA4M1S61S7eS73S2S5aA3M2A1A2A3S6aS9S6eS6fG1S60G2A1A2S2eA3S5eG1S5fG2A1A2A4S3eA3S1S0S5bS5cS9G0S3dS8fS8cS2bS54S55S2cA4M3S61S7eS73S2S59A3M4A1A2A3S6aS9S6eS6fG3S60G4A1A2S2eA3S5eG3S5fG4A1A2A4S4aA3S1S0S27S91S54S2cS2bS2fS56S35A6S33A3S0S27S91S54S2cS2bS2fS55S35A6S32A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xfb_vt (T : axst) : list axform := ltac2:(tb__ "0|2|
S3S64S66U0M0Za0A2S3S64S68S3S7G0S3S7U3S3S7U1S3S7U2S7bU4M1S97SeS13S19S28VT;A1A1A2G1A2A2A3A3A3A3A1S3S64S67G0A1S8S64A1A3A3A3").
Definition B_vt_ok : axst := Eval vm_compute in optL (apply_axforms T_vt_ok0 (xfb_vt T_vt_ok0)).
Definition B_vt_f : axst := Eval vm_compute in optL (apply_axforms T_vt_f0 (xfb_vt T_vt_f0)).
Definition T_vt_ok1 : axst := Eval vm_compute in ax_tidy B_vt_ok.
Definition T_vt_f : axst := Eval vm_compute in ax_tidy B_vt_f.

Definition t1 : sv := SAlu ALU_ADD c_avt (SLit 1).
Definition avt_cell_old : sv := ltac2:(tb__ "0|0|
S12S78S12S79S37S10Z1A1A3S10Z2A1A3").
Definition avt_cell_new : sv := SAlu ALU_SLL t1 (SLit 1).
Definition upd_cellv (old new : sv) (c : cell) : cell := ltac2:(tb__ "0|0|
S4S16L_;S25S1cVc;A1Vold;A2S1eS1bVc;A1S1dVc;A1Vnew;A3Vc;X4x2").
Definition upd_objv (old new : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1fS20Vo;A1S24Vo;A1S23Vo;A1S7aS16S16S51Vold;Vnew;A2S21Vo;A1A4S22Vo;A1A5").
Definition restate_cells (old new : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
S29VA;S9cS28VA;A1M0S7aS13S13S52Vold;Vnew;A2S19G0A1A4A2A2").
Definition rate_t1 : sprop := ltac2:(tb__ "0|0|
S15S4eS12S78S77S10Z1A1A3A2").
Definition S_vt_okR : sstate := Eval vm_compute in ax_S (restate_cells avt_cell_old avt_cell_new T_vt_ok1).
Definition T_vt_ok : axst := Eval vm_compute in ax_add_facts [rate_t1] (ax_setS T_vt_ok1 S_vt_okR).
Lemma avt_checks_back : ltac2:(tb__ "0|9|
S1S0ScS27A1M0S65S33S3fS33A1A2SaS27S39A2A3S1S0G0S65S32S3fS32A1A2SaS27S38A2A3S1S0S27S8aS39A1S34A3S1S0S27S8aS38A1S40A3S1S0S4S26S2dA1S2A3S1S0ScS5SbS5SfSfA2M1A1M2SbS11A1M3A2M4A1S9aS28S34A1M5S2dA2SaG4S6G2G3S3G1S6SfSfS42S41A4S8G1A1A3S8S11A1M6A4A2A3S1S0S71S14S2dA1M7S14G5A1A3S1S0S27S8bS29S34S2dA2S9S11S3S11S4cG6A3M8S17S2dA1A3A2S3bA3S0S4S80S11S18G7A1G8A3S2A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndX_vt : ndesc := ltac2:(tb__ "0|0|
S5cS30S6aS87Z0A1S5dS74S2A2A4").
Definition cutsT : list efnode := ltac2:(tb__ "0|4|
S3S5S5S5S27S5bA2M0S7A2M1S5S72SfA2M2A2M3S6G1G2S6G0S7S6S27S5bS3bS3eA4U1A4S6S72SfS81S82ZaS83A2A4A4S8G3A1A3").
Definition exitsT : list efnode := ltac2:(tb__ "0|4|
S3S5S5S5S27S5bA2M0S7A2M1S5S72SfA2M2A2M3S6G1G2S6G0S7S6S27S5bS76S49A4U1A4S6S72SfS81S82Z1S83A2A4A4S8G3A1A3").

