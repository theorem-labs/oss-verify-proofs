(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "app"; "nat"; "nil"; "prod"; "pair"; "list"; "Some"; "fst"; "S"; "option"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXSplit"; "AXRebase"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "SAlu"; "sobj"; "SPUle"; "sprop_eqb"; "ss_facts"; "ss_objs"; "DUnknown"; "SPEq"; "SVar"; "ss_next"; "valuation"; "SPUlt"; "ob_cells"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "axwf"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "s_o1c"; "E_o1c"; "R_o1"; "brest_o1"; "kept_o1"; "Xk_o1"; "E_o1r"; "T_op0_0"; "T_op1_0"; "bd_o1"; "payC_o1"; "B_op0"; "B_op1"; "PDk_o1"; "T_op0"; "T_op0r"; "T_op1"; "T_op1r"; "X_1"; "d_avw"; "hand_o1"; "payX_o1"; "payY_o1"; "reo_chk4"; "tv_o1"; "tv_op0"; "tv_op1"; "xfb_o1"; "avw_base"; "bd_op1"; "bdrest_o1"; "k_avw"; "nd_op0"; "nd_op1"; "passed_o1"; "s128"; "vD1"; "vK1"; "xf_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "s1A"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vF"; "g5"; "vDp"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "A1"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4.OP1"; "Pre_op"; "P_op0"; "P_op1"; "PD_op"; "nd0"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "bd_wpos"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "h0"; "tv_keep"; "bd_keep"; "nd_keep"; "objs_nl"; "sh_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "optL'"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLC"; "alA"; "bA"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC";
"T_afterA3"; "pdescA"; "xrs_inclb"; "pd_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3 Lib_load_obj_hv3m.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Module OP1. Include Lib_opt_push1. End OP1.
Definition avw_t : T3 := v_avw vsP.
Definition d_avw : sv := t_d avw_t. Definition c_avw : sv := t_c avw_t. Definition k_avw : sv := t_k avw_t.

Definition E_o1r : axst := Eval vm_compute in shadow_release_stateA E_o1 (objs_nl E_o1) 110 [(64, 4); (80, 4)].
Definition xf_o1 (T : axst) : list axform := ltac2:(tb__ "0|a|
S3S11S14S57S59S5eVT;A3M0S17N80M1A1A2S3S11S13G0G1A2S7S11A1M2A3A3SaS11A1M3S83S12VT;R1A2A1S29S3S11S13S57S88S17Z98M4A1R1A3G4A2G2A3G3S83S12R2R1A2A1S29S57S5cS17Z20A1R1A3S6S5S11R5S5S11R3S3S11S14R1S17Z40M5A1A2S3S11S14SdR1A1M6S17Z44A1A2S3S11S14SdG6A1M7S17Z50M8A1A2S3S11S14SdG7A1M9S17Z54A1A2S3S11S13G6G5A2S3S11S13G9G8A2G2A3A3A3A3A3A3A3A3Tj;TT2;Tpre2;TT1;Tpre1;").
Definition E_o1c : axst := Eval vm_compute in optL' (apply_axforms E_o1r (xf_o1 E_o1r)).
Definition s_o1c : wsub := ltac2:(tb__ "0|1|
S3S8S72S18A2M0S9S72S18S73S85A4S3G0S9S72S18P13S1aS70S5eS17Z80A1A3A4SadPaS2aS31A1S2aS65A1A3A3A3").
Definition R_o1 : list sobj := Eval vm_compute in optR (entails_frA E_o1c OP1.Pre_op s_o1c).
Definition PDk_o1 : list pdescK := ltac2:(tb__ "0|0|
SafS95S68S73S2A3A1").

Definition passed_o1 : list (sv * sv) := ltac2:(tb__ "0|1|
S3S8S18S18A2M0S9S18S18S43S8dZ4S4fA2A4S7G0A1A3").
Definition kept_o1 : list (sv * sv) := Eval vm_compute in skipn 1 tv_keep.
Definition tv_o1 : list (sv * sv) := kept_o1 ++ passed_o1.
Definition hand_o1 : list bitem := Eval vm_compute in bd_subst s_o1c (nd_bd (ndh h0 true OP1.nd0)).
Definition bdrest_o1 : list bitem := Eval vm_compute in firstn 2 bd_keep ++ skipn 2 bdrest_vr.
Definition bd_o1 : list bitem := Eval vm_compute in (firstn 2 bdrest_vr ++ LA (A1 - 72) :: LAK AK1 :: bdrest_o1).
Definition brest_o1 : list bitem := ltac2:(tb__ "0|0|
S3S6cS64S9aS63Z60A2A1S3S6cSacSabA1S4eA3A3").
Definition payX_o1 : list bitem := Eval vm_compute in [nth 0 bdrest_vr (LA 0); LA (A1 - 72)].
Definition payY_o1 : list bitem := Eval vm_compute in [nth 0 hand_o1 (LA 0); LA (A1 - 96)].
Definition payC_o1 : list bitem := Eval vm_compute in (nth 1 bdrest_vr (LA 0) :: LAK AK1 :: bdrest_o1).
Definition Xk_o1 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_avw)) (ax_X E_o1c).

Lemma hv4_checks_rel : ltac2:(tb__ "0|9|
S1S0SaS1bA1S1fS2aS79A1M0A1S5S1bS77S79A1M1S3S1bSb4S5dZ4M2Z12M3S26S78S79A1A1M4S20A5S7S1bA1A3A3A3S1S0S18S2cS79A1S17Sa9A1A3S1S0S4S2fS3S19S21S2eS5dA1S5cA2S3S19S1cS22S5dA1S17S9aS9bZ2Z3dA2Z1A2A1A2S7S19A1A3A3S1eG0A1M5A2S2A3S1S0S4S97S8S71S71A2M6Sb1G4S20G2G3A4S3G6S9S71S71Z40G2A4S3G6S9S71S71Z50G2A4S7G6A1A3A3M7A3S2A3S1S0S4S81S23G0A1M8S76A2S2A3S1S0S4S5aG5S74S61S58G1A5S2A3S1S0S4S8eG5A1S2A3S1S0S29Sb2S79G1P6eG7A4S36A3S1S0S4Sa7G8S62A2S2A3S1S0S4S96S19S1dS25S89S86A2A1G5A3S2A3S1S0S4S96S19S1dS1cS86S60A2A1G5A3S2A3S0S4S96S19S1dS1cS60S17Z4000000A1A2A1G5A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma hv4_checks_o1 : ltac2:(tb__ "0|b|
S1S0SeS29A1S12S36S56S36A1A2SbS29S31A2A3S1S0SeSaS1bA1M0A1S9fS31S65S30A3SbG0S32A2A3S1S0S4S9eS31S65S30S32SaaS8S8S29S7bA2M1S24S24OF_;F_;M2A2M3S29G3ScS29S7bScG1G2R1A3A3Ld;S3dA4A5S2A3S1S0S4Sb0S5fS30A2S2A3S1S0S4SaeS30Sa0A2S2A3S1S0S4Sa2S30S52S80S94S73S2S69A3M4A1A3S2A3S1S0S4S82S7dS30S7eG4A1A2S7cS85S2A2M5A2S2A3S1S0S4S97S8Sa4G2A2M6G6Sa6S65Sa0S30S23S2aS31A1M7A1M8ScSa4G2R1A3A5Ld;S3dA3S2A3S1S0S4S93S74S48A2S2A3S1S0S4S92S75S39A2S2A3S1S0S4Sa5S35S2bS31A1A2S2A3S1S0SaS6cA1S6dS30S7fG4A1A2S44A3S1S0S4S92S39S5S6cS3aS45A3A2S2A3S1S0S4S92S5S6cS3aS46A3S5S6cS44S33A3A2S2A3S1S0S4S6fS3aA1S2A3S1S0S4Sa8S1eG7A1M9S17Z0MaA1GaS45S46A5S2A3S1S0S4S81G8S7aS48S61S39G5A4A2S2A3S1S0S4S6eG8S33A2S2A3S1S0S4Sb5S5fG8A2S2A3S1S0S4S8fG9S34S61S58S32A5S2A3S1S0S4S91G9S34S61S90S35A5S2A3S1S0S4S8eG9A1S2A3S1S0S4Sa7G8S62A2S2A3S1S0S18S8cS30PcA2S1aS70S5cS17Z258A1A3A3S1S0S18S8cS30P24A2S87A3S1S0S18S8cS30P21A2S1aS70S5cS17Z40A1A3A3S0S18S8cS30P22A2S1aS70S5cS17Z50A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_op1_0 : axst := Eval vm_compute in T_afterA3 OP1.Pre_op E_o1c s_o1c R_o1 OP1.P_op1 Xk_o1.
Definition T_op0_0 : axst := Eval vm_compute in T_afterA3 OP1.Pre_op E_o1c s_o1c R_o1 OP1.P_op0 Xk_o1.
Definition isub_op1 : wsub := Eval vm_compute in import_subA s_o1c OP1.Pre_op OP1.P_op1 E_o1c.
Definition isub_op0 : wsub := Eval vm_compute in import_subA s_o1c OP1.Pre_op OP1.P_op0 E_o1c.
Definition vD1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 140).
Definition vC1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 141).
Definition vK1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 142).
Definition tv_op1 : list (sv * sv) := Eval vm_compute in (kept_o1 ++ import_tv isub_op1 (nd_tv (ndh h0 true OP1.nd1))).
Definition bd_op1 : list bitem := Eval vm_compute in (bd_subst isub_op1 (nd_bd (ndh h0 true OP1.nd1)) ++ brest_o1).
Definition tv_op0 : list (sv * sv) := Eval vm_compute in (kept_o1 ++ import_tv isub_op0 (nd_tv (ndh h0 true OP1.nd0'))).
Definition nd_op1 : ndesc := ltac2:(tb__ "0|0|
S7aS4aS61S4dS7cS85S2A2A4").
Definition nd_op0 : ndesc := ltac2:(tb__ "0|0|
S7aS49S61S33S7cS85S2A2A4").
Definition s128 : sv := SAlu ALU_ADD (SVar 10) (SLit (-768)).
Definition avw_base : sv := SAlu ALU_ADD vF (SLit 600).
Definition xfb_o1 (T : axst) : list axform := ltac2:(tb__ "0|a|
S3S11S13S57S53S1aS70S5eS17Z80M0A1A3VT;A3G0A2S3S11S13S57S4cS17Z0A1M1VT;A3N98A2S3S11S15S57S1aS70S5cS17Z40A1M2A3G1VT;A3A1S3S11S15S57S1aS70S5cS17Z50A1M3A3G1VT;A3A1S7S11A1M4A3A3A3A3SaS11A1M5S83S12VT;R1A2A1S29S3S11S5bS3S6S57S59S5eR1A3S3S6S57S59S17N80A1R1A3S7S6A1M6A3A3SfS1bS1fS2aR1A1A1A2M7A2S3S11S16U0A1M8G4A3M9A3G5S83S12R2R1A2A1S29S5S11R4S5S11R2S3S11S5bS3S6S57S5cS17Z20A1R1A3S3S6S57S5cG2R1A3S3S6S57S5cS17Z44A1R1A3S3S6S57S5cG3R1A3S3S6S57S5cS17Z54A1R1A3G6A3A3A3A3A3G7A2S3S11G8S3S11G8S3S11G8G9A3A3A3A3A3A3TT2;Tg1;TT1;Tpre;").
Definition B_op1 : axst := Eval vm_compute in optL' (apply_axforms T_op1_0 (xfb_o1 T_op1_0)).
Definition B_op0 : axst := Eval vm_compute in optL' (apply_axforms T_op0_0 (xfb_o1 T_op0_0)).
Definition T_op1r : axst := Eval vm_compute in ax_tidy B_op1.
Definition T_op0r : axst := Eval vm_compute in ax_tidy B_op0.
Definition X_1 : list (sv * sv) := ltac2:(tb__ "0|1|
S3S8S18S18A2M0S9S18S18S54S8dZ4S55A2A4S99G0G0S10S27ScS18S18R1A3S43A2A1Lr;S84A3A3").
Definition T_op1 : axst := Eval vm_compute in shadow_reopen_stateA T_op1r X_1 g5 4 18.
Definition T_op0 : axst := Eval vm_compute in shadow_reopen_stateA T_op0r X_1 g5 4 18.

Definition reo_chk4 (tv : list (sv * sv)) (X : list (sv * sv)) (Tb T : axst) : Prop := ltac2:(tb__ "0|2|
S1S0S18S2cVTb;A1S17Sa9A1A3S1S0S4S2fS3S19S21S2eS5dA1S5cA2S3S19S1cS22S5dA1S17S9aS9bZ2Z3dA2Z1A2A1A2S7S19A1A3A3S1eS2aVTb;A1M0A1M1A2S2A3S1S0S4Sa5VX;S2bVTb;A1A2S2A3S1S0S29Sb3VTb;VX;S5dZ4Z12A5VT;A3S1S0S4S28S2aVT;A1A1S2A3S1S0S4S5aG1Vtv;S61S58S1fG0A1A5S2A3S0S4S8eG1A1S2A3A2A2A2A2A2A2").
Lemma hv4_checks_o1_nd : ltac2:(tb__ "0|6|
S1S0S7bS7aS5S8S18S18A2M0S34Sa1S9dS30S65S67S31A4M1S80S94S73S2S6bA3M2A1A2A3S61S5S6cS6dG1S7fG2A1A2S33A3S7dG1S7eG2A1A2A4S51A3S1S0S7bS7aS5G0S34Sa1S9dS30S65S66S31A4M3S80S94S73S2S6aA3M4A1A2A3S61S5S6cS6dG3S7fG4A1A2S33A3S7dG3S7eG4A1A2A4S50A3S1S0S29Sa3S65S31S30S32S67S35A6S38A3S1S0S29Sa3S65S31S30S32S66S35A6S37A3S1S0SeS29A1M5S12S38S4bS38A1A2SbS29S3cA2A3S1S0G5S12S37S4bS37A1A2SbS29S3bA2A3S1S0S29S9cS3cA1S41A3S1S0S29S9cS3bA1S3fA3S1S47S4aS42S41S40A4S1S47S49S42S3fS3eA4S1S0S4S2dS40A1S2A3S1S0S4S2dS3eA1S2A3S98G0S9S18S18S8aS8dZ10S8bA2A4S34A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity. repeat (first [left; reflexivity | right]). Qed.
