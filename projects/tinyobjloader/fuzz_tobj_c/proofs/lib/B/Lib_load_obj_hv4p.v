(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "app"; "pair"; "nat"; "prod"; "nil"; "Some"; "fst"; "list"; "S"; "option"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXSplit"; "AXRebase"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SAlu"; "SMd"; "sprop"; "sprop_eqb"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "SPUlt"; "ss_objs"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p"; "s_o3c"; "E_o3c"; "R_o3"; "brest_o3"; "kept_o3"; "Xk_o3"; "T_p0_0"; "T_p1_0"; "bd_o3"; "k_acol"; "payC_o3"; "B_p0"; "B_p1"; "PDk_o3"; "T_p0"; "T_p0r"; "T_p1"; "T_p1r"; "X_3"; "d_acol"; "hand_o3"; "payY_o3"; "tv_o3"; "tv_p0"; "tv_p1"; "xfb_o3"; "acol_base"; "bd_p1"; "nd_p0"; "nd_p1"; "passed_o3"; "payX_o3"; "phi_new"; "phi_old"; "rest_o3"; "vD3"; "vK3"; "xf_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "s1A"; "sel_front"; "extra_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_wpos"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vF"; "vDp"; "NP"; "vLEN"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p.OP3"; "Pre_op"; "P_op0"; "P_op1"; "PD_op"; "nd0"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "LA"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "h0"; "c_av"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLC"; "alA"; "bA"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Stdlib.Lists.List"; "existsb"; "In"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4w"; "E_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "reo_chk4"; "X_1"; "bd_op1"; "nd_op1"; "s128"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "@Corelib.Lists.ListDef";
"map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1 Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv4 Lib_load_obj_hv4w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Module OP3. Include Lib_opt_push3. End OP3.
Definition acol_t : T3 := v_acol vsP.
Definition d_acol : sv := t_d acol_t. Definition c_acol : sv := t_c acol_t. Definition k_acol : sv := t_k acol_t.

Definition xf_o3 (T : axst) : list axform := ltac2:(tb__ "0|a|
S2S11S14S4fS50S5bVT;A3M0S17N80M1A1A2S2S11S13G0G1A2S9S11A1M2A3A3ScS11A1M3S78S12VT;R1A2A1S4bS2S11S13S4fS7cS17Z118M4A1R1A3G4A2G2A3G3S78S12R2R1A2A1S4bS4fS5aS17Z20A1R1A3S7S5S11R5S5S11R3S2S11S14R1S17Z60M5A1A2S2S11S14SdR1A1M6S17Z6cA1A2S2S11S14SdG6A1M7S17Z80M8A1A2S2S11S14SdG7A1M9S17Z8cA1A2S2S11S13G6G5A2S2S11S13G9G8A2G2A3A3A3A3A3A3A3A3Tj;TT2;Tpre2;TT1;Tpre1;").
Definition E_o3c : axst := Eval vm_compute in optL' (apply_axforms E_o3 (xf_o3 E_o3)).
Definition s_o3c : wsub := ltac2:(tb__ "0|1|
S2S8S61S18A2M0S6S61S18S6dS79A4S2G0S6S61S18P13S19S5eS5bS17Z80A1A3A4Sa5PaS4cS26A1S4cS62A1A3A3A3").
Definition R_o3 : list sobj := Eval vm_compute in optR (entails_frA E_o3c OP3.Pre_op s_o3c).
Definition PDk_o3 : list pdescK := ltac2:(tb__ "0|0|
Sa7S8aS65S6dS3A3A1").

Definition passed_o3 : list (sv * sv) := ltac2:(tb__ "0|1|
S2S8S18S18A2M0S6S18S18S38S85Z4S2eA2A4S9G0A1A3").
Definition kept_o3 : list (sv * sv) := Eval vm_compute in firstn 3 tv_op1 ++ skipn 4 tv_op1.
Definition tv_o3 : list (sv * sv) := kept_o3 ++ passed_o3.
Definition hand_o3 : list bitem := Eval vm_compute in bd_subst s_o3c (nd_bd (ndh h0 true OP3.nd0)).
Definition rest_o3 : list bitem := Eval vm_compute in firstn 2 bd_op1 ++ firstn 8 bdrest_o1 ++ skipn 10 bdrest_o1.
Definition bd_o3 : list bitem := Eval vm_compute in (firstn 2 (skipn 8 bdrest_o1) ++ LA (A1 - 96) :: LAK AK1 :: rest_o3).
Definition brest_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S6bS8bS6aZa8A2A1S2S53Sa4Sa3A1S47A3A3").
Definition phi_old (c k : sv) : bitem := ltac2:(tb__ "0|3|
S57Z1Z0M0S2S8S60S54A2M1S6S60S54Z6S55S1aS5fS17Z4A1M2S19S5eS1aS5fS17Z3A1Vc;A3S17Z2A1A3A3A1A4S2G1S6S60S54N4S55S1aS5fG2Vk;A3A1A4S2G1S6S60S54Z20S55G2A1A4S9G1A1A3A3A3G0A4").
Definition phi_new (c k : sv) : bitem := ltac2:(tb__ "0|3|
S57Z1Z0M0S2S8S60S54A2M1S6S60S54Z6S55S1aS5fS17Z4A1M2S19S5eS1aS5fS17Z3A1Vc;A3S17Z5A1A3A3A1A4S2G1S6S60S54N4S55S1aS5fG2Vk;A3A1A4S2G1S6S60S54Z20S55G2A1A4S9G1A1A3A3A3G0A4").
Definition payX_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S46S6eS2eA2S2S53S6bS8bS6aZ60A2A1S9S53A1A3A3").
Definition payY_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S45S6eS2eA2S2S53S6bS8bS6aZa8A2A1S9S53A1A3A3").
Definition payC_o3 : list bitem := Eval vm_compute in (nth 9 bdrest_o1 (LA 0) :: LAK AK1 :: rest_o3).
Definition Xk_o3 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_acol)) (ax_X E_o3c).

Lemma hv4_checks_o3 : ltac2:(tb__ "0|d|
S0S1SeS4bA1S12S86S4aS86A1A2SaS4bS26A2A3S0S1SeScS1eA1M0A1S95S26S62S25A3SaG0S27A2A3S0S1S4S94S26S62S25S27S9eS8S8S4bS70A2M1S21S21OF_;F_;M2A2M3S4bG3SbS4bS70SbG1G2R1A3A3Ld;S32A4A5S3A3S0S1S4Sa8S5cS25A2S3A3S0S1S4Sa6S25S96A2S3A3S0S1S4S98S25S43S75S89S6dS3S66A3M4A1A3S3A3S0S1S4S77S72S25S73G4A1A2S71S79S3A2M5A2S3A3S0S1S4S84S8S9aG2A2M6G6S9bS62S96S25S20S4cS26A1M7A1M8SbS9aG2R1A3A5Ld;S32A3S3A3S0S1S4S88S91S3bA2S3A3S0S1S4S87S8eS2dA2S3A3S0S1S4S9cS2aS4eS26A1A2S3A3S0S1ScS53A1S56S25S74G4A1A2S39A3S0S1S4S87S2dS5S53S2fS44A3A2S3A3S0S1S4S87S5S53S2fS3aA3S5S53S39S28A3A2S3A3S0S1S4S58S2fA1S3A3S0S1S4S58S3aA1S3A3S0S1S4S81S1bS1cS1dS6eS17Z8000000A1A2A1S1fG7A1M9A3S3A3S0S1S4S76G8S6fS3bS69S2dG5A4A2S3A3S0S1S4S59G8S28A2S3A3S0S1S4Sa9S5cG8A2S3A3S0S1S4Sa0G9S29S69S52S27A5S3A3S0S1S4Sa2G9S29S69Sa1S2aA5S3A3S0S1S4S9fG9A1S3A3S0S1S4S9dG8S6cA2S3A3S0S1S18S80S25PcA2S19S5eS5aS17Z2d8A1A3A3S0S1S18S80S25P24A2S7bA3S0S1S18S80S25P21A2S19S5eS5aS17Z60A1A3A3S0S1S18S80S25P22A2S19S5eS5aS17Z80A1A3A3S0S1S4S76S20S4cS86A1MaA1MbS8fA2S3A3S0S1S4S9dGbS6cA2S3A3S0S1S4S81S1bS1cS22S7dS7aA2A1S1fGaA1McA3S3A3S0S1S4S81S1bS1cS1dS7aS5dA2A1GcA3S3A3S1S4S81S1bS1cS1dS5dS17Z4000000A1A2A1GcA3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_p1_0 : axst := Eval vm_compute in T_afterA3 OP3.Pre_op E_o3c s_o3c R_o3 OP3.P_op1 Xk_o3.
Definition T_p0_0 : axst := Eval vm_compute in T_afterA3 OP3.Pre_op E_o3c s_o3c R_o3 OP3.P_op0 Xk_o3.
Definition isub_p1 : wsub := Eval vm_compute in import_subA s_o3c OP3.Pre_op OP3.P_op1 E_o3c.
Definition isub_p0 : wsub := Eval vm_compute in import_subA s_o3c OP3.Pre_op OP3.P_op0 E_o3c.
Definition vD3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 140).
Definition vC3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 141).
Definition vK3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 142).
Definition tv_p1 : list (sv * sv) := Eval vm_compute in (kept_o3 ++ import_tv isub_p1 (nd_tv (ndh h0 true OP3.nd1))).
Definition bd_p1 : list bitem := Eval vm_compute in (bd_subst isub_p1 (nd_bd (ndh h0 true OP3.nd1)) ++ brest_o3).
Definition tv_p0 : list (sv * sv) := Eval vm_compute in (kept_o3 ++ import_tv isub_p0 (nd_tv (ndh h0 true OP3.nd0'))).
Definition nd_p1 : ndesc := ltac2:(tb__ "0|0|
S6fS3dS69S40S71S79S3A2A4").
Definition nd_p0 : ndesc := ltac2:(tb__ "0|0|
S6fS3cS69S28S71S79S3A2A4").
Definition acol_base : sv := SAlu ALU_ADD vF (SLit 728).
Definition xfb_o3 (T : axst) : list axform := ltac2:(tb__ "0|a|
S2S11S13S4fS90S19S5eS5bS17Z80M0A1M1A3VT;A3G0A2S2S11S13S4fS3fS17Z0A1M2VT;A3N118A2S2S11S15S4fS19S5eS5aS17Z60A1M3A3G2VT;A3A1S2S11S15S4fS19S5eS5aG1A3G2VT;A3A1S9S11A1M4A3A3A3A3ScS11A1M5S78S12VT;R1A2A1S4bS2S11S51S2S7S4fS50S5bR1A3S2S7S4fS50S17N80A1R1A3S9S7A1M6A3A3SfS1eS23S4cR1A1A1A2M7A2S2S11S16U0A1M8G4A3M9A3G5S78S12R2R1A2A1S4bS5S11R4S5S11R2S2S11S51S2S7S4fS5aS17Z20A1R1A3S2S7S4fS5aG3R1A3S2S7S4fS5aS17Z6cA1R1A3S2S7S4fS5aG1R1A3S2S7S4fS5aS17Z8cA1R1A3G6A3A3A3A3A3G7A2S2S11G8S2S11G8S2S11G8G9A3A3A3A3A3A3TT2;Tg1;TT1;Tpre;").
Definition B_p1 : axst := Eval vm_compute in optL' (apply_axforms T_p1_0 (xfb_o3 T_p1_0)).
Definition B_p0 : axst := Eval vm_compute in optL' (apply_axforms T_p0_0 (xfb_o3 T_p0_0)).
Definition T_p1r : axst := Eval vm_compute in ax_tidy B_p1.
Definition T_p0r : axst := Eval vm_compute in ax_tidy B_p0.
Definition X_3 : list (sv * sv) := ltac2:(tb__ "0|1|
S2S8S18S18A2M0S6S18S18S48S85Z4S49A2A4S83G0G0S10S24SbS18S18R1A3S38A2A1Lr;S8dA3A3").
Definition T_p1 : axst := Eval vm_compute in shadow_reopen_stateA T_p1r X_3 g5 4 18.
Definition T_p0 : axst := Eval vm_compute in shadow_reopen_stateA T_p0r X_3 g5 4 18.

Lemma hv4_checks_o3_nd : ltac2:(tb__ "0|6|
S0S1S70S6fS5S8S18S18A2M0S29S97S93S25S62S64S26A4M1S75S89S6dS3S68A3M2A1A2A3S69S5S53S56G1S74G2A1A2S28A3S72G1S73G2A1A2A4S42A3S0S1S70S6fS5G0S29S97S93S25S62S63S26A4M3S75S89S6dS3S67A3M4A1A2A3S69S5S53S56G3S74G4A1A2S28A3S72G3S73G4A1A2A4S41A3S0S1S4bS99S62S26S25S27S64S2aA6S2cA3S0S1S4bS99S62S26S25S27S63S2aA6S2bA3S0S1SeS4bA1M5S12S2cS3eS2cA1A2SaS4bS31A2A3S0S1G5S12S2bS3eS2bA1A2SaS4bS30A2A3S0S1S4bS92S31A1S36A3S0S1S4bS92S30A1S34A3S0S8cS3dS37S36S35A4S0S8cS3cS37S34S33A4S0S1S4S4dS35A1S3A3S0S1S4S4dS33A1S3A3S82G0S6S18S18S7eS85Z10S7fA2A4S29A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity. repeat (first [left; reflexivity | right]). Qed.
