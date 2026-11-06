(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "pair"; "app"; "prod"; "nil"; "Some"; "nat"; "fst"; "option"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SAlu"; "SLit"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al"; "s_l"; "E_l"; "R_l"; "brest_l"; "T_l_f0"; "T_l_ok"; "T_l_ok0"; "Xk_l"; "bd_l"; "hand_l"; "payC_l"; "tv_l"; "B_l_f"; "B_l_ok"; "LAr"; "PDk_l"; "kept_l"; "payX_l"; "payY_l"; "rates_l"; "xfb_l"; "T_l_f"; "T_l_okR"; "bd_l_f"; "bd_l_ok"; "bdrest_l"; "cg_lc"; "cg_li"; "d_lc"; "d_li"; "gLC'"; "gLI'"; "k_lc"; "k_li"; "nd_l_f"; "nd_l_ok"; "passed_l"; "qCURl"; "rate_glc"; "rate_gli"; "tv_l_f"; "tv_l_ok"; "xf_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al.HL"; "Pre_hl"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "gLI"; "pE0"; "HNEXT"; "gLC"; "pCP"; "pLNL"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al.HL2"; "P_fail"; "P_ok"; "Posts_hl"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.
Module HL. Include Lib_handle_l. End HL.
Module HL2. Include Lib_handle_l_s2. End HL2.

Definition c_li : sv := t_c (v_li vsP).  Definition d_li : sv := t_d (v_li vsP).  Definition k_li : sv := t_k (v_li vsP).
Definition c_lc : sv := t_c (v_lc vsP).  Definition d_lc : sv := t_d (v_lc vsP).  Definition k_lc : sv := t_k (v_lc vsP).
Definition xf_l : list axform := ltac2:(tb__ "0|2|
S2S51S56U7M0S12N140M1A1A2S2S51S53G0G1A2S8S51A1A3A3").
Definition E_l : axst := Eval vm_compute in optL (apply_axforms E_hl xf_l).

Definition s_l : wsub := ltac2:(tb__ "0|1|
S2S7S57SfA2M0S5S57SfP81S6aA4S2G0S5S57SfP82S6dA4S2G0S5S57SfS59S69A4S2G0S5S57SfP13S11S67S80S12Z140A1A3A4S92PaS1bS25A1S1bS4fA1A3A3A3A3A3").
Definition R_l : list sobj := Eval vm_compute in optR (entails_frA E_l HL.Pre_hl s_l).
Definition PDk_l : list pdescK := ltac2:(tb__ "0|0|
S96S74S7cS59S3A3A1").
Definition passed_l : list (sv * sv) := ltac2:(tb__ "0|1|
S2S7SfSfA2M0S5SfSfS41S79ZcS45A2A4S2G0S5SfSfS40S79Z4S44A2A4S8G0A1A3A3").
Definition kept_l : list (sv * sv) := Eval vm_compute in (firstn 11 tvL ++ skipn 13 tvL).
Definition tv_l : list (sv * sv) := kept_l ++ passed_l.

Definition LAr : bitem := ltac2:(tb__ "0|1|
S21Z1Z0S2S7S58S1eA2M0S5S58S1eS5bS1fS81A1A4S2G0S5S58S1eS99S5bA1S1fS70A1A4S2G0S5S58S1eN48S1fS6fA1A4S8G0A1A3A3A3S9aS5bZ18A2A4").
Definition bdrest_l : list bitem := Eval vm_compute in (firstn 22 bd_rest ++ skipn 26 bd_rest).
Definition brest_l : list bitem := ltac2:(tb__ "0|0|
S2S1dS32S2S1dS8fS8eA1S3dA3A3").
Definition hand_l : list bitem := Eval vm_compute in bd_subst s_l (nd_bd (ndh h0 true HL.nd0)).
Definition bd_l : list bitem := Eval vm_compute in (firstn 4 (skipn 22 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_l).
Definition Xk_l : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_li) && negb (sv_eqb (fst r) d_lc)) (ax_X E_l).

Definition payX_l : list bitem := [LA A1].
Definition payY_l : list bitem := ltac2:(tb__ "0|1|
S2S1dS32S2S1dS75S1dU0S2dS5dZ0A1M0A4S2S1dS75S1dU5S2dG0A4S8S1dA1A3A3A3").
Definition payC_l : list bitem := Eval vm_compute in (firstn 4 (skipn 22 bd_rest) ++ LAK AK1 :: bdrest_l).

Lemma al_checks : ltac2:(tb__ "0|a|
S1S0ScS1aA1S52S91S4eA2S9S1aS25A2A3S1S0ScSeS14A1M0A1S85S25S4fS24A3S9G0S26A2A3S1S0S4S84S25S4fS24S26S76S7S7S1aS5fA2M1S17S17OF_;F_;M2A2M3S1aG3SbS1aS5fSbG1G2R1A3A3Ld;S33A4A5S3A3S1S0S4S97S7fS24A2S3A3S1S0S4S93S24S78A2S3A3S1S0S4S87S24S48S63S73S59S3S50A3M4A1A3S3A3S1S0S4S65S61S24S62G4A1A2S60S69S3A2M5A2S3A3S1S0S4S8cS7S89G2A2M6G6S8aS4fS78S24S16S1bS25A1M7A1M8SbS89G2R1A3A5Ld;S33A3S3A3S1S0S4S72S5cS2fA2S3A3S1S0S4S72S2fS5cA2S3A3S1S0S4S71S90S5bA1S2cA2S3A3S1S0S4S8bS2bS1cS25A1A2S3A3S1S0S4S71S2cS6S1dS2eS35A3A2S3A3S1S0S4S71S6S1dS2eS36A3S6S1dS2dS27A3A2S3A3S1S0S4S23S2eA1S3A3S1S0S4S95S15G7A1S12Z0M9A1G9S35S36A5S3A3S1S0S4S66G8S5eS2fS5aS2cG5A4A2S3A3S1S0S4S22G8S27A2S3A3S1S0S4S98S7fG8A2S3A3S0S57G8S6cA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_l_ok0 : axst := Eval vm_compute in T_afterA3 HL.Pre_hl E_l s_l R_l HL2.P_ok Xk_l.
Definition T_l_f0 : axst := Eval vm_compute in T_afterA3 HL.Pre_hl E_l s_l R_l HL2.P_fail Xk_l.
Definition isub_ok_l : wsub := Eval vm_compute in import_subA s_l HL.Pre_hl HL2.P_ok E_l.
Definition isub_f_l : wsub := Eval vm_compute in import_subA s_l HL.Pre_hl HL2.P_fail E_l.
Definition tv_l_ok : list (sv * sv) := Eval vm_compute in (kept_l ++ import_tv isub_ok_l (nd_tv HL2.nd_ok)).
Definition bd_l_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_l (nd_bd HL2.nd_ok) ++ brest_l).
Definition tv_l_f : list (sv * sv) := Eval vm_compute in (kept_l ++ import_tv isub_f_l (nd_tv HL2.nd_fail)).
Definition bd_l_f : list bitem := Eval vm_compute in (bd_subst isub_f_l (nd_bd HL2.nd_fail) ++ brest_l).
Definition nd_l_ok : ndesc := ltac2:(tb__ "0|0|
S5eS4dS5aS3cS60S69S3A2A4").
Definition nd_l_f : ndesc := ltac2:(tb__ "0|0|
S5eS4cS5aS3bS60S69S3A2A4").
Definition xfb_l (T : axst) : list axform := ltac2:(tb__ "0|2|
S2S51S53U0M0Z140A2S2S51S55S2SaG0S2SaU3S2SaU1S2SaU2S77U4M1S8dSdS14S19S1bVT;A1A1A2G1A2A2A3A3A3A3A1S2S51S54G0A1S8S51A1A3A3A3").
Definition B_l_ok : axst := Eval vm_compute in optL (apply_axforms T_l_ok0 (xfb_l T_l_ok0)).
Definition B_l_f : axst := Eval vm_compute in optL (apply_axforms T_l_f0 (xfb_l T_l_f0)).
Definition T_l_ok : axst := Eval vm_compute in ax_tidy B_l_ok.
Definition T_l_f : axst := Eval vm_compute in ax_tidy B_l_f.

Definition qCURl : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qCUR.
Definition gLI' : sv := ltac2:(tb__ "0|0|
S11S67S6aS11S68S49S6eA3A3").
Definition gLC' : sv := SAlu ALU_ADD gLC (SLit 1).

Definition rate_gli : sprop := ltac2:(tb__ "0|0|
S13S43S11S67S6bS12Z1A1A3A2").
Definition rate_glc : sprop := ltac2:(tb__ "0|0|
S13S42S11S67S6bS12Z1A1A3A2").

Definition qCl : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qC.
Definition qC2l : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qC2.
Definition cg_li : sprop := SPUle qCl gLI'.
Definition cg_lc : sprop := SPUle qC2l gLC'.
Definition rates_l : list sprop := ltac2:(tb__ "0|0|
S2S10S4bS2S10S4aS2S10S3fS2S10S3eS8S10A1A3A3A3A3").
Definition T_l_okR : axst := Eval vm_compute in ax_add_facts rates_l T_l_ok.
Lemma al_checks_nd : ltac2:(tb__ "0|7|
S1S0S5fS5eS6S7SfSfA2M0S34S86S83S24S4fS7bS25A4M1S63S73S59S3S7eA3M2A1A2A3S5aS6S1dS20G1S64G2A1A2S27A3S61G1S62G2A1A2A4S47A3S1S0S5fS5eS6G0S34S86S83S24S4fS7aS25A4M3S63S73S59S3S7dA3M4A1A2A3S5aS6S1dS20G3S64G4A1A2S27A3S61G3S62G4A1A2A4S46A3S1S0S1aS88S4fS25S24S26S7bS2bA6S2aA3S1S0S1aS88S4fS25S24S26S7aS2bA6S28A3S1S0ScS1aA1M5S52S2aS38S2aA1A2S9S1aS31A2A3S1S0G5S52S28S38S28A1A2S9S1aS30A2A3S1S0S1aS82S31A1S29A3S1S0S1aS82S30A1S39A3S1S0S1aS94S29S6S10S37S15S1bS29A1M6A1A3A2S3aA3S0S4S8cS10S18S16G6A1A1S37A3S3A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
