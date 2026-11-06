(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "app"; "pair"; "prod"; "nil"; "Some"; "nat"; "fst"; "option"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap"; "s_p"; "E_p"; "R_p"; "brest_p"; "T_p_f0"; "T_p_ok"; "T_p_ok0"; "Xk_p"; "bd_p"; "payC_p"; "tv_p"; "B_p_f"; "B_p_ok"; "LAr"; "PDk_p"; "hand_p"; "kept_p"; "payX_p"; "payY_p"; "xfb_p"; "T_p_f"; "T_p_okR"; "bd_p_f"; "bd_p_ok"; "bdrest_p"; "d_pi"; "gPI'"; "k_pi"; "nd_p_f"; "nd_p_ok"; "passed_p"; "qCURp"; "rate_gp"; "tv_p_f"; "tv_p_ok"; "xf_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "SLit"; "sprop"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "SPUle"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap.HP"; "Pre_hp"; "P_fail"; "P_ok"; "Posts_hp"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "gPI"; "HNEXT"; "pCP"; "pE0"; "pLNL"; "pNX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HPAddr.
Module HP. Include Lib_handle_p. End HP.

Definition c_pi : sv := t_c (v_pi vsP).  Definition d_pi : sv := t_d (v_pi vsP).  Definition k_pi : sv := t_k (v_pi vsP).
Definition xf_p : list axform := ltac2:(tb__ "0|2|
S3S4fS54U7M0S3fN120M1A1A2S3S4fS51G0G1A2S8S4fA1A3A3").
Definition E_p : axst := Eval vm_compute in optL (apply_axforms E_hp xf_p).

Definition s_p : wsub := ltac2:(tb__ "0|1|
S3S7S55S3dA2M0S6S55S3dP95S66A4S3G0S6S55S3dS57S65A4S3G0S6S55S3dP13S3eS6cS75S3fZ120A1A3A4S8aPaS10S13A1S10S48A1A3A3A3A3").
Definition R_p : list sobj := Eval vm_compute in optR (entails_frA E_p HP.Pre_hp s_p).
Definition PDk_p : list pdescK := ltac2:(tb__ "0|0|
S8eS71S4bS57S2A3A1").
Definition passed_p : list (sv * sv) := ltac2:(tb__ "0|1|
S3S7S3dS3dA2M0S6S3dS3dS2bS73ZcS2dA2A4S8G0A1A3").
Definition kept_p : list (sv * sv) := Eval vm_compute in (firstn 13 tvL ++ skipn 14 tvL).
Definition tv_p : list (sv * sv) := kept_p ++ passed_p.

Definition LAr : bitem := ltac2:(tb__ "0|1|
S3aZ1Z0S3S7S56S37A2M0S6S56S37S59S38S76A1A4S3G0S6S56S37S91S59A1S38S6bA1A4S3G0S6S56S37N48S38S6aA1A4S8G0A1A3A3A3S59A4").
Definition bdrest_p : list bitem := Eval vm_compute in (firstn 26 bd_rest ++ skipn 28 bd_rest).
Definition brest_p : list bitem := ltac2:(tb__ "0|0|
S3S36S1fS3S36S87S86A1S2aA3A3").
Definition hand_p : list bitem := Eval vm_compute in bd_subst s_p (nd_bd (ndh h0 true HP.nd0)).
Definition bd_p : list bitem := Eval vm_compute in (firstn 2 (skipn 26 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_p).
Definition Xk_p : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_pi)) (ax_X E_p).

Definition payX_p : list bitem := [LA A1].
Definition payY_p : list bitem := ltac2:(tb__ "0|0|
S3S36S1fS3S36S84S36U2S21S5bZ0A1A4S8S36A1A3A3").
Definition payC_p : list bitem := Eval vm_compute in (firstn 2 (skipn 26 bd_rest) ++ LAK AK1 :: bdrest_p).

Lemma ap_checks : ltac2:(tb__ "0|a|
S1S0ScSfA1S50S89S35A2S9SfS13A2A3S1S0ScSeS41A1M0A1S7aS13S48S12A3S9G0S14A2A3S1S0S4S79S13S48S12S14S83S7S7SfS5dA2M1S44S44OF_;F_;M2A2M3SfG3SbSfS5dSbG1G2R1A3A3Ld;S20A4A5S2A3S1S0S4S8fS74S12A2S2A3S1S0S4S8bS12S72A2S2A3S1S0S4S7cS12S30S61S70S57S2S4cA3M4A1A3S2A3S1S0S4S63S5fS12S60G4A1A2S5eS65S2A2M5A2S2A3S1S0S4S81S7S7eG2A2M6G6S7fS48S72S12S43S10S13A1M7A1M8SbS7eG2R1A3A5Ld;S20A3S2A3S1S0S4S6fS5aS1cA2S2A3S1S0S4S6fS1cS5aA2S2A3S1S0S4S6eS88S59A1S1aA2S2A3S1S0S4S80S19S11S13A1A2S2A3S1S0S4S6eS1aS5S36S1bS23A3A2S2A3S1S0S4S6eS5S36S1bS24A3S5S36S21S15A3A2S2A3S1S0S4S3cS1bA1S2A3S1S0S4S8dS42G7A1S3fZ0M9A1G9S23S24A5S2A3S1S0S4S64G8S5cS1cS58S1aG5A4A2S2A3S1S0S4S3bG8S15A2S2A3S1S0S4S90S74G8A2S2A3S0S55G8S67A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_p_ok0 : axst := Eval vm_compute in T_afterA3 HP.Pre_hp E_p s_p R_p HP.P_ok Xk_p.
Definition T_p_f0 : axst := Eval vm_compute in T_afterA3 HP.Pre_hp E_p s_p R_p HP.P_fail Xk_p.
Definition isub_ok_p : wsub := Eval vm_compute in import_subA s_p HP.Pre_hp HP.P_ok E_p.
Definition isub_f_p : wsub := Eval vm_compute in import_subA s_p HP.Pre_hp HP.P_fail E_p.
Definition tv_p_ok : list (sv * sv) := Eval vm_compute in (kept_p ++ import_tv isub_ok_p (nd_tv HP.nd_ok)).
Definition bd_p_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_p (nd_bd HP.nd_ok) ++ brest_p).
Definition tv_p_f : list (sv * sv) := Eval vm_compute in (kept_p ++ import_tv isub_f_p (nd_tv HP.nd_fail)).
Definition bd_p_f : list bitem := Eval vm_compute in (bd_subst isub_f_p (nd_bd HP.nd_fail) ++ brest_p).
Definition nd_p_ok : ndesc := ltac2:(tb__ "0|0|
S5cS34S58S29S5eS65S2A2A4").
Definition nd_p_f : ndesc := ltac2:(tb__ "0|0|
S5cS33S58S28S5eS65S2A2A4").
Definition xfb_p (T : axst) : list axform := ltac2:(tb__ "0|2|
S3S4fS51U0M0Z120A2S3S4fS53S3SaG0S3SaU3S3SaU1S3SaU2S85U4M1S82SdS41S47S10VT;A1A1A2G1A2A2A3A3A3A3A1S3S4fS52G0A1S8S4fA1A3A3A3").
Definition B_p_ok : axst := Eval vm_compute in optL (apply_axforms T_p_ok0 (xfb_p T_p_ok0)).
Definition B_p_f : axst := Eval vm_compute in optL (apply_axforms T_p_f0 (xfb_p T_p_f0)).
Definition T_p_ok : axst := Eval vm_compute in ax_tidy B_p_ok.
Definition T_p_f : axst := Eval vm_compute in ax_tidy B_p_f.

Definition qCURp : sv := Eval vm_compute in sv_subst isub_ok_p HP.qCUR.
Definition gPI' : sv := ltac2:(tb__ "0|0|
S3eS6cS66S3eS6dS31S68A3A3").

Definition rate_gp : sprop := ltac2:(tb__ "0|0|
S45S2cS3eS6cS69S3fZ1A1A3A2").
Definition T_p_okR : axst := Eval vm_compute in ax_add_facts [rate_gp] T_p_ok.
Lemma ap_checks_nd : ltac2:(tb__ "0|8|
S1S0S5dS5cS5S7S3dS3dA2M0S22S7bS78S12S48S4aS13A4M1S61S70S57S2S4eA3M2A1A2A3S58S5S36S39G1S62G2A1A2S15A3S5fG1S60G2A1A2A4S2fA3S1S0S5dS5cS5G0S22S7bS78S12S48S49S13A4M3S61S70S57S2S4dA3M4A1A2A3S58S5S36S39G3S62G4A1A2S15A3S5fG3S60G4A1A2A4S2eA3S1S0SfS7dS48S13S12S14S4aS19A6S18A3S1S0SfS7dS48S13S12S14S49S19A6S16A3S1S0ScSfA1M5S50S18S25S18A1A2S9SfS1eA2A3S1S0G5S50S16S25S16A1A2S9SfS1dA2A3S1S0SfS77S1eA1S17A3S1S0SfS77S1dA1S26A3S1S0SfS8cS17S5S40S3S40S32S8S40A1A3M6S42S10S17A1M7A1A3A2S27A3S0S4S81S40S46S43G7A1A1G6A3S2A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
