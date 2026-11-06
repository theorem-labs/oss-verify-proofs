(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "app"; "prod"; "nat"; "pair"; "Some"; "list"; "fst"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "ax_base"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "ss_objs"; "SAlu"; "sprop_below"; "sprop_eqb"; "DUnknown"; "SPEq"; "SVar"; "valuation"; "SMd"; "SPUlt"; "ob_cells"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "s_vr"; "E_vr"; "R_vr"; "brest_vr"; "h0"; "T_failr"; "Xk_vr"; "kept_vr"; "E_vr1"; "K_vrr"; "T_fail"; "T_fail0"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "bd_vr"; "cb_av"; "xfb_vr"; "B_fail"; "B_grown"; "B_keep"; "PDk_vr"; "T_grownS"; "T_keepS"; "d_av"; "hand_vr"; "k_av"; "tv_fail"; "tv_vr"; "PD_vr"; "av_base"; "bd_grown"; "bd_keep"; "bdrest_vr"; "cnt_av"; "inj_grown"; "inj_keep"; "nd_fail"; "nd_grown"; "nd_keep"; "objs_nl"; "passed_vr"; "room_av"; "s64"; "sh_of"; "slot_facts"; "tv_grown"; "tv_keep"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "V_B"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3.VR"; "Pre_vr"; "P_fail"; "P_grown"; "P_keep"; "nd0"; "bdP"; "tv0"; "tvP"; "vKn"; "vW"; "B32"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AHead"; "ND"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "s1A"; "extra_hv"; "robjs_chkR"; "sel_front"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "g5"; "vDp"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "xLC"; "bA"; "pI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "last"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "xrs_inclb"; "pd_okA"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "X_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "sh_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module VR. Include Lib_vec_reserve. End VR.

Definition av_t : T3 := v_av vsP.
Definition d_av : sv := t_d av_t. Definition c_av : sv := t_c av_t. Definition k_av : sv := t_k av_t.
Definition cnt_av : sv := SMd M_MUL c_av (SLit 3).
Definition room_av : sprop := ltac2:(tb__ "0|0|
S19S25S93S17Z4A1S1eS92S51S17Z3A1A3A3S17S70A1A2").
Definition xf_vr (T : axst) : list axform := ltac2:(tb__ "0|4|
SeS1aS1dS10VT;A1A1A2S8S4S29S82S4S8S7eS7fS86VT;A3S4S8S7eS7fS17N30A1VT;A3S5S8A1A3A3R1A2S4S29S2cU0M0A1S4S29S2dG0S17N40M1A1A2S4S29S2bG0G1A2S5S29A1M2A3A3A3A3SbS29A1Sa9S2aVT;R1A2A1SfS6S29R2S4S29S2bS7eS8dS17Z78M3A1R1A3G3A2G2A3A3TT1;Tpre;Tn;").
Definition objs_nl (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Definition sh_of (A : axst) : sobj := ltac2:(tb__ "0|0|
S91S1aS1dS10VA;A1A1Sb4A3").
Definition K_vrr : axst := Eval vm_compute in shadow_release_stateA K_vr (objs_nl K_vr) 110 [(32, 12)].
Definition E_vr1 : axst := Eval vm_compute in optL' (apply_axforms K_vrr (xf_vr K_vrr)).
Definition E_vr : axst := Eval vm_compute in ax_add_facts [room_av] E_vr1.
Definition h0 : positive := 99%positive.
Definition s_vr : wsub := ltac2:(tb__ "0|1|
S4S7S84S18A2M0S9S84S18S32S8bA4S4G0S9S84S18P13S1eS92S86S17Z40A1A3A4Sb5PaS10S2fA1S10S65A1A3A3A3").
Definition R_vr : list sobj := Eval vm_compute in optR (entails_frA E_vr VR.Pre_vr s_vr).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S4S7SfS74A2M0S9SfS74S68S69A4S4G0S9SfS74S66S77S6bS5S7S7S18S83A2S18A2A1M1S5S71A1A3A4S4G0S9SfS74S67S77S6cG1S6aS6eS6dA2A3A4S5G0A1A3A3A3").
Definition PDk_vr : list pdescK := ltac2:(tb__ "0|0|
Sb9S95S4cS32S2A3A1").

Definition passed_vr : list (sv * sv) := ltac2:(tb__ "0|1|
S4S7S18S18A2M0S9S18S18S47Sa7Z4S49A2A4S5G0A1A3").
Definition kept_vr : list (sv * sv) := Eval vm_compute in skipn 1 tvL.
Definition tv_vr : list (sv * sv) := kept_vr ++ passed_vr.
Definition bdrest_vr : list bitem := Eval vm_compute in skipn 2 bd_rest.
Definition brest_vr : list bitem := ltac2:(tb__ "0|0|
S4S71S64Sa5S61Z48A2A1S4S71Sb1Sb0A1S50A3A3").
Definition hand_vr : list bitem := Eval vm_compute in bd_subst s_vr (nd_bd (ndh h0 true VR.nd0)).
Definition bd_vr : list bitem := Eval vm_compute in (firstn 2 bd_rest ++ LA A1 :: LAK AK1 :: bdrest_vr).
Definition Xk_vr : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_av)) (ax_X E_vr).

Lemma hv3_checks_rel : ltac2:(tb__ "0|9|
S1S0SbS1aA1S1dS10S8aA1M0A1S6S1aS57S8aA1M1S4S1aSbeS85Z4M2Z12M3S27S5bS8aA1A1M4S21A5S5S1aA1A3A3A3S1S0S18S13S8aA1S17SadA1A3S1S0S3S15S4S16S22S14S85A1S88A2S4S16S19S23S85A1S17Sa5Sa6Z2Z3dA2Z1A2A1A2S5S16A1A3A3S1bG0A1M5A2S2A3S1S0S3S8fS7S83S83A2M6SbbG4S21G2G3A4S4G6S9S83S83Z20ZcA4S5G6A1A3M7A3S2A3S1S0S3S7cS1cG0A1M8Sb3A2S2A3S1S0S3S81G5S63S60S80G1A5S2A3S1S0S3S96G5A1S2A3S1S0SfSbcS8aG1P6eG7A4S37A3S1S0S3SabG8S62A2S2A3S1S0S3S90S16S20S26S8eS8cA2A1G5A3S2A3S1S0S3S90S16S20S19S8cS89A2A1G5A3S2A3S0S3S90S16S20S19S89S17Z4000000A1A2A1G5A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma hv3_checks_vr : ltac2:(tb__ "0|d|
S1S0SdSfA1S2aS37S5fS37A1A2SaSfS36A2A3S1S0SfS9bS36S6S16S4S16S59S5S16A1A3S1bS10S36A1M0A1A3M1A2S2fA3S1S0S3S8fS16S1fS1cG0A1A1G1A3S2A3S1S0SdSbS1aA1M2A1S9eS2fS65S2eA3SaG2S30A2A3S1S0S3S9dS2fS65S2eS30SafS7S7SfS74A2M3S24S24OF_;F_;M4A2M5SfG5ScSfS74ScG3G4R1A3A3Ld;S44A4A5S2A3S1S0S3SbaS87S2eA2S2A3S1S0S3Sb6S2eSaaA2S2A3S1S0S3Sa0S2eS58S7bS94S32S2S69A3M6A1A3S2A3S1S0S3S7dS78S2eS79G6A1A2S76S8bS2A2M7A2S2A3S1S0S3S8fS7Sa2G4A2M8G8Sa4S65SaaS2eS1cS10S2fA1M9A1MaScSa2G4R1A3A5Ld;S44A3S2A3S1S0S3Sb8S63S4bA2S2A3S1S0S3Sb7Sb2S61A1S3eA2S2A3S1S0S3Sa3S34S12S2fA1A2S2A3S1S0SbS71A1S72S2eS7aG6A1A2S48A3S1S0S3SacS1bG9A1MbS17Z0McA1GcS3eS6S71S48S31A3A5S2A3S1S0S3S7cGaS75S4bS60S3eG7A4A2S2A3S1S0S3S73GaS31A2S2A3S1S0S3SbfS87GaA2S2A3S1S0S3S97GbS35S60S80S30A5S2A3S1S0S3S99GbS35S60S98S34A5S2A3S1S0S3S96GbA1S2A3S0S3SabGaS62A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VR.Pre_vr E_vr s_vr R_vr VR.P_keep Xk_vr.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VR.Pre_vr E_vr s_vr R_vr VR.P_grown Xk_vr.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VR.Pre_vr E_vr s_vr R_vr VR.P_fail Xk_vr.
Definition isub_keep : wsub := Eval vm_compute in import_subA s_vr VR.Pre_vr VR.P_keep E_vr.
Definition isub_grown : wsub := Eval vm_compute in import_subA s_vr VR.Pre_vr VR.P_grown E_vr.
Definition isub_fail : wsub := Eval vm_compute in import_subA s_vr VR.Pre_vr VR.P_fail E_vr.
Definition vDg : sv := Eval vm_compute in sv_subst isub_grown VR.vDn.
Definition vKg : sv := Eval vm_compute in sv_subst isub_grown VR.vKn.
Definition tv_keep : list (sv * sv) := Eval vm_compute in (kept_vr ++ import_tv isub_keep (nd_tv (ndh h0 true VR.nd0))).
Definition bd_keep : list bitem := Eval vm_compute in (bd_subst isub_keep (nd_bd (ndh h0 true VR.nd0)) ++ brest_vr).
Definition tv_grown : list (sv * sv) := Eval vm_compute in (kept_vr ++ import_tv isub_grown VR.tvP).
Definition bd_grown : list bitem := Eval vm_compute in (bd_subst isub_grown (VR.bdP VR.vW VR.vKn) ++ brest_vr).
Definition tv_fail : list (sv * sv) := Eval vm_compute in (kept_vr ++ import_tv isub_fail VR.tv0).
Definition nd_keep : ndesc := ltac2:(tb__ "0|0|
S75S5eS60S4fS76S8bS2A2A4").
Definition nd_grown : ndesc := ltac2:(tb__ "0|0|
S75S5dS60S4eS76S8bS2A2A4").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S75S4aS60S31S76S8bS2A2A4").

Definition s64 : sv := SAlu ALU_ADD (SVar 10) (SLit (-704)).
Definition av_base : sv := SAlu ALU_ADD vF (SLit 568).
Definition xfb_vr (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S29S2bS7eS5aS1eS92S86S17Z40M0A1A3VT;A3G0A2S4S29S2bS7eS4dS17Z0A1VT;A3N78A2S5S29A1M1A3A3SbS29A1Sa9S2aVT;R1A2A1SfS6S29R2S4S29S82S4S8S7eS7fS86R1A3S4S8S7eS7fS17N40A1R1A3S5S8A1A3A3SeS1aS1dS10R1A1A1A2A2S4S29S2cU0A1G1A3A3A3TT1;Tpre;").
Definition B_keep : axst := Eval vm_compute in optL' (apply_axforms T_keep0 (xfb_vr T_keep0)).
Definition B_grown : axst := Eval vm_compute in optL' (apply_axforms T_grown0 (xfb_vr T_grown0)).
Definition B_fail : axst := Eval vm_compute in optL' (apply_axforms T_fail0 (xfb_vr T_fail0)).
Definition T_keep : axst := Eval vm_compute in ax_tidy B_keep.
Definition T_grown : axst := Eval vm_compute in ax_tidy B_grown.
Definition T_failr : axst := Eval vm_compute in ax_tidy B_fail.

Definition T_fail : axst := Eval vm_compute in shadow_reopen_stateA T_failr X_hv g5 4 18.

Definition cb_av : sv := SMd M_MUL cnt_av (SLit 4).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S4S16S19S1eS92S3fS17ZcA1A3Sa7Z4Vk;A2M0A2S4S16S19S3fG0A2S4S16S19S3fS17S6fA1A2S5S16A1A3A3A3").
Definition inj_keep : list sprop := ltac2:(tb__ "0|0|
S6S16S5cS49A1S4S16S19S17SaeA1S47A2S5S16A1A3A3").
Definition inj_grown : list sprop := slot_facts vKg.
Definition T_keepS : axst := Eval vm_compute in ax_add_facts inj_keep T_keep.
Definition T_grownS : axst := Eval vm_compute in ax_add_facts inj_grown T_grown.

Lemma hv3_checks_vr_nd : ltac2:(tb__ "0|f|
S1S0S74S75S6S7S18S18A2M0S35S9fS9cS2eS65S68S2fA4M1S7bS94S32S2S69A3M2A1A2A3S60S6S71S72G1S7aG2A1A2S31A3S78G1S79G2A1A2A4S56A3S1S0S74S75S6G0S35S9fS9cS2eS65S67S2fA4M3S7bS94S32S2S77S6cS5S7S7S18S83A2S18A2A1M4S6aS6eS6dA2A3A3M5A1A2A3S60S6S71S72G3S7aG5A1A2S31A3S78G3S79G5A1A2A4S55A3S1S0S74S75S6G0S35S9fS9cS2eS65S66S2fA4M6S7bS94S32S2S77S6bG4S5S71A1A3A3M7A1A2A3S60S6S71S72G6S7aG7A1A2S31A3S78G6S79G7A1A2A4S54A3S1S0SfSa1S65S2fS2eS30S68S34A6S3dA3S1S0SfSa1S65S2fS2eS30S67S34A6S3bA3S1S0SfSa1S65S2fS2eS30S66S34A6S39A3S1S0SdSfA1M8S2aS3dS40S3dA1A2SaSfS43A2A3S1S0G8S2aS3bS40S3bA1A2SaSfS42A2A3S1S0G8S2aS39S40S39A1A2SaSfS41A2A3S1S0SfS9aS43A1S3cA3S1S0SfS9aS42A1S3aA3S1S0SfS9aS41A1S33A3S1S0SfSbdS33Sa8S85Z4Z12A5S38A3S1S0S18S13S33A1S17SadA1A3S1S0S3S15S4S16S22S14S85A1S88A2S4S16S19S23S85A1S17Sa5Sa6Z2Z3dA2Z1A2A1A2S5S16A1A3A3S1bS10S33A1M9A1MaA2S2A3S1S0S3Sa3Sa8S12S33A1A2S2A3S1S0S3S28S10S38A1A1S2A3S1S0S3S81GaS4aS60S80S1dG9A1A5S2A3S1S0S3S96GaA1S2A3S1S0SfS9bS3cS6S16S53S1bS10S3cA1MbA1A3McA2S46A3S1S0SfS9bS3aS6S16S52S1bS10S3aA1MdA1A3MeA2S45A3S1S0S3S8fS16S1fS1cGbA1A1GcA3S2A3S1S0S3S8fS16S1fS1cGdA1A1GeA3S2A3S1S0S3S11S46A1S2A3S1S0S3S11S45A1S2A3S0S3S11S38A1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
