(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "pair"; "nil"; "prod"; "list"; "Some"; "false"; "app"; "fst"; "negb"; "option"; "nat"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "ss_facts"; "ss_next"; "ss_pc"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_regs"; "ss_resv"; "sstate"; "sv_eqb"; "SPBranch"; "sprop_eqb"; "valuation"; "DUnknown"; "SAlu"; "SPNot"; "cell"; "mkObj"; "ob_base"; "ob_lo"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "axwf"; "ax_setS"; "la_reason"; "la_state"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "vOUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "s_bd"; "E_bd"; "K_disp"; "K_j1"; "brest_bd"; "kept_bd"; "s_fl"; "E_fl"; "E_flG"; "L_j1s"; "Pre_fr"; "R_bd"; "T_fl"; "cps_epi"; "pc_j1"; "tv_bd"; "B_bd"; "E_flF"; "La_errx"; "Lb_j1"; "PDk_bd"; "R_fl"; "T_bd"; "T_bd0"; "Xk_bd"; "bd_disp"; "free_pc"; "hand_bd"; "ndEp"; "pc_disp"; "s_dispA"; "s_dispX"; "s_j1b"; "s_j1s"; "szL"; "E_bd0"; "E_flC"; "L_fl0"; "L_fl1"; "L_fr"; "Ls_bd"; "PD_bd"; "T_fl0"; "dnz"; "fact_sz"; "mentions"; "passed_bd"; "pc_fa"; "xf_bd"; "xfb_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "bd_subst"; "bd_below"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1.BD"; "Pre_bd"; "P_bd"; "NP"; "ndP"; "ndL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "apply_axforms"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "pH"; "hf"; "hx"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_below"; "nd_tv"; "NDA"; "am_eqb"; "amode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@Stdlib.Lists.List"; "existsb"; "filter"; "forallb"; "fold_left"; "nth_error"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tvL"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_errxE2"; "K_afterE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pdescA"; "T_afterA3"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "lo_ret"; "memcpy_pc"; "memset_pc"; "sf5_pc"; "ss00_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1.BD.BDAddr"; "bd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Module BD. Include Lib_builder_dispose. End BD.

Definition pc_disp : Z := 0x8e7cc.  Definition pc_j1 : Z := 0x8e818.  Definition pc_fa : Z := 0x8e900.  Definition free_pc : Z := 0x5e1f0.
Definition cps_epi : list Z := ltac2:(tb__ "0|0|
S2S11S5cS2S11S4dS2S11S6eS2S11Sb9S2S11Z903e4S2S11Z91de8S2S11Za6ab4S2S11Z917fcS2S11Z949d4S2S11S59S2S11Sb5S2S11Sb7S2S11Sb6S2S11Sb4S2S11Sb3S2S11Sb2S6S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition mentions (v : positive) (f : sprop) : bool := ltac2:(tb__ "0|0|
SdSbaS12SdSb0R1Vv;A2A1Lw;Vf;A2A1").
Definition junkR (l : list nat) (A : axst) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S21S34VA;S1aS19R1A1S98S8S13A1M0SfG0SfS3eS13R2R1S85R1A1A4Lr;Lrs;Vl;S1fR1A1A5S1cR1A1S1bR1A1S20R1A1S1eR1A1S17R1A1S18R1A1S1dR1A1A9A2TS;").
Definition junkF8 (A : axst) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S21S34VA;S1aS19R1A1S1fR1A1S3eS13S1cR1A1U8M0S84G0A1A4S1bR1A1S20R1A1S1eR1A1S17R1A1S18R1A1S1dR1A1A9A2TS;").
Definition dropV (vs : list positive) (A : axst) : axst := ltac2:(tb__ "0|0|
Sa2VA;S96S15S15SdS95S12S12S6cR1R2A2Lv;Vvs;A3A1Lf;S17S2fVA;A1A1A3A2").
Definition dropX (b : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
Sa3VA;S96S7S13S13A2M0G0SdS22ScS13S13R1A3Vb;A2A1Lr;S37VA;A1A3A2").
Definition ndEp (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S91Vtv;S9dVbd;S8bS83SaA2A4").
Definition bd_disp : list bitem := ltac2:(tb__ "0|2|
S2S71S72Z0M0S73Z12A3S2S71S72G0S73Z1A3M1S2S71G1S6S71A1A3A3A3").

Definition Pre_fr : axst := Pre_free AE_A W2 UStopLe.
Definition L_fr : axst := L_free AE_A W2 UStopLe.
Definition s_free (E : axst) (sz : sv) : wsub := ltac2:(tb__ "0|1|
S2S7S12S13A2M0S5S12S13Sc0S3aA4S2G0S5S12S13PdVsz;A4S7cPaS2fVE;A1S2fS49A1A3A3A3").

Definition La_errx : axst := Eval vm_compute in leafL (runL 300 cps_epi K_afterE2) pc_disp 0.

Definition gen_outD (A : axst) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S21S34VA;S1aS19R1A1S1fR1A1S1cR1A1S1bR1A1S20R1A1S76S16S16S16S3S16L_;S10S22S2bR1A1S3bA2S22S2cR1A1S14Z0A1M0A2A2S2aS3bG0S14Zd0A1S6S29A1S26A5R1X3x2Lo;S1eR1A1A4S17R1A1S18R1A1S1dR1A1A9A2TS;").
Definition K_disp : axst := Eval vm_compute in gen_outD (dropV [460; 461]%positive (junkF8 (junkR [1; 10; 24; 29; 31]%nat La_errx))).
Definition s_dispA : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS51A1S2fS41A1A3").
Definition s_dispX : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS9eA1S2fS41A1A3").

Definition E_bd0 : axst := Eval vm_compute in leafL (runL 300 cps_epi K_disp) BD.BDAddr.bd_entry 0.
Definition xf_bd : list axform := ltac2:(tb__ "0|2|
S2S7dS81U7M0S14N40M1A1A2S2S7dS7eG0G1A2S6S7dA1A3A3").
Definition E_bd : axst := Eval vm_compute in optL (apply_axforms E_bd0 xf_bd).
Definition s_bd : wsub := ltac2:(tb__ "0|1|
S2S7S12S13A2M0S5S12S13S87S83A4S2G0S5S12S13P13S27S9bS3aS14Z40A1A3A4S7cPaS2fS40A1S2fS77A1A3A3A3").
Definition R_bd : list sobj := Eval vm_compute in optR (entails_frA E_bd BD.Pre_bd s_bd).
Definition PD_bd : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2S7S30S8aA2M0S5S30S8aS78S7aA4S6G0A1A3").
Definition PDk_bd : list pdescK := ltac2:(tb__ "0|0|
SbeSadS68S87SaA3A1").
Definition passed_bd : list (sv * sv) := Eval vm_compute in import_tv s_bd (nd_tv (BD.ndL 0)).
Definition kept_bd : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (existsb (fun p => sv_eqb (fst p) (fst t)) passed_bd)) tvL.
Definition tv_bd : list (sv * sv) := kept_bd ++ passed_bd.
Definition hand_bd : list bitem := Eval vm_compute in bd_subst s_bd (nd_bd (ndh h0 false (BD.ndL 0))).
Definition brest_bd : list bitem := ltac2:(tb__ "0|1|
S2S71S72Z0S73Z1A3M0S2S71G0S6S71A1A3A3").
Definition Xk_bd : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_bd)) (ax_X E_bd).
Definition T_bd0 : axst := Eval vm_compute in T_afterA3 BD.Pre_bd E_bd s_bd R_bd BD.P_bd Xk_bd.
Definition xfb_bd : list axform := ltac2:(tb__ "0|1|
S2S7dS7eU0M0Z40A2S2S7dS80G0A1S6S7dA1A3A3").
Definition B_bd : axst := Eval vm_compute in optL (apply_axforms T_bd0 xfb_bd).
Definition T_bd : axst := Eval vm_compute in ax_tidy B_bd.
Definition Ls_bd : list leafA := Eval vm_compute in runL 300 cps_epi T_bd.
Definition isub_bd : wsub := Eval vm_compute in import_subA s_bd BD.Pre_bd BD.P_bd E_bd.

Lemma epiD1_checks_join : ltac2:(tb__ "0|5|
S1S0S3S33S41A1S4A3S1S0S3S32S51S41S5dA3S4A3S1S0S3S32S9eS41S5eA3S4A3S1S0S3S88S5dS39A2S4A3S1S0S3S88S5eS39A2S4A3S1S0S8S7S11S3cA2M0A1M1S76S31G0S31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;M2S94U12cM3S4cS9fA3A4S2G0S5S11S3cS5cS3dA4S6G0A1M4A3A3S0G1S76S31G0G2S94G3S4cS41A3A4S2G0S5S11S3cSb8S3dA4G4A3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD1_checks_bd : ltac2:(tb__ "0|10|
S1S0SeS30A1M0S7fS62S6fA2S9S30S40A2A3S1S0SeS8S16A1M1A1Sa5S40S77S3fA3S9G1S4aA2A3S1S0S3Sa4S40S77S3fS4aS76S7S7S30S8aA2M2S25S25OF_;F_;M3A2M4S30G4ScS30S8aScG2G3R1A3A3Ld;S53A4A5S4A3S1S0S3SaeS39S3fA2S4A3S1S0S3SbbS3fS79A2S4A3S1S0S3SbdS3fS6dS90SacS87SaS7bU0A1A3M5A1A3S4A3S1S0S3S92S8cS3fS8dG5A1A2S8bS83SaA2M6A2S4A3S1S0S3S97S7Sa7G3A2M7G7Sa9S77S79S3fS18S2fS40A1A1M8ScSa7G3R1A3A5Ld;S53A3S4A3S1S0S3SabS9cS4eA2S4A3S1S0S3SabS4eS9cA2S4A3S1S0S3SaaS57S37S40A1A2S4A3S1S0S8S71A1M9S74S3fS8eG5A1A2S5aA3S1S0G9SbS71S5aS43A3S58A3S1S0S3S8fG8S5bS4eS58A2A2S4A3S1S0S3S75G8S43A2S4A3S1S0S3SafS39G8A2S4A3S1S0S30Sa8S77S40S3fS4aS78S57A6S56A3S1S0G0S7fS56S70A2S9S30S4fA2A3S1S0S30Sa0S4fA1S55A3S1S0S3S33S55A1S4A3S1S0S8S7S13S13A2MaA1MbS44S2GaS5S13S13S82Sb1Z10S86A2A4S2GaS5S13S13Sa1S14Z40A1A4S6GaA1A3A3A3S1S0GbSbGaS44SbcSa6S3fS77S78S40A4McS90SacS87SaS7aA3MdA1A2A3S44A3S1S0G9SbS71S74GcS8eGdA1A2S43A3S43A3S1S0S93S8cGcS8dGdA1A2G6A3S0S8S7S11S3cA2MeA1S76S31GeS31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;S67A4S2GeS5S11S3cS4dS3dA4S2GeS5S11S3cS59S3dA4MfS2GeGfS6GeA1A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition L_j1s : axst := Eval vm_compute in la_state (nth 0 Ls_bd (mkLeafA Pre_lo RsCut)).
Definition L_fl0 : axst := Eval vm_compute in la_state (nth 1 Ls_bd (mkLeafA Pre_lo RsCut)).
Definition L_fl1 : axst := Eval vm_compute in la_state (nth 2 Ls_bd (mkLeafA Pre_lo RsCut)).
Definition capz : sprop := SPBranch BC_EQ xLK (SLit 0).
Definition E_flG : axst := Eval vm_compute in ax_with_facts L_fl1 (List.filter (fun f => negb (sprop_eqb f capz || sprop_eqb f (SPNot capz))) (ss_facts (ax_S L_fl1))).
Definition szL : sv := kb 16 xLK.
Definition fact_sz : sprop := SPUle (SLit 1) szL.
Definition E_flF : axst := Eval vm_compute in ax_add_facts [fact_sz] E_flG.
Definition E_flC : axst := Eval vm_compute in carve_stateA E_flF xLD szL.
Definition E_fl : axst := Eval vm_compute in dropX xLD E_flC.
Definition s_fl : wsub := s_free E_fl szL.
Definition R_fl : list sobj := Eval vm_compute in optR (entails_frA E_fl Pre_fr s_fl).
Definition T_fl0 : axst := Eval vm_compute in T_afterA Pre_fr E_fl s_fl R_fl L_fr.
Definition T_fl : axst := Eval vm_compute in ax_tidy T_fl0.
Definition Lb_j1 : axst := Eval vm_compute in leafL (runL 300 cps_epi T_fl) pc_j1 0.
Definition dnz : sprop := ltac2:(tb__ "0|0|
S28S23S9aS82S14Z0A1A3A1").
Definition K_j1 : axst := Eval vm_compute in
  junkR [1]%nat (ax_with_facts Lb_j1 (List.filter (fun f => negb (sprop_eqb f dnz || sprop_eqb f fact_sz)) (ss_facts (ax_S Lb_j1)))).
Definition s_j1s : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS48A1S2fS42A1A3").
Definition s_j1b : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS52A1S2fS42A1A3").

Lemma epiD1_checks_fl : ltac2:(tb__ "0|8|
S1S0S3S32S64S47S6S7S12S13A2A1M0A3S4A3S1S0S3S32S65S47G0A3S4A3S1S0S30Sa2S47SbS15S2S15S6bS6S15A1A3S17S2fS47A1M1A1M2A3M3A2S50A3S1S0S3S97S15S2dS18G1A1A1G3A3S4A3S1S0S3S95S15S24S6aA1G2A3S4A3S1S0S3S2eS2fS63A1A1S4A3S1S0S13S38S50A1S14SbfA1A3S1S0SeS7S13S13A2M4A1S99G4S44U0A3S9G4S5S13S13S82S61A4A2A3S1S0S3S33S46A1S4A3S1S0SeS8S16A1M5A1Sa5S46S49S45A3S9G5S54A2A3S1S0S3Sa4S46S49S45S54S2S30S66S6S30A1A3A5S4A3S1S0S3SaeS39S45A2S4A3S1S0S3SafS39S18S2fS46A1A1M6A2S4A3S1S0S3S8fG6S5bS44S43A2A2S4A3S1S0S13S89S45PcA2S82A3S1S0S13S89S45PdA2S61A3S1S0S30Sa0S69A1S4bA3S1S0S3S33S4bA1S4A3S0S8S7S11S3cA2M7A1S76S31G7S31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;S94U12cS4cS4bA3A4S2G7S5S11S3cS4dS3dA4S6G7A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD1_checks_j1 : ltac2:(tb__ "0|0|
S1S0S3S33S42A1S4A3S1S0S3S32S48S42S60A3S4A3S1S0S3S32S52S42S5fA3S4A3S1S0S3S88S60S39A2S4A3S1S0S3S88S5fS39A2S4A3S0S3S95S15S24S23S9aS82S14Z0A1A3A1S17S2fS48A1A1A3S4A3A2A2A2A2A2").
Proof. conj_vmc. Qed.
