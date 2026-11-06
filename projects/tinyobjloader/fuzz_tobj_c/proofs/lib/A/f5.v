(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_030.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3 Lib_builder_dispose.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6 Lib_handle_vt.

(* [comment removed for export] *)
Module Lib_load_obj_epiD1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "pair"; "nil"; "prod"; "list"; "Some"; "false"; "app"; "fst"; "negb"; "option"; "nat"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "ss_facts"; "ss_next"; "ss_pc"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_regs"; "ss_resv"; "sstate"; "sv_eqb"; "SPBranch"; "sprop_eqb"; "valuation"; "DUnknown"; "SAlu"; "SPNot"; "cell"; "mkObj"; "ob_base"; "ob_lo"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "axwf"; "ax_setS"; "la_reason"; "la_state"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "vOUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "s_bd"; "E_bd"; "K_disp"; "K_j1"; "brest_bd"; "kept_bd"; "s_fl"; "E_fl"; "E_flG"; "L_j1s"; "Pre_fr"; "R_bd"; "T_fl"; "cps_epi"; "pc_j1"; "tv_bd"; "B_bd"; "E_flF"; "La_errx"; "Lb_j1"; "PDk_bd"; "R_fl"; "T_bd"; "T_bd0"; "Xk_bd"; "bd_disp"; "free_pc"; "hand_bd"; "ndEp"; "pc_disp"; "s_dispA"; "s_dispX"; "s_j1b"; "s_j1s"; "szL"; "E_bd0"; "E_flC"; "L_fl0"; "L_fl1"; "L_fr"; "Ls_bd"; "PD_bd"; "T_fl0"; "dnz"; "fact_sz"; "mentions"; "passed_bd"; "pc_fa"; "xf_bd"; "xfb_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "bd_subst"; "bd_below"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1.BD"; "Pre_bd"; "P_bd"; "NP"; "ndP"; "ndL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "apply_axforms"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "pH"; "hf"; "hx"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_below"; "nd_tv"; "NDA"; "am_eqb"; "amode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@Stdlib.Lists.List"; "existsb"; "filter"; "forallb"; "fold_left"; "nth_error"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tvL"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_errxE2"; "K_afterE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pdescA"; "T_afterA3"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "lo_ret"; "memcpy_pc"; "memset_pc"; "sf5_pc"; "ss00_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1.BD.BDAddr"; "bd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Module BD. Include Lib_builder_dispose. End BD.

Definition pc_disp : Z := 0x8e6bc.  Definition pc_j1 : Z := 0x8e710.  Definition pc_fa : Z := 0x8e804.  Definition free_pc : Z := 0x5e05c.
Definition cps_epi : list Z := ltac2:(tb__ "0|0|
S2S11S5cS2S11S4dS2S11S6eS2S11Z8f45cS2S11Z90ef0S2S11Za8000S2S11Z90850S2S11Z9311cS2S11S59S2S11Sb5S2S11Sb7S2S11Sb6S2S11Sb4S2S11Sb3S2S11Sb2S6S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition mentions (v : positive) (f : sprop) : bool := ltac2:(tb__ "0|0|
SdSb9S12SdSb0R1Vv;A2A1Lw;Vf;A2A1").
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
S2S7S12S13A2M0S5S12S13SbfS3aA4S2G0S5S12S13PdVsz;A4S7cPaS2fVE;A1S2fS49A1A3A3A3").

Definition La_errx : axst := Eval vm_compute in leafL (runL 300 cps_epi K_afterE2) pc_disp 0.

Definition gen_outD (A : axst) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S21S34VA;S1aS19R1A1S1fR1A1S1cR1A1S1bR1A1S20R1A1S76S16S16S16S3S16L_;S10S22S2bR1A1S3bA2S22S2cR1A1S14Z0A1M0A2A2S2aS3bG0S14Zd0A1S6S29A1S26A5R1X3x2Lo;S1eR1A1A4S17R1A1S18R1A1S1dR1A1A9A2TS;").
Definition K_disp : axst := Eval vm_compute in gen_outD (dropV [460; 461]%positive (junkF8 (junkR [1; 10; 20; 21; 24; 25; 29; 31]%nat La_errx))).
Definition s_dispA : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS51A1S2fS41A1A3").
Definition s_dispX : wsub := ltac2:(tb__ "0|0|
S7cS39S2fS9eA1S2fS41A1A3").

Definition E_bd0 : axst := Eval vm_compute in leafL (runL 300 cps_epi K_disp) BD.BDAddr.bd_entry 0.
Definition xf_bd : list axform := ltac2:(tb__ "0|2|
S2S7dS81U7M0S14N30M1A1A2S2S7dS7eG0G1A2S6S7dA1A3A3").
Definition E_bd : axst := Eval vm_compute in optL (apply_axforms E_bd0 xf_bd).
Definition s_bd : wsub := ltac2:(tb__ "0|1|
S2S7S12S13A2M0S5S12S13S87S83A4S2G0S5S12S13P13S27S9bS3aS14Z30A1A3A4S7cPaS2fS40A1S2fS77A1A3A3A3").
Definition R_bd : list sobj := Eval vm_compute in optR (entails_frA E_bd BD.Pre_bd s_bd).
Definition PD_bd : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2S7S30S8aA2M0S5S30S8aS78S7aA4S6G0A1A3").
Definition PDk_bd : list pdescK := ltac2:(tb__ "0|0|
SbdSadS68S87SaA3A1").
Definition passed_bd : list (sv * sv) := Eval vm_compute in import_tv s_bd (nd_tv (BD.ndL 0)).
Definition kept_bd : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (existsb (fun p => sv_eqb (fst p) (fst t)) passed_bd)) tvL.
Definition tv_bd : list (sv * sv) := kept_bd ++ passed_bd.
Definition hand_bd : list bitem := Eval vm_compute in bd_subst s_bd (nd_bd (ndh h0 false (BD.ndL 0))).
Definition brest_bd : list bitem := ltac2:(tb__ "0|1|
S2S71S72Z0S73Z1A3M0S2S71G0S6S71A1A3A3").
Definition Xk_bd : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_bd)) (ax_X E_bd).
Definition T_bd0 : axst := Eval vm_compute in T_afterA3 BD.Pre_bd E_bd s_bd R_bd BD.P_bd Xk_bd.
Definition xfb_bd : list axform := ltac2:(tb__ "0|1|
S2S7dS7eU0M0Z30A2S2S7dS80G0A1S6S7dA1A3A3").
Definition B_bd : axst := Eval vm_compute in optL (apply_axforms T_bd0 xfb_bd).
Definition T_bd : axst := Eval vm_compute in ax_tidy B_bd.
Definition Ls_bd : list leafA := Eval vm_compute in runL 300 cps_epi T_bd.
Definition isub_bd : wsub := Eval vm_compute in import_subA s_bd BD.Pre_bd BD.P_bd E_bd.

Lemma epiD1_checks_join : ltac2:(tb__ "0|5|
S1S0S3S33S41A1S4A3S1S0S3S32S51S41S5dA3S4A3S1S0S3S32S9eS41S5eA3S4A3S1S0S3S88S5dS39A2S4A3S1S0S3S88S5eS39A2S4A3S1S0S8S7S11S3cA2M0A1M1S76S31G0S31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;M2S94U12cM3S4cS9fA3A4S2G0S5S11S3cS5cS3dA4S6G0A1M4A3A3S0G1S76S31G0G2S94G3S4cS41A3A4S2G0S5S11S3cSb8S3dA4G4A3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD1_checks_bd : ltac2:(tb__ "0|10|
S1S0SeS30A1M0S7fS62S6fA2S9S30S40A2A3S1S0SeS8S16A1M1A1Sa5S40S77S3fA3S9G1S4aA2A3S1S0S3Sa4S40S77S3fS4aS76S7S7S30S8aA2M2S25S25OF_;F_;M3A2M4S30G4ScS30S8aScG2G3R1A3A3Ld;S53A4A5S4A3S1S0S3SaeS39S3fA2S4A3S1S0S3SbaS3fS79A2S4A3S1S0S3SbcS3fS6dS90SacS87SaS7bU0A1A3M5A1A3S4A3S1S0S3S92S8cS3fS8dG5A1A2S8bS83SaA2M6A2S4A3S1S0S3S97S7Sa7G3A2M7G7Sa9S77S79S3fS18S2fS40A1A1M8ScSa7G3R1A3A5Ld;S53A3S4A3S1S0S3SabS9cS4eA2S4A3S1S0S3SabS4eS9cA2S4A3S1S0S3SaaS57S37S40A1A2S4A3S1S0S8S71A1M9S74S3fS8eG5A1A2S5aA3S1S0G9SbS71S5aS43A3S58A3S1S0S3S8fG8S5bS4eS58A2A2S4A3S1S0S3S75G8S43A2S4A3S1S0S3SafS39G8A2S4A3S1S0S30Sa8S77S40S3fS4aS78S57A6S56A3S1S0G0S7fS56S70A2S9S30S4fA2A3S1S0S30Sa0S4fA1S55A3S1S0S3S33S55A1S4A3S1S0S8S7S13S13A2MaA1MbS44S2GaS5S13S13S82Sb1Z10S86A2A4S2GaS5S13S13Sa1S14Z40A1A4S6GaA1A3A3A3S1S0GbSbGaS44SbbSa6S3fS77S78S40A4McS90SacS87SaS7aA3MdA1A2A3S44A3S1S0G9SbS71S74GcS8eGdA1A2S43A3S43A3S1S0S93S8cGcS8dGdA1A2G6A3S0S8S7S11S3cA2MeA1S76S31GeS31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;S67A4S2GeS5S11S3cS4dS3dA4S2GeS5S11S3cS59S3dA4MfS2GeGfS6GeA1A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
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
S1S0S3S32S64S47S6S7S12S13A2A1M0A3S4A3S1S0S3S32S65S47G0A3S4A3S1S0S30Sa2S47SbS15S2S15S6bS6S15A1A3S17S2fS47A1M1A1M2A3M3A2S50A3S1S0S3S97S15S2dS18G1A1A1G3A3S4A3S1S0S3S95S15S24S6aA1G2A3S4A3S1S0S3S2eS2fS63A1A1S4A3S1S0S13S38S50A1S14SbeA1A3S1S0SeS7S13S13A2M4A1S99G4S44U0A3S9G4S5S13S13S82S61A4A2A3S1S0S3S33S46A1S4A3S1S0SeS8S16A1M5A1Sa5S46S49S45A3S9G5S54A2A3S1S0S3Sa4S46S49S45S54S2S30S66S6S30A1A3A5S4A3S1S0S3SaeS39S45A2S4A3S1S0S3SafS39S18S2fS46A1A1M6A2S4A3S1S0S3S8fG6S5bS44S43A2A2S4A3S1S0S13S89S45PcA2S82A3S1S0S13S89S45PdA2S61A3S1S0S30Sa0S69A1S4bA3S1S0S3S33S4bA1S4A3S0S8S7S11S3cA2M7A1S76S31G7S31S5S11S3cS19S2fS36R1A1A1A1S35R1A1A4LL;S94U12cS4cS4bA3A4S2G7S5S11S3cS4dS3dA4S6G7A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD1_checks_j1 : ltac2:(tb__ "0|0|
S1S0S3S33S42A1S4A3S1S0S3S32S48S42S60A3S4A3S1S0S3S32S52S42S5fA3S4A3S1S0S3S88S60S39A2S4A3S1S0S3S88S5fS39A2S4A3S0S3S95S15S24S23S9aS82S14Z0A1A3A1S17S2fS48A1A1A3S4A3A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiD1.

(* [comment removed for export] *)
Module Lib_load_obj_af.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "pair"; "nil"; "app"; "prod"; "option"; "list"; "Some"; "fst"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "sprop"; "SLit"; "sobj"; "ss_next"; "valuation"; "SPUle"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "ax_X"; "la_state"; "sym_runA"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af"; "s_f"; "E_f"; "E_f1"; "R_f"; "brest_f"; "qAf"; "T_f_f"; "T_f_f0"; "T_f_ok"; "T_f_ok0"; "Xk_f"; "bd_f"; "hand_f"; "payC_f"; "tv_f"; "B_f_f"; "B_f_ok"; "LAr_f"; "PDk_f"; "gsub_f"; "kept_f"; "payY_f"; "xfb_f"; "bd_f_f"; "bd_f_ok"; "bdrest_f"; "nd_f_f"; "nd_f_ok"; "passed_f"; "payX_f"; "qCURf"; "room_f"; "tv_f_f"; "tv_f_ok"; "xf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "bd_wpos"; "BI"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.HF"; "Pre_hf"; "cVF"; "nd0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "gCO"; "gMI"; "gRP"; "gTR"; "gTS"; "pCP"; "HNEXT"; "gFV"; "gMM"; "gSG"; "pLNL"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "NPH"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.HFE"; "P_fail"; "P_ok"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.HFI"; "PD_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "pc_latch";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Module HF. Include Lib_handle_f_defs. End HF.
Module HF2. Include Lib_handle_f_s2. End HF2.
Module HFE. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi. End HFE.
Module HFI. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_handle_f_iface. End HFI.

Definition xf_f : list axform := ltac2:(tb__ "0|2|
S0S53S58U7M0S12N160M1A1A2S0S53S55G0G1A2S5S53A1A3A3").
Definition E_f1 : axst := Eval vm_compute in optL (apply_axforms E_hf xf_f).
Definition gsub_f : wsub := ltac2:(tb__ "0|1|
S0S7S22SfA2M0S4S22SfP81S60A4S0G0S4S22SfP84S62A4S0G0S4S22SfP87S63A4S0G0S4S22SfP8aS64A4S0G0S4S22SfP8dS61A4S0G0S4S22SfP8eS67A4S0G0S4S22SfP8fS68A4S0G0S4S22SfP95S69A4S5G0A1A3A3A3A3A3A3A3A3").
Definition s_f1 : wsub := ltac2:(tb__ "0|1|
S6S7S22SfA2M0S37S0G0S4S22SfS59S5fA4S0G0S4S22SfP13S10S51S83S12Z160A1A3A4S86PaS1cS26A1S1cS4eA1A3A3A3A3").
Definition optP (x : option sprop) : sprop := ltac2:(tb__ "0|1|
S8S11A1S11Lx;Vx;S11R1Lp;S16S12Z0A1M0G0A2X8x2").

Definition room_f : list sprop := Eval vm_compute in map (fun p => optP (sprop_subst s_f1 p)) [HF.room_r 12 3 36 HF.mi_c tI; HF.room_r 12 3 36 HF.mi_n tI; HF.room_r 1 37 37 HF.ts_n tI].
Definition E_f : axst := Eval vm_compute in ax_add_facts room_f E_f1.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S6S7S22SfA2M0S37S0G0S4S22SfS59S5fA4S0G0S4S22SfP13S10S51S83S12Z160A1A3A4S86PaS1cS25A1S1cS4eA1A3A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_f HF.Pre_hf s_f).
Definition PDk_f : list pdescK := ltac2:(tb__ "0|0|
S9dS7dS94S59S2A3A1").

Definition idx_p : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1UeS0S1UfS0S1U10S0S1U11S5S1A1A3A3A3A3A3A3A3A3A3").
Definition passed_f : list (sv * sv) := Eval vm_compute in map (fun i => nth i tvL (SLit 0, SLit 0)) idx_p.
Definition kept_f : list (sv * sv) := Eval vm_compute in map (fun i => nth i tvL (SLit 0, SLit 0)) (List.filter (fun i => negb (existsb (Nat.eqb i) idx_p)) (seq 0 (length tvL))).
Definition tv_f : list (sv * sv) := kept_f ++ passed_f.

Definition idx_b : list nat := ltac2:(tb__ "0|0|
S0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U1cS0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U22S0S1U23S5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bdpass_f : list bitem := Eval vm_compute in map (fun i => nth i bd_rest (LA 0)) idx_b.
Definition bdrest_f : list bitem := Eval vm_compute in map (fun i => nth i bd_rest (LA 0)) (List.filter (fun i => negb (existsb (Nat.eqb i) idx_b)) (seq 0 (length bd_rest))).
Definition LAr_f : bitem := ltac2:(tb__ "0|1|
S4cZ1Z0S0S7S23S48A2M0S4S23S48S5cS49S84A1A4S0G0S4S23S48S91S5cA1S49S6bA1A4S0G0S4S23S48S91S4fA1S49S6aA1A4S5G0A1A3A3A3S5cA4").
Definition brest_f : list bitem := ltac2:(tb__ "0|0|
S0S47S35S0S47S96S95A1S3dA3A3").
Definition hand_f : list bitem := Eval vm_compute in bd_subst s_f (nd_bd (ndh h0 true HF.nd0)).
Definition bd_f : list bitem := Eval vm_compute in (bdpass_f ++ LA A1 :: LAK AK1 :: bdrest_f).
Definition Xk_f : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_f)) (ax_X E_f).

Definition payX_f : list bitem := [LA A1].
Definition payY_f : list bitem := ltac2:(tb__ "0|0|
S0S47S35S0S47S78S47U0S30S5eZ0A1A4S5S47A1A3A3").
Definition payC_f : list bitem := Eval vm_compute in (bdpass_f ++ LAK AK1 :: bdrest_f).

Lemma af_checks : ltac2:(tb__ "0|a|
SeSdS8S1bA1S54S98S46A2SaS1bS26A2A3SeSdS1bS9cS26S6S11S43S18S1cS26A1M0A1A3M1A2S25A3SeSdS3S90S11S17S14G0A1A1G1A3S2A3SeSdS8S9S13A1M2A1S89S25S4eS24A3SaG2S27A2A3SeSdS3S88S25S4eS24S27S77S7S7S1bS6dA2M3S15S15OF_;F_;M4A2M5S1bG5SbS1bS6dSbG3G4R1A3A3Ld;S36A4A5S2A3SeSdS3S9eS82S24A2S2A3SeSdS3S9bS24S76A2S2A3SeSdS3S8bS24S40S72S7cS59S2S50A3M6A1A3S2A3SeSdS3S73S6fS24S70G6A1A2S6eS5fS2A2M7A2S2A3SeSdS3S90S7S8dG4A2M8G8S8eS4eS76S24S14S1cS25A1A1M9SbS8dG4R1A3A5Ld;S36A3S2A3SeSdS3S7bS5dS32A2S2A3SeSdS3S7bS32S5dA2S2A3SeSdS3S7aS97S5cA1S2fA2S2A3SeSdS3S8fS2eS1fS25A1A2S2A3SeSdS9S47A1S4aS24S71G6A1A2S30A3SeSdS3S7aS2fS6S47S31S41A3A2S2A3SeSdS3S7aS6S47S31S39A3S6S47S30S28A3A2S2A3SeSdS3S4bS31A1S2A3SeSdS3S4bS39A1S2A3SeSdS3S74G9S6cS32S5bS2fG7A4A2S2A3SeSdS3S4dG9S28A2S2A3SeSdS3S9fS82G9A2S2A3SeSdS22G9S66A3SdSfS9aS24P10A2S65A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_f_ok0 : axst := Eval vm_compute in T_afterA3 HF.Pre_hf E_f s_f R_f HFE.P_ok Xk_f.
Definition T_f_f0 : axst := Eval vm_compute in T_afterA3 HF.Pre_hf E_f s_f R_f HFE.P_fail Xk_f.
Definition isub_ok_f : wsub := Eval vm_compute in import_subA s_f HF.Pre_hf HFE.P_ok E_f.
Definition isub_f_f : wsub := Eval vm_compute in import_subA s_f HF.Pre_hf HFE.P_fail E_f.
Definition tv_f_ok : list (sv * sv) := Eval vm_compute in (kept_f ++ import_tv isub_ok_f (nd_tv HFE.nd_ok)).
Definition bd_f_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_f (nd_bd HFE.nd_ok) ++ brest_f).
Definition tv_f_f : list (sv * sv) := Eval vm_compute in (kept_f ++ import_tv isub_f_f (nd_tv HFE.nd_fail)).
Definition bd_f_f : list bitem := Eval vm_compute in (bd_subst isub_f_f (nd_bd HFE.nd_fail) ++ brest_f).
Definition nd_f_ok : ndesc := ltac2:(tb__ "0|0|
S6cS45S5bS3cS6eS5fS2A2A4").
Definition nd_f_f : ndesc := ltac2:(tb__ "0|0|
S6cS44S5bS3bS6eS5fS2A2A4").
Definition xfb_f (T : axst) : list axform := ltac2:(tb__ "0|2|
S0S53S55U0M0Z160A2S0S53S57S0S1G0S0S1U3S0S1U1S0S1U2S79U4M1S92ScS13S19S1cVT;A1A1A2G1A2A2A3A3A3A3A1S0S53S56G0A1S5S53A1A3A3A3").
Definition B_f_ok : axst := Eval vm_compute in optL (apply_axforms T_f_ok0 (xfb_f T_f_ok0)).
Definition B_f_f : axst := Eval vm_compute in optL (apply_axforms T_f_f0 (xfb_f T_f_f0)).
Definition T_f_ok : axst := Eval vm_compute in ax_tidy B_f_ok.
Definition T_f_f : axst := Eval vm_compute in ax_tidy B_f_f.

Definition qCURf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCUR.
Definition qAf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qA.
Definition gMI' : sv := ltac2:(tb__ "0|0|
S10S51S61S75Z3S29A2A3").   Definition gFV' : sv := SAlu ALU_ADD gFV qAf.   Definition gMM' : sv := SAlu ALU_ADD gMM qAf.   Definition gSG' : sv := SAlu ALU_ADD gSG qAf.
Definition gCO' : sv := ltac2:(tb__ "0|0|
S10S51S60S10S52S42S65A3A3").
Definition gRP' : sv := ltac2:(tb__ "0|0|
S10S51S62S75Z3S29A2A3").   Definition gTR' : sv := ltac2:(tb__ "0|0|
S10S51S63S75Z3S29A2A3").   Definition gTS' : sv := ltac2:(tb__ "0|0|
S10S51S64S75Z25S29A2A3").
Lemma af_checks_nd : ltac2:(tb__ "0|9|
SeSdS6dS6cS6S7SfSfA2M0S38S8aS87S24S4eS7fS25A4M1S72S7cS59S2S81A3M2A1A2A3S5bS6S47S4aG1S71G2A1A2S28A3S6fG1S70G2A1A2A4S3fA3SeSdS6dS6cS6G0S38S8aS87S24S4eS7eS25A4M3S72S7cS59S2S80A3M4A1A2A3S5bS6S47S4aG3S71G4A1A2S28A3S6fG3S70G4A1A2A4S3eA3SeSdS1bS8cS4eS25S24S27S7fS2eA6S2dA3SeSdS1bS8cS4eS25S24S27S7eS2eA6S2bA3SeSdS8S1bA1M5S54S2dS3aS2dA1A2SaS1bS34A2A3SeSdG5S54S2bS3aS2bA1A2SaS1bS33A2A3SeSdS1bS85S34A1S2cA3SeSdS1bS85S33A1S2aA3SeSdS3S1eS2cA1S2A3SeSdS3S1eS2aA1S2A3SdS9S9S23A1M6A1S77S1bG6S1bS77S1dS23S1dS1aS1cS20R1A1A1A1LL;S8S9S1dA1M7A1G7Lx;S21S93Uc8S5aR1S2A5G7R1Ll;S5S1dA1X8x2A4LT;S0S1bS2cS0S1bS2aS5S1bA1A3A3A4S0G6S0S23S99S5S23A1A3M8S0G6G8S5G6A1A3A3A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_af.

(* [comment removed for export] *)
Module Lib_load_obj_land_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "Some"; "app"; "nil"; "option"; "S"; "list"; "prod"; "length"; "nat"; "None"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sstate"; "sv"; "swf"; "rm"; "ss_next"; "sv_eqb"; "SVar"; "sobj"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "idxB"; "NP"; "optL"; "vF"; "sel2last"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land"; "s_landA"; "s_landB"; "K1a"; "K1b"; "M_after0"; "M_bodyN"; "iD"; "splits_from"; "iK"; "XR_after1"; "XR_body1"; "bb_hi"; "fofs"; "iC"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "uval"; "BIc"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "am_eqb"; "am_subst"; "fr_below"; "fr_sub_eqb"; "nd_bd"; "AK0"; "AV0"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk"; "Za1_a1"; "Za1_b1"; "Za2_a1"; "Za2_b1"; "Za3_a1"; "Za3_b1"; "Za4_a1"; "Za4_b1"; "Zs1_a1"; "Zs1_b1"; "Zs2_a1"; "Zs2_b1"; "Zs3_a1"; "Zs3_b1"; "Zs4_a1"; "Zs4_b1"; "i1256_a1"; "i1256_b1"; "i480_a1"; "i480_b1"; "i880_a1"; "i880_b1"; "i96_a1"; "i96_b1"; "tvLand_a1"; "tvLand_b1"; "C10_a1"; "C10_b1"; "C11_a1"; "C11_b1"; "C12_a1"; "C12_b1"; "C13_a1"; "C13_b1"; "C9_a1"; "C9_b1"; "add_objs"; "add_objs_wf"; "nulls_a1"; "nulls_b1"; "tv1"; "PhiP0"; "XF_a1"; "XF_b1"; "bdLand_a1"; "bdLand_b1"; "unb_list"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "datasA"; "pH"; "vsP"; "X_bodyN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "decodes"; "lines_ok"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVAy TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition PhiP0 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S27S1S96S44Vrho;S36A2M0R1A2S97R1S95G0S98Z10S44Vrho;S38A2A2A2A2A2S3S0SaS9bQ8A1M1A1S21Vrho;S9aQ40R2A2A2S10G1A1A3A1F_;Fz;").
Definition PhiP1 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2ScSdS27S27A2M0A1M1G1S1S0S27S99SeG0R1A2A1S44Vrho;S3dA2A3S1S93S21Vrho;A1S44Vrho;S36A2R1A3S94R1S44Vrho;S2fA2A2A2A2LT;A2S79Vrho;A1A2").
Definition V_P : list positive := ltac2:(tb__ "0|0|
S4S28P71fS4S28P720S4S28P721S4S28PeS9S28A1A3A3A3A3").
Lemma PhiP0_reads : phi_reads V_P PhiP0.
Proof.
  intros rho rho' HV _ HM H z Hz. rewrite <- HM. apply H.
  rewrite <- (uval_rw rho rho' 1823 iD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 1825 iK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhiP1_reads : phi_reads V_P PhiP1.
Proof.
  intros rho rho' HV HL HM [(T & H1 & H2 & H3) HD]. split; [exists T | exact (PhiP0_reads rho rho' HV HL HM HD)].
  rewrite (uval_rw rho rho' 1824 iC eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 1823 iD eq_refl ltac:(apply HV; cbn; tauto)),
          (uval_rw rho rho' 14 vLEN eq_refl ltac:(apply HV; cbn; tauto)).
  split; [exact H1|]. split; [|exact H3]. eapply decodes_ext; [|exact H2]. intros z _. symmetry. apply HM.
Qed.

Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S8SdS1fS1fA2M0S3eS4G0S11S1fS1fS36S91Z10S38A2A4S9G0A1A3A3").

Definition ENDOW : list bitem := ltac2:(tb__ "0|2|
S4S43S45Z1M0Z0M1S4eA3S4S43S45G1G0S4dA3S9S43A1A3A3").

Fixpoint unb_list (n : nat) (A : axst) : list axform :=
  match n with O => [] | S n' =>
    let i := find_idxb (fun o => sv_eqb (ob_base o) vF && match ob_lo o with SLit l => (544 <=? l) && (l <? 1848) | _ => false end) (ss_objs (ax_S A)) 0%nat in
    if (i <? length (ss_objs (ax_S A)))%nat then AXUnbase i 544 :: unb_list n' (optL (apply_axforms A [AXUnbase i 544])) else [] end.
Definition canon_xf (A0 : axst) : list axform := ltac2:(tb__ "0|8|
S37S2aVA0;S2dZ280A3S3cS3bA1A2ScS12A1M0S2cS13VA0;R1A2A1S18S37S2aR1S2dZ200A3S4S27Z220S4S27Z228S4S27Z240S9S27A1M1A3A3A3A2G0S2cS13R2R1A2A1M2S18S37S2aR1S24PaA1M3Nb8A3S4S27Na0M4S4S27N98M5S4S27N90G1A3A3A3A2G0G2S18S4S12S14S2aR1S2dZ0M6A3S1cZ20A1A2S9S12A1M7A3G0G2S18S7eU2dR1A2G0G2S18S4S12S16S2aR1G3G4A3G4A2G7A3G0G2S18S4S12S16S2aR1G3G5A3G4A2G7A3G0G2S18S4S12S17S2eR1S2aR1S86G6A3S2aR1S86Z30A3A3A1G7A3G0G2S18S4S12S15S90SeS25S26S19R1A1A1A2U2A2A1G7A3G0S8S12R11S8S12RfS8S12RdS8S12RbS8S12R9S8S12R7S8S12R5S8S12R3R1A3A3A3A3A3A3A3A3Tx9;TA8;Tx8;TA7;Tx7;TA6;Tx6;TA5;Tx5;TA4;Tx4;TA3;Tx3;TA2;Tx2;TA1;Tx1;").

Definition zs1 (A : axst) (i : nat) (mid : Z) : axst := ltac2:(tb__ "0|0|
S2cS13VA;S4S12S14Vi;S1cVmid;A1A2S9S12A1A3A2A1").
Definition zs2 (A1 : axst) (j : nat) (cs : list cell) : sstate := ltac2:(tb__ "0|1|
SaS1eA1S1eLx;S29S19VA1;A1M0Vj;Vcs;A3S1eR1LSt;G0Xax2").

Fixpoint add_objs (A : axst) (ds : list sobj) : axst :=
  match ds with [] => A | o :: r => add_objs (ax_setS A (add_obj (ax_S A) o)) r end.
Fixpoint add_objs_wf (A : axst) (ds : list sobj) : bool :=
  match ds with [] => true | o :: r => swf (add_obj (ax_S A) o) && obj_wf (ss_next (ax_S A)) o && add_objs_wf (ax_setS A (add_obj (ax_S A) o)) r end.

Definition tvLand_b1 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landB) tvL.
Definition nulls_b1 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_b1.
Definition bdLand_b1 : list bitem := Eval vm_compute in bd_subst s_landB (nd_bd ndA1).
Definition XF_b1 : list axform := Eval vm_compute in canon_xf XR_body1.
Definition C9_b1 : axst := Eval vm_compute in optL (apply_axforms XR_body1 XF_b1).
Definition i96_b1 : nat := Eval vm_compute in idxB C9_b1 bA 96.
Definition Za1_b1 : axst := Eval vm_compute in zs1 C9_b1 i96_b1 112.
Definition Zs1_b1 : sstate := Eval vm_compute in zs2 Za1_b1 i96_b1 [c4 96 (SLit 0); c8 104 (SLit 0)].
Definition C10_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_b1 Zs1_b1) [AXMerge i96_b1]).
Definition i480_b1 : nat := Eval vm_compute in idxB C10_b1 bA 480.
Definition Za2_b1 : axst := Eval vm_compute in zs1 C10_b1 i480_b1 488.
Definition Zs2_b1 : sstate := Eval vm_compute in zs2 Za2_b1 (S i480_b1) [c1 488 (SLit 0)].
Definition C11_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_b1 Zs2_b1) [AXMerge i480_b1]).
Definition i1256_b1 : nat := Eval vm_compute in idxB C11_b1 bA 1256.
Definition Za3_b1 : axst := Eval vm_compute in zs1 C11_b1 i1256_b1 1260.
Definition Zs3_b1 : sstate := Eval vm_compute in zs2 Za3_b1 (S i1256_b1) [c4 1260 (SLit 0); c1 1264 (SLit 0)].
Definition C12_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_b1 Zs3_b1) [AXMerge i1256_b1]).
Definition i880_b1 : nat := Eval vm_compute in idxB C12_b1 bA 880.
Definition Za4_b1 : axst := Eval vm_compute in zs1 C12_b1 i880_b1 904.
Definition Zs4_b1 : sstate := Eval vm_compute in zs2 Za4_b1 i880_b1 [c1 885 (SLit 0)].
Definition C13_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_b1 Zs4_b1) [AXMerge i880_b1]).

Lemma pipe_b1 : ltac2:(tb__ "0|7|
S1S0SaS18A1M0S13S3aS7bA2S7S18S73A2A3S1S0G0S13S73S4S12S14S67S1cZ70A1A2S9S12A1M1A3A2S7S18S51A2A3S1S0SaS1eA1M2S29S19S51A1S67S4S1dS40Z60S1cZ0A1M3A2S4S1dS87Z68G3A2S9S1dA1M4A3A3A3S7S1eS59A2A3S1S0S6S20S59A1S5A3S1S0G0S13S1aS51S59A2S4S12S15S67A1G1A3A2S7S18S6bA2A3S1S0G0S13S6bS4S12S14S63S1cZ1e8M5A1A2G1A3A2S7S18S53A2A3S1S0G2S29S19S53A1SbS63A1S4S1dS3fG5G3A2G4A3A3S7S1eS5bA2A3S1S0S6S20S5bA1S5A3S1S0G0S13S1aS53S5bA2S4S12S15S63A1G1A3A2S7S18S6dA2A3S1S0G0S13S6dS4S12S14S61S1cZ4ecM6A1A2G1A3A2S7S18S55A2A3S1S0G2S29S19S55A1SbS61A1S4S1dS40G6G3A2S4S1dS3fZ4f0G3A2G4A3A3A3S7S1eS5dA2A3S1S0S6S20S5dA1S5A3S1S0G0S13S1aS55S5dA2S4S12S15S61A1G1A3A2S7S18S6fA2A3S1S0G0S13S6fS4S12S14S65S1cZ388A1A2G1A3A2S7S18S57A2A3S1S0G2S29S19S57A1S65S4S1dS3fZ375G3A2G4A3A3S7S1eS5fA2A3S1S0S6S20S5fA1S5A3S1S0G0S13S1aS57S5fA2S4S12S15S65A1G1A3A2S7S18S71A2A3S0S18S71S33A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_b1 : ltac2:(tb__ "0|1|
S1S0S18S74S35S82S84A1M0A2S85A3S0S6S75S35G0A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_b1 : ltac2:(tb__ "0|3|
S1S0S6S1bS33S35S31A3S5A3S1S0S6S89S31S2bA2S5A3S1S0S6S8eS2bS22S19S33A1A1M0A2S5A3S1S0S6S8bS31S69S42A3S5A3S1S0S6S4bS31S41S41A3S5A3S1S0S6S48S49S31S47S83S5A2A2S47S1cZ0A1M1S5A2A2S5A3S1S0S6S8dS8SdS1fS1fA2M2S78S77A3S69A2S5A3S1S0S6S4fG2S8cS77A3S5A3S1S0S6S8aG0S69A2S5A3S1S0S6S4aG0S41A2S5A3S1S0ScS43A1S46S31S4cS81A1A2S7dA3S0S6S4fS28S28S23S88S31R1A2G1A2Lx;S7fSfS28S8fS80U190U36A2A4A3S5A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition tvLand_a1 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landA) tvL.
Definition nulls_a1 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_a1.
Definition bdLand_a1 : list bitem := Eval vm_compute in bd_subst s_landA (nd_bd ndA1).
Definition XF_a1 : list axform := Eval vm_compute in canon_xf XR_after1.
Definition C9_a1 : axst := Eval vm_compute in optL (apply_axforms XR_after1 XF_a1).
Definition i96_a1 : nat := Eval vm_compute in idxB C9_a1 bA 96.
Definition Za1_a1 : axst := Eval vm_compute in zs1 C9_a1 i96_a1 112.
Definition Zs1_a1 : sstate := Eval vm_compute in zs2 Za1_a1 i96_a1 [c4 96 (SLit 0); c8 104 (SLit 0)].
Definition C10_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_a1 Zs1_a1) [AXMerge i96_a1]).
Definition i480_a1 : nat := Eval vm_compute in idxB C10_a1 bA 480.
Definition Za2_a1 : axst := Eval vm_compute in zs1 C10_a1 i480_a1 488.
Definition Zs2_a1 : sstate := Eval vm_compute in zs2 Za2_a1 (S i480_a1) [c1 488 (SLit 0)].
Definition C11_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_a1 Zs2_a1) [AXMerge i480_a1]).
Definition i1256_a1 : nat := Eval vm_compute in idxB C11_a1 bA 1256.
Definition Za3_a1 : axst := Eval vm_compute in zs1 C11_a1 i1256_a1 1260.
Definition Zs3_a1 : sstate := Eval vm_compute in zs2 Za3_a1 (S i1256_a1) [c4 1260 (SLit 0); c1 1264 (SLit 0)].
Definition C12_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_a1 Zs3_a1) [AXMerge i1256_a1]).
Definition i880_a1 : nat := Eval vm_compute in idxB C12_a1 bA 880.
Definition Za4_a1 : axst := Eval vm_compute in zs1 C12_a1 i880_a1 904.
Definition Zs4_a1 : sstate := Eval vm_compute in zs2 Za4_a1 i880_a1 [c1 885 (SLit 0)].
Definition C13_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_a1 Zs4_a1) [AXMerge i880_a1]).

Lemma pipe_a1 : ltac2:(tb__ "0|7|
S1S0SaS18A1M0S13S39S7aA2S7S18S72A2A3S1S0G0S13S72S4S12S14S66S1cZ70A1A2S9S12A1M1A3A2S7S18S50A2A3S1S0SaS1eA1M2S29S19S50A1S66S4S1dS40Z60S1cZ0A1M3A2S4S1dS87Z68G3A2S9S1dA1M4A3A3A3S7S1eS58A2A3S1S0S6S20S58A1S5A3S1S0G0S13S1aS50S58A2S4S12S15S66A1G1A3A2S7S18S6aA2A3S1S0G0S13S6aS4S12S14S62S1cZ1e8M5A1A2G1A3A2S7S18S52A2A3S1S0G2S29S19S52A1SbS62A1S4S1dS3fG5G3A2G4A3A3S7S1eS5aA2A3S1S0S6S20S5aA1S5A3S1S0G0S13S1aS52S5aA2S4S12S15S62A1G1A3A2S7S18S6cA2A3S1S0G0S13S6cS4S12S14S60S1cZ4ecM6A1A2G1A3A2S7S18S54A2A3S1S0G2S29S19S54A1SbS60A1S4S1dS40G6G3A2S4S1dS3fZ4f0G3A2G4A3A3A3S7S1eS5cA2A3S1S0S6S20S5cA1S5A3S1S0G0S13S1aS54S5cA2S4S12S15S60A1G1A3A2S7S18S6eA2A3S1S0G0S13S6eS4S12S14S64S1cZ388A1A2G1A3A2S7S18S56A2A3S1S0G2S29S19S56A1S64S4S1dS3fZ375G3A2G4A3A3S7S1eS5eA2A3S1S0S6S20S5eA1S5A3S1S0G0S13S1aS56S5eA2S4S12S15S64A1G1A3A2S7S18S70A2A3S0S18S70S32A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_a1 : ltac2:(tb__ "0|1|
S1S0S18S74S34S82S84A1M0A2S92A3S0S6S75S34G0A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_a1 : ltac2:(tb__ "0|3|
S1S0S6S1bS32S34S30A3S5A3S1S0S6S89S30S2bA2S5A3S1S0S6S8eS2bS22S19S32A1A1M0A2S5A3S1S0S6S8bS30S68S42A3S5A3S1S0S6S4bS30S41S41A3S5A3S1S0S6S48S49S30S47S83S5A2A2S47S1cZ0A1M1S5A2A2S5A3S1S0S6S8dS8SdS1fS1fA2M2S78S76A3S68A2S5A3S1S0S6S4fG2S8cS76A3S5A3S1S0S6S8aG0S68A2S5A3S1S0S6S4aG0S41A2S5A3S1S0ScS43A1S46S30S4cS81A1A2S7cA3S0S6S4fS28S28S23S88S30R1A2G1A2Lx;S7fSfS28S8fS80U190U36A2A4A3S5A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

End Lib_load_obj_land_chk.

(* [comment removed for export] *)
Module Lib_load_obj_hv3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "app"; "prod"; "nat"; "pair"; "Some"; "list"; "fst"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "ax_base"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "ss_objs"; "SAlu"; "sprop_below"; "sprop_eqb"; "DUnknown"; "SPEq"; "SVar"; "valuation"; "SMd"; "SPUlt"; "ob_cells"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "s_vr"; "E_vr"; "R_vr"; "brest_vr"; "h0"; "T_failr"; "Xk_vr"; "kept_vr"; "E_vr1"; "K_vrr"; "T_fail"; "T_fail0"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "bd_vr"; "cb_av"; "xfb_vr"; "B_fail"; "B_grown"; "B_keep"; "PDk_vr"; "T_grownS"; "T_keepS"; "d_av"; "hand_vr"; "k_av"; "tv_fail"; "tv_vr"; "PD_vr"; "av_base"; "bd_grown"; "bd_keep"; "bdrest_vr"; "cnt_av"; "inj_grown"; "inj_keep"; "nd_fail"; "nd_grown"; "nd_keep"; "objs_nl"; "passed_vr"; "room_av"; "s64"; "sh_of"; "slot_facts"; "tv_grown"; "tv_keep"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "V_B"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3.VR"; "Pre_vr"; "P_fail"; "P_grown"; "P_keep"; "nd0"; "bdP"; "tv0"; "tvP"; "vKn"; "vW"; "B32"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AHead"; "ND"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "s1A"; "extra_hv"; "robjs_chkR"; "sel_front"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "g5"; "vDp"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLC"; "bA"; "pI"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "last"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "xrs_inclb"; "pd_okA"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "sh_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
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
Definition K_vrr : axst := Eval vm_compute in shadow_release_stateA K_vr (objs_nl K_vr) 110 [(128, 12)].
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
S1S0SbS1aA1S1dS10S8aA1M0A1S6S1aS57S8aA1M1S4S1aSbeS85Z4M2Z1eM3S27S5bS8aA1A1M4S21A5S5S1aA1A3A3A3S1S0S18S13S8aA1S17SadA1A3S1S0S3S15S4S16S22S14S85A1S88A2S4S16S19S23S85A1S17Sa5Sa6Z2Z3dA2Z1A2A1A2S5S16A1A3A3S1bG0A1M5A2S2A3S1S0S3S8fS7S83S83A2M6SbbG4S21G2G3A4S4G6S9S83S83Z80ZcA4S5G6A1A3M7A3S2A3S1S0S3S7cS1cG0A1M8Sb3A2S2A3S1S0S3S81G5S63S60S80G1A5S2A3S1S0S3S96G5A1S2A3S1S0SfSbcS8aG1P6eG7A4S37A3S1S0S3SabG8S62A2S2A3S1S0S3S90S16S20S26S8eS8cA2A1G5A3S2A3S1S0S3S90S16S20S19S8cS89A2A1G5A3S2A3S0S3S90S16S20S19S89S17Z4000000A1A2A1G5A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
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

Definition s64 : sv := SAlu ALU_ADD (SVar 10) (SLit (-576)).
Definition av_base : sv := SAlu ALU_ADD vF (SLit 664).
Definition xfb_vr (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S29S2bS7eS5aS1eS92S86S17Z40M0A1A3VT;A3G0A2S4S29S2bS7eS4dS17Z0A1VT;A3N78A2S5S29A1M1A3A3SbS29A1Sa9S2aVT;R1A2A1SfS6S29R2S4S29S82S4S8S7eS7fS86R1A3S4S8S7eS7fS17N40A1R1A3S5S8A1A3A3SeS1aS1dS10R1A1A1A2A2S4S29S2cU0A1G1A3A3A3TT1;Tpre;").
Definition B_keep : axst := Eval vm_compute in optL' (apply_axforms T_keep0 (xfb_vr T_keep0)).
Definition B_grown : axst := Eval vm_compute in optL' (apply_axforms T_grown0 (xfb_vr T_grown0)).
Definition B_fail : axst := Eval vm_compute in optL' (apply_axforms T_fail0 (xfb_vr T_fail0)).
Definition T_keep : axst := Eval vm_compute in ax_tidy B_keep.
Definition T_grown : axst := Eval vm_compute in ax_tidy B_grown.
Definition T_failr : axst := Eval vm_compute in ax_tidy B_fail.

Definition T_fail : axst := Eval vm_compute in shadow_reopen_stateA T_failr X_hv g5 4 30.

Definition cb_av : sv := SMd M_MUL cnt_av (SLit 4).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S4S16S19S1eS92S3fS17ZcA1A3Sa7Z4Vk;A2M0A2S4S16S19S3fG0A2S4S16S19S3fS17S6fA1A2S5S16A1A3A3A3").
Definition inj_keep : list sprop := ltac2:(tb__ "0|0|
S6S16S5cS49A1S4S16S19S17SaeA1S47A2S5S16A1A3A3").
Definition inj_grown : list sprop := slot_facts vKg.
Definition T_keepS : axst := Eval vm_compute in ax_add_facts inj_keep T_keep.
Definition T_grownS : axst := Eval vm_compute in ax_add_facts inj_grown T_grown.

Lemma hv3_checks_vr_nd : ltac2:(tb__ "0|f|
S1S0S74S75S6S7S18S18A2M0S35S9fS9cS2eS65S68S2fA4M1S7bS94S32S2S69A3M2A1A2A3S60S6S71S72G1S7aG2A1A2S31A3S78G1S79G2A1A2A4S56A3S1S0S74S75S6G0S35S9fS9cS2eS65S67S2fA4M3S7bS94S32S2S77S6cS5S7S7S18S83A2S18A2A1M4S6aS6eS6dA2A3A3M5A1A2A3S60S6S71S72G3S7aG5A1A2S31A3S78G3S79G5A1A2A4S55A3S1S0S74S75S6G0S35S9fS9cS2eS65S66S2fA4M6S7bS94S32S2S77S6bG4S5S71A1A3A3M7A1A2A3S60S6S71S72G6S7aG7A1A2S31A3S78G6S79G7A1A2A4S54A3S1S0SfSa1S65S2fS2eS30S68S34A6S3dA3S1S0SfSa1S65S2fS2eS30S67S34A6S3bA3S1S0SfSa1S65S2fS2eS30S66S34A6S39A3S1S0SdSfA1M8S2aS3dS40S3dA1A2SaSfS43A2A3S1S0G8S2aS3bS40S3bA1A2SaSfS42A2A3S1S0G8S2aS39S40S39A1A2SaSfS41A2A3S1S0SfS9aS43A1S3cA3S1S0SfS9aS42A1S3aA3S1S0SfS9aS41A1S33A3S1S0SfSbdS33Sa8S85Z4Z1eA5S38A3S1S0S18S13S33A1S17SadA1A3S1S0S3S15S4S16S22S14S85A1S88A2S4S16S19S23S85A1S17Sa5Sa6Z2Z3dA2Z1A2A1A2S5S16A1A3A3S1bS10S33A1M9A1MaA2S2A3S1S0S3Sa3Sa8S12S33A1A2S2A3S1S0S3S28S10S38A1A1S2A3S1S0S3S81GaS4aS60S80S1dG9A1A5S2A3S1S0S3S96GaA1S2A3S1S0SfS9bS3cS6S16S53S1bS10S3cA1MbA1A3McA2S46A3S1S0SfS9bS3aS6S16S52S1bS10S3aA1MdA1A3MeA2S45A3S1S0S3S8fS16S1fS1cGbA1A1GcA3S2A3S1S0S3S8fS16S1fS1cGdA1A1GeA3S2A3S1S0S3S11S46A1S2A3S1S0S3S11S45A1S2A3S0S3S11S38A1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv3.

(* [comment removed for export] *)
Module Lib_load_obj_pro_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "list"; "app"; "fst"; "option"; "true"; "S"; "andb"; "bool"; "negb"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sv_eqb"; "valuation"; "SVar"; "sobj"; "ss_pc"; "DUnknown"; "cell"; "mkObj"; "ob_base"; "ob_hi"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "la_reason"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "z0"; "nd_r2"; "nd_r1"; "bd_pro"; "P_errN"; "PhisZ"; "cpsR"; "nd_rn"; "nd_rz"; "nobj"; "runR"; "vrank"; "En_sf"; "En_sf0"; "Pre_sf"; "Tn8"; "Tn_sf"; "bk_xf3"; "bk_xf4"; "bk_xf5"; "cutsR"; "cutsV"; "cv_i"; "cv_xf"; "exitsR"; "exitsV"; "vl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXSplit"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "optL"; "NP"; "fr_lo"; "FUEL_lo"; "sel2last"; "vF"; "BAD"; "C_pro"; "C_pro2"; "C_pro3"; "E_f8a0"; "E_ma0"; "E_mo0"; "E_mz0"; "E_sm0"; "Pre_lo"; "T_mz1"; "find_idxb"; "idxB"; "idxC"; "optS"; "vLEN"; "z24"; "@Corelib.Lists.ListDef"; "map"; "seq"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "batom"; "bitem"; "BI"; "ASv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "div"; "eqb"; "mul"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "T_mb"; "vs_T"; "vsn"; "E_mb0"; "E_mc0"; "E_s00_0"; "T_ma_ok"; "T_mc"; "T_s00"; "blkAR"; "vALo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LI"; "nd_lo0"; "P_err"; "bd_lo0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "filter"; "@Corelib.Init.Logic"; "True"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LND"; "E_blr0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "CK0"; "CK_DIV"; "CV"; "CV0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module LI. Include Lib_load_obj_iface. End LI. Module LND. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land. End LND.

Definition cpsR : list Z := LND.cps_proR.
Definition runR (S : axst) : list leafA := ltac2:(tb__ "0|1|
S8S5S21A1M0A1G0Lx;S25S71S4dS2fVS;S9A5G0R1Ll;S4S21A1X8x2").
Definition showR (S : axst) : ltac2:(tb__ "0|0|
S5S3S1dS65A2A1") := ltac2:(tb__ "0|0|
S61S21S3S1dS65A2S21S0S1dS65S16S20S22R1A1A1A1S24R1A1A4LL;S33VS;A1A4").
Definition leafR (S : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S64S1fU0S61S21S1fS22S81S21S21S6eS16S20S22R1A1A1A1Vpc;A2LL;S33VS;A1A3A4S50A4").
Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).

Definition vT (j : nat) : axst := ltac2:(tb__ "0|0|
S2S1fLj;Vj;S72S2S73S74R1A1A1Lj';X2x2").
Definition VL : list axst := Eval vm_compute in map (fun j => leafR (vT j) memset_pc) (seq 0 34).
Definition vl (j : nat) : axst := nth j VL BAD.

Definition cv_i (L : axst) (b : sv) (off : Z) : nat := ltac2:(tb__ "0|0|
S5dVL;Vb;Voff;A3").
Definition cv_xf (L : axst) (b : sv) (off n : Z) : list axform := ltac2:(tb__ "0|1|
S1S44S48S3fVL;Vb;Voff;A3M0S11Voff;A1A2S1S44S48SaG0A1S11S6bVoff;Vn;A2A1A2S4S44A1A3A3").
Definition cv_1 (L : axst) (b : sv) (off n : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VL;S40VL;Vb;Voff;Vn;A4A2A1").

Definition bk_1 (T0 : axst) : axst := ltac2:(tb__ "0|0|
S5eVT0;S85S20VT0;A1U1S60A3A2").
Definition bk_2 (T1 : axst) : axst := ltac2:(tb__ "0|0|
S4aS45VT1;S1S44S49U1A1S4S44A1A3A2A1").
Definition bk_xf3 (T2 : axst) (b : sv) (off : Z) : list axform := ltac2:(tb__ "0|0|
S1S44S47S4eVT2;S5bS15S15SbS12S1aR1A1Vb;A2S12S1bR1A1S11Voff;A1A2A2Lo;S1cS20VT2;A1A1U0A4U1A3A1S4S44A1A3").
Definition bk_3 (T2 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VT2;S3aVT2;Vb;Voff;A3A2A1").
Definition bk_xf4 (T3 : axst) (b : sv) (off : Z) : list axform := ltac2:(tb__ "0|0|
S1S44S47S4eVT3;S70S32VT3;A1U1A2S5cVT3;Vb;S6bVoff;Z18A2A3A3A1S4S44A1A3").
Definition bk_4 (T3 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VT3;S3bVT3;Vb;Voff;A3A2A1").
Definition bk_xf5 (T4 : axst) : list axform := ltac2:(tb__ "0|1|
S1S44S46S70S32VT4;A1U3A2A1M0S1S44G0S4S44A1A3A3").
Definition bk_5 (T4 : axst) : axst := ltac2:(tb__ "0|0|
S4aS45VT4;S3cVT4;A1A2A1").

Definition XN (E : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S81S3S10S10A2M0G0SdSeS12S7S10S10R1A3M1S7cA2S12G1S4fA2A2A1Lr;S23VE;A1A3").
Definition Tn8 : axst := Eval vm_compute in shadow_reopen_stateA T_ma_null (XN T_ma_null) g5 32 64.
Definition En_sf0 : axst := Eval vm_compute in leafR Tn8 sf5_pc.
Definition En_sfB : axst := Eval vm_compute in shadow_release_stateA En_sf0 (objs_butlast En_sf0) 110 [].
Definition zmid : sobj := ltac2:(tb__ "0|0|
S19S4fS11Z1f0A1S11Z200A1S4S18A1S17A5").
Definition En_sfC : axst := Eval vm_compute in ax_setS En_sfB (reshape_obj_at (ax_S En_sfB) 5 zmid).
Definition xf_nm : list axform := ltac2:(tb__ "0|3|
S1S44S47S1S2U6S1S2U5S1S2U7S1S2U8S1S2U9S1S2U1S1S2U0M0S1S2U2M1S1S2U3S1S2U4S1S2UaS1S2UbS1S2UcS4S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S44S46G0A1M2S1S44G2S1S44S46G1A1S4S44A1A3A3A3A3").
Definition En_sfD : axst := Eval vm_compute in optL (apply_axforms En_sfC xf_nm).
Definition En_sf : axst := Eval vm_compute in flag_carve_stateA En_sfD 120.
Definition Pre_sf : axst := Pre_stack_free AE_A 5.
Definition L_sf : axst := L_stack_free AE_A 5.
Definition s_sfn : wsub := ltac2:(tb__ "0|1|
S1S3S1eS10A2M0S0S1eS10P10S14P78A1A4S1G0S0S1eS10PfS14P13A1A4S80PaS20S35A1S20S37A1A3A3A3").
Definition Rn_sf : list sobj := Eval vm_compute in optR (entails_frA En_sf Pre_sf s_sfn).
Definition Tn_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf En_sf s_sfn Rn_sf L_sf (ax_X En_sf).
Definition Tn_sf : axst := Eval vm_compute in ax_tidy Tn_sf0.
Definition P_errN : axst := Eval vm_compute in leafR Tn_sf lo_ret.
Definition s_pe : wsub := ltac2:(tb__ "0|0|
S80S4bS20S2dA1S20S7eA1A3").

Definition PhisZ : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S1S3S5S1eA1M0S13OF_;M1A2M2S0G0G1S4S1eA1S13S82L_;A4S4G2A1A3").
Definition z0 : sv := SLit 0.
Definition bd_pro : list bitem := ltac2:(tb__ "0|5|
S1S68S69Z1M0Z0M1S1S3S1dS67A2M2S0S1dS67S8aS6aS5fA1M3A4S4G2A1M4A3S6cS8bZ40A2A4S1S68S69G1G0S1G2S0S1dS67S6dS66S89A2G3A4G4A3S6cS6fS66S88A2S66A2A4S4S68A1A3A3").
Definition nd_r1 : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S4cS7fS27A4").
Definition nd_rn : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S4cS2cS27A4").
Definition nd_r2 : ndesc := ltac2:(tb__ "0|1|
S28S1S3S10S10A2M0S7bS4G0A1A3S4cS2cS27A4").
Definition nd_rz : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S4S3S3S10S1dA2S10A2A1S2cS27A4").
Definition vrank (j : nat) : Z := 2900 - 10 * Z.of_nat j.
Definition cutsV : list efnode := ltac2:(tb__ "0|4|
S61S2S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2S2S0G1G2S0G0S2S0S1fS26S73S74R1A1A1S2aA4U0M3A4S0S1dS10S34R1A1S29A4A4Lj;S62G3U22A2A4").
Definition exitsV : list efnode := ltac2:(tb__ "0|4|
S61S2S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2S2S0G1G2S0G0S2S0S1fS26S43R1A1S2aA4U0M3A4S0S1dS10S6bS34R1A1Z9A2S29A4A4Lj;S62G3U22A2A4").
Definition cutsR : list efnode := ltac2:(tb__ "0|5|
S6S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2M3S1G3S0G1G2S0G0S2S0S1fS26S59S7dA4U0M4A4S0S1dS10Zbb8S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S51S2bA4G4A4S0S1dS10ZbaeS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S52S2bA4G4A4S0S1dS10Zba4S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S53S2bA4G4A4S0S1dS10Zb9aS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S5aS2bA4G4A4S0S1dS10Zb90S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S78S2aA4G4A4S0S1dS10Zb86S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S79S2aA4G4A4S0S1dS10Zb7cS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S7aS2aA4G4A4S0S1dS10Zb72S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S72S2aA4G4A4S0S1dS10Zb68S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S38S30A4G4A4S0S1dS10Z960S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S39S31A4G4A4S0S1dS10Z956S29A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3S3eA3").
Definition exitsR : list efnode := ltac2:(tb__ "0|5|
S6S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2M3S1G3S0G1G2S0G0S2S0S1fS26S58S7dA4U0M4A4S0S1dS10Zbb7S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S54S2bA4G4A4S0S1dS10ZbadS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S56S2bA4G4A4S0S1dS10Zba3S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S57S2bA4G4A4S0S1dS10Zb99S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S55S2bA4G4A4S0S1dS10Zb8fS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S76S2aA4G4A4S0S1dS10Zb85S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S77S2aA4G4A4S0S1dS10Zb7bS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S75S2aA4G4A4S0S1dS10Zb71S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S84S2aA4G4A4S0S1dS10Za09S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S36S30A4G4A4S0S1dS10Z95fS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S2dS31A4G4A4S0S1dS10Z955S29A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3S42A3").

Lemma ecertR_ok : ltac2:(tb__ "0|0|
S83ScS86S71S4bS2eS4dS2fS4bS3dS41A8S9A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma PhisZ_reads : ltac2:(tb__ "0|3|
S63S3S5S1eA1M0S13OF_;M1A2M2G2S87S7G0G1R1A3SfG0G1R1A3A2Lp;S2eA3").
Proof. constructor; [intros rho rho' _ _ _ _; exact I | constructor]. Qed.
End Lib_load_obj_pro_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_avt.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "prod"; "pair"; "nat"; "nil"; "app"; "Some"; "list"; "option"; "fst"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "sobj"; "ss_next"; "SPUle"; "cell"; "ss_facts"; "sprop_below"; "ss_objs"; "valuation"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt"; "s_vt"; "E_vt"; "S_vt_okR"; "brest_vt"; "R_vt"; "tv_vt"; "E_vt1"; "T_vt_f0"; "T_vt_ok0"; "T_vt_ok1"; "Xk_vt"; "bd_vt"; "c_avt"; "B_vt_f"; "B_vt_ok"; "PDk_vt"; "T_vt_ok"; "hand_vt"; "kept_vt"; "nd_vt_ok"; "xfb_vt"; "T_vt_f"; "avt_cell_new"; "avt_cell_old"; "bd_vt_ok"; "bdrest_vt"; "d_avt"; "d_aw"; "k_avt"; "k_aw"; "ndX_vt"; "nd_vt_f"; "passed_vt"; "rate_t1"; "room_vt"; "t1"; "tv_vt_f"; "tv_vt_ok"; "upd_cellv"; "upd_objv"; "xf_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt.HVT"; "Pre_vt"; "P_fail"; "P_ok"; "Posts_vt"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "HNEXT"; "X_latch"; "pE0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "AK1"; "LAK"; "bdA"; "bdX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "bd_permb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hvt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
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

End Lib_load_obj_avt.

