(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SPUle"; "SAlu"; "FcsrFrm0"; "mkSS"; "cell"; "SExt"; "SPBranch"; "SVar"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "apply_axforms"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l"; "pQ"; "pK"; "X_hl"; "pD"; "pX"; "lc_n"; "tv_hl"; "vKg"; "PHIN"; "optAp"; "tvI"; "bd_hl"; "C24"; "O_F"; "O_Wl"; "builderL"; "li_n"; "nd0"; "pP"; "vDg"; "C_cg"; "C_ck"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_pc0"; "E_sm0"; "E_unp0"; "E_vr0"; "F_cells"; "H"; "J"; "K"; "L1"; "L2"; "NA"; "O_flag"; "O_frame"; "Pre_hl"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_pc"; "XN"; "X_pro"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "cg_var"; "ck_var"; "fr_hl"; "frame_factsH"; "ghostL_facts"; "pT0"; "prog_fact"; "shF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2"; "z0"; "VR"; "ndF"; "qK"; "qK2"; "ndJ"; "qD"; "qD2"; "qCUR"; "yCUR"; "yK"; "yK2"; "ndG"; "ndK"; "bdL"; "ndX2"; "tvL"; "yD"; "yD2"; "ndO"; "ndOg"; "ndT"; "qC"; "qC2"; "qHP"; "tvY"; "bd_ok"; "lcn1"; "ndN"; "ndNs"; "ndP"; "ndX"; "post_base_facts"; "yC"; "yC2"; "P_fail"; "P_ok"; "YC"; "bdJK"; "bdO"; "fail_facts"; "ndEf"; "ndEo"; "ndH"; "ndXs"; "nd_fail"; "nd_ok"; "objs_post"; "ok_facts"; "qERR"; "slot4_facts"; "tvN"; "yERR"; "yHP"; "C_c2g"; "C_c2k"; "C_e8g"; "C_e8k"; "C_epf"; "C_epo"; "C_f2a"; "C_f2b"; "C_fa0"; "C_fa1"; "C_few"; "C_ok"; "C_rlf"; "C_rlo"; "E_da2"; "E_da2x"; "E_vc"; "E_vc0"; "NZ32"; "T_fail2"; "T_grown2"; "T_grown2_0"; "T_keep2"; "T_keep2_0"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_f7a"; "X_f7b"; "X_fp0"; "X_fp1"; "X_ok0"; "X_rlf"; "X_rlo"; "c2g_var"; "c2k_var"; "cmul4"; "epi_regs"; "lcc1"; "ndEf'"; "ndEo'"; "objs_epi"; "sel_e8"; "sel_f"; "sel_f2"; "sel_rel"; "tvG"; "tvN2"; "xf_e8"; "xf_f"; "xf_f2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "lc_k"; "PROG"; "lc_d"; "O_data"; "bd_vec"; "li_k"; "vec_facts"; "HNEXT"; "h_fregs"; "tI"; "O_cE"; "O_cP"; "O_text"; "kb"; "li_d"; "tE"; "cnt_facts"; "hF"; "hG"; "h_xregs"; "handle_facts"; "lc_c"; "li_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "KLG"; "B32"; "vDp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.HLAddr"; "hl_ret"; "DW"; "FR"; "hl_EPI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "flag_carve_stateA"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
SfeSffVY;SbVY;A1Se2Z0Z10A5PaaA2").

Definition X_fp0 : axst := Eval vm_compute in leaf_at T_fail0 hl_FP 0.
Definition X_fp1 : axst := Eval vm_compute in leaf_at T_fail0 hl_FP 1.
Definition sel_f : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U9S0S2U8S0S2UaS0S2UbS0S2U5S0S2U6S0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U2S0S2U14S0S2U15S0S2U16S0S2U3S0S2U17S0S2U18S0S2U7S0S2U4S0S2U19S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_f : list axform := ltac2:(tb__ "0|2|
S0S21S22U1M0Z40A2S0S21S22U2N270A2S0S21S24Sc8A1S0S21S23U0A1S0S21S23G0A1M1S0S21G1S3S21A1A3A3A3A3A3A3").
Definition canon_f (A : axst) : axst := ltac2:(tb__ "0|0|
SefS30S25VA;SceA2A1S29S2aS28Sd2Sd0A4A2").
Definition Y_fp0 : axst := Eval vm_compute in canon_f X_fp0.
Definition Y_fp1 : axst := Eval vm_compute in canon_f X_fp1.
Definition C_fa0 : axst := Eval vm_compute in epi_state Y_fp0.
Definition C_fa1 : axst := Eval vm_compute in epi_state Y_fp1.
Goal lvs T_fail0 = [(hl_FP, RsCut); (hl_FP, RsCut)] /\ shape Y_fp1 = shape Y_fp0
  /\ map (fun o => (ob_base o, ob_lo o, ob_hi o)) (ss_objs (ax_S Y_fp0)) = map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pQ pHP pD pC pK [] [])
  /\ lvs C_fa0 = [(hl_EPI, RsCut)] /\ lvs C_fa1 = [(hl_EPI, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition yCUR : sv := SVar 320. Definition yD : sv := SVar 321. Definition yC : sv := SVar 322. Definition yK : sv := SVar 323.
Definition yD2 : sv := SVar 324. Definition yC2 : sv := SVar 325. Definition yK2 : sv := SVar 326. Definition yHP : sv := SVar 327. Definition yERR : sv := SVar 328.
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1bSecS1aS8Q20Ve;A3S14Z0A1A3").
Definition objs_epi (err cur hp d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S4S12S0S12S35S0S12S51S3S19A1A1S0S12S50S3S12A1M0A3A3A3S4S12SeeS4S12S0S12S34S49A1G0A3S4S12S36Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S0S12Sf2S0S12SdbVcur;A1S0S12SdaS0S12SdcS0S12Sd3Vd;ZcVk;A3S0S12Sd3Vd2;Z4Vk2;A3G0A3A3A3A3A3A3A3A3A3A3").
Definition post_base_facts (cur hp : sv) : list sprop := ltac2:(tb__ "0|0|
S4S13Se4Sf6Sf5A2S4S13Se0S4S13S0S13S15Vhp;S14Z1A1A2S0S13S15Se6S14Se8A1A2S0S13S15Sd9Vcur;A2S0S13S15Vcur;SdfA2S3S13A1A3A3A3A3S62A3A3A3").
Definition lcc1 : sv := SAlu ALU_ADD lc_c (SLit 1).
Definition lcn1 : sv := SAlu ALU_ADD lc_n (SLit 1).
Definition ok_facts (cur d c k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|0|
S4S13S0S13S64Vc;Vcur;A2S0S13S15Vc2;Sc3A2S3S13A1A3A3S4S13Sd6Vd;Vc;Vk;ZcVdv;A5Sd6Vd2;Vc2;Vk2;Z4Vdv2;A5A3A3").
Definition fail_facts (err d c k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|0|
S4S13S0S13SaeVerr;A1S3S13A1A3S4S13Sd6Vd;Vc;Vk;ZcVdv;A5Sd6Vd2;Vc2;Vk2;Z4Vdv2;A5A3A3").
Definition epi_regs : list sv := ltac2:(tb__ "0|1|
Se3S0S5S2S11A2M0S1S2S11U8S1cPaA1A4S0G0S1S2S11U12Se1A4S0G0S1S2S11U17S65A4S3G0A1A3A3A3A1").
Definition YC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SedS18Sf7Sc2Sd8S17S6S11A1Sc6Verr;S6fS9bS77S87S70S78S88S71A9S4S13Vfacts;S4S13S86S6fS9bA2S61A3A3Sd7S7A9S29S77S70S78S71A4A2").
Definition Y_ok : axst := ltac2:(tb__ "0|0|
S8bSf3S96S6fS77S87S70S78S88S71P141P144A9A2").
Definition Y_fail : axst := ltac2:(tb__ "0|0|
S8bS9aS8eS9aS77S87S70S78S88S71P141P144A9A2").
Definition C_epo : axst := Eval vm_compute in epi_state Y_ok.
Definition C_epf : axst := Eval vm_compute in epi_state Y_fail.
Goal map (fun L => leaf_matchesA NPH L [C_epo; C_epf]) (leavesA_at FUEL_hl cutpcs_hl C_fa0 hl_EPI ++ leavesA_at FUEL_hl cutpcs_hl C_fa1 hl_EPI) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition X_ok0 : axst := Eval vm_compute in leaf_at XN hl_OK 0.
Definition E_da2 : axst := Eval vm_compute in leaf_at XN da_entry 0.

Definition E_da2x : axst := Eval vm_compute in optAp (apply_axforms E_da2 [AXSplit 0 (SLit (-96))]).
Definition s_da2 : wsub := ltac2:(tb__ "0|0|
Sf8PaSaSabA1SaSfbA1A3").
Definition R_da2 : list sobj := Eval vm_compute in optR (entails_frA E_da2x Pre_da s_da2).
Goal entails_frA E_da2x Pre_da s_da2 = Some R_da2 /\ call_checkA E_da2x Pre_da s_da2 R_da2 (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da2 : axst := Eval vm_compute in T_pure Pre_da E_da2x s_da2 R_da2 P_da.
Definition xf_tda2 : list axform := ltac2:(tb__ "0|1|
S0S21S24S4S2S0S2U3S0S2U0M0S0S2U4S0S2U5S0S2U1S0S2U2S3S2A1A3A3A3A3A3A3Sf0U6U12A2A3A1S0S21S23G0A1S3S21A1A3A3").
Definition Y_few : axst := Eval vm_compute in optAp (apply_axforms T_da2 xf_tda2).
Definition C_few : axst := Eval vm_compute in epi_state Y_few.
Goal map (fun o => (ob_base o, ob_lo o, ob_hi o)) (ss_objs (ax_S Y_few)) = map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pX pHP pD li_c pK [] [])
  /\ lvs C_few = [(hl_EPI, RsCut)] /\ map (fun L => leaf_matchesA NPH L [C_epf; C_epo]) (leavesA_at FUEL_hl cutpcs_hl C_few hl_EPI) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_ok : axst := Eval vm_compute in shadow_reopen_stateA X_ok0 (ax_X X_ok0) hG 8 9.
Definition E_vc0 : axst := Eval vm_compute in leaf_at C_ok vr_entry 0.
Goal lvs C_ok = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition sh_ok : sobj := Eval vm_compute in last (ss_objs (ax_S E_vc0)) O_Wl.
Definition objs_vc0 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_vc0)).
Goal sh_ok = shobj hG 8 9 (ob_cells sh_ok) DUnknown /\ local_ok (ob_cells sh_ok) DUnknown 8 9 (64, 4) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_vc1 : axst := Eval vm_compute in shadow_release_stateA E_vc0 objs_vc0 160 [(64, 4)].
Definition xf_vc : list axform := ltac2:(tb__ "0|2|
S0S21S26U0M0S14N40M1A1A2S0S21S22G0G1A2S0S21S22UfZ290A2S3S21A1A3A3A3").
Definition E_vc : axst := Eval vm_compute in optAp (apply_axforms E_vc1 xf_vc).

Definition PD_vr : list (axst * ndesc) := PD_vn.
Definition s_v2 : wsub := ltac2:(tb__ "0|1|
S0S5S1fS11A2M0S1S1fS11P3bS81A4S0G0S1S1fS11P13S16SeaSe9S14Z40A1A3A4Sf8PaSaSacA1SaSfcA1A3A3A3").
Definition R_v2 : list sobj := Eval vm_compute in optR (entails_frA E_vc VN.Pre_vr s_v2).
Goal entails_frA E_vc VN.Pre_vr s_v2 = Some R_v2 /\ call_checkPA E_vc VN.Pre_vr s_v2 R_v2 (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition Xk_v2 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) lc_d)) (ax_X E_vc1).
Definition T_keep2_0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_keep Xk_v2.
Definition T_fail2 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_fail Xk_v2.
Definition T_grown2_0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_grown Xk_v2.

Definition cmul4 (c : sv) : sv := SMd M_MUL c (SLit 4).
Definition slot4_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0S13S15S16SeaSc1Se5A1M0S14Z4M1A1A3SddG1Vk;A2M2A2S0S13S15G0G2A2S0S13S15G0S14Se8A1A2S3S13A1A3A3A3").
Definition T_keep2 : axst := ltac2:(tb__ "0|0|
Sf9S4S13S98Sd0A1S0S13S15S14S100A1Sd2A2S3S13A1A3A3Sb3A2").
Definition T_grown2 : axst := ltac2:(tb__ "0|0|
Sf9S98S2eA1Sb1A2").
Goal lvs T_keep2 = [(hl_cp2, RsCut)] /\ lvs T_grown2 = [(hl_cp2, RsCut)] /\ lvs T_fail2 = [(hl_RP8, RsCut); (hl_RP8, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition L_c2k : axst := Eval vm_compute in leaf_at T_keep2 hl_cp2 0.
Definition L_c2g : axst := Eval vm_compute in leaf_at T_grown2 hl_cp2 0.
Definition C_c2k : axst := Eval vm_compute in bl_cut L_c2k 14 (SLit 4) [10; 11; 16; 17]%nat [].
Definition C_c2g : axst := Eval vm_compute in bl_cut L_c2g 14 (SLit 4) [10; 11; 16; 17]%nat [].
Definition c2k_var : sv := Eval vm_compute in bl_var L_c2k (SLit 4).
Definition c2g_var : sv := Eval vm_compute in bl_var L_c2g (SLit 4).

Definition X_e8k : axst := Eval vm_compute in bl_junk (leaf_at C_c2k hl_RP8 0) [16; 17]%nat.
Definition X_e8g : axst := Eval vm_compute in bl_junk (leaf_at C_c2g hl_RP8 0) [16; 17]%nat.
Goal lvs C_c2k = [(hl_cp2, RsCut); (hl_RP8, RsCut); (hl_cp2, RsCut); (hl_RP8, RsCut)] /\ lvs C_c2g = lvs C_c2k. Proof. vm_compute. split; reflexivity. Qed.

Definition sel_e8 : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U7S0S2U8S0S2U5S0S2U6S0S2U9S0S2UaS0S2UbS0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U2S0S2U12S0S2U13S0S2U3S0S2U14S0S2U15S0S2U16S0S2U17S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_e8 : list axform := ltac2:(tb__ "0|0|
S0S21S22U1Z40A2S0S21S22U2N290A2S0S21S24Sc7A1S0S21S23U0A1S3S21A1A3A3A3A3").
Definition canon_e8 (A : axst) (d2 k2 : sv) : axst := ltac2:(tb__ "0|0|
SefS30S25VA;ScdA2A1S29S2aS28Vd2;Vk2;A4A2").
Definition Y_e8k : axst := Eval vm_compute in canon_e8 X_e8k lc_d lc_k.
Definition Y_e8g : axst := Eval vm_compute in canon_e8 X_e8g vDg vKg.
Definition C_e8k : axst := Eval vm_compute in epi_state Y_e8k.
Definition C_e8g : axst := Eval vm_compute in epi_state Y_e8g.

Definition X_f2a : axst := Eval vm_compute in leaf_at T_fail2 hl_RP8 0.
Definition X_f2b : axst := Eval vm_compute in leaf_at T_fail2 hl_RP8 1.
Definition sel_f2 : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U7S0S2U8S0S2U5S0S2U6S0S2U9S0S2UaS0S2UbS0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U2S0S2U12S0S2U13S0S2U3S0S2U14S0S2U15S0S2U16S0S2U17S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_f2 : list axform := ltac2:(tb__ "0|0|
S0S21S22U1Z40A2S0S21S22U2N290A2S0S21S24Sc9A1S0S21S23U0A1S3S21A1A3A3A3A3").
Definition canon_f2 (A : axst) : axst := ltac2:(tb__ "0|0|
SefS30S25VA;ScfA2A1S29S2aS28Sd2Sd0A4A2").
Definition Y_f2a : axst := Eval vm_compute in canon_f2 X_f2a.
Definition Y_f2b : axst := Eval vm_compute in canon_f2 X_f2b.
Definition C_f2a : axst := Eval vm_compute in epi_state Y_f2a.
Definition C_f2b : axst := Eval vm_compute in epi_state Y_f2b.
Goal map (fun Y => map (fun o => (ob_base o, ob_lo o, ob_hi o)) (ss_objs (ax_S Y))) [Y_e8k; Y_f2a; Y_f2b]
     = map (fun _ => map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pX pHP pD pC pK [] [])) [0;1;2]
  /\ shape Y_e8g = shape (ax_setS Y_e8k (set_objs (ax_S Y_e8k) (firstn 22 (ss_objs (ax_S Y_e8k)) ++ [O_data vDg 4 vKg])))
  /\ map lvs [C_e8k; C_e8g; C_f2a; C_f2b] = map (fun _ => [(hl_EPI, RsCut)]) [0;1;2;3]
  /\ map (fun C => map (fun L => (leaf_matchesA NPH L [C_epf], leaf_matchesA NPH L [C_epo])) (leavesA_at FUEL_hl cutpcs_hl C hl_EPI)) [C_e8k; C_e8g; C_f2a; C_f2b]
     = [[(false, true)]; [(false, true)]; [(true, true)]; [(true, false)]].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_f7a : axst := Eval vm_compute in leaf_at K hl_EPI 0.
Definition X_f7b : axst := Eval vm_compute in leaf_at K hl_EPI 1.
Definition Z_f7a : axst := Eval vm_compute in epi_state X_f7a.
Definition Z_f7b : axst := Eval vm_compute in epi_state X_f7b.
Goal leaf_matches1A NPH Z_f7a C_epf = true /\ leaf_matches1A NPH Z_f7b C_epf = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_rlo : axst := Eval vm_compute in leaf_at C_epo hl_REL 0.
Definition X_rlf : axst := Eval vm_compute in leaf_at C_epf hl_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S4S2S0S2U0S3S2A1M0A3S4S2Sf0U3U14A2S0S2U1S0S2U2S0S2U17S0S2U18G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S30S25VX;S0S21S24ScaA1S3S21A1A3A2A1S9ScR1SfdSaR1A1M0Sf1S12U15S1dG0A1A3A2A2TX1;").
Definition C_rlo : axst := Eval vm_compute in rel_state X_rlo.
Definition C_rlf : axst := Eval vm_compute in rel_state X_rlf.
Goal lvs C_epo = [(hl_REL, RsCut)] /\ lvs C_epf = [(hl_REL, RsCut)]
  /\ map (fun X => release_objs_ok 160 170 hG 1 (skipn 21 (ss_objs (ax_S (optAp (apply_axforms X [AXSelect sel_rel])))))) [X_rlo; X_rlf] = [true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rlo; C_rlf] = [21; 21]%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_reto : axst := Eval vm_compute in leaf_at C_rlo hl_ret 0.
Definition X_retf : axst := Eval vm_compute in leaf_at C_rlf hl_ret 0.
Goal lvs C_rlo = [(hl_ret, RsSymJump)] /\ lvs C_rlf = [(hl_ret, RsSymJump)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition qCUR : sv := SVar 310. Definition qD : sv := SVar 311. Definition qC : sv := SVar 312. Definition qK : sv := SVar 313.
Definition qHP : sv := SVar 314. Definition qERR : sv := SVar 315. Definition qD2 : sv := SVar 316. Definition qC2 : sv := SVar 317. Definition qK2 : sv := SVar 318.
Definition objs_post (err hp d c k d2 c2 k2 cur : sv) : list sobj := ltac2:(tb__ "0|1|
S4S12S0S12S35S3S12A1M0A3S4S12SeeS4S12S0S12S34S3S19A1A1G0A3S4S12S36Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S0S12Sf2S0S12SdbVcur;A1S0S12SdaS0S12SdcS0S12Sd3Vd;ZcVk;A3S0S12Sd3Vd2;Z4Vk2;A3G0A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
SedS18Sf4SfaP190A1Sd8S17S6S11A1S95Sf3S7eS6cS7cS69S6dS7dS6aS6eA9S4S13S96S6eS6cS7cS69S6dS7dS6aP137P13cA9S86S6eS7eA2A3Sd7S7A9S29S6cS69S6dS6aA4A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
SedS18Sf4SfaP190A1Sd8S17S6S11A1S95S97S7eS6cS7cS69S6dS7dS6aS6eA9S4S13S8eS97S6cS7cS69S6dS7dS6aP137P13cA9S86S6eS7eA2A3Sd7S7A9S29S6cS69S6dS6aA4A2").

Definition bd_ok (k k2 cur : sv) : list bitem := ltac2:(tb__ "0|0|
S4S20S0S20Sd1Z48Vcur;A2S0S20S2fVcur;Vk;A2S0S20Se7Vk;A1S3S20A1A3A3A3Sd4Z4S81Vk2;A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
SeS2dS6cS69S6dS6aA4S3S5S5S11S1eA2S11A2A1S80S69S6aS6eA3A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
SeS2dS6cS69S6dS6aA4S3S5S5S11S1eA2S11A2A1S0S20Sd1Z48S6eA2S3S20A1A3A3").
Definition Posts_hl : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S5S9SdA2M0S1S9SdS89S93A4S0G0S1S9SdS8aS94A4S3G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S10Vtv;S60Vbd;SfA4").
Definition bdL (k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S32S4fVcur;A1Vk;S2cSd0Vcur;A5").
Definition bdJK (k : sv) : list bitem := ltac2:(tb__ "0|1|
S4S20S0S20S2fS27Vk;A2S0S20Se7Vk;A1S0S20Sd1Z48S27A2S3S20A1M0A3A3A3S4S20Sd4Z4S2cSd0A3S0S20S33G0A3A3A3").
Definition bdX : list bitem := ltac2:(tb__ "0|1|
S4S20S0S20Sd1Z48S27A2S3S20A1M0A3S4S20Sd4Z4S2cSd0A3S0S20S33G0A3A3A3").
Definition bdO (k2 : sv) : list bitem := ltac2:(tb__ "0|0|
S4S20Sd4Z4S81Vk2;A3S0S20Sd1Z48S2bA2S0S20S2fS2bS28A2S0S20Se7S28A1S3S20A1A3A3A3A3").
Definition bdX2 : list bitem := ltac2:(tb__ "0|0|
S0S20Sd1Z48S2bA2S0S20S2fS2bS28A2S0S20Se7S28A1S3S20A1A3A3A3").
Definition tvL : list (sv * sv) := ltac2:(tb__ "0|0|
S31S2aS28Sd2Sd0A4").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
S31S3aS2eSd2Sd0A4").
Definition tvN : list (sv * sv) := ltac2:(tb__ "0|0|
S2dS2aS28Sd2Sd0A4").
Definition tvN2 : list (sv * sv) := ltac2:(tb__ "0|0|
S2dS2aS28S3aS2eA4").
Definition tvY : list (sv * sv) := ltac2:(tb__ "0|0|
S2dS77S70S78S71A4").
Definition nd0' : ndesc := ltac2:(tb__ "0|0|
SeS31SdeSd5Sd2Sd0A4S3S5S5S11S1eA2S11A2A1S32S37Sd5S2cSd0Sd9A5A3").
Definition ndP : ndesc := ltac2:(tb__ "0|0|
S68S31SdeSd5Sd2Sd0A4S32S37Sd5S2cSd0Sd9A5A2").
Definition ndH : ndesc := ltac2:(tb__ "0|0|
S68S76S74S28S39A2A2").
Definition ndT : ndesc := ltac2:(tb__ "0|0|
S68S76S74S28S63A2A2").
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S68S76S74S28S27A2A2").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S68S76S8cS28A1A2").
Definition ndG : ndesc := ltac2:(tb__ "0|0|
S68ScbS8cS2eA1A2").
Definition ndX : ndesc := ndF tvL bdX.
Definition ndXs : ndesc := ndF tvN bdX.
Definition ndN : ndesc := ltac2:(tb__ "0|0|
S68S76S74S28S2bA2A2").
Definition ndNs : ndesc := ltac2:(tb__ "0|0|
S68S99S74S28S2bA2A2").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S68S99S8dSd0A1A2").
Definition ndOg : ndesc := ltac2:(tb__ "0|0|
S68SccS8dS2eA1A2").
Definition ndX2 : ndesc := ndF tvN bdX2.
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
S68S7fS80S70S71S6fA3A2").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
S68S7fS0S20Sd1Z48S6fA2S3S20A1A3A2").
Definition ndEo' : ndesc := ltac2:(tb__ "0|0|
SeS7fS3S5S5S11S1eA2S11A2A1S80S70S71S6fA3A3").
Definition ndEf' : ndesc := ltac2:(tb__ "0|0|
SeS7fS3S5S5S11S1eA2S11A2A1S0S20Sd1Z48S6fA2S3S20A1A3A3").

Definition VR (cur : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S16SeaSddZ40S16SebSdfVcur;A3A2S14Vpos;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsL : list edescA := ltac2:(tb__ "0|e|
S0S5S5S9SdA2M0S5S1eS11A2M1A2M2S1G0G1S1S9SdS52S38A4S1S1eS11Z64S66A4A4S0G2S1G0G1S1S9SdS40S84A4S1S1eS11Z60S66A4A4S0G2S1G0G1S1S9SdS3fS84A4S1S1eS11Z5cS66A4A4S0G2S1G0G1S1S9SdS4aS91A4S1S1eS11Z50M3S67S39Z2A2A4A4S0G2S1G0G1S1S9SdS4dS91A4S1S1eS11G3S67S27Z1A2A4A4S0G2S1G0G1S1S9SdS4eS7bA4S1S1eS11G3S67S27Z0A2A4A4S0G2S1G0G1S1S9SdS4cS7bA4S1S1eS11G3S67S27Z3cA2A4A4S0G2S1G0G1S1S9SdS43S6bA4S1S1eS11G3S67S27Z3aA2A4A4S0G2S1G0G1S1S9SdS57S6bA4S1S1eS11G3S67S27Z38A2A4A4S0G2S1G0G1S1S9SdS53S6bA4S1S1eS11G3S67S27Z36A2A4A4S0G2S1G0G1S1S9SdS4bS6bA4S1S1eS11G3S67S27Z35A2A4A4S0G2S1G0G1S1S9SdS56S73A4S1S1eS11G3S67S27Z33A2A4M4A4S0G2S1G0G1S1S9SdS55S72A4G4A4S0G2S1G0G1S1S9SdS54S85A4S1S1eS11Z1eS66A4M5A4S0G2S1G0G1S1S9SdS3cS73A4S1S1eS11G3S5fA4A4S0G2S1G0G1S1S9SdS3bS72A4S1S1eS11G3S5eA4A4S0G2S1G0G1S1S9SdS3eS73A4S1S1eS11G3S67S27Z1dA2A4M6A4S0G2S1G0G1S1S9SdS3dS72A4G6A4S0G2S1G0G1S1S9SdS42S73A4S1S1eS11G3S67S27Z1bA2A4M7A4S0G2S1G0G1S1S9SdS41S72A4G7A4S0G2S1G0G1S1S9SdSa4S92A4S1S1eS11Z1aS66A4M8A4S0G2S1G0G1S1S9SdSa5S92A4G8A4S0G2S1G0G1S1S9SdS58S82A4S1S1eS11Z28S66A4A4S0G2S1G0G1S1S9SdSa6S83A4G5A4S0G2S1G0G1S1S9SdSa7S83A4S1S1eS11Z24S66A4A4S0G2S1G0G1S1S9SdSb2S79A4S1S1eS11Z20S66A4M9A4S0G2S1G0G1S1S9SdSb0S7aA4G9A4S0G2S1G0G1S1S9SdSafS75A4G9A4S0G2S1G0G1S1S9SdS9dS79A4S1S1eS11Z1cMaSc0A4A4S0G2S1G0G1S1S9SdS9cS7aA4S1S1eS11GaSbfA4A4S0G2S1G0G1S1S9SdS9fS79A4S1S1eS11Z18S66A4MbA4S0G2S1G0G1S1S9SdS9eS7aA4GbA4S0G2S1G0G1S1S9SdSa2S75A4GbA4S0G2S1G0G1S1S9SdSa3S75A4GbA4S0G2S1G0G1S1S9SdSa0S8fA4S1S1eS11ZeS66A4McA4S0G2S1G0G1S1S9SdSa1S90A4GcA4S0G2S1G0G1S1S9SdSa8Sc4A4S1S1eS11ZaS66A4MdA4S0G2S1G0G1S1S9SdSa9Sc5A4GdA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsL : list edescA := ltac2:(tb__ "0|d|
S0S5S5S9SdA2M0S5S1eS11A2M1A2M2S1G0G1S1S9SdS46S38A4S1S1eS11Z62S66A4A4S0G2S1G0G1S1S9SdS59S84A4S1S1eS11Z5eS66A4A4S0G2S1G0G1S1S9SdS47S6bA4S1S1eS11Z50M3S67S27Z3bA2A4A4S0G2S1G0G1S1S9SdS45S6bA4S1S1eS11G3S67S27Z39A2A4A4S0G2S1G0G1S1S9SdS44S6bA4S1S1eS11G3S67S27Z37A2A4A4S0G2S1G0G1S1S9SdS48S6bA4S1S1eS11G3S67S27Z34A2A4A4S0G2S1G0G1S1S9SdS5dS73A4S1S1eS11G3S67S27Z1eA2A4M4A4S0G2S1G0G1S1S9SdS5cS72A4G4A4S0G2S1G0G1S1S9SdS5bS73A4S1S1eS11G3S67S27Z1cM5A2A4M6A4S0G2S1G0G1S1S9SdS5aS72A4G6A4S0G2S1G0G1S1S9SdSbaS85A4S1S1eS11G5S66A4M7A4S0G2S1G0G1S1S9SdSbbS85A4G7A4S0G2S1G0G1S1S9SdSb8S7bA4S1S1eS11Z14S66A4M8A4S0G2S1G0G1S1S9SdSb9S7bA4G8A4S0G2S1G0G1S1S9SdSbcS82A4S1S1eS11Z26S66A4M9A4S0G2S1G0G1S1S9SdSaaS82A4G9A4S0G2S1G0G1S1S9SdSadS83A4S1S1eS11Z22S66A4A4S0G2S1G0G1S1S9SdSb5S79A4S1S1eS11Z1aS66A4MaA4S0G2S1G0G1S1S9SdSb4S7aA4GaA4S0G2S1G0G1S1S9SdSb6S75A4GaA4S0G2S1G0G1S1S9SdSb7S75A4GaA4S0G2S1G0G1S1S9SdSbdS8fA4S1S1eS11ZcS66A4MbA4S0G2S1G0G1S1S9SdSbeS90A4GbA4S0G2S1G0G1S1S9SdS89S93A4S1S1eS11Z0S66A4McA4S0G2S1G0G1S1S9SdS8aS94A4GcA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
