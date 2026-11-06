(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SPUle"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkObj"; "SExt"; "SPBranch"; "SVar"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l"; "pQ"; "pK"; "X_hl"; "pD"; "pX"; "lc_n"; "optAp"; "tv_hl"; "vKg"; "PHIN"; "tvI"; "bd_hl"; "C24"; "O_F"; "O_Wl"; "builderL"; "li_n"; "nd0"; "pP"; "reshapeA"; "vDg"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_mg0"; "E_mk0"; "E_pc0"; "E_sm0"; "E_unp0"; "E_vr0"; "F_cells"; "H"; "J"; "K"; "L1"; "L2"; "NA"; "O_flag"; "O_frame"; "Pre_hl"; "Pre_mc"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_mcg"; "T_mck"; "T_pc"; "XN"; "X_pro"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "fr_hl"; "frame_factsH"; "ghostL_facts"; "pT0"; "prog_fact"; "shF"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2"; "z0"; "VR"; "ndF"; "qK"; "qK2"; "ndJ"; "qD"; "qD2"; "ndG"; "ndK"; "qCUR"; "yCUR"; "yK"; "yK2"; "bdL"; "ndO"; "ndOg"; "ndX2"; "tvL"; "yD"; "yD2"; "cmul4"; "ndT"; "qC"; "qC2"; "qHP"; "tvY"; "bd_ok"; "lcn1"; "ndN"; "ndNs"; "ndP"; "ndX"; "post_base_facts"; "yC"; "yC2"; "P_fail"; "P_ok"; "YC"; "bdJK"; "bdO"; "fail_facts"; "ndEf"; "ndEo"; "ndH"; "ndXs"; "nd_fail"; "nd_ok"; "objs_post"; "ok_facts"; "qERR"; "slot4_facts"; "tvN"; "yERR"; "yHP"; "C_e8g"; "C_e8k"; "C_epf"; "C_epo"; "C_f2a"; "C_f2b"; "C_fa0"; "C_fa1"; "C_few"; "C_ok"; "C_rlf"; "C_rlo"; "E_da2"; "E_da2x"; "E_m2g0"; "E_m2k0"; "E_vc"; "E_vc0"; "NZ32"; "T_fail2"; "T_grown2"; "T_grown2_0"; "T_keep2"; "T_keep2_0"; "T_m2g"; "T_m2k"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_f7a"; "X_f7b"; "X_fp0"; "X_fp1"; "X_ok0"; "X_rlf"; "X_rlo"; "dst4_obj"; "epi_regs"; "lcc1"; "mid4_dst"; "ndEf'"; "ndEo'"; "objs_epi"; "sel_e8"; "sel_f"; "sel_f2"; "sel_rel"; "tvG"; "tvN2"; "xf_e8"; "xf_f"; "xf_f2"; "xf_mc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "lc_k"; "PROG"; "lc_d"; "O_data"; "bd_vec"; "lc_c"; "li_k"; "vec_facts"; "HNEXT"; "h_fregs"; "kb"; "tI"; "O_cE"; "O_cP"; "O_text"; "li_d"; "tE"; "cnt_facts"; "hF"; "hG"; "h_xregs"; "handle_facts"; "li_c"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "KLG"; "B32"; "vDp"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "O_al"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.HLAddr"; "hl_ret"; "DW"; "FR"; "hl_EPI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "flag_carve_stateA"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
S107S108VY;SbVY;A1SecZ0Z10A5PaaA2").

Definition X_fp0 : axst := Eval vm_compute in leaf_at T_fail0 hl_FP 0.
Definition X_fp1 : axst := Eval vm_compute in leaf_at T_fail0 hl_FP 1.
Definition sel_f : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U9S0S2U8S0S2UaS0S2UbS0S2U5S0S2U6S0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U2S0S2U14S0S2U15S0S2U16S0S2U3S0S2U17S0S2U18S0S2U7S0S2U4S0S2U19S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_f : list axform := ltac2:(tb__ "0|2|
S0S22S23U1M0Z40A2S0S22S23U2N270A2S0S22S25Sd0A1S0S22S24U0A1S0S22S24G0A1M1S0S22G1S3S22A1A3A3A3A3A3A3").
Definition canon_f (A : axst) : axst := ltac2:(tb__ "0|0|
SfbS30S27VA;Sd6A2A1S2cS2dS2bSdbSd9A4A2").
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
S1dSf2S1cS8Q20Ve;A3S14Z0A1A3").
Definition objs_epi (err cur hp d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S4S12S0S12S38S0S12S55S3S17A1A1S0S12S54S3S12A1M0A3A3A3S4S12Sf9S4S12S0S12S37S4dA1G0A3S4S12S39Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S0S12SfcS0S12Se6Vcur;A1S0S12Se5S0S12Se7S0S12SdcVd;ZcVk;A3S0S12SdcVd2;Z4Vk2;A3G0A3A3A3A3A3A3A3A3A3A3").
Definition post_base_facts (cur hp : sv) : list sprop := ltac2:(tb__ "0|0|
S4S13SeeS100SffA2S4S13SeaS4S13S0S13S15Vhp;S14Z1A1A2S0S13S15SefS14Sf4A1A2S0S13S15Se4Vcur;A2S0S13S15Vcur;Se9A2S3S13A1A3A3A3A3S67A3A3A3").
Definition lcc1 : sv := SAlu ALU_ADD lc_c (SLit 1).
Definition lcn1 : sv := SAlu ALU_ADD lc_n (SLit 1).
Definition ok_facts (cur d c k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|0|
S4S13S0S13S69Vc;Vcur;A2S0S13S15Vc2;ScaA2S3S13A1A3A3S4S13Se0Vd;Vc;Vk;ZcVdv;A5Se0Vd2;Vc2;Vk2;Z4Vdv2;A5A3A3").
Definition fail_facts (err d c k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|0|
S4S13S0S13Sb5Verr;A1S3S13A1A3S4S13Se0Vd;Vc;Vk;ZcVdv;A5Se0Vd2;Vc2;Vk2;Z4Vdv2;A5A3A3").
Definition epi_regs : list sv := ltac2:(tb__ "0|1|
SedS0S5S2S11A2M0S1S2S11U8S1ePaA1A4S0G0S1S2S11UbSebA4S0G0S1S2S11U17S6aA4S3G0A1A3A3A3A1").
Definition YC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sf8S19S101Sc9Se2S18S6S11A1SceVerr;S77Sa2S7fS8eS78S80S8fS79A9S4S13Vfacts;S4S13S8dS77Sa2A2S66A3A3Se1S7A9S2cS7fS78S80S79A4A2").
Definition Y_ok : axst := ltac2:(tb__ "0|0|
S92SfdS9dS77S7fS8eS78S80S8fS79P141P144A9A2").
Definition Y_fail : axst := ltac2:(tb__ "0|0|
S92Sa1S95Sa1S7fS8eS78S80S8fS79P141P144A9A2").
Definition C_epo : axst := Eval vm_compute in epi_state Y_ok.
Definition C_epf : axst := Eval vm_compute in epi_state Y_fail.
Goal map (fun L => leaf_matchesA NPH L [C_epo; C_epf]) (leavesA_at FUEL_hl cutpcs_hl C_fa0 hl_EPI ++ leavesA_at FUEL_hl cutpcs_hl C_fa1 hl_EPI) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition X_ok0 : axst := Eval vm_compute in leaf_at XN hl_OK 0.
Definition E_da2 : axst := Eval vm_compute in leaf_at XN da_entry 0.

Definition E_da2x : axst := Eval vm_compute in optAp (apply_axforms E_da2 [AXSplit 0 (SLit (-96))]).
Definition s_da2 : wsub := ltac2:(tb__ "0|0|
SfaPaSaSb0A1SaS104A1A3").
Definition R_da2 : list sobj := Eval vm_compute in optR (entails_frA E_da2x Pre_da s_da2).
Goal entails_frA E_da2x Pre_da s_da2 = Some R_da2 /\ call_checkA E_da2x Pre_da s_da2 R_da2 (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da2 : axst := Eval vm_compute in T_pure Pre_da E_da2x s_da2 R_da2 P_da.
Definition xf_tda2 : list axform := ltac2:(tb__ "0|1|
S0S22S25S4S2S0S2U3S0S2U0M0S0S2U4S0S2U5S0S2U1S0S2U2S3S2A1A3A3A3A3A3A3Sf6U6U12A2A3A1S0S22S24G0A1S3S22A1A3A3").
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
S0S22S26U0M0S14N40M1A1A2S0S22S23G0G1A2S0S22S23UfZ290A2S3S22A1A3A3A3").
Definition E_vc : axst := Eval vm_compute in optAp (apply_axforms E_vc1 xf_vc).

Definition PD_vr : list (axst * ndesc) := PD_vn.
Definition s_v2 : wsub := ltac2:(tb__ "0|1|
S0S5S21S11A2M0S1S21S11P3bS88A4S0G0S1S21S11P13S16Sf0Sf5S14Z40A1A3A4SfaPaSaSb3A1SaS105A1A3A3A3").
Definition R_v2 : list sobj := Eval vm_compute in optR (entails_frA E_vc VN.Pre_vr s_v2).
Goal entails_frA E_vc VN.Pre_vr s_v2 = Some R_v2 /\ call_checkPA E_vc VN.Pre_vr s_v2 R_v2 (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition Xk_v2 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) lc_d)) (ax_X E_vc1).
Definition T_keep2_0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_keep Xk_v2.
Definition T_fail2 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_fail Xk_v2.
Definition T_grown2_0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vc s_v2 R_v2 VN.P_grown Xk_v2.

Definition cmul4 (c : sv) : sv := SMd M_MUL c (SLit 4).
Definition slot4_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0S13S15S16Sf0S81SdeA1M0S14Z4M1A1A3Se3G1Vk;A2M2A2S0S13S15G0G2A2S0S13S15G0S14Sf4A1A2S3S13A1A3A3A3").
Definition T_keep2 : axst := ltac2:(tb__ "0|0|
S102S4S13S9fSd9A1S0S13S15S14S109A1SdbA2S3S13A1A3A3SbaA2").
Definition T_grown2 : axst := ltac2:(tb__ "0|0|
S102S9fS32A1Sb8A2").
Definition E_m2k0 : axst := Eval vm_compute in leaf_at T_keep2 memcpy_pc 0.
Definition E_m2g0 : axst := Eval vm_compute in leaf_at T_grown2 memcpy_pc 0.
Goal lvs T_keep2 = [(memcpy_pc, RsCut)] /\ lvs T_grown2 = [(memcpy_pc, RsCut)] /\ lvs T_fail2 = [(hl_RP8, RsCut); (hl_RP8, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition dst4_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S1bS16Sf0Vd;S81SdeA1A3S14Z0A1S14Z4A1S3S17A1S1aA5").
Definition xf_mc2 : list axform := ltac2:(tb__ "0|5|
S0S22S23U1M0Z40M1A2S0S22S25S4S2S0S2G0S0S2U0M2S3S2A1A3A3Sf6U2U16A2A3A1S0S22S24G2A1S0S22S26U3S81SdeA1M3A2S0S22S26U4S16Sf0G3S14Z4A1A3A2S0S22S26U8S14G1A1A2S0S22S26U9M4S14Z44A1A2S0S22S23G4G1A2S3S22A1A3A3A3A3A3A3A3A3").
Definition E_mc2 (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S3dS30S27VE0;Sd8A2A1U4Sc8Vd;A1A3").
Definition E_m2k : axst := Eval vm_compute in E_mc2 E_m2k0 lc_d.
Definition E_m2g : axst := Eval vm_compute in E_mc2 E_m2g0 vDg.
Definition s_mc2 (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|2|
S0S5S21S11A2M0S1S21S11P35Vd;A4S0G0S1S21S11P36Se3Z4M1Vk;A2A4S0G0S1S21S11P37S6bZ40A1A4S0G0S1S21S11P38S14G1A1A4S0G0S1S21S11S10aSf5A4SfaPaSaVE;A1SaS57A1A3A3A3A3A3A3").
Definition R_m2k : list sobj := Eval vm_compute in optR (entails_frA E_m2k Pre_mc (s_mc2 E_m2k lc_d lc_k)).
Definition R_m2g : list sobj := Eval vm_compute in optR (entails_frA E_m2g Pre_mc (s_mc2 E_m2g vDg vKg)).
Goal entails_frA E_m2k Pre_mc (s_mc2 E_m2k lc_d lc_k) = Some R_m2k /\ call_checkPA E_m2k Pre_mc (s_mc2 E_m2k lc_d lc_k) R_m2k [L_mc1; L_mc1] = true
  /\ entails_frA E_m2g Pre_mc (s_mc2 E_m2g vDg vKg) = Some R_m2g /\ call_checkPA E_m2g Pre_mc (s_mc2 E_m2g vDg vKg) R_m2g [L_mc1; L_mc1] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_m2k : axst := Eval vm_compute in T_afterA Pre_mc E_m2k (s_mc2 E_m2k lc_d lc_k) R_m2k L_mc1.
Definition T_m2g : axst := Eval vm_compute in T_afterA Pre_mc E_m2g (s_mc2 E_m2g vDg vKg) R_m2g L_mc1.

Definition X_e8k : axst := Eval vm_compute in leaf_at T_m2k hl_RP8 0.
Definition X_e8g : axst := Eval vm_compute in leaf_at T_m2g hl_RP8 0.
Goal lvs T_m2k = [(hl_RP8, RsCut)] /\ lvs T_m2g = [(hl_RP8, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition mid4_dst (d : sv) : sobj := ltac2:(tb__ "0|1|
S1bVd;S81SdeA1M0S16Sf0G0S14Z4A1A3S3S17A1S1aA5").
Definition sel_e8 : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U9S0S2U2S0S2UaS0S2UbS0S2U3S0S2U4S0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U14S0S2U5S0S2U15S0S2U16S0S2U6S0S2U17S0S2U18S0S2U19S0S2U1aS0S2U7S0S2U1S0S2U8S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_e8 : list axform := ltac2:(tb__ "0|2|
S0S22S28U2A1S0S22S23U5N290A2S0S22S25ScfA1S0S22S24U1A1M0S0S22G0S0S22S24U16A1M1S0S22G1S3S22A1A3A3A3A3A3A3A3").
Definition canon_e8 (A : axst) (d2 k2 : sv) : axst := ltac2:(tb__ "0|0|
SfbS30S27S3dVA;U1ScbVd2;A1A3Sd5A2A1S2cS2dS2bVd2;Vk2;A4A2").
Definition Y_e8k : axst := Eval vm_compute in canon_e8 X_e8k lc_d lc_k.
Definition Y_e8g : axst := Eval vm_compute in canon_e8 X_e8g vDg vKg.
Definition C_e8k : axst := Eval vm_compute in epi_state Y_e8k.
Definition C_e8g : axst := Eval vm_compute in epi_state Y_e8g.

Definition X_f2a : axst := Eval vm_compute in leaf_at T_fail2 hl_RP8 0.
Definition X_f2b : axst := Eval vm_compute in leaf_at T_fail2 hl_RP8 1.
Definition sel_f2 : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U7S0S2U8S0S2U5S0S2U6S0S2U9S0S2UaS0S2UbS0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U2S0S2U12S0S2U13S0S2U3S0S2U14S0S2U15S0S2U16S0S2U17S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_f2 : list axform := ltac2:(tb__ "0|0|
S0S22S23U1Z40A2S0S22S23U2N290A2S0S22S25Sd1A1S0S22S24U0A1S3S22A1A3A3A3A3").
Definition canon_f2 (A : axst) : axst := ltac2:(tb__ "0|0|
SfbS30S27VA;Sd7A2A1S2cS2dS2bSdbSd9A4A2").
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
S4S2S0S2U0S3S2A1M0A3S4S2Sf6U3U14A2S0S2U1S0S2U2S0S2U17S0S2U18G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S30S27VX;S0S22S25Sd2A1S3S22A1A3A2A1S9ScR1S106SaR1A1M0Sf7S12U15S1fG0A1A3A2A2TX1;").
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
S4S12S0S12S38S3S12A1M0A3S4S12Sf9S4S12S0S12S37S3S17A1A1G0A3S4S12S39Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S0S12SfcS0S12Se6Vcur;A1S0S12Se5S0S12Se7S0S12SdcVd;ZcVk;A3S0S12SdcVd2;Z4Vk2;A3G0A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
Sf8S19SfeS103P190A1Se2S18S6S11A1S9cSfdS85S72S83S6fS73S84S70S76A9S4S13S9dS76S72S83S6fS73S84S70P137P13cA9S8dS76S85A2A3Se1S7A9S2cS72S6fS73S70A4A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
Sf8S19SfeS103P190A1Se2S18S6S11A1S9cS9eS85S72S83S6fS73S84S70S76A9S4S13S95S9eS72S83S6fS73S84S70P137P13cA9S8dS76S85A2A3Se1S7A9S2cS72S6fS73S70A4A2").

Definition bd_ok (k k2 cur : sv) : list bitem := ltac2:(tb__ "0|0|
S4S29S0S29SdaZ48Vcur;A2S0S29S33Vcur;Vk;A2S0S29Sf3Vk;A1S3S29A1A3A3A3SddZ4S88Vk2;A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
SeS31S72S6fS73S70A4S3S5S5S11S20A2S11A2A1S87S6fS70S76A3A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
SeS31S72S6fS73S70A4S3S5S5S11S20A2S11A2A1S0S29SdaZ48S76A2S3S29A1A3A3").
Definition Posts_hl : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S5S9SdA2M0S1S9SdS90S9aA4S0G0S1S9SdS91S9bA4S3G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S10Vtv;S65Vbd;SfA4").
Definition bdL (k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S35S53Vcur;A1Vk;S2fSd9Vcur;A5").
Definition bdJK (k : sv) : list bitem := ltac2:(tb__ "0|1|
S4S29S0S29S33S2aVk;A2S0S29Sf3Vk;A1S0S29SdaZ48S2aA2S3S29A1M0A3A3A3S4S29SddZ4S2fSd9A3S0S29S36G0A3A3A3").
Definition bdX : list bitem := ltac2:(tb__ "0|1|
S4S29S0S29SdaZ48S2aA2S3S29A1M0A3S4S29SddZ4S2fSd9A3S0S29S36G0A3A3A3").
Definition bdO (k2 : sv) : list bitem := ltac2:(tb__ "0|0|
S4S29SddZ4S88Vk2;A3S0S29SdaZ48S2eA2S0S29S33S2eS2bA2S0S29Sf3S2bA1S3S29A1A3A3A3A3").
Definition bdX2 : list bitem := ltac2:(tb__ "0|0|
S0S29SdaZ48S2eA2S0S29S33S2eS2bA2S0S29Sf3S2bA1S3S29A1A3A3A3").
Definition tvL : list (sv * sv) := ltac2:(tb__ "0|0|
S34S2dS2bSdbSd9A4").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
S34S3eS32SdbSd9A4").
Definition tvN : list (sv * sv) := ltac2:(tb__ "0|0|
S31S2dS2bSdbSd9A4").
Definition tvN2 : list (sv * sv) := ltac2:(tb__ "0|0|
S31S2dS2bS3eS32A4").
Definition tvY : list (sv * sv) := ltac2:(tb__ "0|0|
S31S7fS78S80S79A4").
Definition nd0' : ndesc := ltac2:(tb__ "0|0|
SeS34Se8SdfSdbSd9A4S3S5S5S11S20A2S11A2A1S35S3aSdfS2fSd9Se4A5A3").
Definition ndP : ndesc := ltac2:(tb__ "0|0|
S6eS34Se8SdfSdbSd9A4S35S3aSdfS2fSd9Se4A5A2").
Definition ndH : ndesc := ltac2:(tb__ "0|0|
S6eS7eS7aS2bS3cA2A2").
Definition ndT : ndesc := ltac2:(tb__ "0|0|
S6eS7eS7aS2bS68A2A2").
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S6eS7eS7aS2bS2aA2A2").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S6eS7eS93S2bA1A2").
Definition ndG : ndesc := ltac2:(tb__ "0|0|
S6eSd3S93S32A1A2").
Definition ndX : ndesc := ndF tvL bdX.
Definition ndXs : ndesc := ndF tvN bdX.
Definition ndN : ndesc := ltac2:(tb__ "0|0|
S6eS7eS7aS2bS2eA2A2").
Definition ndNs : ndesc := ltac2:(tb__ "0|0|
S6eSa0S7aS2bS2eA2A2").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S6eSa0S94Sd9A1A2").
Definition ndOg : ndesc := ltac2:(tb__ "0|0|
S6eSd4S94S32A1A2").
Definition ndX2 : ndesc := ndF tvN bdX2.
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
S6eS86S87S78S79S77A3A2").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
S6eS86S0S29SdaZ48S77A2S3S29A1A3A2").
Definition ndEo' : ndesc := ltac2:(tb__ "0|0|
SeS86S3S5S5S11S20A2S11A2A1S87S78S79S77A3A3").
Definition ndEf' : ndesc := ltac2:(tb__ "0|0|
SeS86S3S5S5S11S20A2S11A2A1S0S29SdaZ48S77A2S3S29A1A3A3").

Definition VR (cur : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S16Sf0Se3Z40S16Sf1Se9Vcur;A3A2S14Vpos;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsL : list edescA := ltac2:(tb__ "0|f|
S0S5S5S9SdA2M0S5S20S11A2M1A2M2S1G0G1S1S9SdS56S3bA4S1S20S11Z64S6cA4A4S0G2S1G0G1S1S9SdS42S8bA4S1S20S11Z60S6cA4A4S0G2S1G0G1S1S9SdS41S8bA4S1S20S11Z5cS6cA4A4S0G2S1G0G1S1S9SdS4eS98A4S1S20S11Z50M3S6dS3cZ2A2A4A4S0G2S1G0G1S1S9SdS51S98A4S1S20S11G3S6dS2aZ1A2A4A4S0G2S1G0G1S1S9SdS52S82A4S1S20S11G3S6dS2aZ0A2A4A4S0G2S1G0G1S1S9SdS50S82A4S1S20S11G3S6dS2aZ3cA2A4A4S0G2S1G0G1S1S9SdS45S71A4S1S20S11G3S6dS2aZ3aA2A4A4S0G2S1G0G1S1S9SdS5eS71A4S1S20S11G3S6dS2aZ38A2A4A4S0G2S1G0G1S1S9SdS58S71A4S1S20S11G3S6dS2aZ36A2A4A4S0G2S1G0G1S1S9SdS4fS71A4S1S20S11G3S6dS2aZ35A2A4A4S0G2S1G0G1S1S9SdS5bS75A4S1S20S11G3S6dS2aZ33A2A4M4A4S0G2S1G0G1S1S9SdS5aS74A4G4A4S0G2S1G0G1S1S9SdS59S8cA4S1S20S11Z1eS6cA4M5A4S0G2S1G0G1S1S9SdS5dS75A4S1S20S11G3S6dS2aZ31A2A4M6A4S0G2S1G0G1S1S9SdS5cS74A4G6A4S0G2S1G0G1S1S9SdS40S75A4S1S20S11G3S6dS2aZ2fA2A4M7A4S0G2S1G0G1S1S9SdS3fS74A4G7A4S0G2S1G0G1S1S9SdS44S75A4S1S20S11G3S6dS2aZ2dA2A4M8A4S0G2S1G0G1S1S9SdS43S74A4G8A4S0G2S1G0G1S1S9SdSa9S99A4S1S20S11Z1aS6cA4M9A4S0G2S1G0G1S1S9SdSaaS99A4G9A4S0G2S1G0G1S1S9SdS5fS89A4S1S20S11Z28S6cA4A4S0G2S1G0G1S1S9SdSabS8aA4G5A4S0G2S1G0G1S1S9SdSacS8aA4S1S20S11Z24S6cA4A4S0G2S1G0G1S1S9SdSb9S7bA4S1S20S11Z20S6cA4MaA4S0G2S1G0G1S1S9SdSb7S7cA4GaA4S0G2S1G0G1S1S9SdSb6S7dA4GaA4S0G2S1G0G1S1S9SdSbcS7bA4S1S20S11Z1cS6cA4MbA4S0G2S1G0G1S1S9SdSbbS7cA4GbA4S0G2S1G0G1S1S9SdSa4S7bA4S1S20S11Z18S6cA4McA4S0G2S1G0G1S1S9SdSa3S7cA4GcA4S0G2S1G0G1S1S9SdSa7S7dA4GcA4S0G2S1G0G1S1S9SdSa8S7dA4GcA4S0G2S1G0G1S1S9SdSa5S96A4S1S20S11ZeS6cA4MdA4S0G2S1G0G1S1S9SdSa6S97A4GdA4S0G2S1G0G1S1S9SdSadSccA4S1S20S11ZaS6cA4MeA4S0G2S1G0G1S1S9SdSaeScdA4GeA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsL : list edescA := ltac2:(tb__ "0|e|
S0S5S5S9SdA2M0S5S20S11A2M1A2M2S1G0G1S1S9SdS4aS3bA4S1S20S11Z62S6cA4A4S0G2S1G0G1S1S9SdS60S8bA4S1S20S11Z5eS6cA4A4S0G2S1G0G1S1S9SdS4bS71A4S1S20S11Z50M3S6dS2aZ3bA2A4A4S0G2S1G0G1S1S9SdS49S71A4S1S20S11G3S6dS2aZ39A2A4A4S0G2S1G0G1S1S9SdS46S71A4S1S20S11G3S6dS2aZ37A2A4A4S0G2S1G0G1S1S9SdS4cS71A4S1S20S11G3S6dS2aZ34A2A4A4S0G2S1G0G1S1S9SdS48S75A4S1S20S11G3S6dS2aZ32A2A4M4A4S0G2S1G0G1S1S9SdS47S74A4G4A4S0G2S1G0G1S1S9SdS64S75A4S1S20S11G3S6dS2aZ30A2A4M5A4S0G2S1G0G1S1S9SdS63S74A4G5A4S0G2S1G0G1S1S9SdS62S75A4S1S20S11G3S6dS2aZ2eA2A4M6A4S0G2S1G0G1S1S9SdS61S74A4G6A4S0G2S1G0G1S1S9SdSc3S8cA4S1S20S11Z1cS6cA4M7A4S0G2S1G0G1S1S9SdSc4S8cA4G7A4S0G2S1G0G1S1S9SdSc1S82A4S1S20S11Z14S6cA4M8A4S0G2S1G0G1S1S9SdSc2S82A4G8A4S0G2S1G0G1S1S9SdSc5S89A4S1S20S11Z26S6cA4M9A4S0G2S1G0G1S1S9SdSafS89A4G9A4S0G2S1G0G1S1S9SdSb4S8aA4S1S20S11Z22S6cA4A4S0G2S1G0G1S1S9SdSb2S7bA4S1S20S11Z1eS6cA4MaA4S0G2S1G0G1S1S9SdSb1S7cA4GaA4S0G2S1G0G1S1S9SdSbeS7bA4S1S20S11Z1aS6cA4MbA4S0G2S1G0G1S1S9SdSbdS7cA4GbA4S0G2S1G0G1S1S9SdSbfS7dA4GbA4S0G2S1G0G1S1S9SdSc0S7dA4GbA4S0G2S1G0G1S1S9SdSc6S96A4S1S20S11ZcS6cA4McA4S0G2S1G0G1S1S9SdSc7S97A4GcA4S0G2S1G0G1S1S9SdS90S9aA4S1S20S11Z0S6cA4MdA4S0G2S1G0G1S1S9SdS91S9bA4GdA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
