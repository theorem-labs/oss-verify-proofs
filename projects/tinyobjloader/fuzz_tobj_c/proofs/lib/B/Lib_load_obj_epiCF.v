(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "bool"; "true"; "app"; "andb"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "SPUle"; "SAlu"; "SMd"; "cell"; "sobj"; "sv_eqb"; "SPBranch"; "SVar"; "ss_objs"; "ss_pc"; "SPNot"; "SPUlt"; "c_off"; "c_width"; "mkCell"; "mkObj"; "mkSS"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "ALU_ADD"; "ALU_SUB"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_reason"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "vNV"; "fact_nv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "ND"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF"; "cbI"; "k_ac"; "Nt"; "Wt"; "d_ac"; "tv_vr"; "vI"; "vcfB"; "PD_vr"; "bd_grown"; "bd_vr"; "brest_vr"; "cntI"; "iWc"; "kept_vr"; "nv_pos"; "pc_bl"; "pc_blx"; "slot_facts"; "tv_grown"; "vDg"; "vJ"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "bA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "s1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "list_set"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiCF.VRN"; "B32"; "B_EW"; "P_fail"; "P_grown"; "P_keep"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "B32m"; "cps_b"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiS1 Lib_load_obj_epiS2.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VRN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN. End VRN.

Definition vr_pc : Z := 0x949d4.
Definition pc_bl : Z := 0x8eb70.
Definition pc_blx : Z := 0x8ebd0.
Definition cps_cf : list Z := ltac2:(tb__ "0|0|
S0S30S55S0S30S56S74A3A3").
Definition nI : positive := Eval vm_compute in ss_next (ax_S L_cf0).
Definition vI : sv := SVar nI.
Definition cntI : sv := SMd M_MUL (SLit 3) vI.
Definition Wt : sv := SAlu ALU_ADD cntI (SLit 3).
Definition Nt : sv := ltac2:(tb__ "0|0|
SeS32SfS31SaZ3A1S3cA3SaZ2A1A3").
Definition cbI : sv := SMd M_MUL cntI (SLit 4).
Definition d_ac : sv := SVar 415.  Definition k_ac : sv := SVar 417.

Definition vcfB : sv := ltac2:(tb__ "0|0|
SfS31SaZ20A1SeS33S3cS4bA3A3").
Definition vcf (k : Z) : sv := ltac2:(tb__ "0|0|
SeS32S4cSaVk;A1A3").
Definition pcsOf (Ls : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
S42S38S4S30S61A2S38S3S30S61S16S37S3bR1A1A1A1S3aR1A1A4LL;VLs;A4").

Definition set_reg_next (A : axst) (r : nat) (v : sv) (nx : positive) : axst := ltac2:(tb__ "0|0|
S37VA;A1S29S39VA;S1dS16R1A1S62ScS27R1A1Vr;Vv;A4S25R1A1S24R1A1S28R1A1S15R1A1S23R1A1Vnx;S26R1A1A9A2TS;").
Definition set_cnt (A : axst) (c : sv) : axst := ltac2:(tb__ "0|3|
S75VA;S42S11S11S11S5S11L_;S8S12S1eR1A1M0S5eA2S12S22R1A1M1SaZ118A1A2A2S1cG0G1S21R1A1S42S10S10S10S5S10L_;S12S19R1A1M2SaZ120A1A2S1bG2S1aR1A1Vc;A3R1X5x2Lcl;S1fR1A1A4S20R1A1A5R1X5x2Lo;S15S37VA;A1A1A4A2").

Definition nv_pos : sprop := SPUlt (SLit 0) vNV.
Definition nv_src : sprop := ltac2:(tb__ "0|1|
S13S34SfS31S3cSaZ3A1M0A3G0A3").
Definition ent_facts : list sprop := ltac2:(tb__ "0|0|
S0SbS3dS0SbS54S2SbA1A3A3").
Definition L_cfE : axst := Eval vm_compute in ax_add_facts ent_facts L_cf0.
Definition inv_cf : list sprop := ltac2:(tb__ "0|0|
S0SbS18S4bS3cA2S0SbSdS51S46A2S2SbA1A3A3").

Definition junk_cf : list nat := ltac2:(tb__ "0|0|
S0S1U1S0S1U6S0S1U7S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS0S1U1dS0S1U1eS0S1U1fS2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_cf : axst := Eval vm_compute in junkR junk_cf (ax_add_facts inv_cf (dropV [416]%positive (set_cnt (set_reg_next L_cfE 22 vI (Pos.succ nI)) cntI))).

Definition cnt0_src : sprop := ltac2:(tb__ "0|0|
S17S13S35S14P1a0A1SaZ0A1A3A1").
Definition L_cfZ : axst := Eval vm_compute in set_cnt L_cfE (SLit 0).
Definition s_ent : wsub := Eval vm_compute in infer_sub NP (ax_S L_cfZ) (ax_S C_cf).

Definition Ls_c : list leafA := Eval vm_compute in runL 600 cps_cf C_cf.
Definition E_c0 : axst := Eval vm_compute in leafL Ls_c vr_pc 0.

Definition iWc (A : axst) : nat := ltac2:(tb__ "0|0|
S5fS60S66VA;A3").
Definition xf_vr (T : axst) : list axform := ltac2:(tb__ "0|4|
S0S2aS2eS52VT;A1M0SaN40M1A1A2S0S2aS2bG0G1A2S2S2aA1M2A3A3S9S2aA1S65S2fVT;R1A2A1S36S7S2aR2S0S2aS2bS5fS5eSaZ118M3A1R1A3G3A2G2A3A3TT1;Tpre;").
Definition room_vr : list sprop := ltac2:(tb__ "0|2|
S0SbSdSfS31SaZ4A1M0S48A3M1SfS31G0S47A3A2S0SbSdG1SaS68A1A2S0SbSdS48S47A2S2SbA1A3A3A3").
Definition E_c1 : axst := Eval vm_compute in optL (apply_axforms E_c0 (xf_vr E_c0)).
Definition E_c : axst := Eval vm_compute in ax_add_facts room_vr E_c1.
Definition s_c : wsub := Eval vm_compute in (h0, pH) :: (19%positive, SAlu ALU_ADD vDp (SLit 64)) :: (59%positive, Nt) :: infer_sub 10 (ax_S E_c) (ax_S VRN.Pre_vr).
Definition R_c : list sobj := Eval vm_compute in optR (entails_frA E_c VRN.Pre_vr s_c).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S36S3eA2M0S3S36S3eS6bS6dA4S0G0S3S36S3eS69S41S6eS2S4S4ScS30A2ScA2A1M1S2S76A1A3A4S0G0S3S36S3eS6aS41S6fG1S6cS71S70A2A3A4S2G0A1A3A3A3").
Definition PDk_vr : list pdescK := ltac2:(tb__ "0|0|
S78S77S4dS64S6A3A1").

Definition passed_vr : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S3ScScS49S44Z4S46A2A4S2G0A1A3").
Definition kept_vr : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (sv_eqb (fst t) d_ac)) tvL.
Definition tv_vr : list (sv * sv) := kept_vr ++ passed_vr.
Definition bd_cf : list bitem := Eval vm_compute in nd_bd nd_succ.
Definition hand_vr : list bitem := Eval vm_compute in bd_subst s_c (nd_bd (ndh h0 true VRN.nd0)).
Definition brest_vr : list bitem := Eval vm_compute in (firstn 12 bd_cf ++ skipn 14 bd_cf).
Definition bd_vr : list bitem := hand_vr ++ brest_vr.
Definition Xk_vr : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_ac)) (ax_X E_c).
Definition nd_cf : ndesc := ltac2:(tb__ "0|0|
S40S4aS5cS4fS3fS5dS6A2A4").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S40S4aS5cS50S3fS5dS6A2A4").

Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_keep Xk_vr.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_grown Xk_vr.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_fail Xk_vr.
Definition isub_grown : wsub := Eval vm_compute in import_subA s_c VRN.Pre_vr VRN.P_grown E_c.
Definition vDg : sv := Eval vm_compute in sv_subst isub_grown VRN.vDn.
Definition vKg : sv := Eval vm_compute in sv_subst isub_grown VRN.vKn.
Definition tv_grown : list (sv * sv) := ltac2:(tb__ "0|1|
S7S4ScScA2M0S53S0G0S3ScScS59S44Z4S5bA2A4S2G0A1A3A3").
Definition bd_grown : list bitem := Eval vm_compute in (bd_subst isub_grown (VRN.bdP VRN.vN VRN.vKn) ++ brest_vr).
Definition nd_grown : ndesc := ltac2:(tb__ "0|0|
S40S58S5cS4eS3fS5dS6A2A4").

Definition xfb_vr (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S2aS2bU1M0Z40A2S0S2aS2bU2M1N118A2S0S2aS2dS0S1G0S0S1U0M2S43G1S63S72VT;A1G1A2A2A3A3A1S0S2aS2cG2A1S2S2aA1A3A3A3A3").
Definition B_keep : axst := Eval vm_compute in optL (apply_axforms T_keep0 (xfb_vr T_keep0)).
Definition B_grown : axst := Eval vm_compute in optL (apply_axforms T_grown0 (xfb_vr T_grown0)).
Definition B_fail : axst := Eval vm_compute in optL (apply_axforms T_fail0 (xfb_vr T_fail0)).
Definition T_keep : axst := Eval vm_compute in ax_tidy B_keep.
Definition T_grown : axst := Eval vm_compute in ax_tidy B_grown.
Definition T_fail : axst := Eval vm_compute in ax_tidy B_fail.

Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S0SbSdSeS32S45SaZcA1A3S44Z4Vk;A2M0A2S0SbSdS45G0A2S0SbSdS45SaS67A1A2S2SbA1A3A3A3").
Definition inj_keep : list sprop := ltac2:(tb__ "0|0|
S7SbS57S46A1S0SbSdSaS79A1S49A2S2SbA1A3A3").
Definition inj_grown : list sprop := slot_facts vKg.
Definition T_keepS : axst := Eval vm_compute in ax_add_facts inj_keep T_keep.
Definition T_grownS : axst := Eval vm_compute in ax_add_facts inj_grown T_grown.
Definition K_w : axst := T_keepS.
Definition s_gk : wsub := Eval vm_compute in infer_sub NP (ax_S T_grownS) (ax_S K_w).

Definition junk_bl : list nat := ltac2:(tb__ "0|0|
S0S1UaS0S1UbS0S1U10S0S1U11S2S1A1A3A3A3A3").
Definition Ls_w : list leafA := Eval vm_compute in runL 600 cps_cf K_w.
Definition L_bl : axst := Eval vm_compute in leafL Ls_w pc_bl 0.
Definition C_bl : axst := Eval vm_compute in bl_cut L_bl 13 (SLit 12) junk_bl [].
Definition vJ : sv := Eval vm_compute in SVar (bl_vi L_bl).
Definition v_bl : sv := ltac2:(tb__ "0|0|
SeS32S4cSeS33SaZ1cA1S5aA3A3").
Definition Ls_b : list leafA := Eval vm_compute in runL 600 cps_cf C_bl.
Definition X_bl0 : axst := Eval vm_compute in bl_junk (leafL Ls_b pc_blx 0) junk_bl.

Definition X_bl : axst := Eval vm_compute in bl_prune (bl_vi L_bl) (bl_forget X_bl0 [oidx d_ac (SLit 0) X_bl0; oidx vF (SLit 1752) X_bl0]).

Definition Ls_x : list leafA := Eval vm_compute in runL 600 cps_cf X_bl.
Definition L_bk : axst := Eval vm_compute in leafL Ls_x pc_cf 0.
Definition L_x : axst := Eval vm_compute in leafL Ls_x pc_rp 0.
Definition Ls_f : list leafA := Eval vm_compute in runL 600 cps_cf T_fail.
Definition Lf0 : axst := Eval vm_compute in leafL Ls_f pc_rp 0.
Definition Lf1 : axst := Eval vm_compute in leafL Ls_f pc_rp 1.
Definition s_bk : wsub := Eval vm_compute in infer_sub NP (ax_S L_bk) (ax_S C_cf).

Definition bnd_nt : sprop := ltac2:(tb__ "0|0|
SdS14P19aA1SaS73A1A2").
Definition L_xF : axst := Eval vm_compute in ax_add_facts [bnd_nt] L_x.
Definition Lf0F : axst := Eval vm_compute in ax_add_facts [bnd_nt] Lf0.
Definition Lf1F : axst := Eval vm_compute in ax_add_facts [bnd_nt] Lf1.
