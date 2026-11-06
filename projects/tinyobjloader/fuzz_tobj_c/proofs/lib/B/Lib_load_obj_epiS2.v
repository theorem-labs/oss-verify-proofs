(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "bool"; "pair"; "false"; "prod"; "app"; "andb"; "S"; "fst"; "list"; "negb"; "option"; "snd"; "true"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXSplit"; "apply_axforms"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "BIc"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "sobj"; "sv_eqb"; "SAlu"; "cell"; "ss_facts"; "ss_objs"; "mkObj"; "ob_base"; "ob_lo"; "ss_next"; "ss_pc"; "DUnknown"; "SPUle"; "c_off"; "c_width"; "mkCell"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "sprop"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "leafA"; "ax_setS"; "entailsA"; "la_reason"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "sel_front"; "s1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vF"; "vDp"; "NP"; "optL"; "optR"; "vOUT"; "idxB"; "idxC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "DUPk"; "DUPv"; "PreR"; "s_vf"; "s_w"; "spmZ"; "B_1"; "LR"; "bd_com"; "cAt"; "cps_b"; "dupAt"; "junk_s"; "kAt"; "set_objs"; "B32m"; "R_vf"; "R_w"; "Xk_vf"; "bdAt"; "bd_restS"; "bd_succP"; "drop368"; "gen_err"; "gen_out"; "iF2"; "iFv"; "iVec"; "iW"; "iWv"; "pc_cf"; "pc_rp"; "pc_vf0"; "pc_w"; "pcs_b"; "vERRq"; "wLen"; "wOff"; "xf_vf"; "xfb_vf"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "mul"; "of_nat"; "opp"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2.VF"; "Pre_vf"; "CHv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "leafL"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "bA"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "AK0"; "AV0"; "NDA"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_below"; "@Stdlib.Lists.List"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "junkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "drop_cell_at"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "EK"; "EV"; "cE"; "cps_s"; "kE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiS1.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VF. Include Lib_vec_finalize. End VF. Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP.

Definition pc_w : Z := 0x8e530.
Definition pc_cf : Z := 0x8eb08.
Definition pc_rp : Z := 0x8e558.
Definition pc_vf0 : Z := 0x8e564.
Definition pcs_b : list Z := ltac2:(tb__ "0|0|
S0S11Z8e5ccS0S11Z8e62cS0S11Z8e68cS0S11Z8e6ecS0S11Z8e74cS0S11Z8e7b0S2S11A1A3A3A3A3A3A3").
Definition cps_b : list Z := ltac2:(tb__ "0|0|
S0S11S71S0S11S6eS0S11S6fS0S11S70S7S11S72S9fA3A3A3A3A3").
Definition callL (B : axst) : axst := ltac2:(tb__ "0|0|
S85S86U12cS5aVB;A3Sa1U0A3").
Definition skipL (B : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S85S86U12cS5aVB;A3Vpc;Vk;A3").
Definition set_objs (A : axst) (os : list sobj) : axst := ltac2:(tb__ "0|0|
S3dVA;A1S3cS41VA;S32S2cR1A1S3aR1A1S38R1A1S37R1A1S3bR1A1Vos;S26R1A1S2bR1A1S39R1A1A9A2TS;").
Definition gen_out (A : axst) : axst := ltac2:(tb__ "0|1|
S5eVA;S7eS22S22S22S3S22L_;S8S23S29R1A1S4dA2S23S2aR1A1S1fZ0A1M0A2A2S28S4dG0S1fZd0A1S2S25A1S2dA5R1X3x2Lo;S27S3dVA;A1A1A4A2").
Definition vERRq : sv := SVar 461.
Definition gen_err (A : axst) : axst := ltac2:(tb__ "0|4|
S5eVA;S7eS22S22S22S3S22L_;S8S23S29R1A1M0S89A2S23S2aR1A1M1S1fZ60A1M2A2A2S28G0G1S35R1A1S7eS25S25S25S3S25L_;S23S2fR1A1M3G2A2S31G3S30R1A1S73A3R1X3x2Lc;S33R1A1A4S34R1A1A5R1X3x2Lo;S27S3dVA;A1A1A4A2").
Definition B32m : Z := 4294967295.
Definition bnds : list sprop := ltac2:(tb__ "0|0|
S7eS12S36S12S2eS21R1A1S1fS5fA1A2Lv;S0S12P191S0S12P197S0S12P19aS0S12P1a3S2S12A1A3A3A3A3A4").
Definition shp (Ls : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
S7eS40S6S11S8bA2S40S4S11S8bS2cS3dS44R1A1A1A1S43R1A1A4LL;VLs;A4").

Definition wK1 : Z := 236.  Definition wK2 : Z := 238.  Definition wOff : Z := 1888.  Definition wLen : Z := 12.
Definition xr_white : sv * sv := ltac2:(tb__ "0|0|
SacP6eS4S11S11S75S74A4A2").
Definition dropXr (r : sv * sv) (X : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S98S6S20S20A2M0G0ScS8S23SaS20S20R1A3SaS20S20Vr;A3A2S23SeS20S20R1A3SeS20S20Vr;A3A2A2A1Lq;VX;A3").

Definition Ls_succ : list leafA := Eval vm_compute in runL 300 cps_b K_succ.
Definition L_v0a : axst := Eval vm_compute in leafL Ls_succ pc_vf0 0.
Definition L_w : axst := Eval vm_compute in leafL Ls_succ pc_w 0.

Definition T_wr : axst := Eval vm_compute in shadow_reopen_stateA L_w (ax_X L_w) g5 wK1 wK2.
Definition Ls_wr : list leafA := Eval vm_compute in runL 300 cps_b T_wr.
Definition E_wm0 : axst := Eval vm_compute in leafL Ls_wr memcpy_pc 0.

Definition PreR : axst := Pre_memcpyR AE_A white_lo 12.
Definition LR : axst := L_memcpyR AE_A white_lo 12.
Definition E_wmr : axst := Eval vm_compute in shadow_release_stateA E_wm0 (objs_butlast E_wm0) 110 [(wOff, wLen)].
Definition xf_w (T : axst) : list axform := ltac2:(tb__ "0|2|
S45S48S1fZ6d8A1VT;A3S1S0S13S15R1S1fZ760M0A1A2S0S13S15S9R1A1M1S1fZ76cA1A2S0S13S14G1G0A2S2S13A1A3A3A3Tj;").
Definition E_wm : axst := Eval vm_compute in optL (apply_axforms E_wmr (xf_w E_wmr)).
Definition s_w (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S6S12S20A2M0S4S12S20P35S24S78S48S1fZ760A1A3A4S0G0S4S12S20P36S1fZcA1A4S0G0S4S12S20SadS49A4S81PaS3dVE;A1S3dS52A1A3A3A3A3").
Definition R_w (E : axst) : list sobj := ltac2:(tb__ "0|0|
S4cS82VE;S52S54VE;A1A3A1").
Definition w_ok (E : axst) : bool := ltac2:(tb__ "0|2|
SdSbS22A1M0A1S3Lx;S82VE;S52S54VE;A1M1A3G0S83VE;S52G1R1S0S3eS57S2S3eA1A3A5LR;S5Xdx2").
Definition T_wc (E : axst) : axst := ltac2:(tb__ "0|0|
SabS52VE;S54VE;A1S61VE;A1S57A5").

Definition xfb_w (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S13S18S45S24S78S48S1fZ760A1M0A3S1fZ0A1VT;A3A1S2S13A1M1A3SbS13A1S4bS16VT;R1A2A1S3eS7S13R2S0S13S46S0S1S45S48S1fZ6d8A1R1A3S0S1S45S48G0R1A3S0S1S45S48S1fZ76cA1R1A3S2S1A1A3A3A3S10S22S27S3dR1A1A1A2A2S0S13S17U0A1M2S0S13G2G1A3A3A3A3TT1;Tpre;").
Definition T_wm0 : axst := Eval vm_compute in T_wc E_wm.
Definition T_wmb : axst := Eval vm_compute in optL (apply_axforms T_wm0 (xfb_w T_wm0)).
Definition T_wm : axst := Eval vm_compute in ax_tidy T_wmb.
Definition Ls_wm : list leafA := Eval vm_compute in runL 300 cps_b T_wm.
Definition L_cf0 : axst := Eval vm_compute in leafL Ls_wm pc_cf 0.
Definition L_rp0 : axst := Eval vm_compute in leafL Ls_wm pc_rp 0.

Definition junk_s : list nat := ltac2:(tb__ "0|0|
S0S1U12S0S1U16S0S1U17S0S1U18S0S1U1bS2S1A1A3A3A3A3A3").
Definition junk_1 : list nat := ltac2:(tb__ "0|0|
S7S1S0S1U1S0S1U6S0S1U7S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS0S1U1dS0S1U1eS0S1U1fS2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5cA3").
Definition junk_b : list nat := ltac2:(tb__ "0|0|
S7S1S0S1U1S0S1U5S0S1U6S0S1U7S0S1UaS0S1UbS0S1UcS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS0S1U1dS0S1U1eS0S1U1fS2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5cA3").
Definition junk_c : list nat := (5 :: junk_1)%nat.

Definition drop368 (A : axst) : axst := ltac2:(tb__ "0|1|
S9aVA;S4fVA;S21PaA1N170M0A3G0A3").
Definition cnz : sprop := SPBranch BC_NE (SVar 416) (SLit 0).
Definition K_vf0 : axst := Eval vm_compute in ax_with_facts L_v0a (List.filter (fun f => negb (sprop_eqb f cnz)) (ss_facts (ax_S L_v0a))).
Definition B_1 : axst := Eval vm_compute in ax_add_facts bnds (drop368 (gen_err (gen_out (junkR junk_1 K_vf0)))).
Definition nextBj (jl : list nat) (L : axst) : axst := ltac2:(tb__ "0|0|
Sa6Sa7S66S67S68S99Vjl;VL;A2A1A1A1S26S3dS56A1A1A2S3fS56A1A2").

Definition K_rp : axst := Eval vm_compute in ax_setX (nextBj junk_1 L_rp0) (xr_white :: ax_X B_1).

Definition T_rp : axst := Eval vm_compute in shadow_reopen_stateA K_rp (ax_X B_1) g5 wK1 wK2.
Definition Ls_rp : list leafA := Eval vm_compute in runL 300 cps_b T_rp.
Definition L_rpx : axst := Eval vm_compute in leafL Ls_rp pc_vf0 0.
Definition L_rpc : axst := Eval vm_compute in shadow_release_stateA L_rpx (objs_butlast L_rpx) 110 [].

Definition iW (A : axst) : nat := ltac2:(tb__ "0|0|
S45S47S49VA;A3").
Definition xf_vf (A : axst) (off : Z) : list axform := ltac2:(tb__ "0|2|
S0S13S14S4eVA;S89Voff;A3Voff;A2S0S13S15S6cVA;A1M0S1fN60M1A1A2S0S13S15S9G0A1S1fN20A1A2S0S13S14G0G1A2S2S13A1A3A3A3A3").
Definition E_vf (E0 : axst) (off : Z) : axst := ltac2:(tb__ "0|0|
S4bS16VE0;S76VE0;Voff;A2A2A1").
Definition s_vf (E : axst) : wsub := ltac2:(tb__ "0|2|
S0S6S12S20A2M0S4S12S20PaM1Sa3S7aZ280Z20A2A1A4S0G0S4S12S20P13S24S78S49S1fZ60A1A3A4S81G1S3dVE;A1S3dS7fA1A3A3A3").
Definition R_vf (E : axst) : list sobj := ltac2:(tb__ "0|0|
S4cS82VE;S7fS53VE;A1A3A1").
Definition Xk_vf (E : axst) (d : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S98S6S20S20A2M0G0S8ScS23SaS20S20R1A3M1Sa2A2A1ScS23G1Vd;A2A1A2Lr;S3fVE;A1A3").
Definition hand_vf (E : axst) : list bitem := ltac2:(tb__ "0|0|
S1eS53VE;A1S80A2").
Definition PDk_vf : list pdescK := liftPD VFP.PD_vf.

Definition spmZ (k : Z) : sv := ltac2:(tb__ "0|0|
S24S78S21PaA1S1fS7dVk;A1A1A3").
Definition iWv (T : axst) : nat := ltac2:(tb__ "0|0|
S45S55Z2e0A1S24S78S49S1fZ60A1A3VT;A3").
Definition iFv (T : axst) : nat := ltac2:(tb__ "0|0|
S45S55Z2a0A1S1fN40A1VT;A3").
Definition iF2 (T : axst) : nat := ltac2:(tb__ "0|0|
S45S55Z2a0A1S1fZ0A1VT;A3").
Definition iVec (T : axst) (off : Z) : nat := ltac2:(tb__ "0|0|
S45S24S78S48S1fS7aZ1c0Voff;A2A1A3S1fZ0A1VT;A3").
Definition xfb_vf (T : axst) (off : Z) : list axform := ltac2:(tb__ "0|5|
S0S13S14S6dVT;A1M0Z60A2S0S13S14S6aVT;A1M1Z20M2A2S0S13S14S69VT;A1M3G2A2S0S13S14S6bVT;Voff;A2S7dVoff;A1A2S0S13S46S0S1G0S0S1G1S0S1G3S2S1A1A3A3A3S9bVT;A1A2S0S13S17U0A1M4S0S13G4S2S13A1A3A3A3A3A3A3A3").
Definition T_vf0 (E : axst) (d : sv) (P : axst) : axst := ltac2:(tb__ "0|0|
Sa9S7fVE;S53VE;A1S60VE;A1VP;S62VE;Vd;A2A6").
Definition T_vfB (T0 : axst) (off : Z) : axst := ltac2:(tb__ "0|0|
S4bS16VT0;S77VT0;Voff;A2A2A1").

Definition bd_restS : list bitem := Eval vm_compute in (firstn 10 bd_rest ++ skipn 12 (firstn 38 bd_rest)).
Definition acolVP : list bitem := Eval vm_compute in firstn 2 (skipn 10 bd_rest).
Definition DUPv (a b c d k : Z) : bitem := ltac2:(tb__ "0|1|
S1cZ1Z0S0S6S11S1aA2M0S4S11S1aVa;S1bS21P191A1A1A4S0G0S4S11S1aVb;S1bS21P197A1A1A4S0G0S4S11S1aVc;S1bS21P19aA1A1A4S0G0S4S11S1aVd;S1bS21P1a3A1A1A4S2G0A1A3A3A3A3Vk;A4").
Definition DUPk (a b c d k : Z) : bitem := ltac2:(tb__ "0|1|
S1cZ0Z1S0S6S11S1aA2M0S4S11S1aVa;S1bS21P191A1A1A4S0G0S4S11S1aVb;S1bS21P197A1A1A4S0G0S4S11S1aVc;S1bS21P19aA1A1A4S0G0S4S11S1aVd;S1bS21P1a3A1A1A4S2G0A1A3A3A3A3Vk;A4").
Definition bd_com (c k : Z) : list bitem := ltac2:(tb__ "0|0|
S0S19S9dVc;A1S0S19S9cVk;A1S64A3A3").
Definition kept_ad : list (sv * sv) := removelast tvL.

Definition dupAt (j : nat) : list bitem := ltac2:(tb__ "0|a|
S1SbS19A1M0Lj;Vj;S0S19S51Z0M1G1G1Z100M2Zc0A5S0S19S50G1G1G1Z200M3Z80A5S2S19A1M4A3A3M5S1S1G0Ln;R1S0S19S51Z38Z8M6Z18M7G2Z310A5S0S19S50Z70Z10M8Z30M9G3Z220A5G4A3A3S1S1G0Ln0;R1S0S19S51Z20G6G7G2Z2b0A5S0S19S50Z40G8G9G3Z1e0A5G4A3A3S1S1G0Ln1;R1S0S19S51G7G6G7G2Z250A5S0S19S50G9G8G9G3Z1a0A5G4A3A3S1S1G0Ln2;R1S0S19S51G7G1G7G2Z1f0A5S0S19S50G9G1G9G3Z160A5G4A3A3S1S1G0Ln3;R1S0S19S51G7G1G6G2Z190A5S0S19S50G9G1G8G3Z120A5G4A3A3S1S1G0Ln4;R1S0S19S51G7G1G1G2Z130A5S0S19S50G9G1G1G3Ze0A5G4A3A3S1G5Ln5;X1x2Ln4;X1x2Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2Ln;X1x2").
Definition cAt (j : nat) : Z := ltac2:(tb__ "0|0|
S79S79S79S9eZ362A2Z100A2S7bS7cS84Vj;U1A2A1S8eA2A2").
Definition kAt (j : nat) : Z := ltac2:(tb__ "0|0|
S79S79S79Sa0Z44A2Z200A2S7bS7cS84Vj;U1A2A1S8dA2A2").
Definition bdAt (j : nat) : list bitem := ltac2:(tb__ "0|0|
S7S19S58S59Vj;A1S5dVj;A1A2S5bVj;A1A3").
Definition ndAt (j : nat) : ndesc := ltac2:(tb__ "0|0|
S8fS88S87S63Vj;A1S8cS8aSfA2A4").
Definition brestAt (j : nat) : list bitem := ltac2:(tb__ "0|0|
S7S19S58S59Vj;A1S5dVj;A1A2S5bS9Vj;A1A1A3").
Definition ENDOWs : list bitem := ltac2:(tb__ "0|2|
S0S19S1dZ1M0Z0M1S8eA3S0S19S1dG1G0S8dA3S2S19A1A3A3").

Definition nd_rp : ndesc := ndAt 1.
Definition bd_succP : list bitem := bdAt 1 ++ acolVP.
Definition nd_succP : ndesc := ltac2:(tb__ "0|0|
S8fS88S87S65S8cS8aSfA2A4").

Definition ent_chk2 (L T : axst) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|3|
S81S4aS3dVL;A1M0S3dVT;A1A3Sa4S3S3L_;M1S42VL;VT;R1A3G1Sa5R1S4aA2G1SaeS4aS2bG0A1M2A2G1S97G2Vndi;A2G1Sa8R1S93Vndi;A1S93Vndj;A1A3G1S96R1S92Vndi;A1S92Vndj;A1A3G1SaaS26G0A1S1eR1S91Vndj;A1A2S91Vndi;A1A3S94S95R1S90Vndj;A1A2S90Vndi;A1A2S5X3x2S5X3x2S5X3x2S5X3x2S5X3x2S5X3x2S5X3x2Ts;").
