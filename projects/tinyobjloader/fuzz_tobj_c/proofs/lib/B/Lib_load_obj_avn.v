(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "nil"; "true"; "length"; "list"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "SMd"; "SPUle"; "sobj"; "ss_objs"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "X_latch"; "X_latchE"; "cps_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "LA"; "V_B"; "V_L"; "tblB"; "tblL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "tv_vn"; "E_vn"; "T_vn_f"; "T_vn_ok"; "bd_vn_ok"; "bdrest_vn"; "brest_vn"; "c_avn"; "d_avn"; "k_avn"; "ndXE_vn"; "ndX_vn"; "nd_vn_f"; "nd_vn_ok"; "tv_vn_f"; "tv_vn_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "AK1"; "LAK"; "LAX"; "LAXK"; "bdX"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf"; "PD_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn.HVN"; "Pre_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module HVN. Include Lib_handle_vn. End HVN.

Definition c_avn : sv := t_c (v_avn vsP).  Definition d_avn : sv := t_d (v_avn vsP).  Definition k_avn : sv := t_k (v_avn vsP).

Definition room_vn : sprop := ltac2:(tb__ "0|0|
SdScS2bSaZ4A1SbS2aS34SaZ3A1A3A3SaS4eA1A2").

Definition xf_vn : list axform := ltac2:(tb__ "0|2|
S0S11S15U7M0SaN80M1A1A2S0S11S12G0G1A2S4S11A1A3A3").
Definition E_vn : axst := Eval vm_compute in ax_add_facts [room_vn] (optL (apply_axforms E_hvn xf_vn)).

Definition h0 : positive := 99%positive.
Definition s_vn : wsub := ltac2:(tb__ "0|1|
S0S2S18S9A2M0S1S18S9S2cS1eA4S0G0S1S18S9P13SbS2aS4bSaZ80A1A3A4S4fPaS1aS2eA1S1aS49A1A3A3A3").
Definition R_vn : list sobj := Eval vm_compute in optR (entails_frA E_vn HVN.Pre_hvn s_vn).

Definition PDk_vn : list pdescK := ltac2:(tb__ "0|0|
S51S50S48S2cS5A3A1").

Definition passed_vn : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S9S9A2M0S1S9S9S35S47Z4S36A2A4S4G0A1A3").
Definition kept_vn : list (sv * sv) := Eval vm_compute in (firstn 2 tvL ++ skipn 3 tvL).
Definition tv_vn : list (sv * sv) := kept_vn ++ passed_vn.

Definition bdrest_vn : list bitem := Eval vm_compute in (firstn 4 bd_rest ++ skipn 6 bd_rest).
Definition brest_vn : list bitem := ltac2:(tb__ "0|0|
S0S22S25S54S24Z48A2A1S0S22S41S40A1S32A3A3").
Definition hand_vn : list bitem := Eval vm_compute in bd_subst s_vn (HVN.bd_hvn vNC vNK).

Definition bd_vn : list bitem := Eval vm_compute in (firstn 2 (skipn 4 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_vn).

Definition Xk_vn : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_avn)) (ax_X E_vn).

Goal entails_frA E_vn HVN.Pre_hvn s_vn = Some R_vn /\ call_checkPA E_vn HVN.Pre_hvn s_vn R_vn (map (fun d => fst (fst d)) PDk_vn) = true
  /\ call_checkTA NP s_vn = true /\ wsub_dom_below s_vn NF = true
  /\ TobjJV.tv_sub_eqb s_vn passed_vn (nd_tv (ndh h0 true HVN.nd0)) = true
  /\ am_eqb (am_subst s_vn (nd_am (ndh h0 true HVN.nd0))) (AHead pH true) = true
  /\ forallb (fun d => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pd_okA HVN.Pre_hvn NF s_vn (ss_next (ax_S E_vn)) (fst d)) PDk_vn = true
  /\ tv_permb tvL tv_vn = true /\ bd_permb (bdA A1) bd_vn = true
  /\ xrs_inclb Xk_vn (ax_X E_vn) = true
  /\ bd_subst s_vn (nd_bd (ndh h0 true HVN.nd0)) = hand_vn
  /\ bud_pay2 (ss_facts (ax_S E_vn)) (SLit 0) 0 bd_vn (hand_vn ++ brest_vn) = true
  /\ nd_below (ss_next (ax_S E_vn)) (NDA tv_vn frL bd_vn (AHead pH true)) = true /\ bd_below (ss_next (ax_S E_vn)) brest_vn = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_vn_ok0 : axst := Eval vm_compute in T_afterA3 HVN.Pre_hvn E_vn s_vn R_vn HVN.P_ok Xk_vn.
Definition T_vn_f0 : axst := Eval vm_compute in T_afterA3 HVN.Pre_hvn E_vn s_vn R_vn HVN.P_fail Xk_vn.

Definition isub_ok : wsub := Eval vm_compute in import_subA s_vn HVN.Pre_hvn HVN.P_ok E_vn.
Definition isub_f : wsub := Eval vm_compute in import_subA s_vn HVN.Pre_hvn HVN.P_fail E_vn.
Definition tv_vn_ok : list (sv * sv) := Eval vm_compute in (kept_vn ++ import_tv isub_ok (nd_tv HVN.nd_ok)).
Definition bd_vn_ok : list bitem := Eval vm_compute in (bd_subst isub_ok (nd_bd HVN.nd_ok) ++ brest_vn).
Definition tv_vn_f : list (sv * sv) := Eval vm_compute in (kept_vn ++ import_tv isub_f (nd_tv HVN.nd_fail)).
Definition nd_vn_ok : ndesc := ltac2:(tb__ "0|0|
S1dS3cS23S31S1cS1eS5A2A4").
Definition nd_vn_f : ndesc := ltac2:(tb__ "0|0|
S1dS3bS23S33S1cS1eS5A2A4").
Goal am_subst isub_ok (nd_am (ndh h0 true HVN.nd_ok)) = AHead pH true /\ am_subst isub_f (nd_am (ndh h0 true HVN.nd_fail)) = AHead pH true
  /\ bd_subst isub_f (nd_bd HVN.nd_fail) = [] /\ tv_vn_f = tv_vn.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vn_back (T : axst) : axst := ltac2:(tb__ "0|2|
S4dS4aS16VT;S0S11S12U0M0Z80A2S0S11S14S0S3G0S0S3U3S0S3U1S0S3U2S46U4M1S45S6SeSfS1aVT;A1A1A2G1A2A2A3A3A3A3A1S0S11S13G0A1S4S11A1A3A3A3A2A1A1").
Definition T_vn_ok : axst := Eval vm_compute in vn_back T_vn_ok0.
Definition T_vn_f : axst := Eval vm_compute in vn_back T_vn_f0.

Definition cps_arm : list Z := ltac2:(tb__ "0|0|
S52S17S17S8S53R1S4cA2A1Lp;S21A3").

Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S0S2S7S18A1M0S10OFrho;M1A2M2S1G0G1S27S29A4S0G2S1G0G1S26S28A4S4G2A1A3A3").

Definition ndX_vn : ndesc := ltac2:(tb__ "0|0|
S1dS2dS23S44Z0A1S1cS1eS5A2A4").
Definition ndXE_vn : ndesc := ltac2:(tb__ "0|1|
S1dS2dS23S0S22S42Z0M0A1S0S22S43G0A1S4S22A1A3A3S1cS1eS5A2A4").
Definition cutsV : list efnode := ltac2:(tb__ "0|6|
S0S2S2S2S19S1bA2M0S3A2M1S2S17S9A2M2A2M3S1G1G2S1G0S3S1S19S1bS30S3aA4U1M4A4S1S17S9S3dS3eZaS3fA2A4M5A4S0G3S1G1G2S1G0S3S1S19S1bS2fS39A4G4A4G5A4S4G3A1A3A3").
Definition exitsV : list efnode := ltac2:(tb__ "0|6|
S0S2S2S2S19S1bA2M0S3A2M1S2S17S9A2M2A2M3S1G1G2S1G0S3S1S19S1bS1fS38A4U1M4A4S1S17S9S3dS3eZ1S3fA2A4M5A4S0G3S1G1G2S1G0S3S1S19S1bS20S37A4G4A4G5A4S4G3A1A3A3").

