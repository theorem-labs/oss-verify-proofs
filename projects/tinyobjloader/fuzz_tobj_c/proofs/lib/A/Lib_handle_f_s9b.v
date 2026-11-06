(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "SAlu"; "sobj"; "SPUle"; "cell"; "@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "pair"; "prod"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "pL"; "lDsg"; "cSG"; "lKsg"; "cMM"; "XL"; "cFV"; "lDmm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "pKn4"; "pDf4"; "pDm4"; "pDn4"; "pKf4"; "pKm4"; "pKs4"; "cMI3"; "pDs4"; "LB"; "regsL4"; "LFX"; "fv4F"; "mi4F"; "sh28o"; "sh38o"; "fv2c"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "vec_facts0"; "V496"; "V528"; "V560"; "V592"; "optAp"; "pA"; "shB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "cFV1"; "E_mm4"; "E_sg4"; "F3"; "JMM4'"; "XL3"; "cMM1"; "mm4F"; "vr_ret_mm4"; "E_mm4_0"; "E_sg4_0"; "F4"; "JSG4"; "R_mm4"; "R_sg4"; "XL4"; "s_mm4"; "s_sg4"; "sg4F"; "vr_ret_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "NMM"; "NSG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition E_mm4_0 : axst := Eval vm_compute in leaf_at T_m4 vr_entry 0.
Definition E_mm4 : axst := Eval vm_compute in ax_add_facts (vr_need 4 (SAlu ALU_ADD (cMM pL) (SLit 1)) (NMM pA)) (optAp (apply_axforms E_mm4_0 (xf_vr 17 560))).
Definition s_mm4 : wsub := ltac2:(tb__ "0|1|
S7SbS27S2A2M0SaS27S2P3bS4cS2fA1A4S7G0SaS27S2P13S3S26S4eS1Z40A1A3A4S4fPaS47S32A1S47S46A1A3A3A3").
Definition R_mm4 : list sobj := Eval vm_compute in optR (entails_frA E_mm4 VN.Pre_vr s_mm4).
Goal entails_frA E_mm4 VN.Pre_vr s_mm4 = Some R_mm4 /\ call_checkPA E_mm4 VN.Pre_vr s_mm4 R_mm4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_mm4 : Z := 0x9fc80.
Definition cFV1 : sv := ltac2:(tb__ "0|0|
S3S26S13SdA1S1Z1A1A3").
Definition XL3 : list (sv * sv) := ltac2:(tb__ "0|0|
S12S17S16S18SeS1aS19S15S10A8").
Definition F3 : list sprop := ltac2:(tb__ "0|2|
S8S0S21S8S0S29S16S19Z4P174M0A4S8S0S22S8S0S29S17S1aZcP172M1A4S20SdS17S1cS1aG1S16S31S19G0S18S11SdA1S15P176SeSfSdA1S10P16eA11A3A3A3A3").
Definition mm4F : list sprop := ltac2:(tb__ "0|2|
S7S0S5S3S26S11SdA1M0S1Z1A1A3S15A2S7S0S5S1S53A1S18A2S7S0S5S3S26S45Z4M1G0A2S1G1A1A3S45G1S15A2A2S9S0A1A3A3A3").
Definition JMM4 (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S1eS49S1fS1S39A1Va0;A2S2aS17S1cS1aA3S2bS16S31S19A3S2cS18S11SdA1S15A3S2dSeSfSdA1S10A3S17S1aS16S19S18S15SeS10S25Vtail;Vfacts;VX;A12").

Definition JMM4' (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S1eS49S8SbScS2A2M0S1fS1S39A1Va0;A2S7G0SaScS2U15S30Z47A1A4S9G0A1A3A3S2aS17S1cS1aA3S2bS16S31S19A3S2cS18S11SdA1S15A3S2dSeSfSdA1S10A3S17S1aS16S19S18S15SeS10S9S6A1Vtail;Vfacts;VX;A12").
Definition JR_mm4 : axst := ltac2:(tb__ "0|2|
S35S1Z1A1S9S4A1S8S0S38S34A3S7SbS2S2A2M0S52Pa0M1SaS28S28Z130Z4A4A2S7G0S52G1SaS28S28Ze0Z24A4A2S36A3A3A4").
Definition JF_mm4 : axst := ltac2:(tb__ "0|0|
S35S1Z0A1S7S4S23S7S4S24S9S4A1A3A3S34S36A4").
Definition contMM4 (P : axst) : axst := ltac2:(tb__ "0|0|
S2eS50S51S46S32S41S3eVP;S4aS14S48S3aA1A2A6S4bU10U1eZ230A3A2A1").
Definition T_mm4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDmm] (contMM4 VN.P_keep).
Definition T_mm4f : axst := Eval vm_compute in contMM4 VN.P_fail.
Definition T_mm4g : axst := Eval vm_compute in contMM4 VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_mm4) [T_mm4k; T_mm4g] = [true; true] /\ leaf_matches1A NPH (reopen2n T_mm4f) JF_mm4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_mm4 = [(vr_entry, RsCut)] /\ lvs JF_mm4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_sg4_0 : axst := Eval vm_compute in leaf_at JR_mm4 vr_entry 0.
Definition E_sg4 : axst := Eval vm_compute in ax_add_facts (vr_need 4 (SAlu ALU_ADD (cSG pL) (SLit 1)) (NSG pA)) (optAp (apply_axforms E_sg4_0 (xf_vr 18 592))).
Definition s_sg4 : wsub := ltac2:(tb__ "0|1|
S7SbS27S2A2M0SaS27S2P3bS4dS2fA1A4S7G0SaS27S2P13S3S26S4eS1Z40A1A3A4S4fPaS47S33A1S47S46A1A3A3A3").
Definition R_sg4 : list sobj := Eval vm_compute in optR (entails_frA E_sg4 VN.Pre_vr s_sg4).
Goal entails_frA E_sg4 VN.Pre_vr s_sg4 = Some R_sg4 /\ call_checkPA E_sg4 VN.Pre_vr s_sg4 R_sg4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_sg4 : Z := 0x9fd8c.
Definition cMM1 : sv := ltac2:(tb__ "0|0|
S3S26S11SdA1S1Z1A1A3").
Definition XL4 : list (sv * sv) := ltac2:(tb__ "0|0|
S12S17S16S18S1dS1aS19S15S1bA8").
Definition F4 : list sprop := ltac2:(tb__ "0|4|
S8S0S38S8S0S29S18S15Z4M0P176M1A4S8S0S21S8S0S29S16S19G0P174M2A4S8S0S22S8S0S29S17S1aZcP172M3A4S20SdS17S1cS1aG3S16S31S19G2S18S37S15G1S1dSfSdA1S1bP178A11A3A3A3A3A3A3").
Definition sg4F : list sprop := ltac2:(tb__ "0|2|
S7S0S5S3S26SfSdA1M0S1Z1A1A3S1bA2S7S0S5S1S53A1S1dA2S7S0S5S3S26S45Z4M1G0A2S1G1A1A3S45G1S1bA2A2S9S0A1A3A3A3").
Definition JSG4 (a0 : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S1eS49S8SbScS2A2M0S1fS1S44A1Va0;A2S7G0SaScS2U15S30Z4bA1A4S9G0A1A3A3S2aS17S1cS1aA3S2bS16S31S19A3S2cS18S37S15A3S2dS1dSfSdA1S1bA3S17S1aS16S19S18S15S1dS1bS9S6A1S7S4S23S7S4S24S9S4A1A3A3Vfacts;S40A12").
Definition JR_sg4 : axst := ltac2:(tb__ "0|0|
S3dS1Z1A1S8S0S43S3cA3A2").
Definition JF_sg4 : axst := JSG4 (SLit 0) F4.
Definition contSG4 (P : axst) : axst := ltac2:(tb__ "0|0|
S2eS50S51S46S33S42S3fVP;S4aSeS48S3bA1A2A6S4bU11U1fZ250A3A2A1").
Definition T_sg4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDsg] (contSG4 VN.P_keep).
Definition T_sg4f : axst := Eval vm_compute in contSG4 VN.P_fail.
Definition T_sg4g : axst := Eval vm_compute in contSG4 VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_sg4) [reopen2n T_sg4k; reopen2n T_sg4g] = [true; true] /\ leaf_matches1A NPH (reopen2n T_sg4f) JF_sg4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal lvs JR_sg4 = [(hf_L14, RsCut); (hf_EPI, RsCut)] /\ lvs JF_sg4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal map (fun L => leaf_matches1A NPH L L14) (leavesA_at FUEL_hf cutpcs_hf JR_sg4 hf_L14) = [true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

