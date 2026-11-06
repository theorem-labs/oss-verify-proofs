(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "app"; "nil"; "prod"; "bool"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "SPUle"; "sobj"; "DUnknown"; "cell"; "mkObj"; "SPBranch"; "SPNot"; "SPUlt"; "mkCell"; "ss_regs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "pL"; "lDmm"; "lDsg"; "lKmm"; "lKsg"; "cFV"; "lDfv"; "cMI"; "cMM"; "cSG"; "lKfv"; "XL"; "FCUT3"; "F_L14"; "datasL"; "lDmi"; "regsLs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "pKm4"; "pDm4"; "pKf4"; "pDf4"; "XnoLoc"; "a0_of"; "E_fv4"; "E_mi4"; "F1"; "F2"; "JFV4"; "JMI4"; "LB"; "LFX"; "XL1"; "XL2"; "cMI3"; "fv2c"; "mi4F"; "offd_of"; "regsL4"; "sh28o"; "sh38o"; "E_c4"; "E_fv4_0"; "E_m4"; "E_mi4_1"; "R_fv4"; "R_mi4"; "fv4F"; "reopen28n"; "s_fv4"; "s_mi4"; "vr_ret_fv4"; "vr_ret_mi4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hG"; "vec_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "BC_EQ"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xlocal"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "pNT"; "qDrp'"; "qDts'"; "qKrp'"; "qKts'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "optAp"; "reshapeA"; "xfo"; "pA"; "vec_facts0"; "V496"; "V528"; "V560"; "V592"; "V752e"; "V784"; "V816"; "am2"; "pKco"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pKtr"; "pDtr"; "hint12"; "trK"; "tr_facts"; "triF"; "@Corelib.Lists.ListDef"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "Pre_mc"; "XkeepF"; "xf_backV"; "NFV"; "NMI"; "coP"; "co_live"; "pX"; "sel_backV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "xr_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pDm4 : sv := SVar 370. Definition pKm4 : sv := SVar 371. Definition pDf4 : sv := SVar 372. Definition pKf4 : sv := SVar 373.
Definition pDn4 : sv := SVar 374. Definition pKn4 : sv := SVar 375. Definition pDs4 : sv := SVar 376. Definition pKs4 : sv := SVar 377.

Definition LFX (t dmi cmi kmi : sv) (ami : positive) (dfv cfv kfv : sv) (afv : positive) (dmm cmm kmm : sv) (amm : positive) (dsg csg ksg : sv) (asg : positive) : list sprop := ltac2:(tb__ "0|2|
S3SbS0SbS14Vt;S61A2S0SbSdS61S73A2S0SbS13S12S59S61SaZ0A1A3A1S0SbS79Vt;A1S0SbSdS54ZcM0S61A2S54Z4M1S77A2A2S0SbSdS54G0S6aA2S54G0S74A2A2S0SbS85S4SbA1A3A3A3A3A3A3A3S3SbS56Vdmi;Vcmi;Vkmi;G0Vami;A5S3SbS56Vdfv;Vcfv;Vkfv;G1Vafv;A5S3SbS56Vdmm;Vcmm;Vkmm;G1Vamm;A5S3SbS56Vdsg;Vcsg;Vksg;G1Vasg;A5S3SbS7bS78S77P157A3S3SbS6bS62S64G1P160A4S3SbS6bS63S65Z1P162A4S7cA3A3A3A3A3A3A3A3").

Definition regsL4 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S3S5S1S9A2M0S2aS0G0S2S1S9U1Vra;A4S0G0S2S1S9UaVa0;A4S0G0S2S1S9U12S1aA4S4G0A1A3A3A3A3").
Definition sh38c : sobj := ltac2:(tb__ "0|1|
S60S55Z26M0Z27S0S10S15SaS8fS8dG0A2A1Z1SaZ4A1A3S4S10A1A3SfA5").
Definition sh28o : sobj := shobj hG 28 33 [] DUnknown.
Definition sh38o : sobj := shobj hG 38 39 [] DUnknown.
Definition fv2c : list cell := [c4 304 (SLit 3)].

Definition LB (pc : Z) (regs : list (nat * sv)) (mi fv mm sg : sobj) (dmi kmi dfv kfv dmm kmm dsg ksg : sv) (fcells : list cell) (tail : list sobj)
              (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S26Vpc;Vregs;S86S84S70S62S64A2S71S78SaZ0A1S77A3Vmi;Vfv;Vmm;Vsg;S72S63S65A2S27Vfcells;S28Vdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;S7aS61A1A9Vtail;Vfacts;VX;A11").
Definition a0_of (E : axst) : sv := ltac2:(tb__ "0|0|
S7eS9UaS16S5bVE;A1A1SaZ0A1A4").
Definition offd_of (E : axst) : sv := ltac2:(tb__ "0|3|
S9S9Lx;S36VE;A1S18SaZ0A1M0Lz;S17G0Li;S58S9S9S58S9Lop;R3R1G0G0G0G0G0G0G0G0G0X58xaLo;La;Lop;S58S9S9G0Lb;La;M1Lop;S5aG1Lop;M2G2S6S19S9G0La;Lw;Lsgn;S17S9S18G0Lk;Li;Ll;X9x8").

Definition xf_backL (vi di : nat) (off : Z) : list axform := ltac2:(tb__ "0|0|
S0S2bS2eU1Z40A2S0S2bS30S3S1S87Vvi;Vdi;A2S0S1U25S4S1A1A3A3A1S0S2bS2fU0A1S0S2bS2eVvi;S90Voff;A1A2S4S2bA1A3A3A3A3").

Definition E_mi4_0 : axst := Eval vm_compute in leaf_at T_g3 vr_entry 0.

Goal local_ok (ob_cells (sh_last E_mi4_0)) DUnknown 38 39 (304, 4) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_mi4_1 : axst := Eval vm_compute in shadow_release_stateA E_mi4_0 (objs_butlast E_mi4_0) 160 [(304, 4)].
Definition E_mi4 : axst := Eval vm_compute in ax_add_facts (vr_need 12 (SAlu ALU_ADD (cMI pL) (SLit 3)) (NMI pA)) (optAp (apply_axforms E_mi4_1 (xf_vr 15 496))).
Definition s_mi4 : wsub := ltac2:(tb__ "0|1|
S0S5S17S9A2M0S2S17S9P3bS83S6aA1A4S0G0S2S17S9P13ScS57S75SaZ40A1A3A4S76PaS5bS38A1S5bS66A1A3A3A3").
Definition R_mi4 : list sobj := Eval vm_compute in optR (entails_frA E_mi4 VN.Pre_vr s_mi4).
Goal entails_frA E_mi4 VN.Pre_vr s_mi4 = Some R_mi4 /\ call_checkPA E_mi4 VN.Pre_vr s_mi4 R_mi4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_mi4 : Z := 0x9fb0c.
Definition XL1 : list (sv * sv) := ltac2:(tb__ "0|0|
S25S32S20S1bS1cS31S24S1dS1eA8").
Definition F1 : list sprop := ltac2:(tb__ "0|0|
S3eS1aS32S21S1aA1S31P172S20S1fS1aA1S24P16aS1bS22S1aA1S1dP16cS1cS23S1aA1S1eP16eA11").
Definition mi4F : list sprop := ltac2:(tb__ "0|2|
S0SbSdScS57S21S1aA1M0SaZ3A1A3S31A2S0SbSdSaS8bA1S32A2S0SbSdScS57S54ZcM1G0A2SaZ24A1A3S54G1S31A2A2S4SbA1A3A3A3").
Definition JMI4 (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S3dS88S45SaS53A1Va0;A2S6cS32S21S1aA1S31A3S6dS20S1fS1aA1S24A3S6eS1bS22S1aA1S1dA3S6fS1cS23S1aA1S1eA3S32S31S20S24S1bS1dS1cS1eS42Vtail;Vfacts;VX;A12").
Definition JR_mi4 : axst := ltac2:(tb__ "0|2|
S3cSaZ1A1S4SeA1S3SbS43S39A3S0S5S9S9A2M0S5ePa0M1S2S18S18Z130Z4A4A2S0G0S5eG1S2S18S18Ze0Z24A4A2S3fA3A3A4").

Definition JF_mi4 : axst := ltac2:(tb__ "0|0|
S3cSaZ0A1S0SeS47S0SeS46S4SeA1A3A3S39S3fA4").
Definition contMI4 (P : axst) : axst := ltac2:(tb__ "0|0|
S67S2dS89S66S38S51S4dVP;S80S29S5cS4bA1A2A6S81UeU1cZ1f0A3A2A1").
Definition T_mi4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDmi] (contMI4 VN.P_keep).
Definition T_mi4f : axst := Eval vm_compute in contMI4 VN.P_fail.
Definition T_mi4g : axst := Eval vm_compute in contMI4 VN.P_grown.

Definition XnoLoc (A : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S8eS5S9S9A2M0G0S7S8S8aR1S5ePa0M1S2S18S18Ze0Z24A4A2A2S8aR1S5eG1S2S18S18Z130Z4A4A2A2A2A1Lr;S5cVA;A1A3").
Definition reopen28n (A : axst) : axst := ltac2:(tb__ "0|0|
S5fVA;S35VA;A1S55Z1cZ21A5").
Definition reopen2n (A : axst) : axst := ltac2:(tb__ "0|0|
S5fS4fVA;A1S35VA;A1S55Z26Z27A5").

Definition reopen2f (A : axst) : axst := ltac2:(tb__ "0|1|
S5fS5fVA;S35VA;A1M0S55Z26Z27A5G0S55Z1cZ21A5").
Goal map (fun L => leaf_matches1A NPH L JR_mi4) [T_mi4k; T_mi4g] = [true; true] /\ leaf_matches1A NPH (reopen2f T_mi4f) JF_mi4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_mi4 = [(memcpy_pc, RsCut)] /\ lvs JF_mi4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_c4_0 : axst := Eval vm_compute in leaf_at JR_mi4 memcpy_pc 0.
Definition c4_site (E : axst) : axst := ltac2:(tb__ "0|6|
S44VE;A1S9S67S2dVE;S0S2bS2cU1SaZe0M0A1A2S0S2bS2cU2M1SaZ104A1A2S0S2bS2cU1eR1A2S0S2bS2cU1fM2ScS57R1SaZ24A1M3A3A2S4S2bA1A3A3A3A3A2A1S5dS68S68R1G1S11S69G0A1SaZ0A1M4G3S4S10A1M5SfA5A3G2S11S36VE;A1G4G3G5SfA5A3TE1;Toff;").
Definition E_c4 : axst := Eval vm_compute in c4_site E_c4_0.
Definition s_c4 : wsub := ltac2:(tb__ "0|1|
S0S5S17S9A2M0S2S17S9P35S32A4S0G0S2S17S9P36S54ZcS31A2A4S0G0S2S17S9P37S69Ze0A1A4S0G0S2S17S9P38SaZ24A1A4S0G0S2S17S9S8cS75A4S76PaS5bS48A1S5bS7fA1A3A3A3A3A3A3").
Definition R_c4 : list sobj := Eval vm_compute in optR (entails_frA E_c4 Pre_mc s_c4).
Goal entails_frA E_c4 Pre_mc s_c4 = Some R_c4 /\ call_checkPA E_c4 Pre_mc s_c4 R_c4 [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition sel_c4 : list nat := ltac2:(tb__ "0|1|
S3S1S0S1U0S0S1U5S0S1U2S0S1U6S0S1U7S0S1U3S0S1U4S0S1U8S4S1A1M0A3A3A3A3A3A3A3A3S3S1S7dU9U15A2S0S1U1eS0S1U1fS0S1U1S0S1U20S0S1U21S0S1U22S0S1U23S0S1U24S0S1U25S0S1U26S0S1U27G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T_c4 : axst := Eval vm_compute in
  (let off := offd_of E_c4_0 in
   let T := T_afterA Pre_mc E_c4 s_c4 R_c4 L_mc1 in
   let T1 := reshapeA (reshapeA T 1 (mkObj pDm4 off (SAlu ALU_ADD off (SLit 36)) [] DUnknown)) 2 (mkObj hF (SLit 224) (SLit 260) [] DUnknown) in
   optAp (apply_axforms T1 [AXSelect sel_c4; AXMerge 1; AXMerge 1; AXMerge 28; AXMerge 28])).

Goal shape T_c4 = shape JR_mi4 /\ lvs T_c4 = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fv4_0 : axst := Eval vm_compute in leaf_at T_c4 vr_entry 0.
Definition E_fv4 : axst := Eval vm_compute in ax_add_facts (vr_need 4 (SAlu ALU_ADD (cFV pL) (SLit 1)) (NFV pA)) (optAp (apply_axforms E_fv4_0 (xf_vr 16 528))).
Definition s_fv4 : wsub := ltac2:(tb__ "0|1|
S0S5S17S9A2M0S2S17S9P3bS82S6aA1A4S0G0S2S17S9P13ScS57S75SaZ40A1A3A4S76PaS5bS37A1S5bS66A1A3A3A3").
Definition R_fv4 : list sobj := Eval vm_compute in optR (entails_frA E_fv4 VN.Pre_vr s_fv4).
Goal entails_frA E_fv4 VN.Pre_vr s_fv4 = Some R_fv4 /\ call_checkPA E_fv4 VN.Pre_vr s_fv4 R_fv4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_fv4 : Z := 0x9fbcc.
Definition cMI3 : sv := ltac2:(tb__ "0|0|
ScS57S21S1aA1SaZ3A1A3").
Definition XL2 : list (sv * sv) := ltac2:(tb__ "0|0|
S25S32S34S1bS1cS31S33S1dS1eA8").
Definition F2 : list sprop := ltac2:(tb__ "0|1|
S3SbS43S3SbS6bS32S31ZcP172M0A4S3eS1aS32S41S31G0S34S1fS1aA1S33P174S1bS22S1aA1S1dP16cS1cS23S1aA1S1eP16eA11A3A3").
Definition fv4F : list sprop := ltac2:(tb__ "0|2|
S0SbSdScS57S1fS1aA1M0SaZ1A1A3S33A2S0SbSdSaS8bA1S34A2S0SbSdScS57S54Z4M1G0A2SaG1A1A3S54G1S33A2A2S4SbA1A3A3A3").
Definition JFV4 (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S3dS88S45SaS52A1Va0;A2S6cS32S41S31A3S6dS34S1fS1aA1S33A3S6eS1bS22S1aA1S1dA3S6fS1cS23S1aA1S1eA3S32S31S34S33S1bS1dS1cS1eS42Vtail;Vfacts;VX;A12").
Definition JR_fv4 : axst := ltac2:(tb__ "0|2|
S3bSaZ1A1S4SeA1S3SbS4eS3aA3S0S5S9S9A2M0S5ePa0M1S2S18S18Z130Z4A4A2S0G0S5eG1S2S18S18Ze0Z24A4A2S40A3A3A4").
Definition JF_fv4 : axst := ltac2:(tb__ "0|0|
S3bSaZ0A1S0SeS47S0SeS46S4SeA1A3A3S3aS40A4").
Definition contFV4 (P : axst) : axst := ltac2:(tb__ "0|0|
S67S2dS89S66S37S50S4cVP;S80S20S5cS49A1A2A6S81UfU1dZ210A3A2A1").
Definition T_fv4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDfv] (contFV4 VN.P_keep).
Definition T_fv4f : axst := Eval vm_compute in contFV4 VN.P_fail.
Definition T_fv4g : axst := Eval vm_compute in contFV4 VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_fv4) [T_fv4k; T_fv4g] = [true; true] /\ leaf_matches1A NPH (reopen2f T_fv4f) JF_fv4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_fv4 = [(memcpy_pc, RsCut)] /\ lvs JF_fv4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_m4_0 : axst := Eval vm_compute in leaf_at JR_fv4 memcpy_pc 0.

Definition E_m4_1 : axst := E_m4_0.

Definition m4_site (E : axst) : axst := ltac2:(tb__ "0|6|
S44VE;A1S9S67S2dVE;S0S2bS2cU1SaZ130M0A1A2S0S2bS2cU2M1SaZ134A1A2S0S2bS2cU1fR1A2S0S2bS2cU20M2ScS57R1SaZ4A1M3A3A2S4S2bA1A3A3A3A3A2A1S5dS68S68R1G1S11S69G0A1SaZ0A1M4G3S4S10A1M5SfA5A3G2S11S36VE;A1G4G3G5SfA5A3TE1;Toff;").
Definition E_m4 : axst := Eval vm_compute in m4_site E_m4_1.
Definition s_m4 : wsub := ltac2:(tb__ "0|2|
S0S5S17S9A2M0S2S17S9P35S34A4S0G0S2S17S9P36S54Z4M1S33A2A4S0G0S2S17S9P37S69Z130A1A4S0G0S2S17S9P38SaG1A1A4S0G0S2S17S9S8cS75A4S76PaS5bS4aA1S5bS7fA1A3A3A3A3A3A3").
Definition R_m4 : list sobj := Eval vm_compute in optR (entails_frA E_m4 Pre_mc s_m4).
Goal entails_frA E_m4 Pre_mc s_m4 = Some R_m4 /\ call_checkPA E_m4 Pre_mc s_m4 R_m4 [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition sel_m4 : list nat := ltac2:(tb__ "0|1|
S3S1S0S1U0S0S1U5S0S1U2S0S1U6S0S1U7S0S1U3S0S1U4S0S1U8S4S1A1M0A3A3A3A3A3A3A3A3S3S1S7dU9U15A2S0S1U1eS0S1U1fS0S1U20S0S1U1S0S1U21S0S1U22S0S1U23S0S1U24S0S1U25S0S1U26S0S1U27G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T_m4 : axst := Eval vm_compute in
  (let off := offd_of E_m4_1 in
   let T := T_afterA Pre_mc E_m4 s_m4 R_m4 L_mc1 in
   let T1 := reshapeA (reshapeA T 1 (mkObj pDf4 off (SAlu ALU_ADD off (SLit 4)) [] DUnknown)) 2 (mkObj hF (SLit 304) (SLit 308) [] DUnknown) in
   optAp (apply_axforms T1 [AXSelect sel_m4; AXMerge 1; AXMerge 1; AXMerge 29; AXMerge 29])).
Goal length (ss_objs (ax_S T_m4)) = 36%nat /\ lvs T_m4 = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

