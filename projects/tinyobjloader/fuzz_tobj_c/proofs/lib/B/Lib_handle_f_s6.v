(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "option"; "prod"; "app"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "DUnknown"; "mkObj"; "SAlu"; "sstate"; "SMd"; "sobj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "am2"; "BAD"; "FUEL_hf"; "pA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6.AR"; "o4A"; "o16A"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "sym_runA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "E_pg4"; "cutpcs_hf6"; "E_pg"; "O_dummy"; "X_sub"; "cap3"; "hf_MD"; "xNXT"; "xOUT"; "xP2D"; "xPRV"; "xPTS"; "xRFX"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "leavesA_at"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "cutpcs_hf5"; "pDrp"; "pDts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Stdlib.Lists.List"; "last"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4 Lib_handle_f_s5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module AR. Include Lib_handle_f_arith. End AR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition optS (x : option sstate) : sstate := ltac2:(tb__ "0|0|
S3SeA1SeLx;Vx;SeR1Ls;S26S18A1X3x2").
Definition O_dummy : sobj := ltac2:(tb__ "0|1|
ScS9Z0A1M0G0G0S1SaA1SbA5").
Definition sh_last (A : axst) : sobj := ltac2:(tb__ "0|0|
S4dS10S11S26VA;A1A1S33A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).

Definition hf_MD : Z := 0x9da58.
Definition cutpcs_hf6 : list Z := ltac2:(tb__ "0|0|
S5S15S46S0S15S36S1S15A1A3A3").
Definition leaf_at6 (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S3eS27Vk;S3fS19S31VS;Vpc;A4S18A4").
Definition lvs6 (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S3S6S28A1M0A1S6S4S15S4bA2M1A1Lx;S2aS40S19S31VS;S7A5G0S3dS28G1S41R1A4Ll;S1G1A1X3x2").
Definition T_md : axst := Eval vm_compute in leaf_at6 JR_ts hf_MD 0.
Goal lvs6 JR_ts = [(hf_MD, RsCut)] /\ lvs T_md = [(pg_pc, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_pg0 : axst := Eval vm_compute in leaf_at T_md pg_pc 0.
Goal sh_last E_pg0 = shobj hG 6 23 (ob_cells (sh_last E_pg0)) DUnknown /\ local_ok (ob_cells (sh_last E_pg0)) DUnknown 6 23 (160, 24) = true
  /\ local_ok (ob_cells (sh_last E_pg0)) DUnknown 6 23 (48, 72) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition rt72 (c : cell) : bool := sv_eqb (c_off c) (SLit 72).
Definition news72 : list cell := ltac2:(tb__ "0|1|
S0SaS2fZ48S9Z0A1M0A2S0SaS2fZ4cG0A2S1SaA1A3A3").
Definition E_pg0t : axst := Eval vm_compute in ax_setS E_pg0 (optS (retile_at (ax_S E_pg0) 1 rt72 news72)).
Goal retile_at (ax_S E_pg0) 1 rt72 news72 = Some (ax_S E_pg0t). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_pg1 : axst := Eval vm_compute in ax_add_facts AR.ts_facts (shadow_release_stateA E_pg0t (objs_butlast E_pg0t) 160 [(160, 24); (48, 72)]).

Definition xf_pg1 : list axform := ltac2:(tb__ "0|6|
S0S12S13U0M0S9N180M1A1A2S0S12S14G0G1A2S0S12S13U2S9Z30M2A1A2S0S12S13U3M3S9Z78A1A2S0S12S13U4S9Za0M4A1A2S0S12S13U5M5S9Zb8A1A2S0S12S14G3G2A2S0S12S14G5G4A2S1S12A1A3A3A3A3A3A3A3A3").

Definition xf_pg2 : list axform := ltac2:(tb__ "0|1|
S0S12S13U26S2eZcM0S1aA2A2S0S12S13U28S2eG0S17A2A2S0S12S13U2aS1cA2S0S12S13U2bS21A2S0S12S13U2cS22A2S0S12S13U2dS23A2S0S12S13U2eS24A2S0S12S13U2fS25A2S1S12A1A3A3A3A3A3A3A3A3").

Definition O_nxt' : sobj := ltac2:(tb__ "0|0|
ScS1eS9Z0A1S1bS1SaA1SbA5").
Definition O_prv' : sobj := ltac2:(tb__ "0|0|
ScS1fS9Z0A1S1bS1SaA1SbA5").
Definition O_rfx' : sobj := ltac2:(tb__ "0|0|
ScS20S9Z0A1S1dS1SaA1SbA5").
Definition E_pg2 : axst := Eval vm_compute in optAp (apply_axforms E_pg1 xf_pg1).
Definition E_pg3 : axst := Eval vm_compute in optAp (apply_axforms E_pg2 xf_pg2).

Definition xPTS : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S47SfS2cS1aS9ZcA1A3A4").
Definition xOUT : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S45SfS2cS17S9ZcA1A3A4").
Definition xP2D : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S48S1cA4").
Definition xNXT : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S1eS1bA4").
Definition xPRV : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S1fS1bA4").
Definition xRFX : sv * sv := ltac2:(tb__ "0|0|
S2S8S8S20S1dA4").
Definition X_sub : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S8S8A2M0S3bS0G0S38S0G0S39S0G0S37S0G0S3aS0G0S3cS1G0A1A3A3A3A3A3A3").
Definition E_pg4 : axst := Eval vm_compute in reshapeA (reshapeA (reshapeA E_pg3 43 O_nxt') 45 O_prv') 47 O_rfx'.
Definition E_pg : axst := ltac2:(tb__ "0|0|
S4cS30S5S4S8S8A2S34S29S30A1A3A2").
Goal length (ss_objs (ax_S E_pg2)) = 41%nat /\ length (ss_objs (ax_S E_pg3)) = 49%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition cap3 : sv := ltac2:(tb__ "0|0|
SdS2bSdS2dS17S9Z1A1A3S17A3").
Definition s_pg : wsub := ltac2:(tb__ "0|1|
S0S4S16S8A2M0S2S16S8P14S35A4S0G0S2S16S8P13SdS2bS49S9Z180A1A3A4S4aPaS26S32A1S26S44A1A3A3A3").
Definition R_pg : list sobj := Eval vm_compute in optR (entails_frA E_pg PG.Pre_pg s_pg).
Definition Posts_pg : list axst := ltac2:(tb__ "0|0|
S0S27S42S0S27S43S1S27A1A3A3").
Goal entails_frA E_pg PG.Pre_pg s_pg = Some R_pg /\ call_checkPA E_pg PG.Pre_pg s_pg R_pg Posts_pg = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_pg : list (sv * sv) := ax_X E_pg1.
Definition T_pgo0 : axst := Eval vm_compute in T_afterA3 PG.Pre_pg E_pg s_pg R_pg PG.P_ok Xk_pg.
Definition T_pgi0 : axst := Eval vm_compute in T_afterA3 PG.Pre_pg E_pg s_pg R_pg PG.P_inv Xk_pg.
Goal length (ss_objs (ax_S T_pgo0)) = 50%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
