(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "prod"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "DUnknown"; "cell"; "mkObj"; "SAlu"; "sstate"; "SMd"; "sobj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "am2"; "pA"; "BAD"; "Pre_ms"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6.AR"; "o4A"; "o16A"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "E_pg4"; "E_md"; "E_pg"; "O_dummy"; "X_sub"; "cap3"; "xNXT"; "xOUT"; "xP2D"; "xPRV"; "xPTS"; "xRFX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDrp"; "pDts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.Lists.List"; "last"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4 Lib_handle_f_s5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module AR. Include Lib_handle_f_arith. End AR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition optS (x : option sstate) : sstate := ltac2:(tb__ "0|0|
S6SdA1SdLx;Vx;SdR1Ls;S16S1bA1X6x2").
Definition O_dummy : sobj := ltac2:(tb__ "0|1|
SbS8Z0A1M0G0G0S2SaA1S9A5").
Definition sh_last (A : axst) : sobj := ltac2:(tb__ "0|0|
S44SfS10S16VA;A1A1S30A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).

Definition E_md0 : axst := Eval vm_compute in leaf_at JR_ts memset_pc 0.
Goal sh_last E_md0 = shobj hG 6 15 (ob_cells (sh_last E_md0)) DUnknown /\ local_ok (ob_cells (sh_last E_md0)) DUnknown 6 15 (48, 72) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_md1 : axst := Eval vm_compute in shadow_release_stateA E_md0 (objs_butlast E_md0) 160 [(48, 72)].
Definition xf_md : list axform := ltac2:(tb__ "0|0|
S0S11S12U1S8Z38A1A2S0S11S12U2S8Z78A1A2S2S11A1A3A3").
Definition E_md : axst := Eval vm_compute in reshapeA (optAp (apply_axforms E_md1 xf_md)) 2 (mkObj (xfo 56) (SLit 0) (SLit 64) [] DUnknown).
Definition s_md : wsub := ltac2:(tb__ "0|1|
S0S4S15S7A2M0S1S15S7P35S1dZ30A1A4S0G0S1S15S7P36S8Z48A1A4S0G0S1S15S7S43S39A4S3aPaS16S2eA1S16S1cA1A3A3A3A3").
Definition R_md : list sobj := Eval vm_compute in optR (entails_frA E_md Pre_ms s_md).
Goal entails_frA E_md Pre_ms s_md = Some R_md /\ call_checkPA E_md Pre_ms s_md R_md [L_ms] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_md0 : axst := Eval vm_compute in T_afterA Pre_ms E_md s_md R_md L_ms.
Definition T_md1 : axst := Eval vm_compute in reshapeA T_md0 1 (mkObj hF (SLit 56) (SLit 120) [] DZero).
Definition zc_desc : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4S14S14A2M0S1S14S14Z40Z8M1A4S0G0S1S14S14Z48Z4A4S0G0S1S14S14Z70G1A4S2G0A1A3A3A3").
Definition T_md2 : axst := Eval vm_compute in ax_setS T_md1 (optS (zcells_at (ax_S T_md1) 1 zc_desc)).
Definition sel_md : list nat := ltac2:(tb__ "0|0|
S5S3S0S3U0S0S3U4S0S3U1S0S3U5S0S3U6S0S3U2S0S3U3S2S3A1A3A3A3A3A3A3A3S3bU7U1fA2A3").
Definition T_md3 : axst := Eval vm_compute in optAp (apply_axforms T_md2 [AXSelect sel_md; AXMerge 1; AXMerge 1]).
Definition T_md : axst := Eval vm_compute in reopenX 20 23 T_md3.
Goal zcells_at (ax_S T_md1) 1 zc_desc = Some (ax_S T_md2) /\ shape T_md3 = shape JF_ts /\ lvs T_md = [(pg_pc, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_pg0 : axst := Eval vm_compute in leaf_at T_md pg_pc 0.
Goal sh_last E_pg0 = shobj hG 20 23 (ob_cells (sh_last E_pg0)) DUnknown /\ local_ok (ob_cells (sh_last E_pg0)) DUnknown 20 23 (160, 24) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_pg1 : axst := Eval vm_compute in ax_add_facts AR.ts_facts (shadow_release_stateA E_pg0 (objs_butlast E_pg0) 160 [(160, 24)]).

Definition xf_pg1 : list axform := ltac2:(tb__ "0|6|
S0S11S12U0M0S8N140M1A1A2S0S11S13G0G1A2S0S11S12U2S8Z30M2A1A2S0S11S12U3M3S8Z78A1A2S0S11S12U4S8Za0M4A1A2S0S11S12U5M5S8Zb8A1A2S0S11S13G3G2A2S0S11S13G5G4A2S2S11A1A3A3A3A3A3A3A3A3").

Definition xf_pg2 : list axform := ltac2:(tb__ "0|1|
S0S11S12U26S2cZcM0S1aA2A2S0S11S12U28S2cG0S19A2A2S0S11S12U2aS1fA2S0S11S12U2bS24A2S0S11S12U2cS25A2S0S11S12U2dS26A2S0S11S12U2eS27A2S0S11S12U2fS28A2S2S11A1A3A3A3A3A3A3A3A3").

Definition O_nxt' : sobj := ltac2:(tb__ "0|0|
SbS21S8Z0A1S1eS2SaA1S9A5").
Definition O_prv' : sobj := ltac2:(tb__ "0|0|
SbS22S8Z0A1S1eS2SaA1S9A5").
Definition O_rfx' : sobj := ltac2:(tb__ "0|0|
SbS23S8Z0A1S20S2SaA1S9A5").
Definition E_pg2 : axst := Eval vm_compute in optAp (apply_axforms E_pg1 xf_pg1).
Definition E_pg3 : axst := Eval vm_compute in optAp (apply_axforms E_pg2 xf_pg2).

Definition xPTS : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S40SeS2aS1aS8ZcA1A3A4").
Definition xOUT : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S3fSeS2aS19S8ZcA1A3A4").
Definition xP2D : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S41S1fA4").
Definition xNXT : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S21S1eA4").
Definition xPRV : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S22S1eA4").
Definition xRFX : sv * sv := ltac2:(tb__ "0|0|
S1S7S7S23S20A4").
Definition X_sub : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S7S7A2M0S37S0G0S34S0G0S35S0G0S33S0G0S36S0G0S38S2G0A1A3A3A3A3A3A3").
Definition E_pg4 : axst := Eval vm_compute in reshapeA (reshapeA (reshapeA E_pg3 43 O_nxt') 45 O_prv') 47 O_rfx'.
Definition E_pg : axst := ltac2:(tb__ "0|0|
S42S2dS5S4S7S7A2S31S18S2dA1A3A2").
Goal length (ss_objs (ax_S E_pg2)) = 41%nat /\ length (ss_objs (ax_S E_pg3)) = 49%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition cap3 : sv := ltac2:(tb__ "0|0|
ScS29ScS2bS19S8Z1A1A3S19A3").
Definition s_pg : wsub := ltac2:(tb__ "0|1|
S0S4S15S7A2M0S1S15S7P14S32A4S0G0S1S15S7P13ScS29S39S8Z140A1A3A4S3aPaS16S2fA1S16S3eA1A3A3A3").
Definition R_pg : list sobj := Eval vm_compute in optR (entails_frA E_pg PG.Pre_pg s_pg).
Definition Posts_pg : list axst := ltac2:(tb__ "0|0|
S0S17S3cS0S17S3dS2S17A1A3A3").
Goal entails_frA E_pg PG.Pre_pg s_pg = Some R_pg /\ call_checkPA E_pg PG.Pre_pg s_pg R_pg Posts_pg = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_pg : list (sv * sv) := ax_X E_pg1.
Definition T_pgo0 : axst := Eval vm_compute in T_afterA3 PG.Pre_pg E_pg s_pg R_pg PG.P_ok Xk_pg.
Definition T_pgi0 : axst := Eval vm_compute in T_afterA3 PG.Pre_pg E_pg s_pg R_pg PG.P_inv Xk_pg.
Goal length (ss_objs (ax_S T_pgo0)) = 50%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
