(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "length"; "prod"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "cell"; "mkObj"; "sobj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "AXUnbase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_build_line_index.BLIAddr"; "FR"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_build_line_index"; "Pre_bli"; "darrL"; "kb16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro2"; "E_bli"; "cps_pro2"; "lo_AFTER"; "lo_BODY"; "lo_LATCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve_darr Lib_build_line_index.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr VRDAddr LOAddr.

Definition bli_entry : Z := BLIAddr.bli_entry.
Definition cps_pro2 : list Z := bli_entry :: cps_pro.
Definition E_bli0 : axst := Eval vm_compute in leafL_at cps_pro2 T_vend bli_entry 0.

Definition E_bli1 : axst := Eval vm_compute in
  let i := idxB E_bli0 (SVar 10) (- FR) in
  optL (apply_axforms E_bli0 [AXSplit i (SLit (-328)); AXSplit (S i) (SLit (-296)); AXUnbase (S i) (-328)]).
Definition E_bli2 : axst := Eval vm_compute in
  let i := find_idxb (fun o => sv_eqb (ob_base o) (spm FR) && sv_eqb (ob_hi o) (SLit 0)) (ss_objs (ax_S E_bli1)) 0%nat in
  optL (apply_axforms E_bli1 [AXSplit i (SLit (- BLIAddr.FR)); AXUnbase i (- BLIAddr.FR)]).
Definition O_ldat0 : sobj := ltac2:(tb__ "0|1|
ScS9Z0A1M0G0S1bG0A1S3SbA1S1aG0A1A5").
Definition E_bli3 : axst := Eval vm_compute in ax_setS E_bli2 (add_obj (ax_S E_bli2) O_ldat0).
Definition E_bli : axst := Eval vm_compute in ax_setX E_bli3 ((SLit 0, SLit 0) :: ax_X E_bli3).
Definition vLNo : sv := spm 328.
Definition s_bli : wsub := ltac2:(tb__ "0|2|
S0S5S6S8A2M0S1S6S8P13SaS18S1dS9S15A1A3A4S0G0S1S6S8PfS9Z0A1M1A4S0G0S1S6S8P10G1A4S0G0S1S6S8P11G1A4S24PaS14S1fA1S14S19A1A3A3A3A3A3").
Definition R_bli : list sobj := Eval vm_compute in R_of E_bli Pre_bli s_bli.

Definition bli_back (T : axst) : axst := ltac2:(tb__ "0|3|
S1eS1cS13VT;S0SfS12U1M0S15A2S0SfS11S0S2G0S0S2U0M1S17U2M2S16S4SdSeS14VT;A1A1A2G2A2A2A3A3A1S0SfS10G1A1S3SfA1A3A3A3A2A1A1").
Definition T_bli1 : axst := Eval vm_compute in bli_back (T_afterA Pre_bli E_bli s_bli R_bli P_ret1).
Definition T_bli0 : axst := Eval vm_compute in bli_back (T_afterA Pre_bli E_bli s_bli R_bli P_ret0).
Goal entails_frA E_bli Pre_bli s_bli = Some R_bli /\ call_checkPA E_bli Pre_bli s_bli R_bli [P_ret1; P_ret0] = true
     /\ length (ss_objs (ax_S T_bli1)) = 21%nat /\ length (ss_objs (ax_S T_bli0)) = 21%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition lo_LATCH : Z := 0x8d674. Definition lo_BODY : Z := 0x8d67c. Definition lo_AFTER : Z := 0x8e4ac.
Definition cps_loop0 : list Z := ltac2:(tb__ "0|0|
S0S7S23S0S7S22S0S7S21S20A3A3A3").

Definition X_body1 : axst := Eval vm_compute in leafL_at cps_loop0 T_bli1 lo_BODY 0.
Definition X_after1 : axst := Eval vm_compute in leafL_at cps_loop0 T_bli1 lo_AFTER 0.
Definition X_body0 : axst := Eval vm_compute in leafL_at cps_loop0 T_bli0 lo_BODY 0.
Definition X_after0 : axst := Eval vm_compute in leafL_at cps_loop0 T_bli0 lo_AFTER 0.
Goal map (fun A => ss_pc (ax_S A)) [X_body1; X_after1; X_body0; X_after0] = [lo_BODY; lo_AFTER; lo_BODY; lo_AFTER].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
