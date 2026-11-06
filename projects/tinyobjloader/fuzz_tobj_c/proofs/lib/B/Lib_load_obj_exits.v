(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "app"; "nil"; "None"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "sv"; "SPUle"; "mkSS"; "FcsrFrm0"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "KJ"; "coreJ"; "jfregsA"; "jregsA"; "spill_common"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "nx_facts"; "pI"; "xLC"; "HNEXT"; "NZ32e"; "X_loopA"; "coreA"; "datasA"; "fpc"; "hx"; "kL"; "kLE"; "k_v"; "loop_factsA"; "lregsA"; "pERR"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "jx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@Stdlib.Lists.List"; "tl"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition spill_cells0 : list cell := Eval vm_compute in ob_cells (nth (idxB X_after1 (SVar 10) (- FR)) (ss_objs (ax_S X_after1)) O_midA).
Definition spill_common : list cell := Eval vm_compute in List.filter (fun c => existsb (cell_eqb c) spill_cells) spill_cells0.
Definition jregsA (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|0|
S34S2bVl;A1S30S0S1U6S0S1U7S0S1U1cS0S1U10S0S1U11S0S1U12S0S1U16S0S1U17S3S1A1A3A3A3A3A3A3A3A3A1A2").
Definition jfregsA : list sv := list_set lfregsA 8%nat (hf 8).
Definition coreJ (k : cst) : list sobj := ltac2:(tb__ "0|0|
S0S8S25S36S2fA1N148S1bA3S35S8S23Vk;A1A2A3").
Definition KJ (pc : Z) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S2eSbVpc;S1aS3S6S1S9A2A1A1S19ScS4S9A1S2S8S18Vk;A1S24S29Vk;A1A1A3S2S7Vfacts;S2aVk;A1A3S20S5A9S22Vk;A1A2").

Definition K_after0 : axst := ltac2:(tb__ "0|0|
S17S1cS27S2dA1S0S7SaS1fS1eA2S1dA3A3").
Definition K_afterE : axst := ltac2:(tb__ "0|0|
S17S1cS28S0S7SaS1fS1eA2S0S7S21S2cA1S1dA3A3A3").

Definition X_after : axst := Eval vm_compute in leafL (runL 150 cps_loop K_loop) pc_after 0.
Definition X_afterE : axst := Eval vm_compute in leafL (runL 150 cps_loop K_loopE) pc_after 0.

Definition junk_a0 (A : axst) : axst := ltac2:(tb__ "0|1|
S32VA;A1S16S33VA;SbS13R1A1S31S9S14R1A1UaM0S26G0A1A4SfR1A1SeR1A1S15R1A1S12R1A1SdR1A1S11R1A1S10R1A1A9A2TS;").
Definition X_bodyE : axst := Eval vm_compute in junk_a0 (leafL (runL 150 cps_loop K_loopE) pc_body 0).
Definition X_errxE : axst := Eval vm_compute in leafL (runL 150 cps_loop X_bodyE) pc_errx 0.
Goal map (fun L => ss_pc (ax_S (la_state L))) (runL 150 cps_loop K_loop) = [pc_after; pc_body]
  /\ map (fun L => ss_pc (ax_S (la_state L))) (runL 150 cps_loop K_loopE) = [pc_after; pc_body]
  /\ map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runL 150 cps_loop X_bodyE) = [(pc_errx, RsCut)]
  /\ map (fun A => ss_pc (ax_S A)) [X_after; X_afterE; X_bodyE; X_errxE] = [pc_after; pc_after; pc_body; pc_errx]
  /\ leaf_matchesA NP X_after [K_after0] = true /\ leaf_matchesA NP X_afterE [K_afterE] = true
  /\ map (fun L => leaf_matchesA NP (la_state L) [X_bodyE; X_afterE]) (runL 150 cps_loop K_loopE) = [true; true]
  /\ (10 <=? length spill_common)%nat = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
