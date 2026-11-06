(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AH_fse_kit AF_fse_iface AF_fse_rd_iface AH_fse_Hiface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Section CANSEC1. Context {rc : runConstT}.
Section PhaseB.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition fzC_state (L : alayout) (RNG0 : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem)
(pP : AsanCtrl.aptr) (s1' : APS) (RNG1 : footprint) (ms : machine_state) : Prop :=
exists (P F SPA : Z) (m : amem) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jb jc jd junk : list byte),
SPA = (bv_unsigned sp - 224) - (bv_unsigned sp - 224) mod 32
/\ ms = MS (mkR (Z_to_bv 64 0x80ec0) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 P) y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 18446744073709551602) (Z_to_bv 64 ASHOFF) s4 s5 (Z_to_bv 64 F)
(Z_to_bv 64 (zlength pl)) (Z_to_bv 64 D) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 (SHF F + 76))
y28 y29 y30 y31)
FR (Z_to_bv 64 0x80ec0) fc None m (seg_rom bsegs)
/\ AHEAP AI L RNG1 (aps_m s1') (HB pP P PRODUCER_SIZE :: FB5 F :: LB) m
/\ aps_rest s1' = aps_rest s /\ fp_le RNG0 RNG1
/\ magree bsegs (aclient_addr CI LB (bv_unsigned sp)) m0 m
/\ ablock_range P PRODUCER_SIZE /\ rng RNG1 P PRODUCER_SIZE /\ rng RNG1 (shad P) (shlen (PRODUCER_SIZE + 7))
/\ rw_cells bsegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength pl))]
/\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP /\ rng RNG1 F 2048 /\ rng RNG1 (shad F) 256
/\ rw_cells bsegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80d20); CB 2016 junk;
C8 (Z_to_bv 64 (fflag L 5 F))]
/\ rw_cells bsegs m (SHF F) (FSH F8S F8S F8S BF8 BF8)
/\ stk bsegs m lo SPA
/\ rw_cells bsegs m SPA [CB 40 jb; C8 (Z_to_bv 64 F); CB 16 jc; C8 (Z_to_bv 64 (SHF F + 148)); CB 40 jd; C8 (Z_to_bv 64 F)]
/\ stk bsegs m (SPA + 120) (bv_unsigned sp + -104)
/\ rw_cells bsegs m (bv_unsigned sp + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
/\ mem_inv bsegs m.
Definition fzBB_stmt : Prop :=
prod_u32r_stmtA -> prod_i32r_stmtA -> fse_wbound_stmtA -> fse_write_stmtA -> fse_iserror_stmtA ->
forall (L : alayout) (RNG0 : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem)
(pP : AsanCtrl.aptr) (s1' : APS) (RNG1 : footprint) (ms : machine_state),
(forall b, In b LB -> exists p A n, b = HB p A n) ->
AHarness_iface.payload_atA LB D pl -> bytes_at bsegs m0 D (map (Z_to_bv 8) pl) ->
Forall (fun c => 0 <= c < 256) pl -> D mod 16 = 0 -> zlength pl < 2^26 ->
ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
tp = Z_to_bv 64 ATP ->
rng RNG0 lo (al_top L - lo) -> rng_aimg RNG0 -> rng_aimg_sh RNG0 ->
fzC_state L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms ->
evtF bsegs RNG1 (fzB_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1) ms.
End PhaseB.
End CANSEC1.
