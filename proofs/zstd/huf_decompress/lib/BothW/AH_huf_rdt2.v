(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit
  AH_huf_iface AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Definition HUF_RDT_STACK_A2 : Z := 14336.

Section CANSEC1. Context {rc : runConstT}.
Section Stmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable dt_ok : amem -> Z -> Z -> Prop.

  Definition huf_rdt_stmtA2 (E : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
           (DT W S mtl flags : Z) (pdt pw : aptr) (src : list Z) (jdt : list byte) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->                  (* [comment removed for export] *)
    (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->  (* [comment removed for export] *)
    1 <= mtl <= 12 ->
    In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
    rw_cells bsegs m DT [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt] ->
    In (HB pw W 8704) LB ->
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (W + 8704 <= S \/ S + zlen src <= W) ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_RDT_STACK_A2 ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    0 <= flags < 64 ->
    harness_invA m ->
    (* [comment removed for export] *)
    hinv_bm m -> (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen src) -> a3 = Z_to_bv 64 W -> a4 = Z_to_bv 64 8704 ->
    a5 = Z_to_bv 64 flags ->
    evtF bsegs RNG (huf_rdt_postA AI dt_ok L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
