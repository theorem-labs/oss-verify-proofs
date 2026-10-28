(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition HDI (L p bits : Z) : Prop := 0 <= p /\ (p = 0 \/ p + 8 <= L) /\ 0 <= bits <= 64 /\ (8 <= p -> bits <= 8).

Section CANSEC1. Context {rc : runConstT}.
Section W4S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition w4_slow_goal : Prop :=
    forall (fr mid l256 l296 l336 : list cell) mm (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
    W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336 ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 n) x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x10
                                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DT) (Z_to_bv 64 SS) x20 x21 x22 x23 (Z_to_bv 64 AW4_KSB)
                                 x25 x26 x27 x28 x29 x30 x31)
                            FR (Z_to_bv 64 AW4_SLOW) fc None mm (seg_rom bsegs)).
End W4S.

(* [comment removed for export] *)
Definition w4_slow_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  AHEAP AI L RNG st LB m0 ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (* [comment removed for export] *)
  1 <= mtl <= 12 -> tl <= mtl + 1 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  x1_table_ok cells tl -> cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells) -> zlen cbs = 2 * 2^tl ->
  (* [comment removed for export] *)
  ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) -> 0 <= dcap < 2^32 ->
  (* [comment removed for export] *)
  Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= SS ->
  (0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + zlen src <= SBH) ->
  (DT + DTABLE_BYTES mtl <= SS \/ SS + zlen src <= DT) -> (DST + dcap <= SS \/ SS + zlen src <= DST) ->
  (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
  (* [comment removed for export] *)
  ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A -> bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP -> harness_invA m0 ->
  rclean m0 rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs.
End CANSEC1.
