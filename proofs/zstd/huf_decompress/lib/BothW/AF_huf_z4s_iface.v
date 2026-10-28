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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section Z4S.
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
  Definition Z4S (mm : amem) : Prop :=
    ((DST = 0 /\ dcap = 0) \/ exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk bsegs mm lo (SP + -104)
    /\ rw_cells bsegs mm (SP + -104) FRS
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Definition z4_slow_goal : Prop :=
    forall mm (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Z4S mm ->
    evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 n) (Z_to_bv 64 (SP + -576)) gp tp (Z_to_bv 64 dcap) (Z_to_bv 64 DT) t2 x8 x9
                                 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 DST) x25 x26 (Z_to_bv 64 2147450880)
                                 t3 t4 t5 (Z_to_bv 64 SS))
                            FR (Z_to_bv 64 0x87d04) fc None mm (seg_rom bsegs)).
End Z4S.

(* [comment removed for export] *)
Definition z4_slow_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  AHEAP AI L RNG st LB m0 ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (* [comment removed for export] *)
  1 <= mtl <= 12 -> tl <= mtl -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  x2_table_ok cells tl -> cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells) -> zlen cbs = 4 * 2^tl ->
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
  z4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs.
End CANSEC1.
