(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg RF_huf_iface RF_huf_h_iface RF_huf_dec_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition Y4S (mm : fmem) : Prop :=
    (exists buf, u8arr psegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at psegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at psegs mm (DT + 4) cbs
    /\ bytes_at psegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk psegs mm lo (SP + -104)
    /\ rw_cells psegs mm (SP + -104) FRS
    /\ mem_inv psegs mm /\ munch DW m0 mm /\ wmono psegs m0 mm.

  (* [comment removed for export] *)
  Definition y4_slow_goal : Prop :=
    forall mm (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4S mm ->
    evt psegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -416)) gp tp t0 t1 t2 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) a0 a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SS) x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15f40) fc None mm (seg_rom psegs)).
End Y4S.

(* [comment removed for export] *)
Definition y4_slow_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte),
  x2_table_ok cells tl ->
  cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells) ->
  zlen cbs = 4 * 2^tl ->
  1 <= mtl <= 12 -> tl <= mtl ->
  0 <= DST -> (0 < dcap -> 8 <= DST) -> 0 <= dcap < 2^32 -> DST + dcap <= lo ->
  16 <= SS -> SS + zlen src <= lo -> zlen src < 2^26 -> Forall (fun c => 0 <= c < 256) src ->
  0 < DT -> DT + 4 + 4 * 2^tl <= lo ->
  (DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT) -> (DST + dcap <= SS \/ SS + zlen src <= DST) ->
  lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
  y4_slow_goal ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs.
End CANSEC1.
