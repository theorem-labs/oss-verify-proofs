(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition x2_geo (SPV lo DT WK wksz : Z) : Prop :=
  4096 <= lo /\ lo <= SPV - 1024 /\ SPV < 2^47
  /\ 4096 <= DT /\ DT + 16388 < 2^47 /\ 4096 <= WK /\ 2124 <= wksz < 2^32 /\ WK + wksz < 2^47
  /\ (DT + 16388 <= lo \/ SPV <= DT) /\ (WK + wksz <= lo \/ SPV <= WK) /\ (DT + 16388 <= WK \/ WK + wksz <= DT).
Ltac open_geo G := pose proof G as (LO0 & LOS & SPR & DTL & DTH & WKL & WKSZ & WKH & OFFDT & OFFWK & DTWK).

(* [comment removed for export] *)
Definition x2_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV DT WK : Z) (c0 c8 hdr3 : word) (r0 : Z) (hdrw : word)
    (scl maxW minBits tl1 : Z) (f112 f120 f128 f136 f144 : cell) (wn wt : word) : list cell :=
  [C8 c0; C8 c8; C8 hdr3; C8 (Z_to_bv 64 r0); C8 hdrw; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 223338299392); C8 (Z_to_bv 64 scl);
   C8 (Z_to_bv 64 maxW); C8 (Z_to_bv 64 (DT + 52)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 minBits); C8 (Z_to_bv 64 WK);
   C8 (Z_to_bv 64 tl1); f112; f120; f128; f136; f144; C8 (Z_to_bv 64 (DT + 4)); C4 wn; C4 wt;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition x2_models (rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z) : Prop :=
  Z.of_nat (length rvl) = 156 /\ Z.of_nat (length rs0) = 15 /\
  (forall w, 1 <= w <= maxW -> Znth w rvl = rv0 rank tl T w) /\
  (forall c w, tl + 1 - maxW <= c <= T - (tl + 1 - maxW) -> 1 <= w <= maxW -> Znth (13 * c + w) rvl = rvc rank tl T c w) /\
  (forall w, 1 <= w <= maxW + 1 -> Znth w rs0 = xs1 rank w).

(* [comment removed for export] *)
Definition X2G (m : fmem) (SPV lo DT WK wksz : Z) (fr : list cell) (hdr : list byte) (cw rvl rank rs0 : list Z) (syb : list byte) (m1 : fmem) : Prop :=
  rw_cells psegs m1 DT [CB 4 hdr] /\ x2_cells m1 DT cw
  /\ u32arr psegs m1 WK (map (Z_to_bv 64) rvl)
  /\ u32arr psegs m1 (WK + 624) (map (Z_to_bv 64) rank)
  /\ u32arr psegs m1 (WK + 676) (map (Z_to_bv 64) rs0)
  /\ bytes_at psegs m1 (WK + 736) syb /\ Z.of_nat (length syb) = 256 /\ stk psegs m1 (WK + 736) (WK + 992)
  /\ stk psegs m1 (WK + 992) (WK + wksz)
  /\ rw_cells psegs m1 (SPV + -272) fr /\ cells_size fr = 272%nat /\ stk psegs m1 lo (SPV + -272)
  /\ mem_inv psegs m1 /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 1024, SPV)] m m1 /\ wmono psegs m m1.
Ltac open_x2g I := destruct I as (HDRC & CWS & RVA & RKA & RSA & SYB & SYLEN & SYS & WKR & FR & FRSZ & STK & MI & MU & WM).
Ltac close_x2g := unfold X2G; repeat (split; [eassumption|]); eassumption.
