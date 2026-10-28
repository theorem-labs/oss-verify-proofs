(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation zlen l := (Z.of_nat (length l)).
(* [comment removed for export] *)
Notation FSE_READ_STACK_A := 4672 (only parsing).   (* [comment removed for export] *)
Notation FSE_READ_DEPTH := 2 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

Definition APFSE_READ_BODY : Z := 0xaaac0.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

(* [comment removed for export] *)
Definition fse_read_any_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV NC MSVP TLP : Z) (rt0 buf : list Z) (msv0 lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r rt' (msvw tlw : word),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - FSE_READ_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ u8arr bsegs m' NC (u16s (map (Z_to_bv 64) rt')) /\ length rt' = length rt0
    /\ rw_cells bsegs m' MSVP [C4 msvw] /\ rw_cells bsegs m' TLP [C4 tlw]
    /\ 0 <= r < 2^64
    /\ ((exists rt msv tl n, read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n)
           /\ r = n /\ rt' = rt /\ msvw = Z_to_bv 64 msv /\ tlw = Z_to_bv 64 tl)
        \/ (exists e, read_ncount rt0 msv0 buf = Err e /\ r = 2^64 - e)).

Definition fse_read_any_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV NC MSVP TLP BUF : Z) (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word),
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV FSE_READ_DEPTH -> tp = Z_to_bv 64 ATP ->
  areg RNG m NC (2 * zlen rt0) -> ainblk LB NC (2 * zlen rt0) -> ahull RNG m NC (2 * zlen rt0) ->
  areg RNG m MSVP 4 -> ainblk LB MSVP 4 ->
  areg RNG m TLP 4 -> ainblk LB TLP 4 ->
  aregU RNG m BUF (zlen buf) -> ahull RNG m BUF (zlen buf) -> (0 < zlen buf -> ainimg LB BUF (zlen buf)) ->   (* [comment removed for export] *)
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  u8arr bsegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells bsegs m MSVP [C4 (Z_to_bv 64 msv0)] -> rw_cells bsegs m TLP [C4 tl0] ->
  bytes_at bsegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen rt0 <= 65536 -> zlen buf <= 1048576 ->
  (* [comment removed for export] *)
  4096 <= NC -> NC + 2 * zlen rt0 < 2^47 -> NC mod 2 = 0 ->
  4096 <= MSVP -> MSVP + 4 < 2^47 -> MSVP mod 4 = 0 ->
  4096 <= TLP -> TLP + 4 < 2^47 -> TLP mod 4 = 0 ->
  4096 <= BUF -> BUF + zlen buf < 2^47 ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FSE_READ_STACK_A ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) -> (TLP + 4 <= lo \/ SPV <= TLP) ->
  (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  evtF bsegs RNG (fse_read_any_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APFSE_READ_BODY) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
