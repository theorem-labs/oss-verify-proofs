(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_BIT_INIT : Z := 0x1a500.     (* [comment removed for export] *)
Definition PHUF_BIT_INIT_F : Z := 0x2082c.   (* [comment removed for export] *)
Definition PHUF_FAST_ARGS : Z := 0x1e184.    (* [comment removed for export] *)
Definition PHUF_SWITCH_TAB : Z := 0x10520.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bitd_cells (S : Z) (d : bitD) (jp : list byte) : list cell :=
  [C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp; C8 (Z_to_bv 64 (S + bd_ptr d)); C8 (Z_to_bv 64 S);
   C8 (Z_to_bv 64 (S + 8))].

Definition bit_init_post (E : Z) (ra sp gp tp t1 t2 s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (D S : Z) (bs : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 a1 a3 a4 a5 a6 a7 : word) (ret : Z) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' S (map (Z_to_bv 8) bs)
    /\ match init_dstream bs with
       | Ok d => ret = zlen bs /\ bd_zero d = false /\ exists jp, rw_cells usegs m' D (bitd_cells S d jp)
       | Err e => ret = - e /\ exists j', rw_cells usegs m' D [CB 40 j']
       | Ub | NoFuel => False
       end.

Definition bit_init_stmt (E : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (D S : Z) (bs : list Z) (j : list byte) (lo : Z),
  rw_cells usegs m D [CB 40 j] -> D mod 8 = 0 -> 0 < D ->
  bytes_at usegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> 0 < S ->
  D + 40 <= 2^64 -> S + zlen bs + 8 <= 2^64 ->
  (S + zlen bs <= D \/ D + 40 <= S) ->
  stk usegs m lo (bv_unsigned sp) -> (D + 40 <= lo \/ bv_unsigned sp <= D) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bs) ->
  evt usegs (bit_init_post E ra sp gp tp t1 t2 s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc D S bs lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 E) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_RDT_X1 : Z := 0x134d8.
Definition PHUF_RDT_X2 : Z := 0x140d0.
Definition PHUF_DEC_1X : Z := 0x154d0.
Definition PHUF_DEC_4X : Z := 0x15a50.

Definition x1_bytes (cells : list deltX1) : list byte :=
  concat (map (fun c => [Z_to_bv 8 (x1_nbBits c); Z_to_bv 8 (x1_byte c)]) cells).
Definition x2_bytes (cells : list deltX2) : list byte :=
  concat (map (fun c => [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256); Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)]) cells).

Definition huf_dt_ok (m : fmem) (DT mtl : Z) : Prop :=
  exists (tt tl : Z),
    bytes_at usegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ ((tt = 0 /\ exists cells : list deltX1, zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
                                               /\ bytes_at usegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)))
        \/ (tt = 1 /\ exists cells : list deltX2, zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
                                               /\ bytes_at usegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)))).
