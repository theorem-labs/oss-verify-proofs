(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

Definition PHUF_RDT_X1 : Z := 0x134d8.      (* [comment removed for export] *)
Definition PHUF_RDT_X2 : Z := 0x140d0.      (* [comment removed for export] *)
Definition PHUF_DEC_1X : Z := 0x154d0.      (* [comment removed for export] *)
Definition PHUF_DEC_4X : Z := 0x15a50.      (* [comment removed for export] *)
Definition PHUF_ISERROR : Z := 0x20e88.     (* [comment removed for export] *)
Definition PPROD_REMAINING : Z := 0x21050.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HUF_RDT_STACK : Z := 4096.
Definition HUF_DEC_STACK : Z := 4096.

(* [comment removed for export] *)
Definition DTABLE_BYTES (mtl : Z) : Z := HufHarness.DT_BYTES mtl.     (* [comment removed for export] *)

Definition PPROD_U32R : Z := 0x20ee4.       (* [comment removed for export] *)
Definition PPROD_I32R : Z := 0x20fb0.       (* [comment removed for export] *)

Section CANSEC0. Context {rc : runConstT}.
Definition prod_at (m : fmem) (P D size : Z) : Prop :=
  rw_cells usegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_at (m : fmem) (D : Z) (pl : list Z) : Prop :=
  bytes_at usegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.

Definition prod_u32r_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ prod_at m' P D (snd (uint32Range pl size mn mx)).

Definition prod_u32r_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk usegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv usegs m ->
  0 <= mn <= mx -> mx < 2^31 ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evt usegs (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PPROD_U32R) fc None m (seg_rom usegs)).

Definition prod_i32r_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (int32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P + 8, P + 16); (SPV - 32, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ prod_at m' P D (snd (int32Range pl size mn mx)).

Definition prod_i32r_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk usegs m lo SPV -> lo <= SPV - 32 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv usegs m ->
  - 2^31 <= mn <= mx -> mx < 2^31 -> mx - mn < 2^31 ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evt usegs (prod_i32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PPROD_I32R) fc None m (seg_rom usegs)).
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Section Stmts.
  Variable dt_ok : fmem -> Z -> Z -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition huf_rdt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DT W S mtl : Z) (src : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : fmem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ 0 <= r < 2^64
      /\ (r < 2^64 - 119 -> dt_ok m' DT mtl).

  Definition huf_rdt_stmt (E : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DT W S mtl flags : Z) (src : list Z) (jdt jw : list byte) (lo : Z),
    (* [comment removed for export] *)
    1 <= mtl <= 12 ->
    rw_cells usegs m DT [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt] ->
    rw_cells usegs m W [CB 8704 jw] ->
    bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S ->
    (* [comment removed for export] *)
    0 < DT -> DT mod 8 = 0 -> 0 < W -> W mod 8 = 0 -> 0 < S ->
    DT + DTABLE_BYTES mtl <= lo -> W + 8704 <= lo -> S + zlen src <= lo ->
    (DT + DTABLE_BYTES mtl <= W \/ W + 8704 <= DT) ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (W + 8704 <= S \/ S + zlen src <= W) ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HUF_RDT_STACK -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned sp <= 2^47 ->
    mem_inv usegs m ->
    0 <= flags < 64 ->
    a0 = Z_to_bv 64 DT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen src) -> a3 = Z_to_bv 64 W -> a4 = Z_to_bv 64 8704 ->
    a5 = Z_to_bv 64 flags ->
    evt usegs (huf_rdt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition huf_dec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST dcap : Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - HUF_DEC_STACK, bv_unsigned sp); (DST, DST + dcap)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp).

  Definition huf_dec_stmt (E : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DST dcap S DT mtl flags : Z) (src : list Z) (jd : list byte) (lo : Z),
    1 <= mtl <= 12 -> dt_ok m DT mtl ->
    (* [comment removed for export] *)
    ((DST = 0 /\ dcap = 0) \/ (0 < DST /\ DST mod 8 = 0 /\ rw_cells usegs m DST [CB (Z.to_nat dcap) jd])) ->
    0 <= dcap < 2^32 ->
    bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> 0 < S ->
    0 < DT -> DT mod 8 = 0 ->
    DT + DTABLE_BYTES mtl <= lo -> DST + dcap <= lo -> S + zlen src <= lo ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HUF_DEC_STACK -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned sp <= 2^47 ->
    mem_inv usegs m ->
    0 <= flags < 64 ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    a5 = Z_to_bv 64 flags ->
    evt usegs (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).
End Stmts.
End CANSEC1.
