(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition DBOX_ENTRY : Z := 0x40640.
Definition FMT_ENTRY : Z := 0x407f8.
Definition DBOX_STACK : Z := 96.
Definition FMT_STACK : Z := 80.

Definition dbox_post (ra : word) (p : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo NB : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (n e : Z) (nb : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(p - 96, p); (p + 8, p + 16); (NB, NB + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo p
    /\ 1 <= n <= 20 /\ SF_EMIN <= e <= SF_EMAX
    /\ rw_cells usegs m' (p + 8) [C4 (Z_to_bv 64 (e mod 4294967296)); C4 (Z_to_bv 64 n)]
    /\ u8arr usegs m' NB nb /\ length nb = 40%nat.

Definition dbox_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo NB sg : Z) (nb : list byte) (c0 c1 : word),
  stk usegs m lo p -> lo <= p - DBOX_STACK -> GLOBALS_TOP <= lo -> mem_inv usegs m ->
  p + 32 <= NB -> NB + 40 < 2^63 -> 0 <= sg <= 1 ->
  rw_cells usegs m (p + 8) [C4 c0; C4 c1] -> u8arr usegs m NB nb -> length nb = 40%nat ->
  evt usegs (dbox_post ra p gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB m)
      (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (p + 8)) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DBOX_ENTRY) fc None m (seg_rom usegs)).

Definition fmt_post (ra : word) (p : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo NB sg : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (e : Z) (nb : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(p - 80, p); (NB, NB + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo p
    /\ NB + sg < e <= NB + sg + 26
    /\ u8arr usegs m' NB nb /\ length nb = 40%nat.

Definition fmt_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo NB sg n e : Z) (nb : list byte),
  stk usegs m lo p -> lo <= p - FMT_STACK -> GLOBALS_TOP <= lo -> mem_inv usegs m ->
  p <= NB -> NB + 40 < 2^63 -> 0 <= sg <= 1 -> 1 <= n <= 20 -> SF_EMIN <= e <= SF_EMAX ->
  u8arr usegs m NB nb -> length nb = 40%nat ->
  evt usegs (fmt_post ra p gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB sg m)
      (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) (Z_to_bv 64 e) (Z_to_bv 64 (-4)) (Z_to_bv 64 15) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FMT_ENTRY) fc None m (seg_rom usegs)).
