(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Exit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Definition RATEXIT : Z := 0xbff40.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (func : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x10f5d8, 0x10f5f8); (0x10f6f0, 0x10f6f8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0x10f5d4 [C4 z64; C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m' 0x10f5e0 [C8 (Z_to_bv 64 0x10f5e8); C8 z64; C8 (Z_to_bv 64 RAEX_CALL)]
    /\ rw_cells usegs m' 0x10f6f0 [C8 (Z_to_bv 64 func)].

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m 0x10f818 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells usegs m 0x10f5d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m 0x10f5d4 [C4 z64; C4 z64] ->
  rw_cells usegs m 0x10f5e0 [C8 z64; C8 z64; C8 z64] ->
  rw_cells usegs m 0x10f6f0 [C8 z64] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 func -> (0 <= func < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x111000 <= lo)%Z ->
  evt usegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATEXIT) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH X1 X2 X3 X4 MI -> Hf LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RATEXIT, RAEX_CALL in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x10f5d8, 0x10f5f8); (0x10f6f0, 0x10f6f8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0xd143c%Z. lock_ret.
  lstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep. lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep.
  lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. lstep. if_true.
  steps_to 0xbffdc%Z.
  lstep. astep. unlock_ret.
  steps_to 0xc0000%Z.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold atexit_post. sys_finish.
Time Qed.
