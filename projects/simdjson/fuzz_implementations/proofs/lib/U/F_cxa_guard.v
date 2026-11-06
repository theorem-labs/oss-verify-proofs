(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).

Definition F_CXA_GUARD_ACQUIRE : Z := 0x621bc.
Definition F_CXA_GUARD_RELEASE : Z := 0x6220c.

Definition guard_acquire_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (G : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(G, G + 2)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' G [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 2)].

Lemma guard_acquire_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (G : Z),
  rw_cells usegs m G [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  a0 = Z_to_bv 64 G -> (0 <= G) -> (G + 2 < 2^64) ->
  mem_inv usegs m ->
  evt usegs (guard_acquire_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc G m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_CXA_GUARD_ACQUIRE) fc None m (seg_rom usegs)).
Proof.
  intros until G. intros GC -> G0 GHI MI.
  unfold F_CXA_GUARD_ACQUIRE in *.
  pose proof (munch_refl [(G, G + 2)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  lstep.
  change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep.
  lstep. if_true.
  lstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep. lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep.
  lstep. lstep.
  try match goal with |- context [Z_to_bv 64 (0 + -1)] => change (Z_to_bv 64 (0 + -1)) with (Z_to_bv 64 (-1) : word) end.
  lstep.
  apply evt_done. unfold guard_acquire_post. sys_finish.
Qed.

Definition guard_release_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (G : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(G, G + 2)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' G [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Lemma guard_release_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (G : Z) (g i : byte),
  rw_cells usegs m G [C1 g; C1 i] ->
  a0 = Z_to_bv 64 G -> (0 <= G) -> (G + 2 < 2^64) ->
  mem_inv usegs m ->
  evt usegs (guard_release_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc G m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_CXA_GUARD_RELEASE) fc None m (seg_rom usegs)).
Proof.
  intros until i. intros GC -> G0 GHI MI.
  unfold F_CXA_GUARD_RELEASE in *.
  pose proof (munch_refl [(G, G + 2)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  lstep.
  lstep.
  lstep. lstep.
  lstep.
  apply evt_done. unfold guard_release_post. sys_finish.
Qed.
