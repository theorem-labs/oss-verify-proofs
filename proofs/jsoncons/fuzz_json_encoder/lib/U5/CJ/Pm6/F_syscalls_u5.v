(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ITree Nodes SysStep.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition rsegs := Ubsan.Ubsan_loaded_segments.

Definition sysret_entry := 0xadad4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt rsegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xadad4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition got_ssp := 0xca220%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xfd280%Z.
End CEIL_WRAP_1.
   (* [comment removed for export] *)
