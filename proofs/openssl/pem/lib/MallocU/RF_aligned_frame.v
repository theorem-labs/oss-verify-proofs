(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_enframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RMALLOC_REPLACED : Z := 0x351010.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ra_frame (j8 : list byte) (ra s0 s1 : word) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

Definition rapro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo len : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j8,
    ms' = MS (mkR (Z_to_bv 64 0x2b24cc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 64) (Z_to_bv 64 len) (Z_to_bv 64 (len + 48))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b14ec) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1)
    /\ stk usegs m' lo (bv_unsigned sp + -32)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma raligned_prologue : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo len : Z),
  a0 = Z_to_bv 64 64 -> a1 = Z_to_bv 64 len -> 0 <= len < 2^32 ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  stk usegs m lo (bv_unsigned sp) -> 0x353000 <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
  evt usegs (rapro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo len m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b242c) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until len. intros A0 A1 N REPL ST ILO LO MI. subst a0 a1. unfold RMALLOC_REPLACED in REPL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 32%nat ST. step. step. step.
  (* [comment removed for export] *)
  step. step. step. if_cases K0; zify_cond K0. { exfalso. apply K0. reflexivity. }
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1. { exfalso. apply K1. reflexivity. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }
  (* [comment removed for export] *)
  step. step. step. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  (* [comment removed for export] *)
  step. step. step. step. step.
  replace (64 + len + -16) with (len + 48) by lia.
  apply evt_done. unfold rapro_post, ra_frame. do 16 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

(* [comment removed for export] *)
Definition raepi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp).

Lemma raligned_epilogue : forall (x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (j8 : list byte),
  rw_cells usegs m (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1) ->
  stk usegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
  evt usegs (raepi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2498) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until j8. intros FR ST LO MI. unfold ra_frame in FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold raepi_post. do 14 eexists. split; [reflexivity| exact ST].
Qed.
End WithCeiling0.
