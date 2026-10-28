(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Notation DTOR_KEY := (0x31d4d0)%Z (only parsing).          (* [comment removed for export] *)
Notation DTOR_FN := (0xe2438)%Z (only parsing).            (* [comment removed for export] *)

Definition T_init_thread_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w tsd : word),
    rw_cells usegs m DTOR_KEY [C4 kold] ->
    rw_cells usegs m (bv_unsigned tp + -88) [C8 tsd] -> 88 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells usegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells usegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells usegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 128 ->
    KEY_LOCK + 12 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= DTOR_KEY \/ DTOR_KEY + 4 <= bv_unsigned tp + -88) ->                  (* [comment removed for export] *)
    (bv_unsigned tp + -80 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned tp + -88) ->                     (* [comment removed for export] *)
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' DTOR_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells usegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells usegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 DTOR_FN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe2400) fc None m (seg_rom usegs)).

Theorem T_init_thread_proof : T_init_thread_stmt.
Proof.
  unfold T_init_thread_stmt. intros until tsd. intros KC TC TP TV NK HNK KL KJ PROBE CASE ST LO0 LO S3 S4 S6 S7 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 ths.
  tcall (T_init_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w tsd).
  1-20: first [eassumption | lia].
  cbv beta delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  change (if bv_eqb (Z_to_bv 64 927888) (Z_to_bv 64 0) then Z_to_bv 64 2875164 else Z_to_bv 64 927888) with (Z_to_bv 64 927888) in POST.
  finish.
Qed.
