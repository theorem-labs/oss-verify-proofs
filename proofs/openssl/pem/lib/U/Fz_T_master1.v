(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_master.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition T_get_local_ex_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo id nk j : Z) (sh kold w tsd oldcb canary : word) (ib : byte),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    rw_cells usegs m MK_ONCE [C4 z64] ->
    rw_cells usegs m MK_INIT [C1 ib] ->
    rw_cells usegs m MK_KEY [C4 kold] ->
    ssp_cells m canary ->
    rw_cells usegs m (bv_unsigned tp + -96) [C8 oldcb] ->
    rw_cells usegs m (bv_unsigned tp + -88) [C8 tsd] -> 96 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells usegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells usegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells usegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    ro_cells usegs m (TSD_MAIN + 8 * j) [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 320 ->
    TSD_MAIN + 1024 <= lo ->                                                        (* [comment removed for export] *)
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -96) ->
    (bv_unsigned tp + -80 <= MK_INIT \/ MK_KEY + 4 <= bv_unsigned tp + -96) ->           (* [comment removed for export] *)
    (bv_unsigned tp + -80 <= KEYS \/ TSD_MAIN + 1024 <= bv_unsigned tp + -96) ->           (* [comment removed for export] *)
    (got_ssp + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -80 <= got_ssp) ->            (* [comment removed for export] *)
    (ssp_guard + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -80 <= ssp_guard) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 z64 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (MK_INIT, MK_INIT + 12); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -96, bv_unsigned tp + -80)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
                 /\ rw_cells usegs m' MK_ONCE [C4 (Z_to_bv 64 2)]
                 /\ rw_cells usegs m' MK_INIT [C1 (Z_to_bv 8 1)]
                 /\ rw_cells usegs m' MK_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' (bv_unsigned tp + -96) [C8 oldcb]
                 /\ rw_cells usegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells usegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells usegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3cc0) fc None m (seg_rom usegs)).

Theorem T_get_local_ex_first_proof : T_get_local_ex_first_stmt.
Proof.
  unfold T_get_local_ex_first_stmt. intros until ib.
  intros -> HID -> OC IC KC [GOT GU] CB TC TP TV NK HNK KL KJ PROBE CASE SLOT ST LO0 LO SD S1 S2 S2b S2c S2d MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (MK_INIT, MK_INIT + 12); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -96, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold got_ssp, ssp_guard in *.
  set (Pj := TSD_MAIN + 8 * j) in *.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 ths.
  do 3 ths. th_if_lit.
  do 7 ths.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe3d90 oldcb canary).
  1-21: first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit.
  destruct PC0 as [GOT' GU']. clear GOT GU. unfold once_full_cells in PC3.
  tcall (T_init_master_key_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w tsd ib).
  1-19: first [eassumption | lia].
  cbv beta delta [mkR]. unfold ONCE_RET_INIT. th_ret_lit.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -48) 3333796 (Z_to_bv 64 (bv_unsigned sp + -48 + -128)) oldcb canary
              (Z_to_bv 64 933140) sp (Z_to_bv 64 0) (Z_to_bv 64 id) (Z_to_bv 64 3333792) s4 s5 s6 x3).
  1-22: first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR].
  do 2 ths.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let K := fresh "K8" in destruct c eqn:K; [ zify_cond K; exfalso; lia | ] end.
  ths. th_if_lit.
  do 2 ths.
  pose proof (proj1 PC5) as KRO. pose proof (proj1 PC6) as TRO.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 j (Z_to_bv 64 0)).
  1-15: first [eassumption | lia].
  cbv beta delta [mkR].
  ths. th_if_lit.
  do 8 ths.
  th_release FR (bv_unsigned sp).
  finish. split; [exact GOT' | exact GU'].
Qed.
