(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_sa Fz_T_master.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition T_get_local_ex_zero_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK SA NODES : Z) (pad top ne : word),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
    ro_cells usegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 -> SA mod 8 = 0 ->
    ro_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    ro_cells usegs m NODES [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 ->
    0x32dea8 + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * id + 8 <= lo \/ bv_unsigned sp <= MK + 8 * id) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' a4' a5' a6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 z64 a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3cc0) fc None m (seg_rom usegs)).

Theorem T_get_local_ex_zero_proof : T_get_local_ex_zero_stmt.
Proof.
  unfold T_get_local_ex_zero_stmt, sa_hdr. intros until ne.
  intros -> HID -> OC KC HK TS TP T0 MKC HMK MKA SAC HSA SAA HC HNO NAL VC ST LO0 LO S0 S1 S2 S3 S4 S5 MI.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  set (Pk := T + 8 * k) in *. set (Pi := MK + 8 * id) in *.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 ths.
  do 3 ths. th_if_lit.
  do 7 ths.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  1-6: first [eassumption | lia].
  cbv beta delta [mkR].
  do 2 ths. if_cases K8; zify_cond K8. { exfalso. lia. }
  ths. th_if_lit.
  do 2 ths.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k (Z_to_bv 64 MK)).
  1-15: first [eassumption | lia | (rewrite unsigned_lit by lia; lia)].
  cbv beta delta [mkR].
  ths. if_cases K9; zify_cond K9. { exfalso. lia. }
  do 2 ths. rewrite (t_scale8 id) by lia. fold Pi.
  assert (HPi : 0 <= Pi) by (unfold Pi; lia).
  assert (HPi8 : Pi mod 8 = 0) by (unfold Pi; lia). assert (HPiL : 8 * id < Pi) by (unfold Pi; lia).
  clearbody Pi.
  ths. if_cases KW; zify_cond KW. { exfalso. lia. }
  ths. ths. ubs_if.
  do 2 ths. if_cases K10; zify_cond K10. { exfalso. lia. }
  ths. if_cases KN; zify_cond KN. { exfalso. lia. }
  do 7 ths.
  th_release FR (bv_unsigned sp).
  ths.
  destruct (Z.eq_dec (bv_unsigned ne) 0) as [E0|NE0].
  - assert (EN : ne = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned ne); rewrite E0; reflexivity). subst ne.
    lazymatch goal with H : ro_cells usegs _ SA _ |- _ => rename H into HSAc end.
    unfold sa_hdr in HSAc.
    tcall (T_sa_get_empty_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (Z_to_bv 64 1) pad top (Z_to_bv 64 NODES)).
    1-8: first [eassumption | lia | (unfold sa_hdr; eassumption)].
    finish.
  - replace NODES with (NODES + 8 * 0) in VC, S5 by lia.
    tcall (T_sa_get_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 1 NODES pad top ne z64).
    1-17: first [eassumption | reflexivity | lia].
    finish.
Qed.
