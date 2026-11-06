(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Th_key Fz_T_kit Fz_T_local Fz_T_once Fz_T_sa Fz_T_master.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition T_get_local_ex_steady_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK SA NODES E : Z) (pad top ne : word),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells psegs m 0x2e8704 [C4 (Z_to_bv 64 2)] ->
    ro_cells psegs m 0x2e8708 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells psegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 ->
    ro_cells psegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 ->
    ro_cells psegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 ->
    ro_cells psegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 ->
    0x2e8708 + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * id + 8 <= lo \/ bv_unsigned sp <= MK + 8 * id) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t1' a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 E) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xdf11c) fc None m (seg_rom psegs)).

Theorem T_get_local_ex_steady_proof : T_get_local_ex_steady_stmt.
Proof.
  unfold T_get_local_ex_steady_stmt, sa_hdr. intros until ne.
  intros -> HID -> OC KC HK TS TP T0 MKC HMK SAC HSA HC HNO VC NE0 ST LO0 LO S0 S1 S2 S3 S4 S5 MI.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
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
  1-13: first [eassumption | lia].
  cbv beta delta [mkR].
  ths. if_cases K9; zify_cond K9. { exfalso. lia. }
  do 2 ths. rewrite (t_scale8 id) by lia. fold Pi.
  assert (HPi : 0 <= Pi) by (unfold Pi; lia). clearbody Pi.
  do 2 ths. if_cases K10; zify_cond K10. { exfalso. lia. }
  do 7 ths.
  th_release FR (bv_unsigned sp).
  ths.
  replace NODES with (NODES + 8 * 0) in VC, S5 by lia.
  tcall (T_sa_get_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 1 NODES pad top ne (Z_to_bv 64 E)).
  1-15: first [eassumption | reflexivity | lia].
  finish.
Qed.
