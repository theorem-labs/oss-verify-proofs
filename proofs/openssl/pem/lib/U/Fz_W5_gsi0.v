(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_errno. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base Fz_W5_glx Fz_W5_gsi.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).


Definition T_get_state_steady0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA NODES E : Z) (od pad top ne : word),
    a0 = Z_to_bv 64 0 -> 164 <= bv_unsigned tp ->
    (* [comment removed for export] *)
    rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
    (* [comment removed for export] *)
    ro_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
    ro_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 -> SA mod 8 = 0 ->
    ro_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    ro_cells usegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 -> 0 < E -> E + 904 < 2 ^ 64 ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - GSI_STACK ->
    0x32dea8 + 4 <= lo -> IC_S + 104 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * 3 + 8 <= lo \/ bv_unsigned sp <= MK + 8 * 3) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 E) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - GSI_STACK, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_GSI) fc None m (seg_rom usegs)).

Theorem T_get_state_steady0_proof : T_get_state_steady0_stmt.
Proof.
  unfold T_get_state_steady0_stmt, GSI_STACK, FZ_GSI, sa_hdr. intros until ne.
  intros -> TP STOP ONCE OD OC KC HK TS T0 MKC HMK MKA SAC HSA SAA HC HNO NOA VC NE0 E0 EHI ST GLO LO S6 S7 S0 S1 S2 S3 S4 MI.
  unfold IC_S, GLOBALS_TOP in *.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(bv_unsigned sp - (48 + 96), bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * k) in *. set (P3 := MK + 8 * 3) in *. set (EA := bv_unsigned tp + -164) in *. set (TA := bv_unsigned tp + -88) in *.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  do 8 ths.
  ths. th_if_lit.
  ths.
  (* [comment removed for export] *)
  ths. ths. ths.
  tcall (init_crypto_base_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo od).
  all: try first [eassumption | reflexivity | unfold IC_S, IC_BASE_STACK, GLOBALS_TOP; lia].
  cbv beta delta [mkR].
  ths. th_if_lit.
  (* [comment removed for export] *)
  ths. ths. ths.
  pose proof T_get_local_ex_steady_proof as GLX. unfold T_get_local_ex_steady_stmt, sa_hdr in GLX.
  tcall (GLX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k 3 MK SA NODES E pad top ne).
  all: try first [eassumption | reflexivity | lia].
  clear GLX. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths.
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths.
  ths. if_cases K2; zify_cond K2. 2: { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  (* [comment removed for export] *)
  ths. th_if_lit.
  do 6 ths.
  th_release FR (bv_unsigned sp).
  ths. ths.
  finish.
Qed.
End WithCeiling0.
