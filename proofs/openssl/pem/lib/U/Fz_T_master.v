(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Notation MK_INIT := (0x32dea0)%Z (only parsing).
Notation MK_ONCE := (0x32dea4)%Z (only parsing).
Notation MK_KEY := (0x32dea8)%Z (only parsing).
Notation MK_CLEAN := (0xe3f98)%Z (only parsing).       (* [comment removed for export] *)

Definition T_init_master_key_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w tsd : word) (ib : byte),
    rw_cells usegs m MK_INIT [C1 ib] ->
    rw_cells usegs m MK_KEY [C4 kold] ->
    rw_cells usegs m (bv_unsigned tp + -88) [C8 tsd] -> 88 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells usegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells usegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells usegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 144 ->
    KEY_LOCK + 12 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= MK_INIT \/ MK_KEY + 4 <= bv_unsigned tp + -88) ->                     (* [comment removed for export] *)
    (bv_unsigned tp + -80 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned tp + -88) ->                     (* [comment removed for export] *)
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (MK_INIT, MK_INIT + 1); (MK_KEY, MK_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' MK_INIT [C1 (Z_to_bv 8 1)]
                 /\ rw_cells usegs m' MK_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells usegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells usegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells usegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3d90) fc None m (seg_rom usegs)).

Theorem T_init_master_key_proof : T_init_master_key_stmt.
Proof.
  unfold T_init_master_key_stmt. intros until ib. intros IC KC TC TP TV NK HNK KL KJ PROBE CASE ST LO0 LO S3 S4 S6 S7 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (MK_INIT, MK_INIT + 1); (MK_KEY, MK_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 11 ths.
  tcall (T_init_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w tsd).
  1-20: first [eassumption | lia].
  cbv delta [mkR].
  ths. th_if_lit.
  do 2 ths.
  do 5 ths.
  th_release FR (bv_unsigned sp).
  change (if bv_eqb (Z_to_bv 64 933784) (Z_to_bv 64 0) then Z_to_bv 64 2875164 else Z_to_bv 64 933784) with (Z_to_bv 64 933784) in POST.
  finish.
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_once Fz_T_sa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t_scale8 : forall i, 0 <= i < 2 ^ 60 -> bv_unsigned (Z_to_bv 64 i) ≪ 3 = 8 * i.
Proof. intros i Hi. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Definition T_get_local_ex_found_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK SA LV NODES : Z) (pad top ne v : word),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells usegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
    ro_cells usegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 -> SA mod 8 = 0 ->
    ro_cells usegs m SA (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) -> bv_unsigned ne <> 0 -> 0 <= LV < 2 -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    ro_cells usegs m NODES [C8 v] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 ->
    MK_KEY + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * id + 8 <= lo \/ bv_unsigned sp <= MK + 8 * id) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' a4' a5' a6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 v a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3cc0) fc None m (seg_rom usegs)).

Theorem T_get_local_ex_found_proof : T_get_local_ex_found_stmt.
Proof.
  unfold T_get_local_ex_found_stmt, sa_hdr. intros until v.
  intros -> HID -> OC KC HK TS TP T0 MKC HMK MKA SAC HSA SAA HC HNE HLV HNO NAL VC ST LO0 LO S0 S1 S2 S3 S4 S5 MI.
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
  replace NODES with (NODES + 8 * 0) in VC, S5 by lia.
  tcall (T_sa_get_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 LV NODES pad top ne v).
  1-17: first [eassumption | reflexivity | lia].
  finish.
Qed.

(* [comment removed for export] *)
Ltac glx_prefix ST lo T k mkv :=
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST;
  do 7 ths;
  do 3 ths; th_if_lit;
  do 7 ths;
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); [ first [eassumption | lia] .. | ];
  cbv beta delta [mkR];
  do 2 ths;
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let K := fresh "K8" in destruct c eqn:K; [ zify_cond K; exfalso; lia | ] end;
  ths; th_if_lit;
  do 2 ths;
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k mkv); [ first [eassumption | lia] .. | ];
  cbv beta delta [mkR].

(* [comment removed for export] *)
Definition T_get_local_ex_notable_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id : Z),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells usegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 ->
    MK_KEY + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 z64 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3cc0) fc None m (seg_rom usegs)).

Theorem T_get_local_ex_notable_proof : T_get_local_ex_notable_stmt.
Proof.
  unfold T_get_local_ex_notable_stmt. intros until id.
  intros -> HID -> OC KC HK TS TP T0 MKC ST LO0 LO S0 S1 S2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * k) in *.
  glx_prefix ST lo T k (Z_to_bv 64 0).
  ths. th_if_lit.
  do 8 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_get_local_ex_noarray_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK : Z),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells usegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
    ro_cells usegs m (MK + 8 * id) [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 ->
    MK_KEY + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * id + 8 <= lo \/ bv_unsigned sp <= MK + 8 * id) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 z64 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3cc0) fc None m (seg_rom usegs)).

Theorem T_get_local_ex_noarray_proof : T_get_local_ex_noarray_stmt.
Proof.
  unfold T_get_local_ex_noarray_stmt. intros until MK.
  intros -> HID -> OC KC HK TS TP T0 MKC HMK MKA SAC ST LO0 LO S0 S1 S2 S3 MI.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * k) in *. set (Pi := MK + 8 * id) in *.
  glx_prefix ST lo T k (Z_to_bv 64 MK).
  ths. if_cases K9; zify_cond K9. { exfalso. lia. }
  do 2 ths. rewrite (t_scale8 id) by lia. fold Pi.
  assert (HPi : 0 <= Pi) by (unfold Pi; lia).
  assert (HPi8 : Pi mod 8 = 0) by (unfold Pi; lia). assert (HPiL : 8 * id < Pi) by (unfold Pi; lia).
  clearbody Pi.
  ths. if_cases KW; zify_cond KW. { exfalso. lia. }
  ths. ths. ubs_if.
  do 2 ths. th_if_lit.
  do 8 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_set_local_ex_steady_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK SA NODES : Z) (pad top ne oldv : word),
    a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells usegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells usegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
    ro_cells usegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 -> SA mod 8 = 0 ->
    rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
    rw_cells usegs m NODES [C8 oldv] ->
    (SA + 32 <= NODES \/ NODES + 8 <= SA) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    MK_KEY + 4 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * id + 8 <= lo \/ bv_unsigned sp <= MK + 8 * id) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' : word) (top' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (NODES, NODES + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a2 oldv)) (Z_to_bv 64 NODES))
                 /\ rw_cells usegs m' NODES [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3ddc) fc None m (seg_rom usegs)).

Theorem T_set_local_ex_steady_proof : T_set_local_ex_steady_stmt.
Proof.
  unfold T_set_local_ex_steady_stmt, sa_hdr. intros until oldv.
  intros -> HID -> OC KC HK TS TP T0 MKC HMK MKA SAC HSA HSAA HC HNO NAL VC SEPN ST LO0 LO S0 S1 S2 S3 S4 S5 MI.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (NODES, NODES + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * k) in *. set (Pi := MK + 8 * id) in *.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 ths.
  do 4 ths. th_if_lit.
  do 7 ths.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); [ first [eassumption | lia] .. | ].
  cbv beta delta [mkR].
  do 2 ths.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let K := fresh "K8" in destruct c eqn:K; [ zify_cond K; exfalso; lia | ] end.
  ths. th_if_lit.
  do 3 ths.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k (Z_to_bv 64 MK)); [ first [eassumption | lia] .. | ].
  cbv beta delta [mkR].
  do 2 ths. if_cases K9; zify_cond K9. { exfalso. lia. }
  do 2 ths. rewrite (t_scale8 id) by lia. fold Pi.
  assert (HPi : 0 <= Pi) by (unfold Pi; lia).
  assert (HPi8 : Pi mod 8 = 0) by (unfold Pi; lia). assert (HPiL : 8 * id < Pi) by (unfold Pi; lia).
  clearbody Pi.
  ths. if_cases KW; zify_cond KW. { exfalso. lia. }
  ths. ths. ubs_if.
  do 2 ths. if_cases K10; zify_cond K10. { exfalso. lia. }
  ths. if_cases KN; zify_cond KN. 2:{ exfalso. lia. }
  do 2 ths. do 8 ths.
  th_release FR (bv_unsigned sp).
  ths.
  replace NODES with (NODES + 8 * 0) in VC, S5, SEPN by lia.
  tcall (T_sa_set_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SA 0 NODES pad top ne oldv).
  1-16: first [eassumption | reflexivity | lia].
  replace (NODES + 8 * 0) with NODES in * by lia.
  finish; eassumption.
Qed.
