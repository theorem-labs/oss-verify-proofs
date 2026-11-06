(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Th_tsd Th_key Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition T_get_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k : Z) (v : word),
    ro_cells psegs m (bv_unsigned a0) [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp ->
    ro_cells psegs m (T + 8 * k) [C8 v] -> 0 <= T ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t1' a1' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 v a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xdee60) fc None m (seg_rom psegs)).

Theorem T_get_local_proof : T_get_local_stmt.
Proof.
  unfold T_get_local_stmt. intros until v. intros KC HK TS TP VC T0 ST LO0 LO S1 S2 S3 MI.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  set (Pk := T + 8 * k) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  ths. rewrite (t_sx32_small k) by lia.
  do 3 ths.
  release_frame FR ST (bv_unsigned sp).
  ths.
  eapply evt_mono; [eapply (getspecific_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T k v); first [reflexivity | eassumption | lia] |].
  intros ms' [a1' ->]. do 2 eexists. exists m1.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(* [comment removed for export] *)
Definition T_set_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k : Z) (old : word) (u : byte),
    ro_cells psegs m (bv_unsigned a0) [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 150 <= bv_unsigned tp ->
    rw_cells psegs m (T + 8 * k) [C8 old] -> 0 <= T ->
    rw_cells psegs m (bv_unsigned tp + -150) [C1 u] ->
    (T + 8 * k + 8 <= bv_unsigned tp + -150 \/ bv_unsigned tp + -149 <= T + 8 * k) ->
    (T + 8 * k + 8 <= bv_unsigned tp + -88 \/ bv_unsigned tp + -80 <= T + 8 * k) ->
    (T + 8 * k + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= T + 8 * k) ->
    (bv_unsigned tp + -149 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= bv_unsigned tp + -150) ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -150) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (a2' a3' : word) (u' : byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp)
                 /\ ro_cells psegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 k)]
                 /\ ro_cells psegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)]
                 /\ rw_cells psegs m' (T + 8 * k) [C8 a1]
                 /\ rw_cells psegs m' (bv_unsigned tp + -150) [C1 u'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xdee88) fc None m (seg_rom psegs)).

Theorem T_set_local_proof : T_set_local_stmt.
Proof.
  unfold T_set_local_stmt. intros until u. intros KC HK TS TP VC T0 UC S1 S2 S3 S4 ST LO0 LO S5 S6 S7 MI.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  set (Pk := T + 8 * k) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  ths. rewrite (t_sx32_small k) by lia.
  ths.
  call (setspecific_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T k old u).
  1-10: first [reflexivity | eassumption | lia].
  cbv delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  finish. eassumption.
Qed.

(* [comment removed for export] *)
Definition T_init_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w tsd : word),
    rw_cells psegs m (bv_unsigned a0) [C4 kold] ->
    rw_cells psegs m (bv_unsigned tp + -88) [C8 tsd] -> 88 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells psegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells psegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells psegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells psegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + 4 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned a0) ->
    KEY_LOCK + 12 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned tp + -88) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp)
                 /\ rw_cells psegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 j)]
                 /\ rw_cells psegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells psegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells psegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells psegs m' (KEYS + 8 * j) [C8 (if bv_eqb a1 z64 then Z_to_bv 64 NODTOR else a1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xdee34) fc None m (seg_rom psegs)).

Theorem T_init_local_proof : T_init_local_stmt.
Proof.
  unfold T_init_local_stmt. intros until tsd. intros KC TC TP TV NK HNK KL KJ PROBE CASE ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  pose proof key_create_proof as KCP. unfold key_create_stmt in KCP.
  specialize (KCP (Z_to_bv 64 0xdee4c) (Z_to_bv 64 (bv_unsigned sp + -16))).
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in KCP by lia.
  call (KCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w tsd).
  1-20: first [eassumption | lia].
  cbv delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.
