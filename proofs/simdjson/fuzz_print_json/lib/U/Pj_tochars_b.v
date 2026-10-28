(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout F_memcpy F_memset Sj_kit F_memmove_t2 F_memmove_back Pj_num_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition arr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (L : nat) (wlo whi : Z) (r0 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m' bs',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(wlo, whi)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A bs' /\ length bs' = L.

Lemma arr_memcpy : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A k N Src : Z) (bs src : list byte),
  u8arr usegs m A bs -> (0 <= k)%Z -> (0 <= N)%Z -> (k + N <= Z.of_nat (length bs))%Z ->
  bytes_at usegs m Src src -> length src = Z.to_nat N ->
  (Src + N <= A + k \/ A + k + N <= Src)%Z -> (0 <= Src < 2^64)%Z -> (0 <= A)%Z -> (A + Z.of_nat (length bs) < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (arr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (length bs) (A + k) (A + k + N) (A + k) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + k)) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xcfe78) fc None m (seg_rom usegs)).
Proof.
  intros until src. intros UA Hk HN HL SRC LS SEP HS HA HB MI.
  destruct (u8arr_range_split usegs m A bs (Z.to_nat k) (Z.to_nat (k + N)) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  replace (Z.of_nat (Z.to_nat k)) with k in * by lia.
  replace (Z.of_nat (Z.to_nat (k + N))) with (k + N)%Z in * by lia.
  replace (Z.to_nat (k + N) - Z.to_nat k)%nat with (Z.to_nat N) in * by lia.
  pose proof (munch_refl [(A + k, A + k + N)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (memcpy_callZ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (A + k)%Z Src N src mid).
  1-8: try first [exact SRC | exact LS | exact MID | exact SEP | exact MI | lia].
  destruct (u8arr_range_join usegs _ A b1 (Z.to_nat N) src b3 U1) as (bs' & LB & UB).
  { rewrite L1. replace (Z.of_nat (Z.to_nat k)) with k by lia. exact PC. }
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat k) + Z.of_nat (Z.to_nat N))%Z with (A + (k + N))%Z by lia. exact U3. }
  apply evt_done. unfold arr_post.
  do 14 eexists. eexists. exists bs'.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact UB|]. lia.
Qed.

Lemma arr_memset : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A k N C : Z) (bs : list byte),
  u8arr usegs m A bs -> (0 <= k)%Z -> (0 <= N)%Z -> (k + N <= Z.of_nat (length bs))%Z ->
  (0 <= C < 2^64)%Z -> (0 <= A)%Z -> (A + Z.of_nat (length bs) < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (arr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (length bs) (A + k) (A + k + N) (A + k) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + k)) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd03f8) fc None m (seg_rom usegs)).
Proof.
  intros until bs. intros UA Hk HN HL HC HA HB MI.
  destruct (u8arr_range_split usegs m A bs (Z.to_nat k) (Z.to_nat (k + N)) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  replace (Z.of_nat (Z.to_nat k)) with k in * by lia.
  replace (Z.of_nat (Z.to_nat (k + N))) with (k + N)%Z in * by lia.
  replace (Z.to_nat (k + N) - Z.to_nat k)%nat with (Z.to_nat N) in * by lia.
  pose proof (munch_refl [(A + k, A + k + N)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (memset_callZ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (A + k)%Z C N mid).
  1-6: try first [exact MID | exact MI | lia].
  destruct (u8arr_range_join usegs _ A b1 (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N)) b3 U1) as (bs' & LB & UB).
  { rewrite L1. replace (Z.of_nat (Z.to_nat k)) with k by lia. exact POST. }
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat k) + Z.of_nat (Z.to_nat N))%Z with (A + (k + N))%Z by lia. exact U3. }
  apply evt_done. unfold arr_post.
  do 14 eexists. eexists. exists bs'.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact UB|]. lia.
Qed.

Lemma arr_memmove1 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A k N : Z) (bs : list byte),
  u8arr usegs m A bs -> (0 <= k)%Z -> (2 <= N < 2^62)%Z -> (k + N + 1 <= Z.of_nat (length bs))%Z ->
  (0 <= A)%Z -> (A + Z.of_nat (length bs) < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (arr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (length bs) (A + k + 1) (A + k + 1 + N) (A + k + 1) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + k + 1)) (Z_to_bv 64 (A + k)) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd027c) fc None m (seg_rom usegs)).
Proof.
  intros until bs. intros UA Hk HN HL HA HB MI.
  destruct (u8arr_range_split usegs m A bs (Z.to_nat k) (Z.to_nat (k + N + 1)) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  replace (Z.of_nat (Z.to_nat k)) with k in * by lia.
  replace (Z.of_nat (Z.to_nat (k + N + 1))) with (k + N + 1)%Z in * by lia.
  replace (Z.to_nat (k + N + 1) - Z.to_nat k)%nat with (S (Z.to_nat N)) in * by lia.
  pose proof (u8arr_of_rw_cells usegs _ _ _ _ MID) as UM.

  assert (EM : mid = removelast mid ++ [last mid (Z_to_bv 8 0)]).
  { apply app_removelast_last. intros ->. cbn in L2. lia. }
  assert (LR : length (removelast mid) = Z.to_nat N).
  { rewrite EM in L2. rewrite length_app in L2. cbn [length] in L2. lia. }
  rewrite EM in UM.
  pose proof (munch_refl [(A + k + 1, A + k + 1 + N)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (memmove_right1_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + k + 1)) (Z_to_bv 64 (A + k)) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
          F fc m (A + k)%Z (removelast mid) (last mid (Z_to_bv 8 0))).
  1-8: try first [reflexivity | exact UM | exact MI | rewrite LR; f_equal; lia | rewrite LR; lia].
  pose proof (rw_cells_of_u8arr usegs _ _ _ POST) as PC. rewrite right1_bytes_length, LR in PC.
  destruct (u8arr_range_join usegs _ A b1 (S (Z.to_nat N)) _ b3 U1 ltac:(rewrite L1; replace (Z.of_nat (Z.to_nat k)) with k by lia; exact PC)) as (bs' & LB & UB).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat k) + Z.of_nat (S (Z.to_nat N)))%Z with (A + (k + N + 1))%Z by lia. exact U3. }
  apply evt_done. unfold arr_post.
  do 14 eexists. eexists. exists bs'.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact UB|]. lia.
Qed.
