(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memset F_memmove.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition libc_stk_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' D (D + n).

Lemma memcpy_stk : forall (D S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m D (D + n) -> rdbl usegs m S (S + n) -> 0 <= n -> 0 <= S -> 0 <= D -> S + n < 2^64 -> D + n < 2^64 ->
  (S + n <= D \/ D + n <= S) -> mem_inv usegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  evt usegs (libc_stk_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3526c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD RDS Hn HS HD BS BD SEP MI -> -> ->.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (rdbl_bytes usegs m S (S + n) RDS ltac:(lia)) as (src & LEN & SRC).
  replace (S + n - S) with n in LEN by lia.
  destruct (stk_carve usegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as (_ & junk & DST).
  replace (D + n - Z.of_nat (Z.to_nat n)) with D in DST by lia.
  eapply evt_mono.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m src junk);
      rewrite ?ED, ?ES, ?En; assumption. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & DST' & SRC').
  rewrite ED, En in *.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  pose proof (stk_of_rw_cells usegs m' D _ DST') as ST'. cbn [cells_size csize Nat.add] in ST'. rewrite Nat.add_0_r, Z2Nat.id in ST' by lia. exact ST'.
Qed.

Lemma memset_stk : forall (D c n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m D (D + n) -> 0 <= n -> 0 <= D -> D + n < 2^64 -> mem_inv usegs m ->
  a0 = Z_to_bv 64 D -> a2 = Z_to_bv 64 n ->
  evt usegs (libc_stk_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x357ec) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD Hn HD BD MI -> ->.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (stk_carve usegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as (_ & junk & DST).
  replace (D + n - Z.of_nat (Z.to_nat n)) with D in DST by lia.
  eapply evt_mono.
  { eapply (memset_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) a1 (Z_to_bv 64 n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m junk);
      rewrite ?ED, ?En; assumption. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & DST').
  rewrite ED, En in *.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  pose proof (stk_of_rw_cells usegs m' D _ DST') as ST'. cbn [cells_size csize Nat.add] in ST'. rewrite Nat.add_0_r, Z2Nat.id in ST' by lia. exact ST'.
Qed.

Lemma memmove_stk : forall (D S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m D (D + n) -> rdbl usegs m S (S + n) -> 0 <= n -> 0 <= S -> 0 <= D -> S + n <= 2^63 -> D + n <= 2^63 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  evt usegs (libc_stk_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35670) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD RDS Hn HS HD BS BD MI -> -> ->.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memmove_spec; rewrite ?ED, ?ES, ?En; [split; lia | exact STD | exact RDS | exact MI]. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & I).
  rewrite ED, ES, En in I. destruct I as (STD' & _ & MI' & MU & WM).
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exact STD'.
Qed.
