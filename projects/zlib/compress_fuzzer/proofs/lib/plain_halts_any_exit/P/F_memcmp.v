(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).

Definition R_BCMP : Z := 0x27964.
Definition R_MEMCMP : Z := 0x27968.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (l1 l2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ ((l1 = l2 /\ a0 = wz 0) \/ (l1 <> l2 /\ bv_unsigned a0 <> 0)).

Lemma bytes_at_tail : forall (m : mem) A (b : byte) (l : list byte), bytes_at psegs m A (b :: l) -> bytes_at psegs m (A + 1) l.
Proof. intros m A b l H. apply (proj1 (bytes_at_app psegs m A [b] l)) in H. exact (proj2 H). Qed.

Lemma byte_word_inj : forall b1 b2 : byte, bv_unsigned b1 = bv_unsigned b2 -> b1 = b2.
Proof. intros b1 b2 H. apply bv_eq. exact H. Qed.

Lemma memcmp_loop : forall (l1 l2 : list byte) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (L R : Z),
  bytes_at psegs m L l1 -> bytes_at psegs m R l2 -> length l1 = length l2 -> (1 <= length l1)%nat ->
  0 < L -> L + Z.of_nat (length l1) < 2^63 -> 0 < R -> R + Z.of_nat (length l2) < 2^63 -> mem_inv psegs m ->
  evt psegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l1 l2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz R) (wz (Z.of_nat (length l1))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x2796c) fc None m (seg_rom psegs)).
Proof.
  induction l1 as [|b1 l1 IH]; intros l2; [intros; cbn in *; lia|].
  destruct l2 as [|b2 l2]; [intros; cbn in *; lia|].
  intros until R. intros B1 B2 LEN K1 L0 LN R0 RN MI. cbn [length] in *.
  pose proof (u8ro_read psegs m L (b1 :: l1) 0 b1 (wa (L + 0)) B1 eq_refl ltac:(lia) eq_refl) as RD1. replace (L + 0) with L in RD1 by lia.
  pose proof (u8ro_read psegs m R (b2 :: l2) 0 b2 (wa (R + 0)) B2 eq_refl ltac:(lia) eq_refl) as RD2. replace (R + 0) with R in RD2 by lia.
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. change (bv_modulus 8) with 256 in R1, R2.

  do 3 zstep. if_cases K; zify_cond K.
  -
    do 2 zstep. apply evt_done. unfold memcmp_post. do 15 eexists. exists m.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    right. split; [intros E; inversion E; subst; apply K; reflexivity|].
    rewrite unsigned_lit_wrap. intros E. apply K.
    assert (D : - 256 < bv_unsigned b1 - bv_unsigned b2 < 256) by lia.
    destruct (Z.eq_dec (bv_unsigned b1) (bv_unsigned b2)) as [E'|NE]; [rewrite E'; reflexivity|]. exfalso.
    destruct (Z.ltb_spec (bv_unsigned b1) (bv_unsigned b2)).
    + replace (bv_unsigned b1 - bv_unsigned b2) with ((bv_unsigned b1 - bv_unsigned b2 + 2^64) + (-1) * 2^64) in E by lia.
      rewrite Z.mod_add, Z.mod_small in E by lia. lia.
    + rewrite Z.mod_small in E by lia. lia.
  -
    assert (EB : b1 = b2) by (apply byte_word_inj; lia). subst b2.
    do 4 zstep. if_cases K2; zify_cond K2.
    +
      destruct l1 as [|b1' l1']; [exfalso; cbn [length] in *; rewrite ?Z.mod_small in K2 by lia; lia|].
      replace (wz (Z.of_nat (S (length (b1' :: l1'))) + -1)) with (wz (Z.of_nat (length (b1' :: l1')))) by (f_equal; lia).
      eapply evt_mono.
      { eapply (IH l2 ra sp gp tp t0 t1 t2 s0 s1 _ _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (L + 1) (R + 1)).
        - eapply bytes_at_tail; exact B1.
        - eapply bytes_at_tail; exact B2.
        - lia. - cbn [length]; lia. - lia. - lia. - lia. - lia. - exact MI. }
      intros ms' PO. unfold memcmp_post in *.
      destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & RES).
      do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      destruct RES as [[E Z0]|[NE NZ]]; [left; split; [f_equal; exact E| exact Z0]| right; split; [intros E; inversion E; auto| exact NZ]].
    +
      assert (l1 = []) by (destruct l1; [reflexivity| exfalso; cbn [length] in *; rewrite ?Z.mod_small in K2 by lia; lia]). subst l1.
      assert (l2 = []) by (destruct l2; [reflexivity| cbn in LEN; lia]). subst l2.
      do 2 zstep. apply evt_done. unfold memcmp_post. do 15 eexists. exists m.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. left. split; reflexivity.
Qed.

Lemma bcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (L R : Z) (l1 l2 : list byte),
  bytes_at psegs m L l1 -> bytes_at psegs m R l2 -> length l1 = length l2 ->
  0 < L -> L + Z.of_nat (length l1) < 2^63 -> 0 < R -> R + Z.of_nat (length l2) < 2^63 -> mem_inv psegs m ->
  evt psegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l1 l2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz R) (wz (Z.of_nat (length l1))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz R_BCMP) fc None m (seg_rom psegs)).
Proof.
  intros until l2. intros B1 B2 LEN L0 LN R0 RN MI. unfold R_BCMP.
  do 2 zstep. if_cases K; zify_cond K.
  -
    assert (l1 = []) by (destruct l1; [reflexivity| exfalso; cbn [length] in *; rewrite ?Z.mod_small in K by lia; lia]). subst l1.
    assert (l2 = []) by (destruct l2; [reflexivity| cbn in LEN; lia]). subst l2.
    do 2 zstep. apply evt_done. unfold memcmp_post. do 15 eexists. exists m.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. left. split; reflexivity.
  - apply memcmp_loop; try assumption. destruct l1; [exfalso; apply K; reflexivity| cbn [length]; lia].
Qed.
