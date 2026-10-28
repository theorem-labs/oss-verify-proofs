(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PB.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variable o : Z.
Definition PSP : Z := bv_unsigned sp.
Hypothesis SPR : (2^41 <= PSP /\ PSP <= 2^47)%Z.
Hypothesis ORNG : (4096 <= o /\ o + 24 <= 2^47)%Z.
Hypothesis SEPO : (o + 24 <= PSP - 64 \/ PSP <= o)%Z.
Definition PB_W : list (Z * Z) := [(PSP - 64, PSP); (o, o + 24)]%Z.

Definition pb_post (n : Z) (c : byte) (bs : list byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch PB_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' (PSP - 64) PSP
    /\ u8arr rsegs m' o (upd (upd (upd bs 0 (Z_to_bv 8 (2 * n + 2))) (Z.to_nat (n + 1)) c) (Z.to_nat (n + 2)) (Z_to_bv 8 0)).

Lemma pb_inplace : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (n : Z) (c : byte) (bs : list byte),
  (0 <= n <= 21)%Z -> length bs = 24%nat -> nth_error bs 0 = Some (Z_to_bv 8 (2 * n)) ->
  stk rsegs m (PSP - 64) PSP -> u8arr rsegs m o bs -> mem_inv rsegs m -> m = m0 ->
  evt rsegs (pb_post n c bs) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 (bv_unsigned c)) a2 a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x642a0) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros Hn BL B0 ST BU MI ->.
  pose proof (munch_refl PB_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold PB_W in MU. unfold PSP in *.
  pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. change (2 ^ Z.of_N 8)%Z with 256%Z in Rc.
  carve_frame 64%nat ST.
  do 9 zstep.
  zstep.
  pose proof (u8arr_read rsegs m1 o bs 0 (Z_to_bv 8 (2 * n)) (Z_to_bv 64 o) BU B0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
  zstep. cbv beta. rewrite (Z_to_bv_small 8 (2 * n)) by (unfold bv_modulus; cbn -[Z.pow]; lia).
  assert (E1 : Z.land (2 * n) 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones by lia; rewrite Z.mul_comm; apply Z_mod_mult).
  zstep. rewrite E1.
  do 2 zstep. if_cases K1; zify_cond K1; [exfalso; lia | ].
  do 2 zstep. if_cases K2; zify_cond K2; [ | exfalso; lia ].
  do 3 zstep.
  assert (Hsh : Z.shiftr (2 * n) 1 = n) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1)%Z with 2%Z; rewrite Z.mul_comm; apply Z_div_mult; lia).
  rewrite ?Hsh.
  pose proof (u8arr_store_ok rsegs m1 o bs 0 (Z_to_bv 64 o) BU ltac:(rewrite BL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  replace (write_to_mem m1 (Z_to_bv 64 o) (le1 (Z_to_bv 64 (2 * n + 2)))) with (write_to_mem m1 (wa (o + 0)) [Z_to_bv 8 (2 * n + 2)])
    by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
  pose proof (u8arr_write rsegs m1 o bs 0 (Z_to_bv 8 (2 * n + 2)) BU ltac:(rewrite BL; lia)) as BU1.
  clear BU. store_done.
  set (bs1 := upd bs (Z.to_nat 0) (Z_to_bv 8 (2 * n + 2))) in *.
  assert (BL1 : length bs1 = 24%nat) by (unfold bs1; rewrite upd_length; exact BL).
  do 2 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok rsegs mm o bs1 (n + 1) (Z_to_bv 64 (o + 1 + n)) BU1 ltac:(rewrite BL1; lia) ltac:(unfold wa; f_equal; lia)) as SOK1 end.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    replace (write_to_mem mm (Z_to_bv 64 (o + 1 + n)) (le1 (Z_to_bv 64 (bv_unsigned c)))) with (write_to_mem mm (wa (o + (n + 1))) [c])
      by (f_equal; [unfold wa; f_equal; lia | rewrite le1_lit; f_equal; apply bv_eq; rewrite definitions.Z_to_bv_unsigned; symmetry; apply bv_wrap_bv_unsigned]);
    pose proof (u8arr_write rsegs mm o bs1 (n + 1) c BU1 ltac:(rewrite BL1; lia)) as BU2 end.
  clear BU1. store_done.
  set (bs2 := upd bs1 (Z.to_nat (n + 1)) c) in *.
  assert (BL2 : length bs2 = 24%nat) by (unfold bs2; rewrite upd_length; exact BL1).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok rsegs mm o bs2 (n + 2) (Z_to_bv 64 (o + 1 + n + 1)) BU2 ltac:(rewrite BL2; lia) ltac:(unfold wa; f_equal; lia)) as SOK2 end.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad _) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 0))) with (write_to_mem mm (wa (o + (n + 2))) [Z_to_bv 8 0])
      by (f_equal; try (unfold wa; f_equal; lia); try apply le1_lit);
    pose proof (u8arr_write rsegs mm o bs2 (n + 2) (Z_to_bv 8 0) BU2 ltac:(rewrite BL2; lia)) as BU3 end.
  clear BU2. store_done.
  do 10 zstep.
  replace (Z_to_bv 64 (bv_unsigned sp + -64 + 64)) with sp by (replace (bv_unsigned sp + -64 + 64)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
End PB.
