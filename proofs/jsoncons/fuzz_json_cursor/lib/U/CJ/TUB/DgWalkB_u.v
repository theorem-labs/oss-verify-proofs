(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := Ubsan.Ubsan_loaded_segments.

Lemma le1_lit : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8)%Z. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.

Lemma sx32_small : forall k, (- 2 ^ 31 <= k < 2 ^ 31)%Z -> sx32 (Z_to_bv 64 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace ((k mod 2 ^ 64 + 2 ^ 31) mod 2 ^ 32)%Z with ((k + 2 ^ 31) mod 2 ^ 32)%Z.
  - rewrite Z.mod_small by lia. lia.
  - rewrite (Z.add_mod (k mod 2 ^ 64)) by lia. rewrite (Z.add_mod k (2 ^ 31)) by lia. rewrite Z.mod_mod_divide by (exists (2 ^ 32)%Z; reflexivity). reflexivity.
Qed.

Lemma swrap32_small : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma v_remuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z -> v_remuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold v_remuw. rewrite !Z_to_bv_unsigned.
  assert (Wx : bv_wrap 32 (bv_wrap 64 x) = x) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  assert (Wy : bv_wrap 32 (bv_wrap 64 y) = y) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  rewrite Wx, Wy. destruct (Z.eqb_spec y 0) as [E|E]; [lia|]. f_equal. apply swrap32_small.
  pose proof (Z.mod_pos_bound x y ltac:(lia)). lia.
Qed.

Lemma v_divuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !Z_to_bv_unsigned.
  assert (Wx : bv_wrap 32 (bv_wrap 64 x) = x) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  assert (Wy : bv_wrap 32 (bv_wrap 64 y) = y) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  rewrite Wx, Wy. destruct (Z.eqb_spec y 0) as [E|E]; [lia|]. f_equal. apply swrap32_small.
  split; [pose proof (Z.div_pos x y); lia | ]. pose proof (Z.div_le_upper_bound x y x ltac:(lia) ltac:(nia)). lia.
Qed.

Lemma subw_mod : forall p dv, (0 <= p < 2 ^ 31)%Z -> (1 <= dv < 2 ^ 31)%Z -> bv_swrap 32 (p - p / dv * dv) = (p mod dv)%Z.
Proof.
  intros p dv Hp Hd. rewrite (Z.mod_eq p dv) by lia. replace (p - p / dv * dv)%Z with (p - dv * (p / dv))%Z by ring. apply swrap32_small.
  pose proof (Z.mod_pos_bound p dv ltac:(lia)). rewrite Z.mod_eq in H by lia. lia.
Qed.
Lemma shl_s : forall x s, (0 <= x < 2 ^ 64)%Z -> (0 <= s < 64)%Z -> ((x mod 18446744073709551616) ≪ (s mod 64))%Z = (x * 2 ^ s)%Z.
Proof. intros x s Hx Hs. rewrite !Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia. Qed.

Lemma b2z_lor01 : forall b1 b2, (Z.lor (Z.b2z b1) (Z.b2z b2) = 0 \/ Z.lor (Z.b2z b1) (Z.b2z b2) = 1)%Z.
Proof. intros [|] [|]; cbv; auto. Qed.

Ltac pgoal := match goal with |- ?G => idtac "GOAL:" G end.
Lemma lxor63 : forall x, (0 <= x < 2 ^ 63)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof. intros x H. pose proof (zb_lxor_pow2_small x 63 H ltac:(lia)) as E. change (2 ^ 63)%Z with 9223372036854775808%Z in E. exact E. Qed.

Ltac ub_norm :=
  repeat match goal with |- context [(?x mod 18446744073709551616)%Z] =>
    first [ rewrite (Z.mod_small x 18446744073709551616) by lia | fail ] end;
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) by lia end;
  repeat match goal with |- context [(?x <? ?y)%Z] =>
    first [ replace (x <? y)%Z with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y)%Z with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; zsimp.
Lemma sgn_small : forall x, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x H. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - replace (x mod 2 ^ 64)%Z with (x + 2 ^ 64)%Z by (rewrite <- (Z.mod_add x 1) by lia; rewrite Z.mod_small by lia; lia).
    destruct (Z.ltb_spec0 (x + 2 ^ 64) (2 ^ 63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 x (2 ^ 63)); lia.
Qed.
Lemma swrap32_modl : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616 + y) = (x + y)%Z.
Proof.
  intros x y H. change 18446744073709551616%Z with (2 ^ 64)%Z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite (Z.mod_eq x (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) + y + 2 ^ 31)%Z with (x + y + 2 ^ 31 + (- (2 ^ 32) * (x / 2 ^ 64)) * 2 ^ 32)%Z by (change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac ub_norm_in K :=
  repeat match type of K with context [(?x mod 18446744073709551616)%Z] => rewrite (Z.mod_small x 18446744073709551616) in K by lia end;
  repeat match type of K with context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) in K by lia end;
  repeat match type of K with context [(?x <? ?y)%Z] =>
    first [ replace (x <? y)%Z with true in K by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y)%Z with false in K by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z] in K.
Lemma land3_0 : forall k, (k mod 4 = 0)%Z -> Z.land k 3 = 0%Z.
Proof. intros k H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma swrap32_mod64 : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 2 ^ 64 + y mod 2 ^ 64) = (x + y)%Z.
Proof.
  intros x y H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite (Z.mod_eq x (2 ^ 64)), (Z.mod_eq y (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) + (y - 2 ^ 64 * (y / 2 ^ 64)) + 2 ^ 31)%Z
    with (x + y + 2 ^ 31 + (- (2 ^ 32) * (x / 2 ^ 64 + y / 2 ^ 64)) * 2 ^ 32)%Z by (change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac znorm :=
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y mod 18446744073709551616)] => rewrite (swrap32_mod64 x y) by lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl x y) by lia end;
  repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia end;
  repeat match goal with |- context [Z.land ?x 3] => rewrite (land3_0 x) by lia end.
Ltac zs1 := zstep; try znorm.
Ltac zbcl K := zify_cond K;
  first [ lia | rewrite ?sgn_small in K by lia; lia | ub_norm_in K; lia | ub_norm_in K; cbv in K; discriminate | cbv in K; discriminate ].
Ltac zbf := let K := fresh "K" in if_cases K; [ zbcl K | ].
Ltac zbt := let K := fresh "K" in if_cases K; [ | zbcl K ].

Section DGB.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Definition SP0 : Z := bv_unsigned sp.

Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ lenp + 4 <= buf)%Z.

Definition DG_W : list (Z * Z) := [(SP0 - 64, SP0); (buf, buf + 21); (lenp, lenp + 4); (kp, kp + 4)]%Z.

Definition dg_post (Ks : Z) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (res len kappa : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch DG_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (SP0 - 64) SP0
    /\ u8arr rsegs m' buf bs /\ length bs = 21%nat
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (Ks + kappa))] /\ (-18 <= kappa <= 2)%Z
    /\ (res = 0 \/ res = 1)%Z.

Definition dg_mem (m : word -> option byte) (len Kv : Z) (bs : list byte) : Prop :=
  stk rsegs m (SP0 - 64) (SP0 - 64) /\
  rw_cells rsegs m (SP0 - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  munch DG_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  u8arr rsegs m buf bs /\ length bs = 21%nat /\
  rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] /\ rw_cells rsegs m kp [C4 (Z_to_bv 64 Kv)].

Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DG_W in MU.

Lemma dg_ret : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (res len kappa Ks : Z) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  a0' = Z_to_bv 64 res -> (res = 0 \/ res = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x44cf4) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Ha0 Hres. dg_mem_intro HM. subst a0'.
  do 10 zs1.
  replace (Z_to_bv 64 (SP0 - 64 + 64)) with sp by (unfold SP0; rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST SP0.
  finish. all: first [eassumption | lia].
Qed.

Lemma dg_xori : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (x len kappa Ks : Z) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (x = 0 \/ x = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 x) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x44cf0) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Hx. pose proof HM as HM0. dg_mem_intro HM.
  zs1. eapply dg_ret; [exact HM0 | exact LR | exact KR | reflexivity | ]. destruct Hx as [-> | ->]; cbv; auto.
Qed.

Lemma dg_or : forall t0' t1' t2' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (b1 b2 : bool) (len kappa Ks : Z) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 (Z.b2z b2)) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x44cec) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR. pose proof HM as HM0. dg_mem_intro HM.
  zs1. eapply dg_xori; [exact HM0 | exact LR | exact KR | apply b2z_lor01].
Qed.

Lemma dg_weed1 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (len kappa Ks : Z) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x44c6c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 2 zs1. if_cases K1.
  - do 4 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
  - zs1. if_cases K2.
    + do 4 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 zs1. if_cases K3.
      * do 2 zs1. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 zs1. if_cases K4.
        -- do 2 zs1. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
        -- do 4 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
Qed.

Lemma dg_weed2 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (len kappa Ks : Z) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x44ca4) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 3 zs1. if_cases K1.
  - do 7 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
  - zs1. if_cases K2.
    + do 7 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 zs1. if_cases K3.
      * do 2 zs1. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 zs1. if_cases K4.
        -- do 7 zs1. eapply dg_or; [exact HM | exact LR | exact KR].
        -- do 2 zs1. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
Qed.

Lemma dg_rw2_loop : forall (n : nat) (D r one len : Z) t0' t1' s0' s1' a0' a1' a3' a4' a5' a6' s2' s3' s4' s5' s6' t5' (m : word -> option byte) (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= one)%Z -> (r + one <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' (Z_to_bv 64 r) s0' s1'
                                  a0' a1' (Z_to_bv 64 one) a3' a4' a5' a6' (Z_to_bv 64 (buf + len + -1))
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 0) (Z_to_bv 64 1) t5' (Z_to_bv 64 (D - r - one)))
                              F (Z_to_bv 64 0x44b78) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r one len t0' t1' s0' s1' a0' a1' a3' a4' a5' a6' s2' s3' s4' s5' s6' t5' m kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall t1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1x (Z_to_bv 64 r) (Z_to_bv 64 (D - r - one)) s1'
              a0' a1' (Z_to_bv 64 one) (Z_to_bv 64 (r + one)) a4' a5' a6' (Z_to_bv 64 (buf + len + -1))
              s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
              (Z_to_bv 64 0) (Z_to_bv 64 1) t5' (Z_to_bv 64 (D - r - one)))
         F (Z_to_bv 64 0x44b8c) fc None m (seg_rom rsegs))).
  { intros t1x.
    zs1. zbf.
    zs1. zbf.
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zs1. zs1.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs1.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU RD. store_done.
    assert (HM1 : dg_mem m1 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zs1. zs1. if_cases K2.
    + eapply dg_weed2; [exact HM1 | exact LR | exact KR].
    + do 3 zs1. zs1. if_cases K3; zify_cond K3.
      * replace (Z_to_bv 64 (D - r - one - one)) with (Z_to_bv 64 (D - (r + one) - one)) by (f_equal; lia).
        eapply (IH (Z.to_nat (D - (r + one)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zs1. eapply dg_weed2; [exact HM1 | exact LR | exact KR].
  }
  do 3 zs1. if_cases K1.
  - apply BODY.
  - do 2 zs1. if_cases K4.
    + do 2 zs1. eapply dg_weed2; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_rw1_loop : forall (n : nat) (D r tk len : Z) t0' t1' t2' t3' t4' t6' s0' a0' a3' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= tk)%Z -> (r + tk <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' (Z_to_bv 64 r)
                                  a0' (Z_to_bv 64 D) (Z_to_bv 64 tk) a3' (Z_to_bv 64 (buf + len + -1)) a5' (Z_to_bv 64 1) (Z_to_bv 64 0)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  t3' t4' (Z_to_bv 64 1) t6')
                              F (Z_to_bv 64 0x44c24) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r tk len t0' t1' t2' t3' t4' t6' s0' a0' a3' a5' s2' s3' s4' s5' s6' m kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall t0x t1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0x t1x t2' s0' (Z_to_bv 64 r)
              a0' (Z_to_bv 64 D) (Z_to_bv 64 tk) (Z_to_bv 64 (r + tk)) (Z_to_bv 64 (buf + len + -1)) a5' (Z_to_bv 64 1) (Z_to_bv 64 0)
              s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
              t3' t4' (Z_to_bv 64 1) t6')
         F (Z_to_bv 64 0x44c38) fc None m (seg_rom rsegs))).
  { intros t0x t1x.
    zs1. zbf.
    zs1. zbf.
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zs1. zs1. zs1.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs1.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU RD. store_done.
    assert (HM1 : dg_mem m1 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zs1. zs1. if_cases K2.
    + eapply dg_weed1; [exact HM1 | exact LR | exact KR].
    + zs1. zs1. if_cases K3; zify_cond K3.
      * eapply (IH (Z.to_nat (D - (r + tk)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zs1. eapply dg_weed1; [exact HM1 | exact LR | exact KR].
  }
  zs1. zs1. if_cases K1.
  - apply BODY.
  - do 3 zs1. if_cases K4.
    + do 2 zs1. eapply dg_weed1; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_l2exit : forall (Dold r one len kappa Ks : Z) t1' s1' a0' a4' a5' s2' s3' s4' s5' s6' t3' t5' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= -1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (0 <= r < 10 * Dold)%Z -> (1 <= one <= 2 ^ 59)%Z -> (10 * Dold < 2 ^ 63)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) t1' (Z_to_bv 64 r) (Z_to_bv 64 kappa) s1'
                                  a0' (Z_to_bv 64 (10 * Dold)) (Z_to_bv 64 one) (Z_to_bv 64 1) a4' a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  t3' (Z_to_bv 64 Dold) t5' (Z_to_bv 64 kappa))
                              F (Z_to_bv 64 0x44af0) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hr Ho HD.
  pose proof HM as HM0. dg_mem_intro HM.
  zs1. zbf.
  zs1. zs1. zbf.
  do 3 zs1.
  match goal with |- context [bv_swrap 32 (Ks mod ?M + kappa mod ?M)] =>
    replace (bv_swrap 32 (Ks mod M + kappa mod M)) with (Ks + kappa)%Z by (symmetry; apply swrap32_mod64; lia)
  end.
  zs1. zbf.
  zs1.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HM1 : dg_mem mm len (Ks + kappa) bs)
  end.
  { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  do 4 zs1. if_cases Lx1.
  - zs1. eapply dg_weed2; [exact HM1 | exact LR | lia].
  - zs1. if_cases Lx2; zify_cond Lx2.
    + zs1. eapply dg_weed2; [exact HM1 | exact LR | lia].
    + do 21 zs1.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      replace (Z_to_bv 64 (Dold * 10 - (one + r))) with (Z_to_bv 64 (10 * Dold - r - one)) by (f_equal; lia).
      eapply (dg_rw2_loop (Z.to_nat (10 * Dold - r)) (10 * Dold) r one len); [reflexivity | exact HM1 | exact LR | lia | lia | lia | lia | lia].
Qed.

End DGB.
