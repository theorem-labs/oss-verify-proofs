(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := AsanUbsan.AsanUbsan_loaded_segments.

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

Definition SHB : Z := 2147450880.
Lemma shadow_big : forall y, (0 <= y < 2 ^ 47)%Z -> (0x7fff7000 <= Z.shiftr y 3 + 2147450880 < 0x10007fff8000)%Z.
Proof. intros y Hy. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. split; [pose proof (Z.div_pos y 8); lia | ]. apply Z.lt_le_trans with (2 ^ 44 + 2147450880)%Z; [|lia]. pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44)); lia. Qed.

Lemma mrd_ov1 : forall (m : word -> option byte) (x : Z) (b : byte), (0 <= x < 2 ^ 64)%Z -> mrd rsegs m (wa x) = Some b -> ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [b].
Proof.
  intros m x b Hx H. replace (Z_to_bv 64 x) with (wa (x + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m x [b] 0 1); [reflexivity| |cbn; lia].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth_error]. replace (x + Z.of_nat 0)%Z with x by lia. exact H.
Qed.

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
Hypothesis SEP_B : (buf + 21 <= SP0 - 96 \/ lenp + 4 <= buf)%Z.

Definition app_buf : Prop := (buf + 21 <= 0x7fff7000 \/ 0x10007fff8000 <= buf)%Z.
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 96)%Z.

Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Definition DG_W : list (Z * Z) := [(SP0 - 96, SP0); (buf, buf + 21); (lenp, lenp + 4); (kp, kp + 4)]%Z.

Lemma sh_read : forall (m : word -> option byte) (y x : Z), munch DG_W m0 m -> (0 <= y < 2 ^ 47)%Z -> x = (Z.shiftr y 3 + 2147450880)%Z ->
  mrd rsegs m0 (wa x) = Some (Z_to_bv 8 0) -> ov_read_bytes rsegs m (Z_to_bv 64 (Z.shiftr y 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof using All.
  intros m y x MU Hy -> H. pose proof (shadow_big y Hy) as SBg.
  apply mrd_ov1; [lia|]. unfold mrd. rewrite (MU (wa (Z.shiftr y 3 + 2147450880))). { exact H. }
  unfold DG_W. cbn [outside]. rewrite wa_unsigned by lia. unfold SP0, app_buf in *. repeat split; lia.
Qed.

Definition dg_post (Ks : Z) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (res len kappa : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch DG_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (SP0 - 96) SP0
    /\ u8arr rsegs m' buf bs /\ length bs = 21%nat
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (Ks + kappa))] /\ (-18 <= kappa <= 2)%Z
    /\ (res = 0 \/ res = 1)%Z.

Definition dg_mem (m : word -> option byte) (j8 : list byte) (len Kv : Z) (bs : list byte) : Prop :=
  stk rsegs m (SP0 - 96) (SP0 - 96) /\
  rw_cells rsegs m (SP0 - 96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  munch DG_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  u8arr rsegs m buf bs /\ length bs = 21%nat /\
  rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] /\ rw_cells rsegs m kp [C4 (Z_to_bv 64 Kv)].

Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DG_W in MU.

Lemma dg_ret : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (res len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  a0' = Z_to_bv 64 res -> (res = 0 \/ res = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1b1c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Ha0 Hres. dg_mem_intro HM. subst a0'.
  do 13 zstep.
  replace (Z_to_bv 64 (SP0 - 96 + 96)) with sp by (unfold SP0; rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST SP0.
  finish. all: first [eassumption | lia].
Qed.

Lemma dg_xori : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (x len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (x = 0 \/ x = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 x) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1b18) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Hx. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_ret; [exact HM0 | exact LR | exact KR | reflexivity | ]. destruct Hx as [-> | ->]; cbv; auto.
Qed.

Lemma dg_or : forall t0' t1' t2' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (b1 b2 : bool) (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 (Z.b2z b2)) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1b14) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_xori; [exact HM0 | exact LR | exact KR | apply b2z_lor01].
Qed.

Lemma dg_weed1 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1a94) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 2 step. if_cases K1.
  - do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
  - step. if_cases K2.
    + do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 step. if_cases K3.
      * do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 step. if_cases K4.
        -- do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
        -- do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
Qed.

Lemma dg_weed2 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1acc) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 3 step. if_cases K1.
  - do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
  - step. if_cases K2.
    + do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 step. if_cases K3.
      * do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 step. if_cases K4.
        -- do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
        -- do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
Qed.

Lemma dg_rw2_loop : forall (n : nat) (D r one len : Z) t0' s0' s1' a1' a2' a3' a5' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= one)%Z -> (r + one <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' (Z_to_bv 64 0) (Z_to_bv 64 1) s0' s1'
                                  (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) a5' (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) a7'
                                  (Z_to_bv 64 (D - r - one)) s3' s4' s5' s6' s7' s8' s9' s10 s11
                                  t3' t4' (Z_to_bv 64 r) t6')
                              F (Z_to_bv 64 0xd1a38) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r one len t0' s0' s1' a1' a2' a3' a5' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall s1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 (D - r - one)) s1x
              (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) (Z_to_bv 64 (r + one)) (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) a7'
              (Z_to_bv 64 (D - r - one)) s3' s4' s5' s6' s7' s8' s9' s10 s11
              t3' t4' (Z_to_bv 64 r) t6')
         F (Z_to_bv 64 0xd1a4c) fc None m (seg_rom rsegs))).
  { intros s1x.
    zstep. if_cases Kt1; [cbv in Kt1; discriminate | ].
    zstep. if_cases Kt2; [cbv in Kt2; discriminate | ].
    pose proof (sh_read m (buf + len + -1) (Z.shiftr (buf + (len - 1)) 3 + 2147450880) MU ltac:(lia) ltac:(f_equal; f_equal; lia) (SHBUF (len - 1) ltac:(lia))) as SH.
    zstep. zstep. if_cases K0; [cbv in K0; discriminate | ].
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU SH RD. store_done.
    assert (HM1 : dg_mem m1 j8 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zstep. zstep. if_cases K2.
    + eapply dg_weed2; [exact HM1 | exact LR | exact KR].
    + do 3 zstep. zstep. if_cases K3; zify_cond K3.
      *
        replace (Z_to_bv 64 (D - r - one - one)) with (Z_to_bv 64 (D - (r + one) - one)) by (f_equal; lia).
        eapply (IH (Z.to_nat (D - (r + one)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zstep. eapply dg_weed2; [exact HM1 | exact LR | exact KR].
  }
  do 3 zstep. if_cases K1.
  - apply BODY.
  - do 2 zstep. if_cases K4.
    + do 2 zstep. eapply dg_weed2; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_rw1_loop : forall (n : nat) (D r tk len : Z) t0' t1' t2' s0' s1' a2' a4' s2' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= tk)%Z -> (r + tk <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1'
                                  (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) a4' (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880))
                                  (Z_to_bv 64 1) (Z_to_bv 64 0) s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11
                                  t3' t4' t5' t6')
                              F (Z_to_bv 64 0xd1858) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r tk len t0' t1' t2' s0' s1' a2' a4' s2' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall t1x t2x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1x t2x s0' s1'
              (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) (Z_to_bv 64 (r + tk)) (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880))
              (Z_to_bv 64 1) (Z_to_bv 64 0) s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11
              t3' t4' t5' t6')
         F (Z_to_bv 64 0xd186c) fc None m (seg_rom rsegs))).
  { intros t1x t2x.
    zstep. if_cases Kt1; [cbv in Kt1; discriminate | ].
    zstep. if_cases Kt2; [cbv in Kt2; discriminate | ].
    pose proof (sh_read m (buf + len + -1) (Z.shiftr (buf + (len - 1)) 3 + 2147450880) MU ltac:(lia) ltac:(f_equal; f_equal; lia) (SHBUF (len - 1) ltac:(lia))) as SH.
    zstep. zstep. if_cases K0; [cbv in K0; discriminate | ].
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU SH RD. store_done.
    assert (HM1 : dg_mem m1 j8 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zstep. zstep. if_cases K2.
    + eapply dg_weed1; [exact HM1 | exact LR | exact KR].
    + zstep. zstep. if_cases K3; zify_cond K3.
      *
        eapply (IH (Z.to_nat (D - (r + tk)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zstep. eapply dg_weed1; [exact HM1 | exact LR | exact KR].
  }
  zstep. zstep. if_cases K1.
  - apply BODY.
  - do 3 zstep. if_cases K4.
    + do 2 zstep. eapply dg_weed1; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_l2exit : forall (Dold r one len kappa Ks : Z) t2' t3' t4' t6' s1' a1' a2' s2' s4' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= -1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (0 <= r < 10 * Dold)%Z -> (1 <= one <= 2 ^ 59)%Z -> (10 * Dold < 2 ^ 63)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 Dold) s1'
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 (10 * Dold)) (Z_to_bv 64 one) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' (Z_to_bv 64 kappa) s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' (Z_to_bv 64 r) t6')
                              F (Z_to_bv 64 0xd1984) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hr Ho HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  zstep. if_cases Kz; [zify_cond Kz; lia | ].
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 kp KA) in Ka; lia | ].
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  zstep. rewrite sx32_small by lia.
  zstep. zstep. zstep. if_cases Kov; [zify_cond Kov; rewrite swrap32_mod64 in Kov by lia; exfalso; exact (Kov eq_refl) | ].
  zstep. zstep. if_cases K0b; [cbv in K0b; discriminate | ].
  clear SHk.
  zstep.
  assert (HM1 : dg_mem m1 j8 len (Ks + kappa) bs).
  { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  do 4 zstep. if_cases K1.
  - zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 23 zstep.
      rewrite (swrap32_small (len + -1)) by lia.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      replace (Z_to_bv 64 (Dold * 10 - (one + r))) with (Z_to_bv 64 (10 * Dold - r - one)) by (f_equal; lia).
      eapply (dg_rw2_loop (Z.to_nat (10 * Dold - r)) (10 * Dold) r one len); [reflexivity | exact HM1 | exact LR | lia | lia | lia | lia | lia].
Qed.

End DGB.
