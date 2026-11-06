(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit BigLinkBase BigLinkGlueUb0.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BIU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition img_free (M : word -> option byte) : Prop := forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None.

Definition iframe (M : word -> option byte) (s : Z) : Prop :=
  140735340000000 <= s /\ s + 32 <= 140737488355328 /\ s mod 16 = 0 /\ BGU.writable M (s + -400) 432 /\ img_free M.

Lemma iframe_keep M M' s :
  (forall x : word, ~ (s - 400 <= bv_unsigned x < s + 32) -> M' x = M x) -> mem_grows M M' ->
  iframe M s -> iframe M' s.
Proof.
  intros HF G (A1 & A2 & A3 & A4 & A5). unfold iframe. repeat split; auto.
  - eapply BGU.writable_grows; eauto.
  - intros i Hi. rewrite HF. apply A5; auto. rewrite BGU.unsigned_lit by lia. lia.
Qed.

Lemma kentry_KImg E M : img_free M -> kentry_ok RSEGS E M (KImg 65536 131072).
Proof. intros H. cbn [kentry_ok]. split. lia. split. lia. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_252 b : 0 <= b < 256 -> Z.land b 3 = 0 -> Z.land b 252 = b.
Proof.
  intros Hb H3.
  assert (E255: Z.land b 255 = b). { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite <- E255 at 2. change 255 with (Z.lor 252 3). rewrite Z.land_lor_distr_r, H3, Z.lor_0_r. reflexivity.
Qed.

Lemma land_lt_pow2 a k n : 0 <= a < 2 ^ n -> 0 <= k -> 0 < n -> 0 <= Z.land a k < 2 ^ n.
Proof.
  intros Ha Hk Hn.
  assert (N: 0 <= Z.land a k) by (apply Z.land_nonneg; lia).
  split. exact N.
  destruct (Z.eq_dec (Z.land a k) 0) as [->|NZ]. apply Z.pow_pos_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|A0]. rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia.
  apply Z.log2_lt_pow2. lia.
  pose proof (Z.log2_land a k ltac:(lia) Hk).
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma alu_and_lit a k : 0 <= a < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (Z.land a k).
Proof.
  intros Ha Hk. unfold alu64, alu. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small a), (Z.mod_small k) by lia.
  symmetry. apply Z.mod_small. apply land_lt_pow2; lia.
Qed.

Definition e_flags : expr := EAlu ALU_AND (EVar 36) (ELit 252).

Lemma flags_val E b0 : ev E 36 = Z_to_bv 64 b0 -> 0 <= b0 < 256 -> Z.land b0 3 = 0 -> edenot E e_flags = Z_to_bv 64 b0.
Proof.
  intros H36 Hb H3. cbn [edenot e_flags]. rewrite H36. rewrite alu_and_lit by lia. rewrite land_252 by auto. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kentry_KWord1_e E M j off e (a b : Z) :
  bv_unsigned (ev E j) = a -> edenot E e = Z_to_bv 64 b -> 0 <= a + off -> a + off + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  BGU.u8_at M (a + off) b -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 e).
Proof.
  intros Ha He H1 H2 Hb Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite BGU.estart_var, Ha. lia.
  - rewrite BGU.adenot_var, Ha, He. rewrite BGU.word_to_le_bytes_1 by auto. exact Hu.
Qed.

Lemma u8_of_KWord1_e E M j off e (a b : Z) :
  kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 e) -> bv_unsigned (ev E j) = a -> edenot E e = Z_to_bv 64 b -> 0 <= b < 256 ->
  BGU.u8_at M (a + off) b.
Proof.
  intros K Ha He Hb. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold BGU.u8_at.
  rewrite BGU.adenot_var, Ha, He in Rd. rewrite BGU.word_to_le_bytes_1 in Rd by auto. exact Rd.
Qed.

(* [comment removed for export] *)
Lemma kentry_KWord1_var E M j off k (a b : Z) :
  bv_unsigned (ev E j) = a -> bv_unsigned (ev E k) = b -> 0 <= a + off -> a + off + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  BGU.u8_at M (a + off) b -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (EVar k)).
Proof.
  intros Ha Hb H1 H2 Rb Hu. eapply kentry_KWord1_e; eauto. cbn [edenot]. apply BGU.word_of_unsigned. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_mlo : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 42949672960) (EAlu ALU_SRL (EVar 33) (ELit 32)))
               (EMd M_MUL (ELit 10) (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EVar 33)) (ELit 32))).
Definition t_mhi : expr :=
  EAlu ALU_ADD (EAlu ALU_SLTU t_mlo (EMd M_MUL (ELit 42949672960) (EAlu ALU_SRL (EVar 33) (ELit 32))))
               (EAlu ALU_SRL (EMd M_MUL (ELit 10) (EAlu ALU_SRL (EVar 33) (ELit 32))) (ELit 32)).
Definition z_mlo : BL.za := Eval vm_compute in (BL.zc t_mlo).
Definition z_mhi : BL.za := Eval vm_compute in (BL.zc t_mhi).
Lemma z_mlo_ok : BL.zcomp t_mlo = Some z_mlo. Proof. vm_compute. reflexivity. Qed.
Lemma z_mhi_ok : BL.zcomp t_mhi = Some z_mhi. Proof. vm_compute. reflexivity. Qed.

Lemma lo32_identity X : BL.inrange X ->
  ((42949672960 * (X / 4294967296)) mod BL.MM + (10 * ((4294967296 * X) mod BL.MM / 4294967296)) mod BL.MM) mod BL.MM
  = (10 * X) mod BL.MM.
Proof.
  (* [comment removed for export] *)
  unfold BL.inrange. change BL.MM with 18446744073709551616. intros HX.
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *. clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 18446744073709551616 = 4294967296 * Xl).
  { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul by lia.
  rewrite <- Zplus_mod. f_equal. lia.
Qed.

Lemma t_mlo_val V : BL.inrange (V 33%nat) -> BL.zden V z_mlo = (10 * V 33%nat) mod BL.MM.
Proof. intros HX. cbn [BL.zden z_mlo]. apply lo32_identity. exact HX. Qed.

Lemma t_mhi_val V : BL.inrange (V 33%nat) -> BL.zden V z_mhi = (10 * V 33%nat) / BL.MM.
Proof.
  intros HX. cbn [BL.zden z_mhi]. set (X := V 33%nat) in *. clearbody X.
  rewrite lo32_identity by auto.
  change (if (10 * X) mod BL.MM <? (42949672960 * (X / 4294967296)) mod BL.MM then 1 else 0)
    with (BL.zb ((10 * X) mod BL.MM <? (42949672960 * (X / 4294967296)) mod BL.MM)).
  assert (Hmid: BL.zb ((10 * X) mod BL.MM <? (42949672960 * (X / 4294967296)) mod BL.MM)
                = ((42949672960 * (X / 4294967296)) mod BL.MM + (10 * ((4294967296 * X) mod BL.MM / 4294967296)) mod BL.MM) / BL.MM).
  { rewrite <- (lo32_identity X HX). apply BL.carry_ltu_l; apply BL.mod_inrange. }
  rewrite Hmid. clear Hmid.
  unfold BL.inrange in *. change BL.MM with 18446744073709551616 in *.
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *.
  assert (HXh: 0 <= Xh < 4294967296) by (subst Xh; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 18446744073709551616 = 4294967296 * Xl).
  { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul by lia.
  rewrite (Z.mod_small (10 * Xl)) by lia.
  rewrite (Z.mod_small (10 * Xh)) by lia.
  pose proof (Z.div_mod (10 * Xh) 4294967296 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (10 * Xh) 4294967296 ltac:(lia)) as BA.
  set (a := 10 * Xh / 4294967296) in *. set (b := (10 * Xh) mod 4294967296) in *. clearbody a b.
  assert (E4: (42949672960 * Xh) mod 18446744073709551616 = 4294967296 * b).
  { symmetry. apply Z.mod_unique with a; lia. }
  rewrite E4.
  assert (E5: 10 * X = 18446744073709551616 * a + (4294967296 * b + 10 * Xl)) by lia.
  rewrite E5. rewrite (Z.add_comm (18446744073709551616 * a)), (Z.mul_comm 18446744073709551616 a), Z_div_plus_full by lia.
  assert (HB: 0 <= 4294967296 * b + 10 * Xl < 2 * 18446744073709551616) by lia.
  destruct (Z_lt_le_dec (4294967296 * b + 10 * Xl) 18446744073709551616) as [LT|GE].
  - rewrite (Z.mod_small _ _ ) by lia. rewrite (Z.div_small _ _) by lia. lia.
  - replace ((4294967296 * b + 10 * Xl) mod 18446744073709551616) with (4294967296 * b + 10 * Xl - 18446744073709551616).
    2:{ first [apply Z.mod_unique with 1 | symmetry; apply Z.mod_unique with 1]; lia. }
    replace ((4294967296 * b + 10 * Xl) / 18446744073709551616) with 1.
    2:{ first [apply Z.div_unique with (4294967296 * b + 10 * Xl - 18446744073709551616)
             | symmetry; apply Z.div_unique with (4294967296 * b + 10 * Xl - 18446744073709551616)]; lia. }
    lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land15_digit d : 48 <= d <= 57 -> Z.land d 15 = d - 48.
Proof.
  intros Hd.
  assert (H: forall k, (0 <= k < 10)%Z -> Z.land (48 + k) 15 = k).
  { intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  replace d with (48 + (d - 48)) at 1 by lia. rewrite H; lia.
Qed.

Definition t_av0 : expr := EAlu ALU_ADD (EVar 33) (EAlu ALU_AND (EVar 22) (ELit 15)).
Definition t_acy : expr := EAlu ALU_SLTU t_av0 (EVar 33).
Definition z_av0 : BL.za := Eval vm_compute in (BL.zc t_av0).
Definition z_acy : BL.za := Eval vm_compute in (BL.zc t_acy).
Lemma z_av0_ok : BL.zcomp t_av0 = Some z_av0. Proof. vm_compute. reflexivity. Qed.
Lemma z_acy_ok : BL.zcomp t_acy = Some z_acy. Proof. vm_compute. reflexivity. Qed.

Lemma t_av0_val V : BL.inrange (V 33%nat) -> 48 <= V 22%nat <= 57 -> BL.zden V z_av0 = (V 33%nat + (V 22%nat - 48)) mod BL.MM.
Proof. intros HX Hd. cbn [BL.zden z_av0]. rewrite land15_digit by auto. reflexivity. Qed.

Lemma t_acy_val V : BL.inrange (V 33%nat) -> 48 <= V 22%nat <= 57 -> BL.zden V z_acy = (V 33%nat + (V 22%nat - 48)) / BL.MM.
Proof.
  intros HX Hd. cbn [BL.zden z_acy]. rewrite land15_digit by auto.
  change (if (V 33%nat + (V 22%nat - 48)) mod BL.MM <? V 33%nat then 1 else 0) with (BL.zb ((V 33%nat + (V 22%nat - 48)) mod BL.MM <? V 33%nat)).
  apply BL.carry_ltu_l. exact HX. unfold BL.inrange, BL.MM. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_lit (i : nat) (r : bv 5) : bv_unsigned r = Z.of_nat i -> r = Z_to_bv 5 (Z.of_nat i).
Proof. intros H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.

Lemma pc_lit (z : Z) (w : word) : bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros H. symmetry. apply BGU.word_of_unsigned. exact H. Qed.

Lemma bv_nonzero (w : word) z : bv_unsigned w = z -> z <> 0 -> w <> Z_to_bv 64 0.
Proof. intros Hw Hz E. apply Hz. rewrite <- Hw, E. reflexivity. Qed.
Lemma bv_zero (w : word) : bv_unsigned w = 0 -> w = Z_to_bv 64 0.
Proof. intros Hw. apply BGU.word_of_unsigned. exact Hw. Qed.
Lemma lit_nonzero z : 0 < z < 2 ^ 64 -> Z_to_bv 64 z <> Z_to_bv 64 0.
Proof. intros Hz E. apply (f_equal bv_unsigned) in E. rewrite !BGU.unsigned_lit in E by lia. lia. Qed.

(* [comment removed for export] *)
Definition ICOMMON : list kentry :=
  [KRange (EVar 2) 140735340000000 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-400)) (ELit 432); KImg 65536 131072].

Lemma icommon_kn E M s : bv_unsigned (ev E 2) = s -> iframe M s -> Forall (kentry_ok RSEGS E M) ICOMMON.
Proof.
  intros U2 (A1 & A2 & A3 & A4 & A5). unfold ICOMMON.
  apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
  apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. exact A3. }
  apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact A4. }
  apply Forall_cons. { apply kentry_KImg. exact A5. }
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma u64_at_mod M a v : BGU.u64_at M a v <-> BGU.u64_at M a (v mod 2 ^ 64).
Proof.
  unfold BGU.u64_at. replace (Z_to_bv 64 (v mod 2 ^ 64)) with (Z_to_bv 64 v). tauto.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

End BIU.
