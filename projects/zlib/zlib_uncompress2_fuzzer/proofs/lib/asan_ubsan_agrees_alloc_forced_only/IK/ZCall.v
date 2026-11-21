(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import ZSysLite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma land_m16_id : forall x, x mod 16 = 0 -> Z.land x (-16) = x.
Proof.
  intros x Hx. rewrite <- (Z.lnot_involutive (-16)). change (Z.lnot (-16)) with (Z.ones 4).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite (Z_div_exact_2 x 16) at 2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. lia.
Qed.

Lemma land_ones_mod : forall x n, 0 <= n -> Z.land x (Z.ones n) = x mod 2 ^ n.
Proof. intros. apply Z.land_ones. assumption. Qed.

Lemma land3_of_mod : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hx. Qed.
Lemma land4_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 4 = 0.
Proof.
  intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 2) as [->|Hne].
  - replace x with ((x / 8) * 2^3) by (change (2^3) with 8; pose proof (Z_div_mod_eq_full x 8); lia).
    rewrite Z.mul_pow2_bits by lia. cbn. reflexivity.
  - replace (Z.testbit 4 n) with false; [apply Bool.andb_false_r|].
    symmetry. change 4 with (2^2). apply Z.pow2_bits_false. lia.
Qed.
Lemma land_m4_id : forall x, x mod 4 = 0 -> Z.land x (-4) = x.
Proof.
  intros x Hx. rewrite <- (Z.lnot_involutive (-4)). change (Z.lnot (-4)) with (Z.ones 2).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite (Z_div_exact_2 x 4) at 2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. lia.
Qed.
Lemma land_m8_id : forall x, x mod 8 = 0 -> Z.land x (-8) = x.
Proof.
  intros x Hx. rewrite <- (Z.lnot_involutive (-8)). change (Z.lnot (-8)) with (Z.ones 3).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite (Z_div_exact_2 x 8) at 2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.
Lemma land_m32_floor : forall x, 0 <= x -> Z.land x (-32) = x - x mod 32.
Proof.
  intros x Hx. rewrite <- (Z.lnot_involutive (-32)). change (Z.lnot (-32)) with (Z.ones 5).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  pose proof (Z_div_mod_eq_full x 32). lia.
Qed.

Lemma swrap32_small : forall x, -2147483648 <= x < 2147483648 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap64_small : forall x, -9223372036854775808 <= x < 9223372036854775808 -> bv_swrap 64 x = x.
Proof.
  intros x Hx. unfold bv_swrap. change (bv_half_modulus 64) with 9223372036854775808.
  unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zadd_lit_l : forall a x b, a + (x + b) = x + (a + b). Proof. intros; lia. Qed.
Lemma zadd_lit_l0 : forall a x, a + x = x + a. Proof. intros; lia. Qed.

Lemma Z_to_le_bytes_add : forall n m z,
  Z_to_le_bytes (n + m) z = Z_to_le_bytes n z ++ Z_to_le_bytes m (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros m z.
  - cbn [Z_to_le_bytes app Nat.add]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes app Nat.add]. f_equal. rewrite IH. f_equal. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma mem_u64_lo32 : forall segs M a e, mem_u64 segs M a e -> mem_u32 segs M a e.
Proof.
  intros segs M a e H. unfold mem_u64, mem_u32 in *.
  change 8%nat with (4 + 4)%nat in H. rewrite Z_to_le_bytes_add in H.
  apply mem_is_app_l in H. exact H.
Qed.

Lemma mem_u64_hi32 : forall segs M a e, mem_u64 segs M a e -> mem_u32 segs M (a + 4) (Z.shiftr e 32).
Proof.
  intros segs M a e H. unfold mem_u64, mem_u32 in *.
  change 8%nat with (4 + 4)%nat in H. rewrite Z_to_le_bytes_add in H.
  apply mem_is_app_r in H. rewrite length_Z_to_le_bytes in H. exact H.
Qed.

Lemma mem_is_app : forall segs M a xs ys,
  mem_is segs M a xs -> mem_is segs M (a + Z.of_nat (length xs)) ys ->
  0 <= a -> a + Z.of_nat (length xs) + Z.of_nat (length ys) <= two64 ->
  mem_is segs M a (xs ++ ys).
Proof.
  intros segs M a xs ys Hx Hy Ha Hn. unfold mem_is in *. rewrite length_app.
  apply rdn_app; [exact Hx|]. rewrite w64_add_nat. exact Hy.
Qed.

Lemma mem_u32x2_u64_zero : forall segs M a,
  mem_u32 segs M a 0 -> mem_u32 segs M (a + 4) 0 -> 0 <= a -> a + 8 <= two64 ->
  mem_u64 segs M a 0.
Proof.
  intros segs M a H1 H2 Ha Hn. unfold mem_u64, mem_u32 in *.
  change (Z_to_le_bytes 8 0) with (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0).
  apply mem_is_app; try assumption. cbn [length Z_to_le_bytes Z.of_nat]. lia.
Qed.

Definition framed (Fr : mem -> Prop) (M : mem) : Prop := Fr M.
Definition wb_stable (Fr : mem -> Prop) (lo hi : Z) : Prop :=
  forall M a bs, framed Fr M -> lo <= a -> a + Z.of_nat (length bs) <= hi -> framed Fr (wbytes M (w64 a) bs).
Definition wb_stable2 (Fr : mem -> Prop) (lo1 hi1 lo2 hi2 : Z) : Prop :=
  forall M a bs, framed Fr M ->
    (lo1 <= a /\ a + Z.of_nat (length bs) <= hi1) \/ (lo2 <= a /\ a + Z.of_nat (length bs) <= hi2) ->
    framed Fr (wbytes M (w64 a) bs).

Definition magree (M0 M : mem) (lo1 hi1 lo2 hi2 : Z) : Prop :=
  forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> M x = M0 x.

Lemma magree_refl : forall M lo1 hi1 lo2 hi2, magree M M lo1 hi1 lo2 hi2.
Proof. intros M lo1 hi1 lo2 hi2 x _ _. reflexivity. Qed.

Lemma wbytes_out : forall bs m a (x : word),
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  ~ (a <= bv_unsigned x < a + Z.of_nat (length bs)) -> wbytes m (w64 a) bs x = m x.
Proof.
  intros bs m a x Ha Hn Hx. destruct bs as [|b bs']; [reflexivity|].
  assert (a < two64) by (cbn [length] in Hn; lia).
  destruct (Z.lt_ge_cases (bv_unsigned x) a).
  - apply wbytes_below; rewrite w64_unsigned, mod_small_u64; lia.
  - apply wbytes_above. rewrite w64_unsigned, mod_small_u64; lia.
Qed.

Lemma magree_stable : forall M0 lo1 hi1 lo2 hi2,
  0 <= lo1 -> hi1 <= two64 -> 0 <= lo2 -> hi2 <= two64 ->
  wb_stable2 (fun M => magree M0 M lo1 hi1 lo2 hi2) lo1 hi1 lo2 hi2.
Proof.
  intros M0 lo1 hi1 lo2 hi2 B1 B2 B3 B4 M a bs HF Hr. unfold framed, magree in *.
  intros x Hx1 Hx2. rewrite wbytes_out; [apply HF; assumption| lia | lia |].
  intros Hin. destruct Hr as [[? ?]|[? ?]]; [apply Hx1|apply Hx2]; lia.
Qed.

Lemma mem_is_magree : forall segs M0 M lo1 hi1 lo2 hi2 a bs,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_is segs M0 a bs ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= lo1 \/ hi1 <= a) -> (a + Z.of_nat (length bs) <= lo2 \/ hi2 <= a) ->
  mem_is segs M a bs.
Proof.
  intros segs M0 M lo1 hi1 lo2 hi2 a bs HA H Ha Hn H1 H2. unfold mem_is in *.
  destruct bs as [|b bs']; [reflexivity|].
  assert (a < two64) by (cbn [length] in Hn; lia).
  rewrite (rdn_ext segs (length (b :: bs')) M M0 (w64 a)); [exact H| |];
    rewrite w64_unsigned, mod_small_u64 by lia; [rewrite <- two64_eq; lia|].
  intros x Hx. apply HA; lia.
Qed.

Lemma mem_u64_magree : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u64 segs M0 a e ->
  0 <= a -> a + 8 <= two64 ->
  (a + 8 <= lo1 \/ hi1 <= a) -> (a + 8 <= lo2 \/ hi2 <= a) ->
  mem_u64 segs M a e.
Proof.
  intros. unfold mem_u64 in *. eapply mem_is_magree; try eassumption; rewrite length_Z_to_le_bytes; lia.
Qed.

Definition mpost (segs : list Segment) (M X : mem) (lo1 hi1 lo2 hi2 : Z) : Prop :=
  magree M X lo1 hi1 lo2 hi2 /\ (forall a n, mem_wr segs M a n -> mem_wr segs X a n).

Lemma mpost_refl : forall segs M lo1 hi1 lo2 hi2, mpost segs M M lo1 hi1 lo2 hi2.
Proof. intros. split; [apply magree_refl | auto]. Qed.

Lemma mpost_stable : forall segs M0 lo1 hi1 lo2 hi2,
  0 <= lo1 -> hi1 <= two64 -> 0 <= lo2 -> hi2 <= two64 ->
  wb_stable2 (fun M => mpost segs M0 M lo1 hi1 lo2 hi2) lo1 hi1 lo2 hi2.
Proof.
  intros segs M0 lo1 hi1 lo2 hi2 B1 B2 B3 B4 M a bs [HA HW] Hr. unfold framed. split.
  - apply (magree_stable M0 lo1 hi1 lo2 hi2 B1 B2 B3 B4 M a bs HA Hr).
  - intros a' n' H. apply mem_wr_frame. apply HW. exact H.
Qed.

Lemma mpost_trans : forall segs M1 M2 M3 lo1 hi1 lo2 hi2,
  mpost segs M1 M2 lo1 hi1 lo2 hi2 -> mpost segs M2 M3 lo1 hi1 lo2 hi2 -> mpost segs M1 M3 lo1 hi1 lo2 hi2.
Proof.
  intros segs M1 M2 M3 lo1 hi1 lo2 hi2 [A1 W1] [A2 W2]. split.
  - intros x X1 X2. rewrite (A2 x X1 X2). apply A1; assumption.
  - auto.
Qed.

End FXG.
Ltac zmem_transport M a bs ::=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_tac] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_frame segs M a bs a' len) in H; [|zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zfold_addl :=
  repeat match goal with
  | |- context [?a + (?x + ?b)] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a + b) in
      rewrite (zadd_lit_l a x b); change (a + b) with c
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac znorm_tree ::=
  cbv beta iota delta [wb zrd_l zget_l zalu zalu32 zalu32u zmul zmul32 zcond zjalr_tgt];
  cbn beta iota delta [alookup Pos.eqb];
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd ?Rb _) _ _) _ =>
      tryif is_var Rb then idtac else cbv beta iota delta [zget tget]
  | |- context [zget ?Rb _] => tryif is_var Rb then idtac else cbv beta iota delta [zget tget]
  | |- _ => idtac
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma mod8_neg_mod4 : forall s, s mod 8 = 0 -> (0 - s) mod 4 = 0.
Proof. intros s H. pose proof (Z_div_mod_eq_full s 8). replace (0 - s) with ((- 2 * (s/8)) * 4) by lia. apply Z_mod_mult. Qed.
Lemma mod16_mod8 : forall s k, s mod 16 = 0 -> (s + 8 * k) mod 8 = 0.
Proof. intros s k H. pose proof (Z_div_mod_eq_full s 16). replace (s + 8 * k) with ((2 * (s/16) + k) * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod16_add : forall s k, s mod 16 = 0 -> (s + 16 * k) mod 16 = 0.
Proof. intros s k H. pose proof (Z_div_mod_eq_full s 16). replace (s + 16 * k) with (((s/16) + k) * 16) by lia. apply Z_mod_mult. Qed.

Lemma mem_u32_magree : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u32 segs M0 a e ->
  0 <= a -> a + 4 <= two64 ->
  (a + 4 <= lo1 \/ hi1 <= a) -> (a + 4 <= lo2 \/ hi2 <= a) ->
  mem_u32 segs M a e.
Proof.
  intros. unfold mem_u32 in *. eapply mem_is_magree; try eassumption; rewrite length_Z_to_le_bytes; lia.
Qed.

Lemma framed_magree_trans : forall M0 Mo Mn l1 h1 l2 h2 a1 b1 a2 b2,
  framed (fun X => magree M0 X l1 h1 l2 h2) Mo -> magree Mo Mn a1 b1 a2 b2 ->
  (b1 <= a1 \/ (l1 <= a1 /\ b1 <= h1) \/ (l2 <= a1 /\ b1 <= h2)) ->
  (b2 <= a2 \/ (l1 <= a2 /\ b2 <= h1) \/ (l2 <= a2 /\ b2 <= h2)) ->
  framed (fun X => magree M0 X l1 h1 l2 h2) Mn.
Proof.
  intros M0 Mo Mn l1 h1 l2 h2 a1 b1 a2 b2 HF HA H1 H2. unfold framed, magree in *.
  intros x X1 X2. rewrite (HA x) by lia. apply HF; assumption.
Qed.

Lemma framed_mpost_trans : forall segs M0 Mo Mn l1 h1 l2 h2 a1 b1 a2 b2,
  framed (fun X => mpost segs M0 X l1 h1 l2 h2) Mo -> mpost segs Mo Mn a1 b1 a2 b2 ->
  (b1 <= a1 \/ (l1 <= a1 /\ b1 <= h1) \/ (l2 <= a1 /\ b1 <= h2)) ->
  (b2 <= a2 \/ (l1 <= a2 /\ b2 <= h1) \/ (l2 <= a2 /\ b2 <= h2)) ->
  framed (fun X => mpost segs M0 X l1 h1 l2 h2) Mn.
Proof.
  intros segs M0 Mo Mn l1 h1 l2 h2 a1 b1 a2 b2 [HF HWF] [HA HW] H1 H2. unfold framed. split.
  - apply (framed_magree_trans M0 Mo Mn l1 h1 l2 h2 a1 b1 a2 b2 HF HA H1 H2).
  - auto.
Qed.

End FXG.
Ltac zreattach HP :=
  let HA := fresh "HA" in let HW := fresh "HW" in
  destruct HP as [HA HW];
  lazymatch type of HA with magree ?Mo ?Mn _ _ _ _ =>
  repeat match goal with
  | H : mem_u64 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u64_magree segs Mo Mn _ _ _ _ a e HA) in H; [|zlia|zlia|zlia|zlia]
            | idtac "zreattach: dropped u64 fact at" a; clear H ]
  | H : mem_u32 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u32_magree segs Mo Mn _ _ _ _ a e HA) in H; [|zlia|zlia|zlia|zlia]
            | idtac "zreattach: dropped u32 fact at" a; clear H ]
  | H : mem_is ?segs Mo ?a ?bs |- _ =>
      first [ apply (mem_is_magree segs Mo Mn _ _ _ _ a bs HA) in H; [|zlia|zlen_norm; zlia|zlen_norm; zlia|zlen_norm; zlia]
            | idtac "zreattach: dropped mem_is fact at" a; clear H ]
  | H : framed _ Mo |- _ =>
      first [ let H' := fresh in
              pose proof (framed_mpost_trans _ _ Mo Mn _ _ _ _ _ _ _ _ H (conj HA HW) ltac:(zlia) ltac:(zlia)) as H';
              clear H; rename H' into H
            | idtac "zreattach: could not transfer framed mpost"; clear H ]
  | H : mem_wr ?segs Mo ?a ?n |- _ => apply (HW a n) in H
  | H : mem_u8 ?segs Mo _ _ |- _ => clear H
  | H : mem_zero ?segs Mo _ _ |- _ => clear H
  end; clear HA HW; try clear Mo end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zimport E :=
  cbv [zget_l] in E; cbn [alookup Pos.eqb] in E;
  repeat match goal with
  | H : alookup ?l ?k = _ |- _ => lazymatch type of E with context [alookup l k] => rewrite H in E; cbv iota in E end
  | H : zget ?Rb ?k = _ |- _ => lazymatch type of E with _ = zget Rb k => rewrite H in E end
  end;
  lazymatch type of E with
  | _ = zget ?Rb _ => tryif is_var Rb then idtac else cbv [zget tget] in E
  | _ => idtac
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zfold_in H := revert H; zfold; intros H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma mem_u64_magree_c : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u64 segs M0 a e ->
  (0 <= a /\ a + 8 <= two64 /\ (a + 8 <= lo1 \/ hi1 <= a) /\ (a + 8 <= lo2 \/ hi2 <= a)) ->
  mem_u64 segs M a e.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a e HA H (H1 & H2 & H3 & H4). exact (mem_u64_magree segs M0 M lo1 hi1 lo2 hi2 a e HA H H1 H2 H3 H4). Qed.
Lemma mem_is_magree_c : forall segs M0 M lo1 hi1 lo2 hi2 a bs,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_is segs M0 a bs ->
  (0 <= a /\ a + Z.of_nat (length bs) <= two64 /\ (a + Z.of_nat (length bs) <= lo1 \/ hi1 <= a) /\ (a + Z.of_nat (length bs) <= lo2 \/ hi2 <= a)) ->
  mem_is segs M a bs.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a bs HA H (H1 & H2 & H3 & H4). exact (mem_is_magree segs M0 M lo1 hi1 lo2 hi2 a bs HA H H1 H2 H3 H4). Qed.

End FXG.
Ltac zderive64 HAG SF name :=
  lazymatch type of HAG with framed _ ?Mc =>
  lazymatch type of SF with mem_u64 ?segs ?M0 ?a ?e =>
    pose proof (mem_u64_magree_c segs M0 Mc _ _ _ _ a e (proj1 HAG) SF ltac:(solve [zlia])) as name
  end end.
Ltac zderive_is HAG SF name :=
  lazymatch type of HAG with framed _ ?Mc =>
  lazymatch type of SF with mem_is ?segs ?M0 ?a ?bs =>
    pose proof (mem_is_magree_c segs M0 Mc _ _ _ _ a bs (proj1 HAG) SF ltac:(solve [zlen_norm; zlia])) as name
  end end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma tset_id : forall {X} (p : positive) (x : X) t, tget p t = Some x -> tset p x t = t.
Proof.
  intros X p. induction p as [p IH|p IH|]; intros x [|l v r] H; cbn in H |- *; try discriminate.
  - rewrite IH by exact H. reflexivity.
  - rewrite IH by exact H. reflexivity.
  - subst v. reflexivity.
Qed.

Lemma zget_tget : forall Rb k v, zget Rb k = v -> v <> 0 -> tget k Rb = Some v.
Proof.
  intros Rb k v H Hv. unfold zget in H. destruct (tget k Rb) as [e|]; [subst; reflexivity | subst; lia].
Qed.

Lemma zupd_app_same : forall Rb k v l, tget k Rb = Some v -> zupd Rb (l ++ [(k, v)]) = zupd Rb l.
Proof.
  intros Rb k v l H. induction l as [|[k' e] l IH]; cbn [zupd app].
  - unfold zset. apply tset_id. exact H.
  - rewrite IH. reflexivity.
Qed.
End FXG.
