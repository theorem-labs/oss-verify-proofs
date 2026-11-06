From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcRec.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_eqb0 : forall x, 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof. intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_neq0w : forall x : word, bv_unsigned x <> 0 -> bv_eqb x (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. exact Hx. Qed.

Lemma rc_eq0w : forall x : word, bv_unsigned x = 0 -> bv_eqb x (Z_to_bv 64 0) = true.
Proof. intros x Hx. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_eq. exact Hx. Qed.

Lemma rc_ltu_ge : forall a x : word, bv_unsigned a <= bv_unsigned x -> bv_ltu x a = false.
Proof. intros a x H. unfold bv_ltu. apply Z.ltb_ge. exact H. Qed.

Lemma rc_ubchk : forall a x : word, bv_unsigned a <> 0 -> bv_unsigned x <> 0 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 0) a)) (bv_unsigned (v_sltiu x 1)))) (Z_to_bv 64 0) = false.
Proof.
  intros a x Ha Hx. rewrite v_sltu_b2z, v_sltiu_b2z.
  pose proof (zr_word a) as Ra. pose proof (zr_word x) as Rx. unfold inr64 in Ra, Rx.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. change (bv_wrap 64 1) with 1.
  replace (0 <? bv_unsigned a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (bv_unsigned x <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma rc_mod128 : forall s, (s mod 2^64) mod 128 = s mod 128.
Proof. intros s. Z.div_mod_to_equations. lia. Qed.

Lemma rc_fin1 : forall s,
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 127)) 1 = Z_to_bv 64 (if s mod 128 =? 0 then 1 else 0).
Proof.
  intros s. rewrite v_sltiu_b2z. rewrite (unsigned_lit_wrap s).
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2^7) with 128.
  rewrite rc_mod128.
  pose proof (Z.mod_pos_bound s 128 ltac:(lia)) as M.
  rewrite (unsigned_lit (s mod 128)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (s mod 128) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (s mod 128 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rc_fin2 : forall s,
  Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 127)) 1) + -1) =
  Z_to_bv 64 (if s mod 128 =? 0 then 0 else -1).
Proof. intros s. rewrite rc_fin1. destruct (s mod 128 =? 0); reflexivity. Qed.

Lemma rc_swrap32_mod128 : forall x, bv_swrap 32 x mod 128 = x mod 128.
Proof.
  intros x. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rc_negw : forall s,
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) 127 = (- s) mod 128.
Proof.
  intros s. rewrite !unsigned_lit_wrap.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2^7) with 128.
  rewrite rc_mod128, rc_swrap32_mod128.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rc_le1_stamp : forall s,
  le1 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) 127)) =
  [Z_to_bv 8 ((- s) mod 128)].
Proof.
  intros s. rewrite rc_negw. unfold le1.
  pose proof (Z.mod_pos_bound (- s) 128 ltac:(lia)) as M.
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma psum_app_l : forall bs cs k, (k <= length bs)%nat -> psum (bs ++ cs) k = psum bs k.
Proof.
  intros bs cs k. induction k as [|k IH]; intros Hk; cbn [psum]; [reflexivity|].
  rewrite IH by lia. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma rc_recsum_stamp : forall bs, recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0.
Proof.
  intros bs. unfold recsum, stampck. rewrite length_app. cbn [length].
  replace (length bs + 1)%nat with (S (length bs)) by lia. cbn [psum].
  rewrite psum_app_l by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  pose proof (Z.mod_pos_bound (- psum bs (length bs)) 128 ltac:(lia)) as M.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small _ 256) by lia.
  Z.div_mod_to_equations. lia.
Qed.
