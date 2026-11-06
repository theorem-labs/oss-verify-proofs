From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn1_skipn : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rd_byte : forall segs m (A : Z) (bs : list byte) (i : nat),
  bytes_at segs m A bs -> (i < length bs)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros segs m A bs i HB Hi. rewrite (bytes_at_read segs m A bs (Z.of_nat i) 1 HB) by lia.
  rewrite Nat2Z.id. apply f_equal. apply firstn1_skipn. exact Hi.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma psum_range : forall bs k, 0 <= psum bs k <= 255 * Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [psum]; [lia|].
  pose proof (byte_range (nth k bs (Z_to_bv 8 0))). lia.
Qed.

Lemma psum_S_zxb : forall bs i,
  psum bs i + bv_unsigned (zxb (nth i bs (Z_to_bv 8 0))) = psum bs (S i).
Proof.
  intros bs i. cbn [psum]. unfold zxb. pose proof (byte_range (nth i bs (Z_to_bv 8 0))).
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma eqb_le64 : forall x y, 0 < x <= 2^64 -> 0 < y <= 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E.
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma fin_a0 : forall s, 0 <= s < 2^64 ->
  Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 255)) 1) + -1) =
  Z_to_bv 64 (if s mod 256 =? 0 then 0 else -1).
Proof.
  intros s Hs. rewrite v_sltiu_b2z. rewrite (unsigned_lit s Hs).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  pose proof (Z.mod_pos_bound s 256 ltac:(lia)) as M.
  rewrite (unsigned_lit (s mod 256)) by lia.
  destruct (Z.eqb_spec (s mod 256) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (s mod 256 <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
    reflexivity.
Qed.
