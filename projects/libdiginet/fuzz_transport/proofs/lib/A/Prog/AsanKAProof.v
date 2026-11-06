From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
Import ListNotations.
Open Scope Z_scope.

Lemma rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma rdw : forall m (w : word) k a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w + k = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned w + k)) 1 = Some [b].
Proof. intros m w k a b H E. rewrite E. apply rd1. exact H. Qed.

Lemma rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply rd1. exact H. Qed.

Lemma mrd_tp : forall m m' lo hi a b, munch [(lo, hi)] m m' -> 0 <= a < 2^64 -> (a < lo \/ hi <= a) ->
  mrd rsegs m (wa a) = Some b -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros m m' lo hi a b MU Ha Hd H. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma bytes_nth : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  mrd rsegs m (wa (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros m a bs i (H0 & H1 & H) Hi. rewrite H by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Lemma bytes_one : forall m a k, bytes_at rsegs m a [k] -> mrd rsegs m (wa a) = Some k.
Proof.
  intros m a k H. pose proof (bytes_nth m a [k] 0 H ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma bytes_one_range : forall m a k, bytes_at rsegs m a [k] -> 0 <= a < 2^64.
Proof. intros m a k (H0 & H1 & _). cbn [length Z.of_nat] in H1. lia. Qed.

Lemma bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.

Lemma byte_signed_range : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. pose proof (bv_signed_in_range 8 k ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R. lia.
Qed.

Lemma sxb_eq0 : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof.
  intros k. unfold sxb, bv_eqb. pose proof (byte_signed_range k).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.eqb_spec (bv_signed k) 0) as [E|E].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. change (0 mod 2^64) with 0. Z.div_mod_to_equations. lia.
Qed.

Lemma lts_low : forall (x : Z) (k : byte), 0 <= x < 8 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma zxb_u : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Lemma lor_bytes16 : forall x y : byte,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x)))
  = bv_unsigned x + 256 * bv_unsigned y.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned y) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  apply unsigned_lit. lia.
Qed.

Lemma lor_pow32 : forall x, 0 <= x < 2^32 -> Z.lor x 4294967296 = x + 4294967296.
Proof.
  intros x Hx. change 4294967296 with (2^32).
  rewrite <- Z.lxor_lor by (apply zb_land_pow2_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_small; lia). reflexivity.
Qed.

Ltac gen_addi x w U := match goal with
  | |- context [Some (Z_to_bv 64 (bv_unsigned x + ?c))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned x + c)) = bv_unsigned x + c)
        by (apply unsigned_lit; first [lia | Z.div_mod_to_equations; lia]);
      remember (Z_to_bv 64 (bv_unsigned x + c)) as w eqn:Ew; clear Ew
  end.

Ltac gen_shr x w U := match goal with
  | |- context [Some (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) = bv_unsigned x / 8)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; apply unsigned_lit;
            pose proof (bv_unsigned_in_range 64 x) as Rx; unfold bv_modulus in Rx;
            change (2 ^ Z.of_N 64) with (2^64) in Rx;
            split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
      remember (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) as w eqn:Ew; clear Ew
  end.

Ltac gen_add x y w U := match goal with
  | |- context [Some (Z_to_bv 64 (bv_unsigned x + bv_unsigned y))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned y)) = bv_unsigned x + bv_unsigned y)
        by (apply unsigned_lit; lia);
      remember (Z_to_bv 64 (bv_unsigned x + bv_unsigned y)) as w eqn:Ew; clear Ew
  end.
