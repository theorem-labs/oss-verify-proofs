(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/FrameBytes.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn1_skipn : forall (bs : list byte) k, (k < length bs)%nat ->
  firstn 1 (skipn k bs) = [nth k bs (Z_to_bv 8 0)].
Proof.
  induction bs as [|b bs IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rd1 : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_ov_read rsegs m a bs k 1 H) by lia.
  rewrite firstn1_skipn by exact Hk. reflexivity.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma zxb_u : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Lemma lor_pow32 : forall x, 0 <= x < 2^32 -> Z.lor x 4294967296 = x + 4294967296.
Proof.
  intros x Hx. change 4294967296 with (2^32).
  rewrite <- Z.lxor_lor by (apply zb_land_pow2_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_small; lia). reflexivity.
Qed.

Lemma lor_bytes16 : forall x y : byte,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x)))
  = bv_unsigned x + 256 * bv_unsigned y.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned y) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  apply unsigned_lit. lia.
Qed.
