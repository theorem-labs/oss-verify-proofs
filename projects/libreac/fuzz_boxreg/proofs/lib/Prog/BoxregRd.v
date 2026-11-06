From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
Import ListNotations.
Open Scope Z_scope.

Lemma le_bytes_roundtrip : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg l) as Hl.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [exact IH|].
    Z.div_mod_to_equations. lia.
Qed.

Lemma le4_rd4 : forall bs k, length (bsub bs k 4) = 4%nat -> le4 (Z_to_bv 64 (rd4 bs k)) = bsub bs k 4.
Proof.
  intros bs k L. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (rd4 bs k) 32) by (cbn; lia).
  replace (rd4 bs k mod 2^32) with (bytes_le_to_Z (bsub bs k 4) mod 2^32).
  - rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- L at 1. apply le_bytes_roundtrip.
  - unfold rd4, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
    Z.div_mod_to_equations. lia.
Qed.

Lemma bytes_at_bsub : forall m r bs k n, bytes_at rsegs m r bs -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length bs) -> bytes_at rsegs m (r + k) (bsub bs k n).
Proof.
  intros m r bs k n (H0 & H1 & H2) Hk Hn Hkn.
  assert (Hlen : length (bsub bs k n) = Z.to_nat n) by (apply bsub_length; lia).
  unfold bytes_at. rewrite Hlen.
  split; [lia|]. split; [lia|].
  intros i Hi.
  replace (r + k + Z.of_nat i) with (r + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite H2 by lia.
  unfold bsub. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec i (Z.to_nat n)); [|lia].
  rewrite nth_error_skipn; f_equal; lia.
Qed.

Lemma rd4_bytes_at : forall m r bs k, bytes_at rsegs m r bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  bytes_at rsegs m (r + k) (le4 (Z_to_bv 64 (rd4 bs k))).
Proof.
  intros m r bs k HB Hk H.
  rewrite le4_rd4 by (apply bsub_length; lia).
  apply bytes_at_bsub; [exact HB | lia | lia | exact H].
Qed.
