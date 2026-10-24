(** Exact list decomposition and budgets for the Adler 16-byte blocks. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcModel CrcSuffix AdlerModel AdlerBlock.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Lemma adler_firstn16_bytes : forall (inp : list byte) i,
  0 <= i -> i+16 <= Z.of_nat (length inp) ->
  firstn 16 (skipn (Z.to_nat i) inp) = adler_block16_bytes inp i.
Proof.
  intros inp i HI HL. unfold adler_block16_bytes.
  rewrite (skipn_byte_cons inp (Z.to_nat i) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat i)) with (Z.to_nat (i+1)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+1)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+1))) with (Z.to_nat (i+2)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+2)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+2))) with (Z.to_nat (i+3)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+3)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+3))) with (Z.to_nat (i+4)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+4)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+4))) with (Z.to_nat (i+5)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+5)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+5))) with (Z.to_nat (i+6)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+6)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+6))) with (Z.to_nat (i+7)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+7)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+7))) with (Z.to_nat (i+8)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+8)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+8))) with (Z.to_nat (i+9)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+9)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+9))) with (Z.to_nat (i+10)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+10)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+10))) with (Z.to_nat (i+11)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+11)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+11))) with (Z.to_nat (i+12)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+12)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+12))) with (Z.to_nat (i+13)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+13)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+13))) with (Z.to_nat (i+14)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+14)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+14))) with (Z.to_nat (i+15)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+15)) ltac:(lia)). cbn [firstn].
  reflexivity.
Qed.
Lemma adler_output_suffix_chunk : forall inp i (k : nat) a b,
  0 <= i -> adler_output (skipn (Z.to_nat i) inp) a b =
  let '(u,v) := adler_raw (firstn k (skipn (Z.to_nat i) inp)) a b in
  adler_output (skipn (Z.to_nat (i+Z.of_nat k)) inp) u v.
Proof.
  intros inp i k a b HI. unfold adler_output at 1.
  rewrite <- (firstn_skipn k (skipn (Z.to_nat i) inp)) at 1.
  rewrite adler_raw_append,skipn_skipn.
  replace (Z.to_nat (i+Z.of_nat k)) with (k+Z.to_nat i)%nat by lia.
  destruct (adler_raw (firstn k (skipn (Z.to_nat i) inp)) a b) as [u v]. reflexivity.
Qed.
Lemma adler_suffix_sixteen : forall inp i a b,
  0 <= i -> i+16 <= Z.of_nat (length inp) ->
  adler_output (skipn (Z.to_nat i) inp) a b =
  adler_output (skipn (Z.to_nat (i+16)) inp) (adler_block16_a inp i a b) (adler_block16_b inp i a b).
Proof.
  intros inp i a b HI HL. rewrite (adler_output_suffix_chunk inp i 16 a b HI).
  rewrite adler_firstn16_bytes by assumption. unfold adler_block16_a,adler_block16_b.
  destruct (adler_raw (adler_block16_bytes inp i) a b) as [u v]. reflexivity.
Qed.
Lemma adler_block16_range : forall inp i a b, 0 <= a -> 0 <= b ->
  0 <= adler_block16_a inp i a b <= a+255*16 /\
  0 <= adler_block16_b inp i a b <= b+16*a+255*16*16.
Proof.
  intros inp i a b HA HB. pose proof (adler_raw_bound (adler_block16_bytes inp i) a b HA HB) as H.
  change (length (adler_block16_bytes inp i)) with 16%nat in H.
  unfold adler_block16_a,adler_block16_b.
  destruct (adler_raw (adler_block16_bytes inp i) a b) as [u v]. exact H.
Qed.
Lemma adler_budget_sixteen : forall inp i k a b cap,
  16 <= k -> 0 <= a -> 0 <= b -> a+255*k < cap -> b+k*a+255*k*k < cap ->
  adler_block16_a inp i a b+255*(k-16) < cap /\
  adler_block16_b inp i a b+(k-16)*adler_block16_a inp i a b+255*(k-16)*(k-16) < cap.
Proof.
  intros inp i k a b cap HK HA HB BA BB.
  pose proof (adler_block16_range inp i a b HA HB) as [RA RB]. split;nia.
Qed.
