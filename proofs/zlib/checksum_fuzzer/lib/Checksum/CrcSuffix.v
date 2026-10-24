(** List decomposition for a symbolic CRC suffix. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcLib CrcModel.
Import ListNotations.
Open Scope Z_scope.
Lemma skipn_byte_cons : forall (bs : list byte) n,
  (n < length bs)%nat ->
  skipn n bs = nth n bs (Z_to_bv 8 0) :: skipn (S n) bs.
Proof.
  idtac "CRC SUFFIX list decomposition".
  induction bs as [|b bs IH];intros n Hn;[cbn in Hn;lia|].
  destruct n;cbn;[reflexivity|apply IH;cbn in Hn;lia].
Qed.
Lemma raw_suffix_step : forall bs i q,
  0 <= i < Z.of_nat (length bs) ->
  raw_crc (skipn (Z.to_nat i) bs) q =
  raw_crc (skipn (Z.to_nat (i+1)) bs) (raw_byte q (bbyte bs i)).
Proof.
  idtac "CRC SUFFIX model update".
  intros bs i q Hi. rewrite skipn_byte_cons by lia.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.
