From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require IdentSpec put_dec_c put_dec.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.IdentSpec(DEC, dg).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec(ds_lsb, dec_ds).
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Lemma pd_dec_rev : forall v mn, 0 <= v < 2 ^ 32 -> 0 <= mn <= 10 ->
  DEC v mn = rev (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat mn - length (ds_lsb 10 v)))
  /\ dec_len v mn = Z.max mn (Z.of_nat (length (ds_lsb 10 v))).
Proof.
  intros v mn Hv Hmn.
  assert (DE : DEC v mn = rev (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat mn - length (ds_lsb 10 v)))).
  { unfold DEC. rewrite (dec_ds v Hv). rewrite rev_app_distr, rev_repeat, length_rev. reflexivity. }
  split; [exact DE|].
  unfold dec_len. rewrite DE, length_rev, length_app, repeat_length. lia.
Qed.
