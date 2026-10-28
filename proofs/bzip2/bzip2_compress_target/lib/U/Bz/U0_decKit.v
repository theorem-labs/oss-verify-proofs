From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs.
Open Scope Z_scope.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Lemma strm_flag_ok : forall cx, ctx_ok cx ->
  Z.land (Z.b2z (0 <? b_strm cx)) (Z.b2z (Z.land (b_strm cx) 7 <? 1)) = 1.
Proof.
  intros cx H. unfold ctx_ok, ctx_lin, ctx_al in H. cbv zeta in H. decompose [and] H. clear H.
  assert (L7 : Z.land (b_sp cx) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_divide; [lia|].
    match goal with E : b_sp cx mod 16 = 0 |- _ => apply Z.mod_divide in E; [destruct E as [k E]; exists (2 * k); lia | lia] end. }
  match goal with E : b_strm cx = b_sp cx |- _ => rewrite E end. rewrite L7.
  assert (P : (0 <? b_sp cx) = true) by (apply Z.ltb_lt; unfold DSTATE_SIZE in *; lia).
  rewrite P. reflexivity.
Qed.

End ACeilS1.

Lemma lor_bs100k : forall k, Z.lor (k * 100000) 10 = k * 100000 + 10.
Proof.
  intros k.
  assert (L : Z.land (k * 100000) 10 = 0).
  { assert (Eb : Z.land 10 (Z.ones 5) = 10) by reflexivity.
    rewrite <- Eb, (Z.land_comm 10 (Z.ones 5)), Z.land_assoc, Z.land_ones by lia.
    replace (k * 100000) with ((k * 3125) * 2 ^ 5) by (change (2 ^ 5) with 32; lia).
    rewrite Z.mod_mul by (change (2 ^ 5) with 32; lia). reflexivity. }
  rewrite (Z.add_nocarry_lxor _ _ L). symmetry. apply Z.lxor_lor. exact L.
Qed.
