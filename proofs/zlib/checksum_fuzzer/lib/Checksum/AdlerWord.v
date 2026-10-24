(** Unsigned word identities for the actual Adler-32 instructions. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel CrcLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Lemma adler_mulhu_bounds : forall x, 0 <= x < 2^64 ->
  0 <= x*ADLER_MAGIC/2^64 <= x.
Proof.
  intros x HX. unfold ADLER_MAGIC.
  pose proof (Z.div_mod (x*4223091239536077) (2^64) ltac:(lia)) as DH.
  pose proof (Z.mod_pos_bound (x*4223091239536077) (2^64) ltac:(lia)) as RH.
  split;[apply Z.div_pos;lia|lia].
Qed.
Lemma adler_div_form : forall x, 0 <= x < 2^64 ->
  Z.shiftr (Z.shiftr (x-Z.shiftr (x*ADLER_MAGIC) 64) 1 + Z.shiftr (x*ADLER_MAGIC) 64) 15 = x/ADLER_BASE.
Proof.
  intros x HX. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^1) with 2. rewrite Z.add_comm.
  apply adler_div_magic. exact HX.
Qed.
Lemma adler_pack_range : forall a b, 0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
  0 <= adler_pack a b < 2^32.
Proof. intros. unfold adler_pack,ADLER_BASE in *. lia. Qed.
Lemma adler_pack_low : forall a b, 0 <= a < ADLER_BASE ->
  adler_pack a b mod 65536 = a.
Proof.
  intros a b HA. unfold adler_pack. rewrite Z.add_comm,Z.mod_add by lia.
  apply Z.mod_small. unfold ADLER_BASE in HA. lia.
Qed.
Lemma adler_pack_high : forall a b, 0 <= a < ADLER_BASE ->
  Z.shiftr (adler_pack a b) 16 = b.
Proof.
  intros a b HA. rewrite Z.shiftr_div_pow2 by lia. unfold adler_pack.
  change (2^16) with 65536. rewrite Z.add_comm,Z.div_add by lia.
  rewrite Z.div_small by (unfold ADLER_BASE in HA;lia). ring.
Qed.
Lemma adler_pack_or : forall a b, 0 <= a < 65536 -> 0 <= b < 65536 ->
  Z.lor (Z.shiftl b 16) a = adler_pack a b.
Proof.
  intros a b HA HB.
  assert (HL : Z.land (Z.shiftl b 16) a = 0).
  { apply Z.bits_inj'. intros k HK. rewrite Z.land_spec,(testbit_small 0 0 k ltac:(lia) ltac:(lia)).
    destruct (Z_lt_ge_dec k 16).
    - rewrite Z.shiftl_spec by lia. rewrite Z.testbit_neg_r by lia. reflexivity.
    - rewrite (testbit_small a 16 k ltac:(exact HA) ltac:(lia)),andb_false_r. reflexivity. }
  pose proof (Z.add_lor_land (Z.shiftl b 16) a) as H.
  rewrite HL,Z.add_0_r in H. rewrite H,Z.shiftl_mul_pow2 by lia.
  unfold adler_pack. reflexivity.
Qed.
