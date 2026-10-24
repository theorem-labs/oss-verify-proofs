(** Adler-32 arithmetic and exact unsigned division used by the pinned binary. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcModel CrcLib CrcSuffix.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Definition ADLER_BASE : Z := 65521.
Definition ADLER_MAGIC : Z := 4223091239536077.
Lemma adler_div_magic : forall x, 0 <= x < 2^64 ->
  ((x*ADLER_MAGIC/2^64)+(x-x*ADLER_MAGIC/2^64)/2)/2^15 = x/ADLER_BASE.
Proof.
  intros x HX. unfold ADLER_MAGIC,ADLER_BASE.
  set (q := x/65521). set (r := x mod 65521).
  pose proof (Z.div_mod x 65521 ltac:(lia)) as DX.
  pose proof (Z.mod_pos_bound x 65521 ltac:(lia)) as RX. fold q r in DX,RX.
  assert (HQ : 0 <= q <= 281539415969071) by lia.
  set (h := x*4223091239536077/2^64).
  pose proof (Z.div_mod (x*4223091239536077) (2^64) ltac:(lia)) as DH.
  pose proof (Z.mod_pos_bound (x*4223091239536077) (2^64) ltac:(lia)) as RH. fold h in DH.
  assert (BD : q*2^80 <= x*18450967164949087693 < (q+1)*2^80).
  { replace (x*18450967164949087693) with (q*2^80+(q*26877+r*18450967164949087693)) by nia. nia. }
  assert (BH : q*65536 <= x+h < (q+1)*65536) by nia.
  replace (h+(x-h)/2) with ((x+h)/2).
  2:{ replace (x+h) with ((x-h)+h*2) by ring. rewrite Z.div_add by lia. ring. }
  rewrite Z.div_div by lia. change (2*2^15) with 65536.
  replace (x+h) with ((x+h-q*65536)+q*65536) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. unfold q. lia.
Qed.
Definition adler_pack (a b : Z) : Z := b*65536+a.
Fixpoint adler_raw (bs : list byte) (a b : Z) : Z*Z :=
  match bs with
  | [] => (a,b)
  | c::rest => adler_raw rest (a+bv_unsigned c) (b+a+bv_unsigned c)
  end.
Definition adler_output (bs : list byte) (a b : Z) : Z :=
  let '(u,v) := adler_raw bs a b in adler_pack (u mod ADLER_BASE) (v mod ADLER_BASE).
Lemma adler_raw_append : forall xs ys a b,
  adler_raw (xs++ys) a b = let '(u,v) := adler_raw xs a b in adler_raw ys u v.
Proof. induction xs;intros;cbn;[reflexivity|rewrite IHxs;reflexivity]. Qed.
Lemma adler_output_cons : forall c bs a b,
  adler_output (c::bs) a b = adler_output bs (a+bv_unsigned c) (b+a+bv_unsigned c).
Proof. reflexivity. Qed.
Lemma adler_output_congr : forall bs a b a' b',
  a mod ADLER_BASE = a' mod ADLER_BASE -> b mod ADLER_BASE = b' mod ADLER_BASE ->
  adler_output bs a b = adler_output bs a' b'.
Proof.
  induction bs as [|c bs IH];intros a b a' b' HA HB.
  - cbn [adler_output adler_raw]. rewrite HA,HB. reflexivity.
  - rewrite !adler_output_cons. apply IH.
    + rewrite (Z.add_mod a (bv_unsigned c) ADLER_BASE),
        (Z.add_mod a' (bv_unsigned c) ADLER_BASE),HA by (unfold ADLER_BASE;lia). reflexivity.
    + rewrite (Z.add_mod (b+a) (bv_unsigned c) ADLER_BASE),
        (Z.add_mod (b'+a') (bv_unsigned c) ADLER_BASE),
        (Z.add_mod b a ADLER_BASE),(Z.add_mod b' a' ADLER_BASE),HA,HB by (unfold ADLER_BASE;lia). reflexivity.
Qed.
Theorem adler_chunk_append : forall xs ys a b,
  adler_output (xs++ys) a b = let '(u,v) := adler_raw xs a b in
    adler_output ys (u mod ADLER_BASE) (v mod ADLER_BASE).
Proof.
  intros. unfold adler_output at 1. rewrite adler_raw_append.
  destruct (adler_raw xs a b) as [u v]. change (adler_output ys u v = adler_output ys (u mod ADLER_BASE) (v mod ADLER_BASE)).
  apply adler_output_congr;rewrite Z.mod_mod by (unfold ADLER_BASE;lia);reflexivity.
Qed.
Lemma adler_output_range : forall bs a b, 0 <= adler_output bs a b < 2^32.
Proof.
  intros. unfold adler_output. destruct (adler_raw bs a b) as [u v].
  pose proof (Z.mod_pos_bound u ADLER_BASE ltac:(unfold ADLER_BASE;lia)).
  pose proof (Z.mod_pos_bound v ADLER_BASE ltac:(unfold ADLER_BASE;lia)). unfold adler_pack,ADLER_BASE in *. lia.
Qed.
Lemma adler_raw_bound : forall bs a b, 0 <= a -> 0 <= b ->
  let '(u,v) := adler_raw bs a b in
  0 <= u <= a+255*Z.of_nat (length bs) /\
  0 <= v <= b+Z.of_nat (length bs)*a+255*Z.of_nat (length bs)*Z.of_nat (length bs).
Proof.
  induction bs as [|c bs IH];intros a b HA HB;[cbn;lia|].
  pose proof (byte_unsigned_range c) as HC.
  specialize (IH (a+bv_unsigned c) (b+a+bv_unsigned c) ltac:(lia) ltac:(lia)).
  cbn [adler_raw]. destruct (adler_raw bs (a+bv_unsigned c) (b+a+bv_unsigned c)) as [u v].
  cbn in IH. cbn [length]. rewrite Nat2Z.inj_succ. nia.
Qed.
Lemma adler_suffix_step : forall bs i a b,
  0 <= i < Z.of_nat (length bs) ->
  adler_output (skipn (Z.to_nat i) bs) a b =
  adler_output (skipn (Z.to_nat (i+1)) bs) (a+bv_unsigned (bbyte bs i)) (b+a+bv_unsigned (bbyte bs i)).
Proof.
  intros bs i a b HI. rewrite skipn_byte_cons by lia.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.
