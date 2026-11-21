(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Checksum/AdlerModel.v at , lines 2-2, 25-25, 28-28, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZChecksum ZChkArith ZChkAdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition csub (x : Z) : Z := if 65520 <? x then x - 65521 else x.

Definition lo16 (a : Z) : Z := a mod 2 ^ 16.
Definition hi16 (a : Z) : Z := (a mod 2 ^ 32) / 2 ^ 16.

Lemma lo16_range : forall a, 0 <= lo16 a < 2 ^ 16.
Proof. intro a. unfold lo16. apply Z.mod_pos_bound. lia. Qed.

Lemma hi16_range : forall a, 0 <= hi16 a < 2 ^ 16.
Proof.
  intro a. unfold hi16. pose proof (Z.mod_pos_bound a (2 ^ 32) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Definition adler32_z_spec (adler P : Z) (d : list byte) : Z :=
  let s1 := lo16 adler in
  let s2 := hi16 adler in
  if Z.of_nat (length d) =? 1 then
    let a := csub (s1 + bnth d 0) in
    let b := csub (a + s2) in
    Z.lor (b * 2 ^ 16) a
  else if P =? 0 then 1
  else let (a, b) := adl_raw (bZ d) s1 s2 in
       Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE).

Lemma mod32_div16 : forall a, 0 <= a -> (a mod 2 ^ 32) / 2 ^ 16 = (a / 2 ^ 16) mod 2 ^ 16.
Proof.
  intros a Ha.
  replace (2 ^ 32) with (2 ^ 16 * 2 ^ 16) by reflexivity.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ 16)), Z.div_add by lia.
  rewrite Z.mod_div by lia. lia.
Qed.

Lemma adler32_z_spec_model : forall adler P d,
  0 <= adler -> Z.of_nat (length d) <> 1 -> P <> 0 ->
  adler32_z_spec adler P d = adler32_model adler (bZ d).
Proof.
  intros adler P d Ha Hl HP. unfold adler32_z_spec, lo16, hi16.
  replace (Z.of_nat (length d) =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hl).
  replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; exact HP).
  unfold adler32_model.
  assert (H1 : Z.land adler 65535 = adler mod 2 ^ 16).
  { change 65535 with (Z.ones 16). apply Z.land_ones. lia. }
  assert (H2 : Z.land (Z.shiftr adler 16) 65535 = (adler mod 2 ^ 32) / 2 ^ 16).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    symmetry. apply mod32_div16. exact Ha. }
  rewrite H1, H2, adl_raw_mod.
  destruct (adl_raw (bZ d) (adler mod 2 ^ 16) (adler mod 2 ^ 32 / 2 ^ 16)) as [a b]. cbn [fst snd].
  pose proof (Z.mod_pos_bound a ABASE ltac:(unfold ABASE; lia)) as Hma.
  pose proof (Z.mod_pos_bound b ABASE ltac:(unfold ABASE; lia)) as Hmb.
  rewrite <- Z.shiftl_mul_pow2 by lia. apply combine_lor; unfold ABASE in *; lia.
Qed.


Lemma bZ_range : forall d, Forall (fun b => 0 <= b < 256) (bZ d).
Proof.
  intro d. unfold bZ. induction d as [|x d IH]; cbn; constructor; [apply u8_range | exact IH].
Qed.







Lemma skipn_cons_nth : forall (l : list Z) i, (i < length l)%nat ->
  skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  intros l. induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.





Lemma csub_mod : forall x, 0 <= x < 2 * ABASE -> csub x = x mod ABASE.
Proof.
  intros x Hx. unfold csub. rewrite <- (condsub x Hx).
  destruct (Z.ltb_spec 65520 x); destruct (Z.leb_spec x 65520); unfold ABASE; lia.
Qed.



Definition adler_canon (a : Z) : Prop := 0 <= a < 2 ^ 32 /\ lo16 a < ABASE /\ hi16 a < ABASE.

Lemma adler_canon_1 : adler_canon 1.
Proof. unfold adler_canon, lo16, hi16, ABASE. cbn. lia. Qed.

Lemma adler32_z_spec_canon : forall adler P d,
  adler_canon adler -> P <> 0 -> adler32_z_spec adler P d = adler32_model adler (bZ d).
Proof.
  intros adler P d (Ha & Hlo & Hhi) HP.
  destruct (Z.eq_dec (Z.of_nat (length d)) 1) as [Hl|Hl];
    [| apply adler32_z_spec_model; [lia | exact Hl | exact HP]].
  unfold adler32_z_spec. rewrite (proj2 (Z.eqb_eq _ _) Hl).
  destruct d as [|b [|]]; cbn [length Z.of_nat] in Hl; try lia.
  unfold adler32_model. cbn [bZ map adl].
  replace (bnth [b] 0) with (bv_unsigned b) by reflexivity.
  pose proof (lo16_range adler) as Hl16. pose proof (hi16_range adler) as Hh16.
  pose proof (u8_range b) as Hb.
  assert (H1 : Z.land adler 65535 = lo16 adler).
  { unfold lo16. change 65535 with (Z.ones 16). apply Z.land_ones. lia. }
  assert (H2 : Z.land (Z.shiftr adler 16) 65535 = hi16 adler).
  { unfold hi16. change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    symmetry. apply mod32_div16. lia. }
  rewrite H1, H2. rewrite (Z.mod_small (lo16 adler)) by lia. rewrite (Z.mod_small (hi16 adler)) by lia.
  rewrite (csub_mod (lo16 adler + bv_unsigned b)) by (unfold ABASE in *; lia).
  pose proof (Z.mod_pos_bound (lo16 adler + bv_unsigned b) ABASE ltac:(unfold ABASE; lia)) as Hm1.
  rewrite (csub_mod _) by (unfold ABASE in *; lia).
  rewrite (Z.add_comm ((lo16 adler + bv_unsigned b) mod ABASE) (hi16 adler)).
  pose proof (Z.mod_pos_bound (hi16 adler + (lo16 adler + bv_unsigned b) mod ABASE) ABASE ltac:(unfold ABASE; lia)) as Hm2.
  rewrite <- Z.shiftl_mul_pow2 by lia. apply combine_lor; unfold ABASE in *; lia.
Qed.

Lemma adler32_model_canon : forall a bs, adler_canon (adler32_model a bs).
Proof.
  intros a bs. unfold adler32_model.
  pose proof (adl_canon bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)
                (Z.mod_pos_bound (Z.land a 65535) ABASE ltac:(unfold ABASE; lia))
                (Z.mod_pos_bound (Z.land (Z.shiftr a 16) 65535) ABASE ltac:(unfold ABASE; lia))) as Hc.
  destruct (adl bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)) as [u v].
  cbn [fst snd] in Hc. unfold ABASE in Hc.
  assert (E : Z.lxor (Z.shiftl v 16) u = v * 2 ^ 16 + u).
  { rewrite <- Z.add_nocarry_lxor.
    - rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
    - rewrite Z.land_comm. apply land_shiftl_disj; [change (2 ^ 16) with 65536; lia | lia | lia]. }
  rewrite E. unfold adler_canon, lo16, hi16, ABASE.
  split; [lia|]. split.
  - replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (v * 2 ^ 16 + u)) by lia.
    replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia.
Qed.
