(** * Bridge.DMatch.MBasic — group M: pairs D2 (configuration table) and D5
    (compressBound), and the integer kit the window pairs share.

    - [m_compress_bound]: S5's [compressBound_m] is RT's [zr_deflate_bound 15]
      (S5's [wrap64] is the identity on the range).
    - [m_config]: S5's [configuration_table] row is RT's four [cfg_*] tables,
      levels 0-9, by computation.
    - [m_update_hash]: S5's [update_hash] keeps a [wrap32] cast the mask
      absorbs, so it is RT's [update_hash] at every input (no byte premise).
    - [m_wrap16_u16], [m_wrap8_u8]: the two models' casts are the same
      function. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SDfl := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.
Module SDS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateState.
Module RD := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Deflate.
Module RC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Chunk.

(** [lia] does not evaluate [2 ^ k]: spell out the powers the pairs use. *)
Ltac mpow1 p v :=
  let E := fresh "Epow" in
  try (assert (E : 2 ^ p = v) by reflexivity; rewrite E in *; clear E).
Ltac mpow :=
  mpow1 64 18446744073709551616; mpow1 63 9223372036854775808;
  mpow1 62 4611686018427387904; mpow1 60 1152921504606846976;
  mpow1 32 4294967296; mpow1 16 65536.

Ltac mshl1 k v :=
  let E := fresh "Eshl" in
  try (assert (E : Z.shiftl 1 k = v) by reflexivity; rewrite E in *; clear E).
(** The geometry constants of [cf_geom] (w_size, hash_size, lit_bufsize). *)
Ltac mgeom :=
  mshl1 15 32768; mshl1 14 16384;
  try unfold RC.MIN_MATCH, RC.MAX_MATCH, RC.MIN_LOOKAHEAD in *.

(** Closed comparisons, by computation. *)
Ltac mclosed :=
  repeat split;
  try (apply Z.leb_le; vm_compute; reflexivity);
  try (apply Z.ltb_lt; vm_compute; reflexivity).

(** ** D5 *)

Lemma m_shiftr_le : forall x k, 0 <= x -> 0 <= k -> 0 <= Z.shiftr x k <= x.
Proof.
  intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by exact Hk.
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Theorem m_compress_bound : forall len, 0 <= len < 2 ^ 60 ->
  SDfl.compressBound_m len = ZRepro.zr_deflate_bound 15 len.
Proof.
  intros len Hl. unfold SDfl.compressBound_m, SDfl.sat_bound64, ZRepro.zr_deflate_bound.
  change (ZRepro.zr_wraplen 15) with 6.
  pose proof (m_shiftr_le len 12 ltac:(lia) ltac:(lia)).
  pose proof (m_shiftr_le len 14 ltac:(lia) ltac:(lia)).
  pose proof (m_shiftr_le len 25 ltac:(lia) ltac:(lia)).
  mpow. rewrite wrap64_id by (mpow; lia).
  (* zlib 1.4 (zl14cmp-r1): compressBound saturates; on this range the sum is at least len, so it does not *)
  match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end; lia.
Qed.

(** ** D2 *)

Theorem m_config : forall level, 0 <= level <= 9 ->
  SLz.configuration_table level
  = (RC.cfg_good_length level, RC.cfg_max_lazy level, RC.cfg_nice_length level, RC.cfg_max_chain level).
Proof.
  intros level Hl.
  assert (Hc : level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5
               \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
  repeat destruct Hc as [-> | Hc]; [vm_compute; reflexivity ..|].
  subst level. vm_compute. reflexivity.
Qed.

(** ** Casts and the hash *)

Lemma m_wrap16_u16 : forall z, wrap16 z = Base.u16 z.
Proof. intros z. rewrite wrap16_mod. reflexivity. Qed.

Lemma m_wrap8_u8 : forall z, wrap8 z = Base.u8 z.
Proof. intros z. rewrite wrap8_mod. reflexivity. Qed.

Lemma m_land_lxor_wrap32 : forall x c,
  Z.land (Z.lxor (wrap32 x) c) 32767 = Z.land (Z.lxor x c) 32767.
Proof.
  intros x c. rewrite wrap32_mod.
  apply Z.bits_inj'; intros n Hn.
  rewrite !Z.land_spec, !Z.lxor_spec.
  change 32767 with (Z.ones 15). rewrite Z.testbit_ones by lia.
  destruct (Z.ltb_spec n 15) as [Hlt|Hge].
  - rewrite (Z.mod_pow2_bits_low x 32 n) by lia. reflexivity.
  - rewrite !andb_false_r. reflexivity.
Qed.

(** At compress_fuzzer's memLevel 8 the mask is 32767 (hash_bits 15). *)
Theorem m_update_hash : forall s g h c,
  SDS.ds_hash_shift s = RC.dg_hash_shift g -> SDS.ds_hash_mask s = 32767 ->
  RC.dg_hash_mask g = 32767 ->
  SLz.update_hash s h c = RD.update_hash g h c.
Proof.
  intros s g h c Hsh Hm Hm'. unfold SLz.update_hash, RD.update_hash.
  rewrite Hsh, Hm, Hm'. apply m_land_lxor_wrap32.
Qed.

Lemma m_update_hash_range : forall g h c,
  RC.dg_hash_mask g = 32767 -> 0 <= RD.update_hash g h c < 32768.
Proof.
  intros g h c Hm. unfold RD.update_hash. rewrite Hm.
  change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.
