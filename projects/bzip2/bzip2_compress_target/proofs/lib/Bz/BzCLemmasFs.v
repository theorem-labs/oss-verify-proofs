(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fs_ftab_zero_S : forall n ft i, fs_ftab_zero (S n) ft i = fs_ftab_zero n (zset ft i 0) (i + 1).
Proof. reflexivity. Qed.
Lemma fs_count_S : forall n ft ec i, fs_count (S n) ft ec i = fs_count n (zincr ft (rd8 ec i)) ec (i + 1).
Proof. reflexivity. Qed.
Lemma fs_copy_S : forall n fc ft i, fs_copy (S n) fc ft i = fs_copy n (zset fc i (zget ft i)) ft (i + 1).
Proof. reflexivity. Qed.
Lemma fs_accum_S : forall n ft i, fs_accum (S n) ft i = fs_accum n (zset ft i (zget ft i + zget ft (i - 1))) (i + 1).
Proof. reflexivity. Qed.
Lemma fs_distrib_S : forall n ft fm ec i,
  fs_distrib (S n) ft fm ec i = (let j := rd8 ec i in let k := zget ft j - 1 in fs_distrib n (zset ft j k) (wr32 fm k i) ec (i + 1)).
Proof. reflexivity. Qed.
Lemma fs_bh_zero_S : forall n bh i, fs_bh_zero (S n) bh i = fs_bh_zero n (zset bh i 0) (i + 1).
Proof. reflexivity. Qed.
Lemma fs_bh_init_S : forall n bh ft i, fs_bh_init (S n) bh ft i = fs_bh_init n (set_bh bh (zget ft i)) ft (i + 1).
Proof. reflexivity. Qed.
Lemma fs_sentinel_S : forall n bh nb i,
  fs_sentinel (S n) bh nb i = fs_sentinel n (clear_bh (set_bh bh (nb + 2 * i)) (nb + 2 * i + 1)) nb (i + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fs_ftab_zero_get : forall n ft i j,
  zget (fs_ftab_zero n ft i) j = (if (i <=? j) && (j <? i + Z.of_nat n) then 0 else zget ft j).
Proof.
  induction n as [|n IH]; intros ft i j.
  - cbn [fs_ftab_zero]. replace ((i <=? j) && (j <? i + Z.of_nat 0%nat))%bool with false by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec i j); [right; apply Z.ltb_ge; lia| left; reflexivity]). reflexivity.
  - rewrite fs_ftab_zero_S, IH, zget_zset.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.eqb_spec j i);
    destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.of_nat (S n))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma fs_ftab_zero_def : forall n ft i j,
  zdef (fs_ftab_zero n ft i) j = (((i <=? j) && (j <? i + Z.of_nat n)) || zdef ft j)%bool.
Proof.
  induction n as [|n IH]; intros ft i j.
  - cbn [fs_ftab_zero]. replace ((i <=? j) && (j <? i + Z.of_nat 0%nat))%bool with false by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec i j); [right; apply Z.ltb_ge; lia| left; reflexivity]). reflexivity.
  - rewrite fs_ftab_zero_S, IH, zdef_zset.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.eqb_spec j i);
    destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.of_nat (S n))); cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma fs_bh_zero_get : forall n bh i j,
  zget (fs_bh_zero n bh i) j = (if (i <=? j) && (j <? i + Z.of_nat n) then 0 else zget bh j).
Proof.
  induction n as [|n IH]; intros bh i j.
  - cbn [fs_bh_zero]. replace ((i <=? j) && (j <? i + Z.of_nat 0%nat))%bool with false by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec i j); [right; apply Z.ltb_ge; lia| left; reflexivity]). reflexivity.
  - rewrite fs_bh_zero_S, IH, zget_zset.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.eqb_spec j i);
    destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.of_nat (S n))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma fs_copy_get : forall n fc ft i j,
  zget (fs_copy n fc ft i) j = (if (i <=? j) && (j <? i + Z.of_nat n) then zget ft j else zget fc j).
Proof.
  induction n as [|n IH]; intros fc ft i j.
  - cbn [fs_copy]. replace ((i <=? j) && (j <? i + Z.of_nat 0%nat))%bool with false by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec i j); [right; apply Z.ltb_ge; lia| left; reflexivity]). reflexivity.
  - rewrite fs_copy_S, IH, zget_zset.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.eqb_spec j i);
    destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.of_nat (S n))); cbn [andb]; subst; try reflexivity; lia.
Qed.
Lemma fs_copy_def : forall n fc ft i j,
  zdef (fs_copy n fc ft i) j = (((i <=? j) && (j <? i + Z.of_nat n)) || zdef fc j)%bool.
Proof.
  induction n as [|n IH]; intros fc ft i j.
  - cbn [fs_copy]. replace ((i <=? j) && (j <? i + Z.of_nat 0%nat))%bool with false by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec i j); [right; apply Z.ltb_ge; lia| left; reflexivity]). reflexivity.
  - rewrite fs_copy_S, IH, zdef_zset.
    destruct (Z.leb_spec (i + 1) j); destruct (Z.ltb_spec j (i + 1 + Z.of_nat n)); destruct (Z.eqb_spec j i);
    destruct (Z.leb_spec i j); destruct (Z.ltb_spec j (i + Z.of_nat (S n))); cbn [andb orb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma fs_distrib_add : forall k r ft fm ec i,
  fs_distrib (k + r) ft fm ec i = (let '(ft', fm') := fs_distrib k ft fm ec i in fs_distrib r ft' fm' ec (i + Z.of_nat k)).
Proof.
  induction k as [|k IH]; intros r ft fm ec i.
  - cbn [fs_distrib Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add]. rewrite !fs_distrib_S. cbv zeta. rewrite IH.
    destruct (fs_distrib k _ _ ec (i + 1)) as [ft' fm']. f_equal. lia.
Qed.
Lemma fs_distrib_snoc : forall k ft fm ec i,
  fs_distrib (S k) ft fm ec i =
  (let '(ft', fm') := fs_distrib k ft fm ec i in
   let j := rd8 ec (i + Z.of_nat k) in let kk := zget ft' j - 1 in (zset ft' j kk, wr32 fm' kk (i + Z.of_nat k))).
Proof.
  intros k ft fm ec i. replace (S k) with (k + 1)%nat by lia. rewrite fs_distrib_add.
  destruct (fs_distrib k ft fm ec i) as [ft' fm']. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bh_w32 (bh : zarr) : Prop := forall i, 0 <= zget bh i < 4294967296.

Lemma land31_range : forall zz, 0 <= Z.land zz 31 < 32.
Proof.
  intros zz. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. pose proof (Z.mod_pos_bound zz 32 ltac:(lia)). lia.
Qed.
Lemma shiftl1_range : forall k, 0 <= k < 32 -> 1 <= Z.shiftl 1 k < 4294967296.
Proof.
  intros k Hk. rewrite Z.shiftl_1_l. split.
  - pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) ltac:(lia)) as H. rewrite Z.pow_0_r in H. exact H.
  - change 4294967296 with (2^32). apply Z.pow_lt_mono_r; lia.
Qed.
Lemma lt_pow32 : forall a, 0 < a -> Z.log2 a < 32 -> a < 4294967296.
Proof. intros a Ha H. change 4294967296 with (2^32). apply (proj2 (Z.log2_lt_pow2 a 32 Ha)). exact H. Qed.
Lemma log2_lt32 : forall a, 0 < a -> a < 4294967296 -> Z.log2 a < 32.
Proof. intros a Ha H. apply (proj1 (Z.log2_lt_pow2 a 32 Ha)). exact H. Qed.
Lemma lor_w32 : forall a b, 0 <= a < 4294967296 -> 0 <= b < 4294967296 -> 0 <= Z.lor a b < 4294967296.
Proof.
  intros a b Ha Hb. split; [apply (proj2 (Z.lor_nonneg a b)); lia|].
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)). destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply lt_pow32; [exact Hp|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply log2_lt32; lia.
Qed.
Lemma land_w32_l : forall a b, 0 <= a < 4294967296 -> 0 <= b -> 0 <= Z.land a b < 4294967296.
Proof.
  intros a b Ha Hb. pose proof (proj2 (Z.land_nonneg a b) ltac:(lia)) as H0. split; [exact H0|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hz]; [lia|].
  assert (Hp : 0 < Z.land a b) by lia.
  assert (Ha0 : 0 < a). { destruct (Z.eq_dec a 0) as [E|]; [|lia]. exfalso. apply Hz. rewrite E. apply Z.land_0_l. }
  apply lt_pow32; [exact Hp|].
  pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)) as HL.
  pose proof (log2_lt32 a Ha0 ltac:(lia)). lia.
Qed.

Lemma set_bh_w32 : forall bh zz, bh_w32 bh -> bh_w32 (set_bh bh zz).
Proof.
  intros bh zz H i. unfold set_bh, bh_word. rewrite zget_zset. destruct (i =? Z.shiftr zz 5); [|apply H].
  apply lor_w32; [apply H|]. pose proof (shiftl1_range (Z.land zz 31) (land31_range zz)). lia.
Qed.
Lemma clear_bh_w32 : forall bh zz, bh_w32 bh -> bh_w32 (clear_bh bh zz).
Proof.
  intros bh zz H i. unfold clear_bh, bh_word. rewrite zget_zset. destruct (i =? Z.shiftr zz 5); [|apply H].
  apply land_w32_l; [apply H|]. apply Z.lxor_nonneg. pose proof (shiftl1_range (Z.land zz 31) (land31_range zz)). lia.
Qed.
Lemma fs_bh_zero_w32 : forall n bh i, bh_w32 bh -> bh_w32 (fs_bh_zero n bh i).
Proof. induction n as [|n IH]; intros bh i H; cbn [fs_bh_zero]; [exact H|]. apply IH. intros j. rewrite zget_zset. destruct (j =? i); [lia| apply H]. Qed.
Lemma fs_bh_init_w32 : forall n bh ft i, bh_w32 bh -> bh_w32 (fs_bh_init n bh ft i).
Proof. induction n as [|n IH]; intros bh ft i H; cbn [fs_bh_init]; [exact H|]. apply IH. apply set_bh_w32. exact H. Qed.
Lemma fs_sentinel_w32 : forall n bh nb i, bh_w32 bh -> bh_w32 (fs_sentinel n bh nb i).
Proof. induction n as [|n IH]; intros bh nb i H; cbn [fs_sentinel]; [exact H|]. apply IH. apply clear_bh_w32, set_bh_w32. exact H. Qed.
Lemma fs_headers_w32 : forall n bh ec fm i cc, bh_w32 bh -> bh_w32 (fs_headers n bh ec fm i cc).
Proof.
  induction n as [|n IH]; intros bh ec fm i cc H; cbn [fs_headers]; [exact H|].
  destruct (negb (cc =? rd32 ec (rd32 fm i))); apply IH; [apply set_bh_w32|]; exact H.
Qed.

(* [comment removed for export] *)
Lemma shiftr5_div : forall zz, Z.shiftr zz 5 = zz / 32.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma land31_mod : forall zz, Z.land zz 31 = zz mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fs_eclass_S : forall n ec fm bh H nb i j,
  fs_eclass (S n) ec fm bh H nb i j =
  (let j' := if isset_bh bh i then i else j in
   let k := rd32 fm i - H in let k' := if k <? 0 then k + nb else k in
   fs_eclass n (wr32 ec k' j') fm bh H nb (i + 1) j').
Proof. reflexivity. Qed.
Lemma fs_headers_S : forall n bh ec fm i cc,
  fs_headers (S n) bh ec fm i cc =
  (let cc1 := rd32 ec (rd32 fm i) in if negb (cc =? cc1) then fs_headers n (set_bh bh i) ec fm (i + 1) cc1 else fs_headers n bh ec fm (i + 1) cc).
Proof. reflexivity. Qed.
Lemma fss_outer_S' : forall n fm ec i hi step, fss_outer (S n) fm ec i hi step = fss_outer n (fss_iter fm ec i hi step) ec (i - 1) hi step.
Proof. reflexivity. Qed.
Lemma fvswap_S : forall f fm p1 p2 n, fvswap (S f) fm p1 p2 n = (if 0 <? n then fvswap f (fswap fm p1 p2) (p1 + 1) (p2 + 1) (n - 1) else fm).
Proof. reflexivity. Qed.
Lemma fs_rebuild_S : forall n ec fc fm i j,
  fs_rebuild (S n) ec fc fm i j =
  (let j' := fs_skip0 258%nat fc j in let fc' := zset fc j' (zget fc j' - 1) in fs_rebuild n (wr8 ec (rd32 fm i) j') fc' fm (i + 1) j').
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fs_scan_set_unal_S : forall f bh k, fs_scan_set_unal (S f) bh k = (if isset_bh bh k && unaligned_bh k then fs_scan_set_unal f bh (k + 1) else k).
Proof. reflexivity. Qed.
Lemma fs_scan_word_ff_S : forall f bh k, fs_scan_word_ff (S f) bh k = (if bh_word bh k =? 4294967295 then fs_scan_word_ff f bh (k + 32) else k).
Proof. reflexivity. Qed.
Lemma fs_scan_set_S : forall f bh k, fs_scan_set (S f) bh k = (if isset_bh bh k then fs_scan_set f bh (k + 1) else k).
Proof. reflexivity. Qed.
Lemma fs_scan_clr_unal_S : forall f bh k, fs_scan_clr_unal (S f) bh k = (if negb (isset_bh bh k) && unaligned_bh k then fs_scan_clr_unal f bh (k + 1) else k).
Proof. reflexivity. Qed.
Lemma fs_scan_word_00_S : forall f bh k, fs_scan_word_00 (S f) bh k = (if bh_word bh k =? 0 then fs_scan_word_00 f bh (k + 32) else k).
Proof. reflexivity. Qed.
Lemma fs_scan_clr_S : forall f bh k, fs_scan_clr (S f) bh k = (if negb (isset_bh bh k) then fs_scan_clr f bh (k + 1) else k).
Proof. reflexivity. Qed.

Lemma fs_scan_set_unal_ge : forall f bh k, k <= fs_scan_set_unal f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_set_unal]; [lia|]. destruct (isset_bh bh k && unaligned_bh k); [pose proof (IH bh (k + 1)); lia| lia]. Qed.
Lemma fs_scan_word_ff_ge : forall f bh k, k <= fs_scan_word_ff f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_word_ff]; [lia|]. destruct (bh_word bh k =? 4294967295); [pose proof (IH bh (k + 32)); lia| lia]. Qed.
Lemma fs_scan_set_ge : forall f bh k, k <= fs_scan_set f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_set]; [lia|]. destruct (isset_bh bh k); [pose proof (IH bh (k + 1)); lia| lia]. Qed.
Lemma fs_scan_clr_unal_ge : forall f bh k, k <= fs_scan_clr_unal f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_clr_unal]; [lia|]. destruct (negb (isset_bh bh k) && unaligned_bh k); [pose proof (IH bh (k + 1)); lia| lia]. Qed.
Lemma fs_scan_word_00_ge : forall f bh k, k <= fs_scan_word_00 f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_word_00]; [lia|]. destruct (bh_word bh k =? 0); [pose proof (IH bh (k + 32)); lia| lia]. Qed.
Lemma fs_scan_clr_ge : forall f bh k, k <= fs_scan_clr f bh k.
Proof. induction f as [|f IH]; intros bh k; cbn [fs_scan_clr]; [lia|]. destruct (negb (isset_bh bh k)); [pose proof (IH bh (k + 1)); lia| lia]. Qed.

Lemma unaligned_bh_mod : forall k, unaligned_bh k = negb (k mod 32 =? 0).
Proof. intros. unfold unaligned_bh. rewrite land31_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fss_in_S : forall f fm ec et j hi st,
  fss_in (S f) fm ec et j hi st =
  (if (j <=? hi) && (rd32 ec (rd32 fm j) <? et) then fss_in f (wr32 fm (j - st) (rd32 fm j)) ec et (j + st) hi st else (fm, j)).
Proof. reflexivity. Qed.
Lemma fss_in_stop : forall f fm ec et j hi st, hi < j -> fss_in f fm ec et j hi st = (fm, j).
Proof. intros. destruct f; [reflexivity|]. rewrite fss_in_S. replace (j <=? hi) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

(* [comment removed for export] *)
Definition fm_range (fm : zarr) (nb : Z) : Prop := nb <= 4294967296 /\ forall x, 0 <= x < nb -> 0 <= rd32 fm x < nb.
Lemma fm_range_wr32 : forall fm nb i v, fm_range fm nb -> 0 <= v < nb -> fm_range (wr32 fm i v) nb.
Proof.
  intros fm nb i v [Hn H] Hv. split; [exact Hn|]. intros x Hx. destruct (Z.eq_dec x i) as [->|].
  - rewrite rd32_wr32_same; lia.
  - rewrite rd32_wr32_other by lia. apply H. lia.
Qed.
(* [comment removed for export] *)
Lemma fswap_range : forall fm nb a b, fm_range fm nb -> 0 <= a < nb -> 0 <= b < nb -> fm_range (fswap fm a b) nb.
Proof. intros fm nb a b H Ha Hb. unfold fswap. apply fm_range_wr32; [apply fm_range_wr32; [exact H| apply (proj2 H); lia]| apply (proj2 H); lia]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fpart_lo_S : forall f ec med pp,
  fpart_lo (S f) ec med pp =
  (if fp_unHi pp <? fp_unLo pp then pp else
   let n := rd32 ec (rd32 (fp_fm pp) (fp_unLo pp)) - med in
   if n =? 0 then fpart_lo f ec med (FP (fswap (fp_fm pp) (fp_unLo pp) (fp_ltLo pp)) (fp_unLo pp + 1) (fp_unHi pp) (fp_ltLo pp + 1) (fp_gtHi pp))
   else if 0 <? n then pp else fpart_lo f ec med (FP (fp_fm pp) (fp_unLo pp + 1) (fp_unHi pp) (fp_ltLo pp) (fp_gtHi pp))).
Proof. reflexivity. Qed.
Lemma fpart_hi_S : forall f ec med pp,
  fpart_hi (S f) ec med pp =
  (if fp_unHi pp <? fp_unLo pp then pp else
   let n := rd32 ec (rd32 (fp_fm pp) (fp_unHi pp)) - med in
   if n =? 0 then fpart_hi f ec med (FP (fswap (fp_fm pp) (fp_unHi pp) (fp_gtHi pp)) (fp_unLo pp) (fp_unHi pp - 1) (fp_ltLo pp) (fp_gtHi pp - 1))
   else if n <? 0 then pp else fpart_hi f ec med (FP (fp_fm pp) (fp_unLo pp) (fp_unHi pp - 1) (fp_ltLo pp) (fp_gtHi pp))).
Proof. reflexivity. Qed.
Lemma fpart_loop_S : forall f sz ec med pp,
  fpart_loop (S f) sz ec med pp =
  (let p1 := fpart_lo (S sz) ec med pp in let p2 := fpart_hi (S sz) ec med p1 in
   if fp_unHi p2 <? fp_unLo p2 then p2
   else fpart_loop f sz ec med (FP (fswap (fp_fm p2) (fp_unLo p2) (fp_unHi p2)) (fp_unLo p2 + 1) (fp_unHi p2 - 1) (fp_ltLo p2) (fp_gtHi p2))).
Proof. reflexivity. Qed.
Lemma fpart_lo_stop : forall f ec med pp, fp_unHi pp < fp_unLo pp -> fpart_lo f ec med pp = pp.
Proof. intros f ec med pp H. destruct f; [reflexivity|]. rewrite fpart_lo_S. replace (fp_unHi pp <? fp_unLo pp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma fpart_hi_stop : forall f ec med pp, fp_unHi pp < fp_unLo pp -> fpart_hi f ec med pp = pp.
Proof. intros f ec med pp H. destruct f; [reflexivity|]. rewrite fpart_hi_S. replace (fp_unHi pp <? fp_unLo pp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma fpart_loop_stop : forall f sz ec med pp, fp_unHi pp < fp_unLo pp -> fpart_loop f sz ec med pp = pp.
Proof.
  intros f sz ec med pp H. destruct f; [reflexivity|]. rewrite fpart_loop_S. cbv zeta.
  rewrite !fpart_lo_stop, !fpart_hi_stop by (rewrite ?fpart_lo_stop by lia; lia).
  replace (fp_unHi pp <? fp_unLo pp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition fp_ok (lo hi : Z) (pp : fpart) : Prop :=
  lo <= fp_ltLo pp <= fp_unLo pp /\ fp_unHi pp <= fp_gtHi pp <= hi /\ fp_unLo pp <= fp_unHi pp + 1.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fpart_lo_exit : forall f ec med pp, fp_unHi pp - fp_unLo pp + 2 <= Z.of_nat f ->
  fp_unHi (fpart_lo f ec med pp) < fp_unLo (fpart_lo f ec med pp) \/
  med < rd32 ec (rd32 (fp_fm (fpart_lo f ec med pp)) (fp_unLo (fpart_lo f ec med pp))).
Proof.
  induction f as [|f IH]; intros ec med pp Hf; [cbn in *; left; lia|].
  rewrite fpart_lo_S. destruct (Z.ltb_spec (fp_unHi pp) (fp_unLo pp)); [left; lia|]. cbv zeta.
  destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm pp) (fp_unLo pp)) - med) 0).
  - apply IH. cbn. lia.
  - destruct (Z.ltb_spec 0 (rd32 ec (rd32 (fp_fm pp) (fp_unLo pp)) - med)); [right; lia|]. apply IH. cbn. lia.
Qed.
Lemma rd32_fswap_other : forall fm a b x, x <> a -> x <> b -> rd32 (fswap fm a b) x = rd32 fm x.
Proof. intros. unfold fswap. rewrite !rd32_wr32_other by lia. reflexivity. Qed.

Lemma fvswap_fuel_ge : forall f fm p1 p2 n, n <= Z.of_nat f -> fvswap f fm p1 p2 n = fvswap (S f) fm p1 p2 n.
Proof.
  induction f as [|f IH]; intros fm p1 p2 n Hn.
  - rewrite (fvswap_S 0 fm p1 p2 n). cbn [fvswap]. replace (0 <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite (fvswap_S f fm p1 p2 n), (fvswap_S (S f) fm p1 p2 n).
    destruct (Z.ltb_spec 0 n); [|reflexivity]. apply IH. lia.
Qed.
Lemma fvswap_fuel : forall k fm p1 p2, fvswap (S k) fm p1 p2 (Z.of_nat k) = fvswap k fm p1 p2 (Z.of_nat k).
Proof. intros. symmetry. apply fvswap_fuel_ge. lia. Qed.
Lemma fvswap_le0 : forall f fm p1 p2 n, n <= 0 -> fvswap f fm p1 p2 n = fm.
Proof. intros f fm p1 p2 n Hn. destruct f; [reflexivity|]. rewrite fvswap_S. replace (0 <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
