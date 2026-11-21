(** * W1Content — the f_buf CONTENT pack for the inflate_fast model
      (q7-decode lane, ZrLenFastLeg work item W1, 2026-08-20, OFF-TREE).

    Every landed if_* lemma characterizes budgets and cursors; none says
    WHICH BYTES the writers write (an earlier development run's gap 1).  This file
    characterizes [if_put] and the [SrcOut] copy family byte-for-byte in
    the vocabulary [resolve_lz] consumes ([Huff.lz_copy]'s closed form),
    proves the sequential-copy-vs-closed-form agreement Huff.v's header
    explicitly leaves open, flattens [if_copydirect] to [if_copyn], and
    kills the window phase at [whave = 0] (the ZrLenFastLeg premise
    world) with a [BodyBad] unfold lemma.

    Vocabulary bridge: [zslice] is [ob_slice]'s body over a raw [zarr];
    [ob_slice o i n = zslice (o_buf o) i n] holds by [reflexivity]. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Huff.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Slice vocabulary.
   ========================================================================== *)

Definition zslice (b : zarr) (i n : Z) : list Z :=
  map (fun k => b (i + Z.of_nat k)) (seq 0 (Z.to_nat n)).

Lemma ob_slice_is_zslice : forall o i n, ob_slice o i n = zslice (o_buf o) i n.
Proof. reflexivity. Qed.

Lemma zslice_length : forall b i n, length (zslice b i n) = Z.to_nat n.
Proof. intros; unfold zslice; now rewrite length_map, length_seq. Qed.

Lemma map_seq_shift : forall (f : nat -> Z) (a m : nat),
  map f (seq a m) = map (fun k => f (a + k)%nat) (seq 0 m).
Proof.
  intros f a m. revert a. induction m as [|m IH]; intros a; cbn [seq map].
  - reflexivity.
  - rewrite Nat.add_0_r. f_equal.
    rewrite IH. rewrite <- seq_shift, map_map.
    apply map_ext. intros k. f_equal. lia.
Qed.

Lemma zslice_app : forall b i a m,
  0 <= a -> 0 <= m ->
  zslice b i (a + m) = zslice b i a ++ zslice b (i + a) m.
Proof.
  intros b i a m Ha Hm. unfold zslice.
  rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  rewrite Nat.add_0_l, map_seq_shift. apply map_ext. intros k.
  f_equal. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
Qed.

Lemma zslice_ext : forall (b b' : zarr) i n,
  (forall j, i <= j < i + n -> b j = b' j) ->
  zslice b i n = zslice b' i n.
Proof.
  intros b b' i n H. unfold zslice. apply map_ext_in.
  intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  cbn [Nat.add] in Hk.
  assert (Hkn : Z.of_nat k < n).
  { destruct (Z.le_gt_cases n 0) as [Hn|Hn].
    - exfalso.
      assert (E0 : Z.to_nat n = 0%nat)
        by (destruct n; cbn; [reflexivity | lia | reflexivity]).
      lia.
    - assert (Z.of_nat k < Z.of_nat (Z.to_nat n)) by (apply Nat2Z.inj_lt; exact Hk).
      rewrite Z2Nat.id in * by lia. lia. }
  apply H. lia.
Qed.

Lemma zslice_nth : forall b i n k,
  (k < Z.to_nat n)%nat ->
  nth k (zslice b i n) 0 = b (i + Z.of_nat k).
Proof.
  intros b i n k Hk. unfold zslice.
  rewrite nth_indep with (d' := b (i + Z.of_nat 0))
    by (rewrite length_map, length_seq; exact Hk).
  change (b (i + Z.of_nat 0)) with ((fun k0 => b (i + Z.of_nat k0)) 0%nat).
  rewrite map_nth. rewrite seq_nth by exact Hk. reflexivity.
Qed.

(* ==========================================================================
   2.  [if_put]: the one-byte writer.
   ========================================================================== *)

Lemma if_put_out : forall v s, f_out (if_put v s) = f_out s + 1.
Proof. reflexivity. Qed.

Lemma if_put_in : forall v s, f_in (if_put v s) = f_in s.
Proof. reflexivity. Qed.

Lemma if_put_hold : forall v s, f_hold (if_put v s) = f_hold s.
Proof. reflexivity. Qed.

Lemma if_put_bits : forall v s, f_bits (if_put v s) = f_bits s.
Proof. reflexivity. Qed.

Lemma if_put_buf : forall v s,
  f_buf (if_put v s) = zset (f_buf s) (f_out s) v.
Proof. reflexivity. Qed.

Lemma if_put_slice : forall v s,
  0 <= f_out s ->
  zslice (f_buf (if_put v s)) 0 (f_out s + 1)
  = zslice (f_buf s) 0 (f_out s) ++ [v].
Proof.
  intros v s H. rewrite zslice_app by lia. rewrite Z.add_0_l. f_equal.
  - apply zslice_ext. intros j Hj. cbn [if_put f_buf].
    apply zset_other. lia.
  - unfold zslice. change (Z.to_nat 1) with 1%nat. cbn [seq map].
    cbn [if_put f_buf]. rewrite Z.add_0_r, zset_same. reflexivity.
Qed.

(* ==========================================================================
   3.  [if_copyn] structure: cursors, frames, prefix preservation.
   ========================================================================== *)

Lemma if_copyn_out : forall n c s r,
  f_out (fst (if_copyn n c s r)) = f_out s + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn].
  - cbn [fst]. lia.
  - rewrite IH. cbn [if_put f_out]. lia.
Qed.

Lemma if_copyn_in : forall n c s r,
  f_in (fst (if_copyn n c s r)) = f_in s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma if_copyn_hold : forall n c s r,
  f_hold (fst (if_copyn n c s r)) = f_hold s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma if_copyn_bits : forall n c s r,
  f_bits (fst (if_copyn n c s r)) = f_bits s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** Writes land at [f_out s], [f_out s + 1], ...: everything below the
    initial cursor is preserved — for ANY source. *)
Lemma if_copyn_buf_lo : forall n c s r j,
  j < f_out s ->
  f_buf (fst (if_copyn n c s r)) j = f_buf s j.
Proof.
  induction n as [|n IH]; intros c s r j Hj; cbn [if_copyn]; [reflexivity|].
  rewrite IH by (cbn [if_put f_out]; lia).
  cbn [if_put f_buf]. apply zset_other. lia.
Qed.

Lemma if_copyn_add : forall a b c s r,
  if_copyn (a + b) c s r
  = if_copyn b c (fst (if_copyn a c s r)) (snd (if_copyn a c s r)).
Proof.
  induction a as [|a IH]; intros b c s r.
  - reflexivity.
  - change (S a + b)%nat with (S (a + b))%nat. cbn [if_copyn].
    apply IH.
Qed.

(* ==========================================================================
   4.  THE OVERLAP CONTENT LEMMA: a [SrcOut] copy at distance [dist]
       reads its own writes exactly as [lz_copy]'s mod-[dist] periodic
       extension of the pre-copy prefix.  This is the sequential-vs-
       closed-form agreement Huff.v's header notes as not proved there.
   ========================================================================== *)

Lemma if_copyn_srcout_content :
  forall n c s dist j,
    0 < dist ->
    0 <= j < Z.of_nat n ->
    f_buf (fst (if_copyn n c s (SrcOut (f_out s - dist)))) (f_out s + j)
    = f_buf s (f_out s - dist + j mod dist).
Proof.
  induction n as [|n IH]; intros c s dist j Hd Hj; [cbn in Hj; lia|].
  cbn [if_copyn if_read if_bump].
  set (s' := if_put (f_buf s (f_out s - dist)) s).
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite Z.add_0_r.
    rewrite if_copyn_buf_lo by (unfold s'; cbn [if_put f_out]; lia).
    unfold s'. cbn [if_put f_buf]. rewrite zset_same.
    rewrite Z.mod_0_l by lia. rewrite Z.add_0_r. reflexivity.
  - replace (f_out s - dist + 1) with (f_out s' - dist)
      by (unfold s'; cbn [if_put f_out]; lia).
    replace (f_out s + j) with (f_out s' + (j - 1))
      by (unfold s'; cbn [if_put f_out]; lia).
    rewrite IH by (unfold s'; cbn [if_put f_out]; lia).
    unfold s'. cbn [if_put f_buf f_out].
    set (m := (j - 1) mod dist).
    pose proof (Z.mod_pos_bound (j - 1) dist Hd) as Hm.
    destruct (Z.eq_dec m (dist - 1)) as [Em|Em].
    + replace (f_out s + 1 - dist + m) with (f_out s) by lia.
      rewrite zset_same.
      assert (Hj0m : j mod dist = 0).
      { replace j with ((j - 1) + 1) by lia.
        rewrite <- Z.add_mod_idemp_l by lia.
        fold m. rewrite Em.
        replace (dist - 1 + 1) with dist by lia.
        apply Z_mod_same_full. }
      rewrite Hj0m, Z.add_0_r. reflexivity.
    + rewrite zset_other by lia.
      assert (Hjm : j mod dist = m + 1).
      { replace j with ((j - 1) + 1) by lia.
        rewrite <- Z.add_mod_idemp_l by lia.
        fold m. apply Z.mod_small. lia. }
      rewrite Hjm. f_equal. lia.
Qed.

(** The slice corollary, in [resolve_lz]'s exact vocabulary. *)
Lemma if_copyn_lz :
  forall (len dist : nat) c s,
    0 < Z.of_nat dist <= f_out s ->
    zslice (f_buf (fst (if_copyn len c s (SrcOut (f_out s - Z.of_nat dist)))))
           0 (f_out s + Z.of_nat len)
    = zslice (f_buf s) 0 (f_out s)
      ++ lz_copy (zslice (f_buf s) 0 (f_out s)) len dist.
Proof.
  intros len dist c s Hd.
  assert (Hdn : (dist <> 0)%nat) by lia.
  assert (Hdle : (dist <= Z.to_nat (f_out s))%nat).
  { assert (0 <= Z.of_nat dist) by lia.
    apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
  rewrite zslice_app by lia. rewrite Z.add_0_l. f_equal.
  - apply zslice_ext. intros j Hj.
    apply if_copyn_buf_lo. lia.
  - unfold lz_copy. unfold zslice at 1. rewrite Nat2Z.id.
    apply map_ext_in. intros k Hk. apply in_seq in Hk.
    destruct Hk as [_ Hk]. cbn [Nat.add] in Hk.
    rewrite if_copyn_srcout_content by lia.
    rewrite zslice_length.
    rewrite zslice_nth
      by (pose proof (Nat.mod_upper_bound k dist Hdn); lia).
    f_equal.
    rewrite Nat2Z.inj_add, Nat2Z.inj_sub, Nat2Z.inj_mod by exact Hdle.
    rewrite Z2Nat.id by lia. lia.
Qed.

(* ==========================================================================
   5.  Flattening the copy family to [if_copyn].
   ========================================================================== *)

Lemma if_copy3w_flat : forall fuel c s r len,
  0 <= len <= 3 * Z.of_nat fuel - 1 ->
  len < 4294967296 ->
  exists l',
    0 <= l' <= 2 /\ l' <= len /\
    if_copy3w fuel c s r len
    = Some (fst (if_copyn (Z.to_nat (len - l')) c s r),
            snd (if_copyn (Z.to_nat (len - l')) c s r), l').
Proof.
  induction fuel as [|fuel IH]; intros c s r len Hb Hcap.
  - cbn [Z.of_nat] in Hb. lia.
  - cbn [if_copy3w].
    destruct (Z.ltb_spec 2 len) as [Hlt|Hle].
    + unfold u32. rewrite (Z.mod_small (len - 3)) by lia.
      destruct (if_copyn 3 c s r) as [s1 r1] eqn:E3.
      destruct (IH c s1 r1 (len - 3)
                  ltac:(rewrite Nat2Z.inj_succ in Hb; lia)
                  ltac:(lia))
        as (l' & Hl1 & Hl2 & ->).
      exists l'. split; [lia|]. split; [lia|].
      replace (Z.to_nat (len - l')) with (3 + Z.to_nat (len - 3 - l'))%nat.
      2:{ change 3%nat with (Z.to_nat 3) at 1.
          rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
      rewrite if_copyn_add, E3. cbn [fst snd]. reflexivity.
    + exists len. split; [lia|]. split; [lia|].
      replace (Z.to_nat (len - len)) with 0%nat by lia.
      cbn [if_copyn fst snd]. reflexivity.
Qed.

Lemma if_copytail_flat : forall c s r len,
  0 <= len <= 2 ->
  if_copytail c s r len = fst (if_copyn (Z.to_nat len) c s r).
Proof.
  intros c s r len Hb. unfold if_copytail.
  destruct (Z.eqb_spec len 0) as [->|Hne].
  - reflexivity.
  - destruct (if_copyn 1 c s r) as [s1 r1] eqn:E1.
    destruct (Z.ltb_spec 1 len) as [H2|H1].
    + replace (Z.to_nat len) with (1 + 1)%nat by lia.
      rewrite if_copyn_add, E1. reflexivity.
    + replace (Z.to_nat len) with 1%nat by lia.
      rewrite E1. reflexivity.
Qed.

Lemma if_copydirect_flat : forall c s r len,
  3 <= len <= 258 ->
  if_copydirect c s r len
  = Some (fst (if_copyn (Z.to_nat len) c s r)).
Proof.
  intros c s r len Hb. unfold if_copydirect.
  destruct (if_copyn 3 c s r) as [s1 r1] eqn:E3.
  unfold u32. rewrite (Z.mod_small (len - 3)) by lia.
  destruct (if_copy3w_flat copy_fuel c s1 r1 (len - 3)
              ltac:(change (Z.of_nat copy_fuel) with 87; lia)
              ltac:(lia))
    as (l' & Hl1 & Hl2 & ->).
  rewrite if_copytail_flat by lia.
  f_equal.
  replace (Z.to_nat len)
    with (3 + (Z.to_nat (len - 3 - l') + Z.to_nat l'))%nat.
  2:{ change 3%nat with (Z.to_nat 3) at 1.
      rewrite <- !Z2Nat.inj_add by lia. f_equal. lia. }
  rewrite if_copyn_add, E3. cbn [fst snd].
  rewrite if_copyn_add. reflexivity.
Qed.

(* ==========================================================================
   6.  The window phase at [whave = 0]: the dodist window arm is BAD
       before any window byte is read (ZrLenFastLeg's premise world).
   ========================================================================== *)

Lemma u32_pos : forall x, 0 < x < 4294967296 -> 0 < u32 x.
Proof. intros x H. unfold u32. rewrite Z.mod_small by lia. lia. Qed.

(** Equation-premise form: the consumer computes each let-value by
    [reflexivity] and gets the [BodyBad] verdict without touching the
    let-chain hypothesis-side (R10 discipline). *)
Lemma if_dodist_whave0_bad :
  forall k c len s h s1 e s2 dist s3 od,
    f_whave c = 0 ->
    f_sane c <> 0 ->
    Z.land (c_op h) 16 <> 0 ->
    s1 = if_drop (c_bits h) s ->
    e = Z.land (c_op h) 15 ->
    s2 = (if Z.ltb (f_bits s1) e
          then if Z.ltb (f_bits (if_load1 c s1)) e
               then if_load1 c (if_load1 c s1)
               else if_load1 c s1
          else s1) ->
    dist = c_val h + if_low e s2 ->
    s3 = if_drop e s2 ->
    od = u32 (f_out s3 - f_beg c) ->
    od < dist ->
    dist - od < 4294967296 ->
    if_dodist (S k) c len s h = BodyBad s3 MSG_DIST_FAR.
Proof.
  intros k c len s h s1 e s2 dist s3 od Hwh Hsane H16 Es1 Ee Es2 Edist
         Es3 Eod Hlt Hcap.
  assert (Hod : 0 <= od) by (rewrite Eod; unfold u32; apply Z.mod_pos_bound; lia).
  cbn [if_dodist]. cbv zeta.
  assert (E16 : Z.eqb (Z.land (c_op h) 16) 0 = false)
    by (apply Z.eqb_neq; exact H16).
  rewrite E16. cbn [negb].
  subst od s3 dist s2 e s1.
  match goal with
  | |- context [Z.ltb ?a ?b] =>
      match a with
      | u32 _ => replace (Z.ltb a b) with true
          by (symmetry; apply Z.ltb_lt; exact Hlt)
      end
  end.
  rewrite Hwh.
  match goal with
  | |- context [Z.ltb 0 (u32 ?w)] =>
      replace (Z.ltb 0 (u32 w)) with true
        by (symmetry; apply Z.ltb_lt; apply u32_pos; lia)
  end.
  assert (Es : Z.eqb (f_sane c) 0 = false) by (apply Z.eqb_neq; exact Hsane).
  rewrite Es. cbn [negb andb].
  reflexivity.
Qed.

(* ==========================================================================
   7.  Consumer smoke: the pack composes with [resolve_lz]'s arms.
   ========================================================================== *)

Section Smoke.

(** Literal: one [if_put] is one [LzLit] resolution step. *)
Lemma smoke_put : forall v s,
  0 <= f_out s ->
  resolve_lz [LzLit v] (zslice (f_buf s) 0 (f_out s))
  = Some (zslice (f_buf (if_put v s)) 0 (f_out s + 1)).
Proof.
  intros v s H. cbn [resolve_lz].
  rewrite if_put_slice by exact H. reflexivity.
Qed.

(** Reference: one [SrcOut] copy is one [LzRef] resolution step. *)
Lemma smoke_ref : forall (len dist : nat) c s,
  0 < Z.of_nat dist <= f_out s ->
  resolve_lz [LzRef len dist] (zslice (f_buf s) 0 (f_out s))
  = Some (zslice
            (f_buf (fst (if_copyn len c s (SrcOut (f_out s - Z.of_nat dist)))))
            0 (f_out s + Z.of_nat len)).
Proof.
  intros len dist c s Hd. cbn [resolve_lz].
  assert (Ez : (dist =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
  assert (El : (length (zslice (f_buf s) 0 (f_out s)) <? dist)%nat = false).
  { apply Nat.ltb_ge. rewrite zslice_length.
    assert (0 <= Z.of_nat dist) by lia.
    apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
  rewrite Ez, El. cbn [orb].
  rewrite <- (if_copyn_lz len dist c s) by exact Hd. reflexivity.
Qed.

End Smoke.
