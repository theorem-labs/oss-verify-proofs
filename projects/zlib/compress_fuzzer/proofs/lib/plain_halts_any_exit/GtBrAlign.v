(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtBrAlign — [br_haligned]
      preservation toolkit + the stream-length budget corollary.

    Amendment window 2, q7-decode per TL grant 2026-08-20; owner review
    trails.  Consumers: ZReproQ6P (stage lemmas), ZReproQ6Q (loop
    threading).  [br_haligned] is W2Stream's hold/array alignment
    invariant; this file proves it preserved by the two slow-side BR
    transitions ([br_pullbyte], [br_dropbits]) and lifts that through
    [inf_nb] and the root-only [inf_decode]. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff ZBitsIn ZBitsBridge DecodeBridge Inflate InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W2Stream ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The two primitive preservations.
   ========================================================================== *)

Lemma br_haligned_dropbits : forall n b,
  0 <= n <= br_bits b ->
  br_haligned b -> br_haligned (br_dropbits n b).
Proof.
  intros n b Hn Hal.
  unfold br_haligned in *.
  unfold br_dropbits; cbn [br_bits br_hold br_next br_in].
  intros j Hj.
  assert (Hmd : 8 * ((br_bits b - n) / 8) <= br_bits b - n)
    by (apply Z.mul_div_le; lia).
  rewrite Z.shiftr_shiftr by lia.
  replace (n + (br_bits b - n - 8 * j)) with (br_bits b - 8 * j) by lia.
  apply Hal.
  split; [lia|].
  apply Z.le_trans with ((br_bits b - n) / 8); [lia|].
  apply Z.div_le_mono; lia.
Qed.

Lemma br_haligned_pullbyte : forall b b1,
  br_wf b -> br_pullbyte b = Some b1 ->
  br_haligned b -> br_haligned b1.
Proof.
  intros b b1 Hwf Hp Hal.
  pose proof Hwf as (Hb & Hh & Hv & Hr).
  rewrite Z.shiftl_1_l in Hh.
  assert (H2b : 0 < 2 ^ br_bits b)
    by (apply Z.pow_pos_nonneg; lia).
  unfold br_pullbyte in Hp.
  destruct (Z.eqb_spec (br_have b) 0) as [E|NE]; [discriminate|].
  injection Hp as <-.
  unfold br_haligned in *.
  cbn [br_bits br_hold br_next br_in].
  intros j Hj.
  assert (Hdiv8 : (br_bits b + 8) / 8 = br_bits b / 8 + 1).
  { replace (br_bits b + 8) with (br_bits b + 1 * 8) by lia.
    rewrite Z.div_add by lia. reflexivity. }
  rewrite Hdiv8 in Hj.
  rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.eq_dec j 1) as [->|Hj1].
  - (* the fresh top byte *)
    replace (br_bits b + 8 - 8 * 1) with (br_bits b) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    replace (br_next b + 1 - 1) with (br_next b) by lia.
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    apply Z.mod_small.
    exact (Hr (br_next b)).
  - (* the surviving bytes shift down by one slot *)
    assert (Hjge : 2 <= j) by lia.
    replace (br_bits b + 8 - 8 * j) with (br_bits b - 8 * (j - 1)) by lia.
    set (s := br_bits b - 8 * (j - 1)).
    assert (Hs : 0 <= s).
    { unfold s.
      pose proof (Z.div_mod (br_bits b) 8 ltac:(lia)) as HD.
      pose proof (Z.mod_pos_bound (br_bits b) 8 ltac:(lia)) as HM.
      lia. }
    assert (H2s : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    assert (Hbs : br_bits b - s = 8 * (j - 1)) by (unfold s; lia).
    assert (Hsplit : 2 ^ br_bits b = 2 ^ (br_bits b - s) * 2 ^ s).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Hsplit.
    replace (br_hold b + br_in b (br_next b) * (2 ^ (br_bits b - s) * 2 ^ s))
      with (br_hold b + (br_in b (br_next b) * 2 ^ (br_bits b - s)) * 2 ^ s)
      by ring.
    rewrite Z.div_add by lia.
    assert (E2 : 2 ^ (br_bits b - s) = 2 ^ (br_bits b - s - 8) * 256).
    { change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia.
      f_equal. lia. }
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    rewrite E2.
    replace (br_hold b / 2 ^ s
             + br_in b (br_next b) * (2 ^ (br_bits b - s - 8) * 256))
      with (br_hold b / 2 ^ s
            + (br_in b (br_next b) * 2 ^ (br_bits b - s - 8)) * 256)
      by ring.
    rewrite Z.mod_add by lia.
    replace (br_next b + 1 - j) with (br_next b - (j - 1)) by lia.
    pose proof (Hal (j - 1) ltac:(split; lia)) as HA.
    rewrite Z.shiftr_div_pow2 in HA by (unfold s in Hs; lia).
    replace (br_bits b - 8 * (j - 1)) with s in HA by (unfold s; lia).
    replace 255 with (Z.ones 8) in HA by reflexivity.
    rewrite Z.land_ones in HA by lia.
    change (2 ^ 8) with 256 in HA.
    exact HA.
Qed.

(* ==========================================================================
   2.  Lifted through [inf_nb] (the NEEDBITS pull loop).
   ========================================================================== *)

Lemma inf_nb_go_align : forall f n b b1,
  br_wf b -> n <= 32 ->
  inf_nb_go f n b = NBOk b1 ->
  br_haligned b -> br_haligned b1.
Proof.
  induction f as [|f IH]; intros n b b1 Hwf Hn H Hal; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|].
    injection H as <-. exact Hal.
  - destruct (Z.ltb_spec (br_bits b) n) as [Hlt|Hge].
    + destruct (br_pullbyte b) as [b2|] eqn:HP; [|discriminate].
      assert (Hwf2 : br_wf b2)
        by (apply (br_wf_pullbyte b b2 Hwf ltac:(lia) HP)).
      exact (IH n b2 b1 Hwf2 Hn H
               (br_haligned_pullbyte b b2 Hwf HP Hal)).
    + injection H as <-. exact Hal.
Qed.

Lemma inf_nb_align : forall n b b1,
  br_wf b -> n <= 32 ->
  inf_nb n b = NBOk b1 ->
  br_haligned b -> br_haligned b1.
Proof.
  intros n b b1 Hwf Hn H. exact (inf_nb_go_align (Z.to_nat n) n b b1 Hwf Hn H).
Qed.

(* ==========================================================================
   3.  Lifted through the root fetch and the root-only [inf_decode].
   ========================================================================== *)

Lemma zr_fetch_go_align : forall (T : ztbl) (root : Z) f b h b1,
  br_wf b -> 0 < root <= 15 ->
  (forall i, 0 <= i < 2 ^ root -> 0 <= c_bits (T i) <= root) ->
  inf_fetch_go f T root b = FetchOk h b1 ->
  (br_haligned b -> br_haligned b1)
  /\ (exists i, 0 <= i < 2 ^ root /\ h = T i)
  /\ br_wf b1.
Proof.
  intros T root.
  induction f as [|f IH]; intros b h b1 Hwf Hroot Hcb H;
    cbn [inf_fetch_go] in H; [discriminate|].
  pose proof (DecodeBridge.br_bits_of_in_range root b ltac:(lia)) as Hir.
  destruct (Z.leb_spec (c_bits (T (br_bits_of root b))) (br_bits b))
    as [Hle|Hgt].
  - injection H as <- <-.
    split; [intro Hal; exact Hal|].
    split; [exists (br_bits_of root b); auto|].
    exact Hwf.
  - destruct (br_pullbyte b) as [b2|] eqn:HP; [|discriminate].
    assert (H31 : br_bits b <= 31).
    { pose proof (Hcb (br_bits_of root b) Hir). lia. }
    assert (Hwf2 : br_wf b2) by (apply (br_wf_pullbyte b b2 Hwf H31 HP)).
    destruct (IH b2 h b1 Hwf2 Hroot Hcb H) as (Himp & Hsh & Hwf1).
    split; [|split; [exact Hsh | exact Hwf1]].
    intro Hal.
    exact (Himp (br_haligned_pullbyte b b2 Hwf HP Hal)).
Qed.

Lemma zr_decode_align : forall (sub : Code -> bool) (T : ztbl) (root : Z)
                               b h b1 nb,
  br_wf b -> 0 < root <= 15 ->
  (forall i, 0 <= i < 2 ^ root -> 0 <= c_bits (T i) <= root) ->
  (forall i, 0 <= i < 2 ^ root -> sub (T i) = false) ->
  inf_decode sub T root b = DecOk h b1 nb ->
  br_haligned b -> br_haligned b1.
Proof.
  intros sub T root b h b1 nb Hwf Hroot Hcb Hsub H Hal.
  unfold inf_decode in H.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF; try discriminate.
  pose proof (inf_fetch_ok_bits T root b h0 b0 EF) as Hob.
  unfold inf_fetch in EF.
  destruct (zr_fetch_go_align T root (S (Z.to_nat (br_have b))) b h0 b0
              Hwf Hroot Hcb EF) as (Himp & (i & Hir & ->) & Hwf0).
  rewrite (Hsub i Hir) in H.
  injection H as <- <- <-.
  apply br_haligned_dropbits.
  - split; [exact (proj1 (Hcb i Hir)) | exact Hob].
  - exact (Himp Hal).
Qed.

(* ==========================================================================
   4.  The stream-length budget: [br_have + br_bits/8] is monotone along
       any stream-shortening transition (both trip kinds export the
       stream inequality, so the loop threads the cap for free).
   ========================================================================== *)

Lemma br_budget_mono : forall b b1,
  br_wf b -> br_wf b1 ->
  (length (br_stream b1) <= length (br_stream b))%nat ->
  br_have b1 + br_bits b1 / 8 <= br_have b + br_bits b / 8.
Proof.
  intros b b1 Hwf Hwf1 Hlen.
  pose proof (br_stream_length b Hwf) as E.
  pose proof (br_stream_length b1 Hwf1) as E1.
  assert (HZ : br_bits b1 + 8 * br_have b1 <= br_bits b + 8 * br_have b)
    by (rewrite <- E, <- E1; lia).
  assert (D : forall h w, h + w / 8 = (w + 8 * h) / 8).
  { intros h w.
    replace (w + 8 * h) with (w + h * 8) by ring.
    rewrite Z.div_add by lia. lia. }
  rewrite (D (br_have b1) (br_bits b1)).
  rewrite (D (br_have b) (br_bits b)).
  apply Z.div_le_mono; lia.
Qed.

(* ==========================================================================
   5.  Ownership-to-bound adapters (the premises [zr_decode_align] wants,
       derived from [ZReproQ6M.zr_root_own] at its call sites).
   ========================================================================== *)

Lemma zr_own_cbits : forall (T : ztbl) (root : Z) (lens : list nat)
                            (maxBits : nat) (ent : nat -> Code),
  ZReproQ6M.zr_root_own T root lens maxBits ent ->
  forall i, 0 <= i < 2 ^ root -> 0 <= c_bits (T i) <= root.
Proof.
  intros T root lens maxBits ent Hown i Hir.
  destruct (Hown i Hir) as (sym & cw & _ & Hcwr & HTi & Hcb & _).
  rewrite HTi, Hcb. lia.
Qed.

Lemma zr_own_sub : forall (sub : Code -> bool) (T : ztbl) (root : Z)
                          (lens : list nat) (maxBits : nat)
                          (ent : nat -> Code),
  ZReproQ6M.zr_root_own T root lens maxBits ent ->
  (forall sym cw, code_for lens maxBits sym = Some cw ->
       sub (ent sym) = false) ->
  forall i, 0 <= i < 2 ^ root -> sub (T i) = false.
Proof.
  intros sub T root lens maxBits ent Hown Hsub i Hir.
  destruct (Hown i Hir) as (sym & cw & Hcf & _ & HTi & _).
  rewrite HTi. exact (Hsub sym cw Hcf).
Qed.
