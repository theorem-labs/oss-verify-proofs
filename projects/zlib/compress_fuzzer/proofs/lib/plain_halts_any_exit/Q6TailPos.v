(** * Q6TailPos — the POSITIVE tails: STREAM_END-arm selections (GAP7 F5).

    OWNER: q6-fixedtbl (2026-08-21).  Proves the wrapper hypotheses
    Hzltail / Hgztail at the ratified spellings AS AMENDED by my
    o_put = 0 finding (to q7-decode): each tail
    takes ONE added premise — the running check is a fixed point of the
    empty update — because inf_CHECK skips the update at wrote = 0 and
    compares the RAW h_check, while the check premise pins its
    nil-image.  The two nil-fixed-point DISCHARGE lemmas are exported
    here (adler under AdVal; crc under the word range) so the pump
    consumes them by name.

    The discriminating structure: the stream pinned to padding ++
    trailer, the value equations in the machine's spelling, and THE TIE
    (q_out = o_put + o_left) — which pins the machine's M_CHECK update
    span to the WHOLE output slice, making the value equations
    state-general (do not simplify it away).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn ZBitsBridge Checksum ChecksumThy
  InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproQ6A ZReproL0C ZReproL0E ZReproQ6C GtAdlerChunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Byte ranges.
   ========================================================================== *)

Lemma u8_range : forall x, 0 <= u8 x < 256.
Proof. intro x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma land255_range : forall x, 0 <= Z.land x 255 < 256.
Proof.
  intro x.
  replace 255 with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

(* ==========================================================================
   1.  The aligned pull: a byte-aligned reader holding at least 32 bits
       of stream reaches bits = 32 exactly, preserving stream and wf.
       (Alignment is FREE at both call sites: availability 32 or 64
       forces bits = 8k.)
   ========================================================================== *)

Lemma inf_nb_align_go : forall f b,
  br_wf b ->
  br_bits b mod 8 = 0 ->
  br_bits b <= 32 ->
  32 <= br_bits b + 8 * br_have b ->
  32 <= br_bits b + 8 * Z.of_nat f ->
  exists b', inf_nb_go f 32 b = NBOk b'
    /\ br_bits b' = 32
    /\ 8 * br_have b' = br_bits b + 8 * br_have b - 32
    /\ br_stream b' = br_stream b
    /\ br_wf b'.
Proof.
  induction f as [|k IH]; intros b Hwf Hmod Hle Hav Hfuel.
  - assert (Hb : br_bits b = 32) by (cbn in Hfuel; lia).
    exists b. cbn [inf_nb_go].
    rewrite Hb, Z.ltb_irrefl.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [lia|].
    split; [reflexivity|].
    exact Hwf.
  - cbn [inf_nb_go].
    destruct (Z.ltb_spec (br_bits b) 32) as [Hlt|Hge].
    + assert (Hhpos : 0 < br_have b) by lia.
      assert (EP : br_pullbyte b
        = Some {| br_in := br_in b; br_have := br_have b - 1;
                  br_next := br_next b + 1;
                  br_hold := br_hold b
                     + Z.shiftl (br_in b (br_next b)) (br_bits b);
                  br_bits := br_bits b + 8 |}).
      { unfold br_pullbyte.
        rewrite (proj2 (Z.eqb_neq (br_have b) 0) ltac:(lia)). reflexivity. }
      set (b1 := {| br_in := br_in b; br_have := br_have b - 1;
                    br_next := br_next b + 1;
                    br_hold := br_hold b
                       + Z.shiftl (br_in b (br_next b)) (br_bits b);
                    br_bits := br_bits b + 8 |}) in *.
      assert (Hwf1 : br_wf b1)
        by (apply (br_wf_pullbyte b b1 Hwf ltac:(lia) EP)).
      assert (Hst1 : br_stream b1 = br_stream b)
        by (apply (br_stream_pullbyte b b1 Hwf EP)).
      assert (Hb24 : br_bits b <= 24)
        by (pose proof (Z_div_mod_eq_full (br_bits b) 8); lia).
      assert (Hmod1 : br_bits b1 mod 8 = 0).
      { unfold b1; cbn [br_bits].
        replace (br_bits b + 8) with (br_bits b + 1 * 8) by lia.
        rewrite Z.mod_add by lia. exact Hmod. }
      rewrite EP.
      destruct (IH b1 Hwf1 Hmod1
                  ltac:(unfold b1; cbn [br_bits]; lia)
                  ltac:(unfold b1; cbn [br_bits br_have]; lia)
                  ltac:(unfold b1; cbn [br_bits]; lia))
        as (b' & E & Hb' & Hh' & Hs' & Hwf').
      exists b'.
      split; [exact E|].
      split; [exact Hb'|].
      split; [unfold b1 in Hh'; cbn [br_bits br_have] in Hh'; lia|].
      split; [rewrite Hs'; exact Hst1|].
      exact Hwf'.
    + assert (Hb : br_bits b = 32) by lia.
      exists b.
      split; [reflexivity|].
      split; [exact Hb|].
      split; [lia|].
      split; [reflexivity|].
      exact Hwf.
Qed.

Lemma inf_nb_align32 : forall b,
  br_wf b ->
  br_bits b mod 8 = 0 ->
  br_bits b <= 32 ->
  32 <= br_bits b + 8 * br_have b ->
  exists b', inf_nb 32 b = NBOk b'
    /\ br_bits b' = 32
    /\ 8 * br_have b' = br_bits b + 8 * br_have b - 32
    /\ br_stream b' = br_stream b
    /\ br_wf b'.
Proof.
  intros b Hwf Hmod Hle Hav.
  unfold inf_nb.
  change (Z.to_nat 32) with 32%nat.
  apply inf_nb_align_go; auto.
  change (Z.of_nat 32) with 32.
  destruct Hwf as (Hb & _). lia.
Qed.

(* ==========================================================================
   2.  Stream algebra: four bytes as one 32-bit write; the pinned hold.
   ========================================================================== *)

Lemma bytes4_write32 : forall c0 c1 c2 c3,
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  bytes_bits [c0; c1; c2; c3]
  = write_bits 32 (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3).
Proof.
  intros c0 c1 c2 c3 H0 H1 H2 H3.
  rewrite !bytes_bits_cons, bytes_bits_nil, app_nil_r.
  rewrite !byte_bits_write_bits.
  replace (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3)
    with (c0 + (c1 + (c2 + c3 * 2 ^ Z.of_nat 8) * 2 ^ Z.of_nat 8)
               * 2 ^ Z.of_nat 8)
    by (change (2 ^ Z.of_nat 8) with 256; lia).
  change 32%nat with (8 + 24)%nat.
  rewrite (write_bits_split 8 24)
    by (change (2 ^ Z.of_nat 8) with 256; lia).
  change 24%nat with (8 + 16)%nat.
  rewrite (write_bits_split 8 16)
    by (change (2 ^ Z.of_nat 8) with 256; lia).
  change 16%nat with (8 + 8)%nat.
  rewrite (write_bits_split 8 8)
    by (change (2 ^ Z.of_nat 8) with 256; lia).
  rewrite <- ?app_assoc.
  reflexivity.
Qed.

Lemma bytes_bits_app : forall xs ys,
  bytes_bits (xs ++ ys) = bytes_bits xs ++ bytes_bits ys.
Proof.
  induction xs as [|x r IH]; intro ys; [reflexivity|].
  cbn [app]. rewrite !bytes_bits_cons, IH, app_assoc. reflexivity.
Qed.

Lemma app_skipn32 : forall (l1 l2 : list bool),
  length l1 = 32%nat -> skipn 32 (l1 ++ l2) = l2.
Proof.
  intros l1 l2 HL.
  rewrite skipn_app.
  replace (skipn 32 l1) with (@nil bool)
    by (rewrite <- HL; symmetry; apply skipn_all).
  replace (32 - length l1)%nat with 0%nat by lia.
  reflexivity.
Qed.

(** The wrapper's [br_stream] (ZReproQ6A) and the bridge's are the same
    function by delta; the bridge's [skipn] lemmas transport across. *)
Lemma br_stream_agree : forall b,
  br_stream b = ZBitsBridge.br_stream b.
Proof. reflexivity. Qed.

(** A reader parked at bits = 32 whose stream opens with a pinned
    32-bit write holds exactly that value. *)
Lemma hold32_of_stream : forall b v rest,
  br_wf b -> br_bits b = 32 ->
  br_stream b = write_bits 32 v ++ rest ->
  0 <= v < 4294967296 ->
  br_hold b = v.
Proof.
  intros b v rest Hwf Hb Hs Hv.
  pose proof (br_read_agree 32 b Hwf ltac:(lia)) as HR.
  change (Z.to_nat 32) with 32%nat in HR.
  rewrite Hs in HR.
  rewrite read_bits_write_bits in HR
    by (change (2 ^ Z.of_nat 32) with 4294967296; exact Hv).
  injection HR as HR1 _.
  unfold br_bits_of in HR1.
  destruct Hwf as (_ & Hh & _ & _).
  rewrite Hb in Hh.
  change (Z.shiftl 1 32) with 4294967296 in Hh.
  replace (Z.shiftl 1 32 - 1) with (Z.ones 32) in HR1 by reflexivity.
  rewrite Z.land_ones in HR1 by lia.
  rewrite Z.mod_small in HR1 by (change (2 ^ 32) with 4294967296; lia).
  lia.
Qed.

(** LE recomposition: [zr_le32]'s bytes reassemble to the value. *)
Lemma le32_assemble : forall v, 0 <= v < 4294967296 ->
  Z.land v 255 + 256 * Z.land (Z.shiftr v 8) 255
  + 65536 * Z.land (Z.shiftr v 16) 255
  + 16777216 * Z.land (Z.shiftr v 24) 255 = v.
Proof.
  intros v Hv.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace 255 with (Z.ones 8) by reflexivity.
  rewrite !Z.land_ones by lia.
  change (2 ^ 8) with 256.
  replace (v / 2 ^ 16) with (v / 256 / 256)
    by (rewrite Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 24) with (v / 256 / 256 / 256)
    by (rewrite !Z.div_div by lia; reflexivity).
  assert (Hd3 : v / 256 / 256 / 256 < 256).
  { apply Z.div_lt_upper_bound; [lia|].
    apply Z.div_lt_upper_bound; [lia|].
    apply Z.div_lt_upper_bound; lia. }
  assert (Hd3n : 0 <= v / 256 / 256 / 256)
    by (apply Z.div_pos; [apply Z.div_pos; [apply Z.div_pos|]|]; lia).
  rewrite (Z.mod_small (v / 256 / 256 / 256) 256) by lia.
  pose proof (Z_div_mod_eq_full v 256).
  pose proof (Z_div_mod_eq_full (v / 256) 256).
  pose proof (Z_div_mod_eq_full (v / 256 / 256) 256).
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 256 / 256) 256 ltac:(lia)).
  lia.
Qed.

(* ==========================================================================
   3.  The nil-fixed-point discharge lemmas (the amendment's premises).
   ========================================================================== *)

(** A canonical adler value is a fixed point of the empty update. *)
Lemma adler32_z_nil_fix : forall a,
  AdVal a -> adler32_z a false [] = a.
Proof.
  intros a [[Hlo Hhi] Hw].
  unfold adler32_z. cbv zeta.
  cbn [length].
  change (Z.of_nat 0) with 0.
  change (0 =? 1) with false. cbv beta iota.
  change (0 <? 16) with true. cbv beta iota.
  cbn [ad_run fold_left a_adler a_sum2].
  rewrite (proj2 (Z.leb_gt ADLER_BASE (Z.land a 65535)) (proj2 Hlo)).
  cbv iota.
  rewrite (Z.mod_small _ ADLER_BASE Hhi).
  assert (Ha16 : 0 <= Z.land a 65535 < 65536)
    by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
  assert (Hs16 : 0 <= Z.land (Z.shiftr a 16) 65535) by lia.
  rewrite (lor_is_add16 _ _ Ha16 Hs16).
  rewrite !land16_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536.
  rewrite (Z.mod_small (a / 65536) 65536)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z_div_mod_eq_full a 65536). lia.
Qed.

(** A word-ranged crc value is a fixed point of the empty update. *)
Lemma crc32_z_nil_fix : forall c,
  0 <= c < 4294967296 -> crc32_z c false 0 [] = c.
Proof.
  intros c Hc.
  unfold crc32_z, crc32_z_at. cbv beta iota zeta.
  cbn [length].
  change (Z.of_nat 0) with 0.
  change (NBRAID * WBYTES + WBYTES - 1 <=? 0) with false. cbv beta iota.
  cbn [crc_tail crc_bytes fold_left].
  rewrite u32_lnot_lxor.
  unfold u32. rewrite (Z.mod_small c 4294967296 Hc).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  reflexivity.
Qed.

(* ==========================================================================
   4.  initbits: wf and stream shape.
   ========================================================================== *)

Lemma br_wf_initbits : forall b, br_wf b -> br_wf (br_initbits b).
Proof.
  intros b (Hb & Hh & Hv & Hr).
  unfold br_initbits, br_wf; cbn [br_bits br_hold br_have br_in].
  change (Z.shiftl 1 0) with 1.
  repeat split; try lia; apply Hr.
Qed.

Lemma br_stream_initbits : forall b,
  br_stream (br_initbits b) = bytes_bits (br_bytes b).
Proof. reflexivity. Qed.

(* ==========================================================================
   5.  The positive zlib CHECK arm.
   ========================================================================== *)

Lemma zr_zl_check_pos : forall q AD,
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  br_bits (q_br q) + 8 * br_have (q_br q) = 32 ->
  br_stream (q_br q) = bytes_bits (be32 AD) ->
  0 <= AD < 4294967296 ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q)))
            (ob_slice (q_ob q) 0 (o_put (q_ob q))) = AD ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q))) []
    = h_check (s_hdr (q_st q)) ->
  exists q'', inf_CHECK q = InfLeave q''
    /\ q_ret q'' = Z_STREAM_END
    /\ h_mode (s_hdr (q_st q'')) = M_DONE
    /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q)).
Proof.
  intros q AD Hw Hf Hwf Hav Hpin HAD Htie Hval Hfix.
  rewrite Hf in Hval, Hfix.
  unfold inf_CHECK. cbv zeta.
  rewrite Hw.
  change (5 =? 0) with false. cbv beta iota.
  assert (Hmod : br_bits (q_br q) mod 8 = 0).
  { replace (br_bits (q_br q)) with (0 + (4 - br_have (q_br q)) * 8)
      by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (Hble : br_bits (q_br q) <= 32)
    by (destruct Hwf as (_ & _ & Hhv & _); lia).
  destruct (inf_nb_align32 (q_br q) Hwf Hmod Hble ltac:(lia))
    as (b & EN & Hb32 & Hh0 & Hst & Hwfb).
  rewrite EN.
  (* the hold is exactly the LE assembly of the four trailer bytes *)
  assert (Hhold : br_hold b
    = u8 (AD / 16777216) + 256 * u8 (AD / 65536)
      + 65536 * u8 (AD / 256) + 16777216 * u8 AD).
  { apply (hold32_of_stream b _ []); auto.
    - rewrite app_nil_r, Hst, Hpin. unfold be32.
      apply bytes4_write32; apply u8_range.
    - pose proof (u8_range (AD / 16777216)).
      pose proof (u8_range (AD / 65536)).
      pose proof (u8_range (AD / 256)).
      pose proof (u8_range AD). lia. }
  assert (Hswap : zswap32 (br_hold b) = AD).
  { rewrite Hhold, <- zr_hold4. apply zr_zswap32_be. exact HAD. }
  cbv zeta.
  set (wrote := q_out q - o_left (q_ob q)) in *.
  assert (Hwrote : wrote = o_put (q_ob q)) by (unfold wrote; lia).
  rewrite Hf.
  change (Z.land 5 4) with 4.
  change (negb (4 =? 0)) with true.
  cbn [andb].
  change (0 =? 0) with true. cbv beta iota.
  rewrite Hswap.
  destruct (Z.eqb_spec wrote 0) as [W0|WN].
  - (* no output: the update is skipped; the fixed-point premise makes
       the raw h_check equal AD *)
    cbn [negb]. cbv beta iota.
    assert (Hck : h_check (s_hdr (q_st q)) = AD).
    { rewrite <- Hval.
      replace (o_put (q_ob q)) with 0 by lia.
      unfold ob_slice. change (Z.to_nat 0) with O. cbn [seq map].
      exact (eq_sym Hfix). }
    match goal with |- context [AD =? ?ck] =>
      replace ck with AD by (rewrite <- Hck; reflexivity) end.
    rewrite Z.eqb_refl.
    cbn [negb andb]. cbv beta iota.
    unfold inf_LENGTH. cbv zeta.
    match goal with |- context [if negb (?w =? 0) && negb (?f' =? 0)
                                then _ else _] =>
      replace w with (h_wrap (s_hdr (q_st q))) by reflexivity;
      replace f' with (h_flags (s_hdr (q_st q))) by reflexivity end.
    rewrite Hw, Hf.
    change (negb (5 =? 0) && negb (0 =? 0)) with false.
    cbv beta iota.
    unfold inf_DONE.
    eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
  - (* output present: the update fires over the WHOLE slice (the tie) *)
    cbn [negb]. cbv beta iota.
    replace (o_put (q_ob q) - wrote) with 0 by lia.
    rewrite Hwrote.
    match goal with |- context [AD =? ?ck] =>
      replace ck with AD by (rewrite <- Hval; reflexivity) end.
    rewrite Z.eqb_refl.
    cbn [negb andb]. cbv beta iota.
    unfold inf_LENGTH. cbv zeta.
    match goal with |- context [if negb (?w =? 0) && negb (?f' =? 0)
                                then _ else _] =>
      replace w with (h_wrap (s_hdr (q_st q))) by reflexivity;
      replace f' with (h_flags (s_hdr (q_st q))) by reflexivity end.
    rewrite Hw, Hf.
    change (negb (5 =? 0) && negb (0 =? 0)) with false.
    cbv beta iota.
    unfold inf_DONE.
    eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
Qed.

(* ==========================================================================
   6.  The composed zlib positive tail — Hzltail's ratified spelling,
       AMENDED (the one added fixed-point premise, last).
   ========================================================================== *)

Lemma zr_zl_tail_pos : forall q remb AD,
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  br_wf (q_br q) ->
  W2Stream.br_haligned (q_br q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  br_stream (q_br q) = remb ++ bytes_bits (be32 AD) ->
  (length remb < 8)%nat ->
  0 <= AD < 4294967296 ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q)))
            (ob_slice (q_ob q) 0 (o_put (q_ob q))) = AD ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q))) []
    = h_check (s_hdr (q_st q)) ->
  exists n q'',
    inf_loop n zr_ic q = Some (InfLeave q'')
    /\ q_ret q'' = Z_STREAM_END
    /\ h_mode (s_hdr (q_st q'')) = M_DONE
    /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q)).
Proof.
  intros q remb AD Hw Hf Hmode Hlast Hwf Hal Htie Hpin Hremb HAD Hval Hfix.
  assert (Hfl : zr_cflush_ok zr_ic).
  { unfold zr_cflush_ok, zr_ic. cbn [n_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  set (q1 := qmode (qset_br q (br_bytebits (q_br q))) M_CHECK).
  assert (S1 : inf_step zr_ic q = InfCont q1).
  { unfold inf_step, q_mode. rewrite Hmode.
    unfold inf_TYPE.
    rewrite (zr_eqb_nB zr_ic Hfl), (zr_eqb_nT zr_ic Hfl). cbn [orb].
    unfold inf_TYPEDO. cbv zeta.
    rewrite (proj2 (Z.eqb_neq _ _) Hlast). reflexivity. }
  assert (Hm1 : h_mode (s_hdr (q_st q1)) = M_CHECK) by reflexivity.
  assert (Hk : 0 <= Z.land (br_bits (q_br q)) 7 <= br_bits (q_br q)).
  { destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    pose proof (Z.mod_le (br_bits (q_br q)) 8 ltac:(lia) ltac:(lia)).
    lia. }
  assert (Hwf1 : br_wf (q_br q1)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    unfold br_bytebits.
    apply br_wf_dropbits; [exact Hwf | exact Hk]. }
  (* transport: the drop is exactly the padding *)
  pose proof (br_stream_length (q_br q) Hwf) as HL0.
  assert (HLtr : length (bytes_bits (be32 AD)) = 32%nat).
  { unfold be32. rewrite bytes4_write32 by apply u8_range.
    apply write_bits_length. }
  assert (HLr : Z.of_nat (length remb) = Z.land (br_bits (q_br q)) 7).
  { rewrite Hpin, length_app, HLtr, Nat2Z.inj_add in HL0.
    change (Z.of_nat 32%nat) with 32 in HL0.
    replace (Z.land (br_bits (q_br q)) 7) with (br_bits (q_br q) mod 8)
      by (replace 7 with (Z.ones 3) by reflexivity;
          rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z_div_mod_eq_full (br_bits (q_br q)) 8).
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    lia. }
  assert (Hpin1 : br_stream (q_br q1) = bytes_bits (be32 AD)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    rewrite br_stream_agree, (br_stream_bytebits _ Hwf),
            <- br_stream_agree, Hpin.
    replace (Z.to_nat (Z.land (br_bits (q_br q)) 7)) with (length remb)
      by (rewrite <- HLr, Nat2Z.id; reflexivity).
    rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hav1 : br_bits (q_br q1) + 8 * br_have (q_br q1) = 32).
  { pose proof (br_stream_length (q_br q1) Hwf1) as HL1.
    rewrite Hpin1, HLtr in HL1.
    change (Z.of_nat 32%nat) with 32 in HL1. lia. }
  destruct (zr_zl_check_pos q1 AD Hw Hf Hwf1 Hav1 Hpin1 HAD Htie Hval Hfix)
    as (q2 & E2 & R2 & M2 & W2).
  exists 2%nat, q2. split.
  - cbn [inf_loop]. rewrite S1. cbv iota.
    unfold inf_step, q_mode. rewrite Hm1.
    rewrite E2. reflexivity.
  - split; [exact R2|].
    split; [exact M2|].
    rewrite W2. reflexivity.
Qed.

(* ==========================================================================
   7.  The positive gzip CHECK arm (flags = 8: raw-hold crc compare,
       then the ACTIVE LENGTH arm reads ISIZE from the drained bytes).
   ========================================================================== *)

Lemma zr_gz_check_pos : forall q CRC ISIZE,
  h_wrap (s_hdr (q_st q)) = 6 ->
  h_flags (s_hdr (q_st q)) = 8 ->
  br_wf (q_br q) ->
  br_bits (q_br q) + 8 * br_have (q_br q) = 64 ->
  br_stream (q_br q) = bytes_bits (zr_le32 CRC ++ zr_le32 ISIZE) ->
  0 <= CRC < 4294967296 ->
  0 <= ISIZE < 4294967296 ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  crc32_z (h_check (s_hdr (q_st q))) false 0
          (ob_slice (q_ob q) 0 (o_put (q_ob q))) = CRC ->
  crc32_z (h_check (s_hdr (q_st q))) false 0 [] = h_check (s_hdr (q_st q)) ->
  Z.land (h_total (s_hdr (q_st q)) + o_put (q_ob q)) 4294967295 = ISIZE ->
  exists q'', inf_CHECK q = InfLeave q''
    /\ q_ret q'' = Z_STREAM_END
    /\ h_mode (s_hdr (q_st q'')) = M_DONE
    /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q)).
Proof.
  intros q CRC ISIZE Hw Hf Hwf Hav Hpin HCRC HIS Htie Hval Hfix Htot.
  unfold inf_CHECK. cbv zeta.
  rewrite Hw.
  change (6 =? 0) with false. cbv beta iota.
  assert (Hmod : br_bits (q_br q) mod 8 = 0).
  { replace (br_bits (q_br q)) with (0 + (8 - br_have (q_br q)) * 8)
      by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (Hble : br_bits (q_br q) <= 32)
    by (destruct Hwf as (Hb & _); lia).
  destruct (inf_nb_align32 (q_br q) Hwf Hmod Hble ltac:(lia))
    as (b & EN & Hb32 & Hh4 & Hst & Hwfb).
  rewrite EN.
  (* stream lengths for the split *)
  assert (HLc : length (bytes_bits (zr_le32 CRC)) = 32%nat).
  { unfold zr_le32. rewrite bytes4_write32 by apply land255_range.
    apply write_bits_length. }
  assert (Hstb : br_stream b
    = bytes_bits (zr_le32 CRC) ++ bytes_bits (zr_le32 ISIZE))
    by (rewrite Hst, Hpin; apply bytes_bits_app).
  (* the CRC hold *)
  assert (Hhold : br_hold b = CRC).
  { assert (H4 : br_hold b
      = Z.land CRC 255 + 256 * Z.land (Z.shiftr CRC 8) 255
        + 65536 * Z.land (Z.shiftr CRC 16) 255
        + 16777216 * Z.land (Z.shiftr CRC 24) 255).
    { apply (hold32_of_stream b _ (bytes_bits (zr_le32 ISIZE))); auto.
      - rewrite Hstb. unfold zr_le32 at 1.
        rewrite bytes4_write32 by apply land255_range. reflexivity.
      - pose proof (land255_range CRC).
        pose proof (land255_range (Z.shiftr CRC 8)).
        pose proof (land255_range (Z.shiftr CRC 16)).
        pose proof (land255_range (Z.shiftr CRC 24)). lia. }
    rewrite H4. apply le32_assemble. exact HCRC. }
  (* the drained bytes carry ISIZE *)
  assert (HB : bytes_bits (br_bytes b) = bytes_bits (zr_le32 ISIZE)).
  { pose proof Hstb as HS.
    unfold br_stream, zwrite in HS. rewrite Hb32 in HS.
    change (Z.to_nat 32) with 32%nat in HS.
    pose proof (f_equal (skipn 32%nat) HS) as HSK.
    rewrite (app_skipn32 _ _ (write_bits_length _ _)) in HSK.
    rewrite (app_skipn32 _ _ HLc) in HSK.
    exact HSK. }
  cbv zeta.
  set (wrote := q_out q - o_left (q_ob q)) in *.
  assert (Hwrote : wrote = o_put (q_ob q)) by (unfold wrote; lia).
  rewrite Hf.
  change (Z.land 6 4) with 4.
  change (negb (4 =? 0)) with true.
  cbn [andb].
  change (8 =? 0) with false. cbv beta iota.
  rewrite Hhold.
  (* the LENGTH continuation, shared by both wrote-branches *)
  assert (HLEN : forall q5 : InfSt,
      h_wrap (s_hdr (q_st q5)) = 6 ->
      h_flags (s_hdr (q_st q5)) = 8 ->
      h_total (s_hdr (q_st q5)) = h_total (s_hdr (q_st q)) + wrote ->
      w_wsize (s_win (q_st q5)) = w_wsize (s_win (q_st q)) ->
      exists q'',
        inf_LENGTH (qmode (qset_br q5 (br_initbits b)) M_LENGTH)
          = InfLeave q''
        /\ q_ret q'' = Z_STREAM_END
        /\ h_mode (s_hdr (q_st q'')) = M_DONE
        /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q))).
  { intros q5 Hw5 Hf5 Ht5 Hws5.
    unfold inf_LENGTH. cbv zeta.
    match goal with |- context [if negb (?w =? 0) && negb (?f' =? 0)
                                then _ else _] =>
      replace w with (h_wrap (s_hdr (q_st q5))) by reflexivity;
      replace f' with (h_flags (s_hdr (q_st q5))) by reflexivity end.
    rewrite Hw5, Hf5.
    change (negb (6 =? 0) && negb (8 =? 0)) with true.
    cbv beta iota.
    (* the second read: 32 bits over the 4 drained bytes *)
    assert (Hwfi : br_wf (br_initbits b)) by (apply br_wf_initbits; auto).
    assert (Havi : br_bits (br_initbits b) + 8 * br_have (br_initbits b)
                   = 32)
      by (unfold br_initbits; cbn [br_bits br_have]; lia).
    destruct (inf_nb_align32 (br_initbits b) Hwfi
                ltac:(reflexivity)
                ltac:(unfold br_initbits; cbn [br_bits]; lia)
                ltac:(lia))
      as (b2 & EN2 & Hb232 & Hh20 & Hst2 & Hwfb2).
    match goal with |- context [inf_nb 32 ?r] =>
      replace r with (br_initbits b) by reflexivity end.
    rewrite EN2.
    assert (Hhold2 : br_hold b2 = ISIZE).
    { assert (H4 : br_hold b2
        = Z.land ISIZE 255 + 256 * Z.land (Z.shiftr ISIZE 8) 255
          + 65536 * Z.land (Z.shiftr ISIZE 16) 255
          + 16777216 * Z.land (Z.shiftr ISIZE 24) 255).
      { apply (hold32_of_stream b2 _ []); auto.
        - rewrite app_nil_r, Hst2, br_stream_initbits, HB.
          unfold zr_le32.
          rewrite bytes4_write32 by apply land255_range. reflexivity.
        - pose proof (land255_range ISIZE).
          pose proof (land255_range (Z.shiftr ISIZE 8)).
          pose proof (land255_range (Z.shiftr ISIZE 16)).
          pose proof (land255_range (Z.shiftr ISIZE 24)). lia. }
      rewrite H4. apply le32_assemble. exact HIS. }
    change (Z.land 6 4) with 4.
    change (negb (4 =? 0)) with true.
    cbn [andb].
    rewrite Hhold2.
    match goal with |- context [ISIZE =? Z.land ?t 4294967295] =>
      replace t with (h_total (s_hdr (q_st q5))) by reflexivity end.
    rewrite Ht5, Hwrote, Htot.
    rewrite Z.eqb_refl.
    cbn [negb]. cbv beta iota.
    unfold inf_DONE.
    eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    exact Hws5. }
  destruct (Z.eqb_spec wrote 0) as [W0|WN].
  - (* no output: the update is skipped; fixed point closes the gate *)
    cbn [negb]. cbv beta iota.
    assert (Hck : h_check (s_hdr (q_st q)) = CRC).
    { rewrite <- Hval.
      replace (o_put (q_ob q)) with 0 by lia.
      unfold ob_slice. change (Z.to_nat 0) with O. cbn [seq map].
      exact (eq_sym Hfix). }
    match goal with |- context [CRC =? ?ck] =>
      replace ck with CRC by (rewrite <- Hck; reflexivity) end.
    rewrite Z.eqb_refl.
    cbn [negb andb]. cbv beta iota.
    match goal with |- context [qset_br ?X (br_initbits b)] =>
      destruct (HLEN X ltac:(exact Hw) ltac:(exact Hf)
                  ltac:(reflexivity) ltac:(reflexivity))
        as (q'' & EL & RL & ML & WL)
    end.
    exists q''. rewrite EL.
    split; [reflexivity|]. split; [exact RL|]. split; [exact ML|].
    exact WL.
  - (* output present: the tie makes the update span the whole slice *)
    cbn [negb]. cbv beta iota.
    replace (o_put (q_ob q) - wrote) with 0 by lia.
    rewrite Hwrote.
    match goal with |- context [CRC =? ?ck] =>
      replace ck with CRC by
        (rewrite <- Hval; unfold upd_check;
         change (8 =? 0) with false; cbv beta iota; reflexivity) end.
    rewrite Z.eqb_refl.
    cbn [negb andb]. cbv beta iota.
    match goal with |- context [qset_br ?X (br_initbits b)] =>
      destruct (HLEN X ltac:(exact Hw) ltac:(exact Hf)
                  ltac:(rewrite Hwrote; reflexivity) ltac:(reflexivity))
        as (q'' & EL & RL & ML & WL)
    end.
    exists q''. rewrite EL.
    split; [reflexivity|]. split; [exact RL|]. split; [exact ML|].
    exact WL.
Qed.

(* ==========================================================================
   8.  The composed gzip positive tail — Hgztail's ratified spelling,
       AMENDED (the one added fixed-point premise, after the crc one).
   ========================================================================== *)

Lemma zr_gz_tail_pos : forall q remb CRC ISIZE,
  h_wrap (s_hdr (q_st q)) = 6 ->
  h_flags (s_hdr (q_st q)) = 8 ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  br_wf (q_br q) ->
  W2Stream.br_haligned (q_br q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  br_stream (q_br q) = remb ++ bytes_bits (zr_le32 CRC ++ zr_le32 ISIZE) ->
  (length remb < 8)%nat ->
  0 <= CRC < 4294967296 ->
  0 <= ISIZE < 4294967296 ->
  crc32_z (h_check (s_hdr (q_st q))) false 0
          (ob_slice (q_ob q) 0 (o_put (q_ob q))) = CRC ->
  crc32_z (h_check (s_hdr (q_st q))) false 0 [] = h_check (s_hdr (q_st q)) ->
  Z.land (h_total (s_hdr (q_st q)) + o_put (q_ob q)) 4294967295 = ISIZE ->
  exists n q'',
    inf_loop n zr_ic q = Some (InfLeave q'')
    /\ q_ret q'' = Z_STREAM_END
    /\ h_mode (s_hdr (q_st q'')) = M_DONE
    /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q)).
Proof.
  intros q remb CRC ISIZE Hw Hf Hmode Hlast Hwf Hal Htie Hpin Hremb
         HCRC HIS Hval Hfix Htot.
  assert (Hfl : zr_cflush_ok zr_ic).
  { unfold zr_cflush_ok, zr_ic. cbn [n_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  set (q1 := qmode (qset_br q (br_bytebits (q_br q))) M_CHECK).
  assert (S1 : inf_step zr_ic q = InfCont q1).
  { unfold inf_step, q_mode. rewrite Hmode.
    unfold inf_TYPE.
    rewrite (zr_eqb_nB zr_ic Hfl), (zr_eqb_nT zr_ic Hfl). cbn [orb].
    unfold inf_TYPEDO. cbv zeta.
    rewrite (proj2 (Z.eqb_neq _ _) Hlast). reflexivity. }
  assert (Hm1 : h_mode (s_hdr (q_st q1)) = M_CHECK) by reflexivity.
  assert (Hk : 0 <= Z.land (br_bits (q_br q)) 7 <= br_bits (q_br q)).
  { destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    pose proof (Z.mod_le (br_bits (q_br q)) 8 ltac:(lia) ltac:(lia)).
    lia. }
  assert (Hwf1 : br_wf (q_br q1)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    unfold br_bytebits.
    apply br_wf_dropbits; [exact Hwf | exact Hk]. }
  pose proof (br_stream_length (q_br q) Hwf) as HL0.
  assert (HLtr : length (bytes_bits (zr_le32 CRC ++ zr_le32 ISIZE))
                 = 64%nat).
  { rewrite bytes_bits_app, length_app.
    unfold zr_le32.
    rewrite !bytes4_write32 by apply land255_range.
    rewrite !write_bits_length. reflexivity. }
  assert (HLr : Z.of_nat (length remb) = Z.land (br_bits (q_br q)) 7).
  { rewrite Hpin, length_app, HLtr, Nat2Z.inj_add in HL0.
    change (Z.of_nat 64%nat) with 64 in HL0.
    replace (Z.land (br_bits (q_br q)) 7) with (br_bits (q_br q) mod 8)
      by (replace 7 with (Z.ones 3) by reflexivity;
          rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z_div_mod_eq_full (br_bits (q_br q)) 8).
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    lia. }
  assert (Hpin1 : br_stream (q_br q1)
                  = bytes_bits (zr_le32 CRC ++ zr_le32 ISIZE)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    rewrite br_stream_agree, (br_stream_bytebits _ Hwf),
            <- br_stream_agree, Hpin.
    replace (Z.to_nat (Z.land (br_bits (q_br q)) 7)) with (length remb)
      by (rewrite <- HLr, Nat2Z.id; reflexivity).
    rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hav1 : br_bits (q_br q1) + 8 * br_have (q_br q1) = 64).
  { pose proof (br_stream_length (q_br q1) Hwf1) as HL1.
    rewrite Hpin1, HLtr in HL1.
    change (Z.of_nat 64%nat) with 64 in HL1. lia. }
  destruct (zr_gz_check_pos q1 CRC ISIZE Hw Hf Hwf1 Hav1 Hpin1 HCRC HIS
              Htie Hval Hfix Htot)
    as (q2 & E2 & R2 & M2 & W2).
  exists 2%nat, q2. split.
  - cbn [inf_loop]. rewrite S1. cbv iota.
    unfold inf_step, q_mode. rewrite Hm1.
    rewrite E2. reflexivity.
  - split; [exact R2|].
    split; [exact M2|].
    rewrite W2. reflexivity.
Qed.

Print Assumptions zr_zl_tail_pos.
Print Assumptions zr_gz_tail_pos.
Print Assumptions adler32_z_nil_fix.
Print Assumptions crc32_z_nil_fix.
