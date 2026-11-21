(** * G3Static — the STATIC-Huffman arm of one emitted block.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The 3-bit header ([STATIC_TREES] + BFINAL), then CbFold's
    [compress_block_decodes] instantiated at the static tables — every
    table-side premise is a landed value fact ([static_ltree_codes],
    [fixed_lit_valid], [lit_coded], [dist_coded], [DcodeRange_all],
    [lcode_range]); the token-side [Forall tok_ok] is derived here from
    the walk's [cEnc]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Trees CbEmit CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [cEnc] already carries every shape fact the STATIC [tok_ok] needs. *)
Lemma cEnc_tok_ok_static : forall toks,
  cEnc toks ->
  Forall (tok_ok fixed_lit_lengths fixed_dist_lengths 288 30) toks.
Proof.
  intros toks H. induction H as [|t toks Ht Htoks IH]; constructor; [|exact IH].
  destruct t as [b|len dist]; cbn [tok_enc] in Ht; cbn [tok_ok].
  - split; [exact Ht|].
    apply lit_coded. lia.
  - destruct Ht as [Hlen Hdist].
    unfold MIN_MATCH, MAX_MATCH in Hlen.
    assert (Hlc : 0 <= len - 3 < 256) by lia.
    pose proof (lcode_range (len - 3) Hlc) as (Hli & _ & _).
    assert (HD : DcodeRange (dist - 1)) by (apply DcodeRange_all; lia).
    pose proof HD as (Hdcr & _ & _).
    assert (HnL : (Z.to_nat ((length_code (len - 3) + LITERALS + 1)%Z)
                   < 288)%nat)
      by (unfold LITERALS; lia).
    assert (HnD : (Z.to_nat ((d_code (dist - 1))%Z) < 30)%nat) by lia.
    split; [lia|].
    split; [lia|].
    split; [exact HD|].
    split; [exact HnL|].
    split; [exact HnD|].
    split; [apply lit_coded, HnL | apply dist_coded, HnD].
Qed.

Theorem static_arm_dec_blk : forall sym symnext toks b last acc out,
  bw_wf b ->
  last = 0 \/ last = 1 ->
  BufToks sym 0 symnext toks ->
  cEnc toks ->
  resolve acc toks = Some out ->
  exists delta,
    bw_stream (compress_block sym symnext static_ltree static_dtree
                 (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 b))
      = bw_stream b ++ delta
    /\ bw_wf (compress_block sym symnext static_ltree static_dtree
                (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 b))
    /\ (forall suffix,
         dec_blk (delta ++ suffix) acc = Some (Z.eqb last 1, out, suffix))
    /\ (forall suffix,
         Gap7Strict.dec_blk_strict (delta ++ suffix) acc
         = Some (Z.eqb last 1, out, suffix)).
Proof.
  intros sym symnext toks b last acc out Hwf Hl Hbuf Henc Hres.
  destruct (bw_send_bits_stream (Z.shiftl STATIC_TREES 1 + last) 3 b Hwf
              ltac:(unfold Buf_size; lia)
              ltac:(unfold STATIC_TREES; destruct Hl; subst; cbn; lia))
    as [S0 W0].
  set (b0 := bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 b) in *.
  destruct (compress_block_decodes sym symnext static_ltree static_dtree
              fixed_lit_lengths fixed_dist_lengths 288 30 b0 toks acc out
              static_ltree_codes static_dtree_codes ltac:(lia) W0 Hbuf
              (cEnc_tok_ok_static toks Henc)
              ltac:(apply lit_coded; lia)
              fixed_lit_valid fixed_dist_valid Henc Hres)
    as (delta' & Hs' & Hw' & Hdec).
  exists (zwrite 3 (Z.shiftl STATIC_TREES 1 + last) ++ delta').
  split; [rewrite Hs', S0, app_assoc; reflexivity|].
  split; [exact Hw'|].
  split.
  { intro suffix.
    destruct (Hdec suffix) as (syms & Hsyms & Hlz).
    rewrite <- app_assoc.
    destruct Hl; subst last; unfold dec_blk.
    - change (zwrite 3 (Z.shiftl STATIC_TREES 1 + 0))
        with [false; true; false].
      change (read_bits 1%nat ([false; true; false] ++ delta' ++ suffix))
        with (Some (0, [true; false] ++ delta' ++ suffix)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([true; false] ++ delta' ++ suffix))
        with (Some (1, delta' ++ suffix)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity.
    - change (zwrite 3 (Z.shiftl STATIC_TREES 1 + 1))
        with [true; true; false].
      change (read_bits 1%nat ([true; true; false] ++ delta' ++ suffix))
        with (Some (1, [true; false] ++ delta' ++ suffix)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([true; false] ++ delta' ++ suffix))
        with (Some (1, delta' ++ suffix)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity. }
  { intro suffix.
    destruct (Hdec suffix) as (syms & Hsyms & Hlz).
    rewrite <- app_assoc.
    destruct Hl; subst last; unfold Gap7Strict.dec_blk_strict.
    - change (zwrite 3 (Z.shiftl STATIC_TREES 1 + 0))
        with [false; true; false].
      change (read_bits 1%nat ([false; true; false] ++ delta' ++ suffix))
        with (Some (0, [true; false] ++ delta' ++ suffix)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([true; false] ++ delta' ++ suffix))
        with (Some (1, delta' ++ suffix)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity.
    - change (zwrite 3 (Z.shiftl STATIC_TREES 1 + 1))
        with [true; true; false].
      change (read_bits 1%nat ([true; true; false] ++ delta' ++ suffix))
        with (Some (1, [true; false] ++ delta' ++ suffix)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([true; false] ++ delta' ++ suffix))
        with (Some (1, delta' ++ suffix)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity. }
Qed.

Print Assumptions static_arm_dec_blk.
