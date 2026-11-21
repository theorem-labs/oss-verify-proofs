(** * LdDynEmit — item (v-5c): what [send_all_trees] puts on the wire.

    OWNER: ld-seams.  Pin and shadowing check in LdDynSeam.v.

    One equation: the dynamic header's whole bit stream, as the concatenation of
    the four pieces the previous files proved separately —

      hdr_bits    the three counts               (LdDynHdr)
      sat_bits    the code-length vector          (LdDynHdr)
      bitsL       the literal/length tree         (LdDynSeam, over huffman-id)
      bitsD       the distance tree               (LdDynSeam, over huffman-id)

    EVERY HYPOTHESIS IS NAMED, and the ones that are not mine are named as
    such. The load-bearing one is [Hbl]: the tree [send_all_trees] uses to CODE
    the two tree descriptions is a [gen_codes] output. That is [build_bl_tree]'s
    job ([Trees.v:806]) and it is item (v-6), which huffman-id explicitly puts
    outside their layer. I am not discharging it here and I am not hiding it
    inside a definition either — it sits in the statement where a consumer has
    to look at it.

    Note on [Hbl]'s reach: rewriting it turns the conclusion's [sat_bits] into
    [sat_bits ... (gen_codes blt maxcbl blc)] as well, which is harmless because
    [gen_codes] never touches the length array — the code-length vector is the
    same either way, and LdDynCl's agreement theorem is stated for an arbitrary
    tree precisely so it can be applied at whichever spelling arrives. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam LdDynHdr LdDynCl.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem send_all_trees_stream :
  forall lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD,
  (* the writer arrives mid-stream, after the three-bit block header *)
  bw_wf (ts_bw s) ->
  (* RFC field ranges *)
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= 19 ->
  (* (v-6), NOT discharged here: the coding tree is a gen_codes output *)
  ts_trees s TK_BL = gen_codes blt maxcbl blc ->
  (* the code-length tree's lengths fit in three bits, which is what
     [ValidLengths cl 7] says about the tree the decoder will rebuild *)
  (forall r, 0 <= r < blcodes -> 0 <= t_len (ts_trees s TK_BL) (bl_order r) < 8) ->
  (* huffman-id's four, at each of the two trees *)
  LensOf blt cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  0 <= lcodes - 1 <= 285 ->
  (forall i, 0 <= t_len (ts_trees s TK_L) i) ->
  t_len (ts_trees s TK_L) (lcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  0 <= dcodes - 1 <= 285 ->
  (forall i, 0 <= t_len (ts_trees s TK_D) i) ->
  t_len (ts_trees s TK_D) (dcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= t_len (ts_trees s TK_D) i <= 15) ->
  cl_bits cl (send_tree_items (ts_trees s TK_L) (lcodes - 1)) = Some bitsL ->
  cl_bits cl (send_tree_items (ts_trees s TK_D) (dcodes - 1)) = Some bitsD ->
  bw_stream (send_all_trees lcodes dcodes blcodes s)
  = bw_stream (ts_bw s)
      ++ hdr_bits lcodes dcodes blcodes
      ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes (ts_trees s TK_BL)
      ++ bitsL ++ bitsD.
Proof.
  intros lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD
         Hwf Hl Hd Hc Hbc Hbl HBL8
         Hlens Hblc HV Hab Hmcbl
         HLmc HLnn HLg HL15 HDmc HDnn HDg HD15 HbL HbD.
  (* the range hypothesis, at the spelling the rewrite will produce *)
  assert (HBL8' : forall r, 0 <= r < blcodes ->
                  0 <= t_len (gen_codes blt maxcbl blc) (bl_order r) < 8)
    by (rewrite <- Hbl; exact HBL8).
  (* [cbv zeta] substitutes the six [let]s and NOTHING else -- no delta, so no
     fuelled definition is entered.  Then the three header sends are folded onto
     [hdr_send] by [change], which is a conversion and not a rewrite: the raw
     nesting and the folded name are convertible but not syntactically equal,
     and [rewrite] needs the latter. *)
  unfold send_all_trees. cbv zeta.
  change (bw_send_bits (blcodes - 4) 4
            (bw_send_bits (dcodes - 1) 5
              (bw_send_bits (lcodes - 257) 5 (ts_bw s))))
    with (hdr_send lcodes dcodes blcodes (ts_bw s)).
  rewrite Hbl.
  (* piece 1: the three counts *)
  destruct (header_stream lcodes dcodes blcodes (ts_bw s) Hwf Hl Hd Hc)
    as [Hhs Hhw].
  (* piece 2: the code-length vector *)
  destruct (sat_ranks_stream (Z.to_nat BL_CODES + 1) 0 blcodes
              (gen_codes blt maxcbl blc)
              (hdr_send lcodes dcodes blcodes (ts_bw s)) Hhw HBL8')
    as [Hss Hsw].
  (* piece 3: the literal/length tree *)
  destruct (send_tree_stream_at_any_writer (ts_trees s TK_L) (lcodes - 1)
              cl blt maxcbl blc bitsL
              (sat_ranks (Z.to_nat BL_CODES + 1) 0 blcodes
                 (gen_codes blt maxcbl blc)
                 (hdr_send lcodes dcodes blcodes (ts_bw s)))
              HLmc HLnn HLg HL15 Hlens Hblc HV Hab Hmcbl HbL Hsw)
    as [HLs HLw].
  (* piece 4: the distance tree *)
  destruct (send_tree_stream_at_any_writer (ts_trees s TK_D) (dcodes - 1)
              cl blt maxcbl blc bitsD
              (send_tree (ts_trees s TK_L) (lcodes - 1)
                 (gen_codes blt maxcbl blc)
                 (sat_ranks (Z.to_nat BL_CODES + 1) 0 blcodes
                    (gen_codes blt maxcbl blc)
                    (hdr_send lcodes dcodes blcodes (ts_bw s))))
              HDmc HDnn HDg HD15 Hlens Hblc HV Hab Hmcbl HbD HLw)
    as [HDs _].
  (* and the four pieces, outermost first *)
  rewrite HDs, HLs, Hss, Hhs.
  rewrite <- !app_assoc. reflexivity.
Qed.

Print Assumptions send_all_trees_stream.
