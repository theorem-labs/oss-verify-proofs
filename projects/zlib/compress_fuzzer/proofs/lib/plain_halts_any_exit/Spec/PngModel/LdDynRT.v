(** * LdDynRT — the DYNAMIC HEADER ROUND TRIP.  Item (v), less (v-6).

    OWNER: ld-seams.  Pin and shadowing check in LdDynSeam.v.

    [decode_dynamic_tables] applied to exactly the bits [send_all_trees] writes
    (LdDynEmit) returns exactly the two trees' own code-length vectors, with the
    rest of the stream untouched.

    WHAT WRITING THIS COMPOSITION FOUND, which is the reason to write it before
    the pieces feel finished: **two hypotheses nobody had named.** The decoder's
    last gate is
        [valid_lengths_b lit 15 && valid_lengths_b dst 15]
    i.e. both decoded vectors must be KRAFT-VALID at 15 bits. The range facts
    already in circulation ([0 <= t_len t i <= 15]) give the "every length fits"
    half and say NOTHING about the Kraft sum. So item (v-6)'s list grows from
    four hypotheses to six, and the two new ones are properties of [build_tree]'s
    output rather than of anything in the header path.

    They are taken as named hypotheses here. That is deliberate: a Kraft bound
    invented inside this file would be a fact about my convenience, and the
    consumer who has to discharge it is the one who can tell whether it holds.

    [rest] is universally quantified throughout: what follows a dynamic header is
    the compressed block itself, so stopping in the right place IS the property,
    and a decoder that swallowed its input would satisfy the theorem without it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam LdDynSplit LdDynHdr LdDynCl LdDynEmit.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The bit primitives stay sealed: [cbn] would turn [write_bits 5 v] into a
    five-element literal list and the next rewrite would no longer match.  Same
    reason ClStream.v seals them. *)
Local Opaque write_bits read_bits read_3bit_vals scatter_cl read_lengths.

(** ** Small facts *)

Lemma vl_true : forall l m, ValidLengths l m -> valid_lengths_b l m = true.
Proof.
  intros l m H. destruct (valid_lengths_reflect l m); [reflexivity|contradiction].
Qed.

Lemma firstn_app_exact : forall (l1 l2 : list nat), firstn (length l1) (l1 ++ l2) = l1.
Proof.
  intros l1 l2. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall (l1 l2 : list nat), skipn (length l1) (l1 ++ l2) = l2.
Proof.
  intros l1 l2. rewrite skipn_app, skipn_all, Nat.sub_diag.
  cbn [skipn]. reflexivity.
Qed.

Lemma tree_lens_length : forall t maxc,
  length (tree_lens t maxc) = Z.to_nat (maxc + 1).
Proof.
  intros t maxc. unfold tree_lens. rewrite length_map, length_seq. reflexivity.
Qed.

(** ** THE ROUND TRIP *)

Theorem dynamic_header_roundtrip :
  forall lcodes dcodes blcodes bl cl tL tD bitsL bitsD rest,
  (* RFC field ranges *)
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= 19 ->
  (* the code-length vector the decoder rebuilds IS the emitter's (LdDynCl) *)
  cl = scatter_cl (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes bl) ->
  (* the code-length tree is Kraft-valid at 7 -- huffman-id's hypothesis *)
  ValidLengths cl 7%nat ->
  (* ...and its lengths fit in the three-bit fields the header uses.  Same
     hypothesis LdDynEmit takes on the emitter side; it is a fact about the
     code-length tree, not a convenience. *)
  (forall r, 0 <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  (* the two trees' descriptions, as item streams over that code-length tree *)
  cl_bits cl (send_tree_items tL (lcodes - 1)) = Some bitsL ->
  cl_bits cl (send_tree_items tD (dcodes - 1)) = Some bitsD ->
  CLWf [] (send_tree_items tL (lcodes - 1)) ->
  CLWf [] (send_tree_items tD (dcodes - 1)) ->
  cl_lens (send_tree_items tL (lcodes - 1)) = tree_lens tL (lcodes - 1) ->
  cl_lens (send_tree_items tD (dcodes - 1)) = tree_lens tD (dcodes - 1) ->
  (* (v-6), the two hypotheses this composition discovered *)
  ValidLengths (tree_lens tL (lcodes - 1)) 15%nat ->
  ValidLengths (tree_lens tD (dcodes - 1)) 15%nat ->
  decode_dynamic_tables
    (hdr_bits lcodes dcodes blcodes
       ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes bl
       ++ bitsL ++ bitsD ++ rest)
  = Some (tree_lens tL (lcodes - 1), tree_lens tD (dcodes - 1), rest).
Proof.
  intros lcodes dcodes blcodes bl cl tL tD bitsL bitsD rest
         Hl Hd Hc Hbc Hcl HV7 HBL8 HbL HbD HwL HwD HlensL HlensD HVL HVD.
  destruct (header_decode lcodes dcodes blcodes
              (sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes bl
                 ++ bitsL ++ bitsD ++ rest) Hl Hd Hc) as [H1 [H2 H3]].
  unfold decode_dynamic_tables.
  rewrite H1. cbn [fst snd]. rewrite H2. cbn [fst snd]. rewrite H3.
  cbn [fst snd].
  (* the code-length vector *)
  assert (Hncl : (Z.to_nat (blcodes - 4) + 4)%nat
                 = length (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes bl)).
  { assert (Hb : 0 <= blcodes - 0 <= Z.of_nat (Z.to_nat BL_CODES + 1))
      by (unfold BL_CODES; cbn [Z.to_nat]; lia).
    pose proof (sat_vals_length (Z.to_nat BL_CODES + 1) 0 blcodes bl Hb) as HL.
    lia. }
  unfold read_cl_lengths.
  rewrite Hncl.
  rewrite (read_3bit_vals_sat (Z.to_nat BL_CODES + 1) 0 blcodes bl
             (bitsL ++ bitsD ++ rest))
    by (exact HBL8).
  cbn [fst snd].
  rewrite <- Hcl.
  (* the code-length tree passes its own gate *)
  rewrite (vl_true cl 7%nat HV7).
  (* one read_lengths across BOTH trees *)
  assert (Hnl : (Z.to_nat (lcodes - 257) + 257)%nat
                = length (cl_lens (send_tree_items tL (lcodes - 1))))
    by (rewrite HlensL, tree_lens_length; lia).
  assert (Hnd : (Z.to_nat (dcodes - 1) + 1)%nat
                = length (cl_lens (send_tree_items tD (dcodes - 1))))
    by (rewrite HlensD, tree_lens_length; lia).
  rewrite Hnl, Hnd.
  rewrite (read_lengths_spans_two_trees cl
             (send_tree_items tL (lcodes - 1)) (send_tree_items tD (dcodes - 1))
             bitsL bitsD rest HV7 HwL HwD HbL HbD).
  cbn [fst snd].
  (* split the concatenated vector back at nlit *)
  rewrite <- Hnl.
  rewrite HlensL, HlensD.
  assert (Hsplit : (Z.to_nat (lcodes - 257) + 257)%nat
                   = length (tree_lens tL (lcodes - 1)))
    by (rewrite tree_lens_length; lia).
  rewrite Hsplit, firstn_app_exact, skipn_app_exact.
  (* and both decoded vectors pass the final gate *)
  rewrite (vl_true _ _ HVL), (vl_true _ _ HVD). reflexivity.
Qed.

Print Assumptions dynamic_header_roundtrip.
