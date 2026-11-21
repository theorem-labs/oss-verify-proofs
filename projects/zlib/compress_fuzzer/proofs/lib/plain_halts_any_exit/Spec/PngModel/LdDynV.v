(** * LdDynV — ITEM (v) CLOSED, modulo an enumerated hypothesis surface.

    OWNER: ld-seams.  Pin and shadowing check in LdDynSeam.v.

    ONE statement in which the bits [send_all_trees] WRITES and the bits
    [decode_dynamic_tables] READS are the same syntactic object. Both halves
    were already proved (LdDynEmit, LdDynRT); the point of joining them here is
    that an interface is only checked when it is consumed, and two separately
    green theorems about "the header" can perfectly well disagree about what the
    header is.

    ** THE HYPOTHESIS SURFACE, enumerated because that is what is left of (v)

    Nothing below is discharged in this lane, and each line says whose it is:

      1. [ts_trees s TK_BL = gen_codes blt maxcbl blc]        build_bl_tree
      2. [LensOf blt cl], [BlcOf blc cl], [AbsentBeyond cl maxcbl],
         [ValidLengths cl 7], [length cl = 19]                build_bl_tree
      3. the BL lengths fit three bits, are nonneg, and are ZERO above
         [blcodes]                                            build_bl_tree /
                                                              bbl_scan (the zero
                                                              tail is proved in
                                                              LdDynCl; what is
                                                              owed is that
                                                              [blcodes] IS
                                                              [bbl_scan]'s + 1)
      4. each tree's 0xffff guard at [maxc+1] and lengths in 0..15
                                                              scan_tree/gen_bitlen
      5. [cl_bits cl (send_tree_items t maxc) = Some bits], twice
                                                              huffman-id flag this
                                                              as the ONE genuine
                                                              coverage obligation
      6. [ValidLengths (tree_lens t maxc) 15], twice           build_tree -- NEW,
                                                              found by writing
                                                              LdDynRT's decode gate

    Items 1-5 were known; item 6 is what this composition added. I am recording
    the surface rather than shrinking it: a hypothesis moved inside a definition
    to make a theorem read better is a hypothesis nobody will discharge. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam LdDynSplit LdDynHdr LdDynCl LdDynEmit LdDynRT.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Two length vectors of a tree, at equal length, are equal *)

Lemma lensof_det : forall t L1 L2,
  length L1 = length L2 -> LensOf t L1 -> LensOf t L2 -> L1 = L2.
Proof.
  intros t L1 L2 Hlen H1 H2.
  apply (nth_ext L1 L2 0%nat 0%nat); [exact Hlen|].
  intros n Hn. specialize (H1 n Hn). specialize (H2 n (eq_ind _ _ Hn _ Hlen)).
  lia.
Qed.

(** ** 2. The decoder's reconstructed vector IS [cl]

    LdDynCl proves the reconstruction is A length vector of the BL tree; the
    emitter's hypothesis says [cl] is one too. Determinism closes the gap, and
    [gen_codes_len] is what lets the two be compared at all — the tree in the
    header path carries codes, the tree in [LensOf] does not, and they share
    their length array. *)

Theorem cl_is_the_scattered_vector :
  forall blt maxcbl blc cl blcodes,
  0 <= blcodes <= 19 ->
  length cl = 19%nat ->
  LensOf blt cl ->
  (forall j, 0 <= j <= 18 -> 0 <= t_len blt (bl_order j)) ->
  (forall j, blcodes <= j <= 18 -> t_len blt (bl_order j) = 0) ->
  cl = scatter_cl (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes
                            (gen_codes blt maxcbl blc)).
Proof.
  intros blt maxcbl blc cl blcodes Hbc Hlen Hlens Hnn Htail.
  assert (Hfuel : blcodes <= Z.of_nat (Z.to_nat BL_CODES + 1))
    by (unfold BL_CODES; cbn [Z.to_nat]; lia).
  assert (Hnn' : forall j, 0 <= j <= 18 ->
                 0 <= t_len (gen_codes blt maxcbl blc) (bl_order j))
    by (intros j Hj; rewrite gen_codes_len; apply Hnn, Hj).
  assert (Htail' : forall j, blcodes <= j <= 18 ->
                   t_len (gen_codes blt maxcbl blc) (bl_order j) = 0)
    by (intros j Hj; rewrite gen_codes_len; apply Htail, Hj).
  assert (Hlens' : LensOf (gen_codes blt maxcbl blc) cl)
    by (intros k Hk; rewrite gen_codes_len; apply Hlens, Hk).
  apply (lensof_det (gen_codes blt maxcbl blc)).
  - rewrite Hlen, scatter_cl_length. reflexivity.
  - exact Hlens'.
  - exact (scattered_sat_vals_is_the_tree (Z.to_nat BL_CODES + 1)
             (gen_codes blt maxcbl blc) blcodes Hbc Hfuel Hnn' Htail').
Qed.

(** ** 3. ITEM (v): the emitted bits and the decoded bits are ONE object *)

Theorem dynamic_header_on_the_wire :
  forall lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD blockbits,
  bw_wf (ts_bw s) ->
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= 19 ->
  (* 1, 2 *)
  ts_trees s TK_BL = gen_codes blt maxcbl blc ->
  length cl = 19%nat ->
  LensOf blt cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  (* 3 *)
  (forall r, 0 <= r < blcodes -> 0 <= t_len (ts_trees s TK_BL) (bl_order r) < 8) ->
  (forall j, 0 <= j <= 18 -> 0 <= t_len blt (bl_order j)) ->
  (forall j, blcodes <= j <= 18 -> t_len blt (bl_order j) = 0) ->
  (* 4 *)
  0 <= lcodes - 1 <= 285 ->
  (forall i, 0 <= t_len (ts_trees s TK_L) i) ->
  t_len (ts_trees s TK_L) (lcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  0 <= dcodes - 1 <= 285 ->
  (forall i, 0 <= t_len (ts_trees s TK_D) i) ->
  t_len (ts_trees s TK_D) (dcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= t_len (ts_trees s TK_D) i <= 15) ->
  (* 5 *)
  cl_bits cl (send_tree_items (ts_trees s TK_L) (lcodes - 1)) = Some bitsL ->
  cl_bits cl (send_tree_items (ts_trees s TK_D) (dcodes - 1)) = Some bitsD ->
  (* 6 *)
  ValidLengths (tree_lens (ts_trees s TK_L) (lcodes - 1)) 15%nat ->
  ValidLengths (tree_lens (ts_trees s TK_D) (dcodes - 1)) 15%nat ->
  bw_stream (send_all_trees lcodes dcodes blcodes s)
    = bw_stream (ts_bw s)
        ++ hdr_bits lcodes dcodes blcodes
        ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes (ts_trees s TK_BL)
        ++ bitsL ++ bitsD
  /\ decode_dynamic_tables
       (hdr_bits lcodes dcodes blcodes
          ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes (ts_trees s TK_BL)
          ++ bitsL ++ bitsD ++ blockbits)
     = Some (tree_lens (ts_trees s TK_L) (lcodes - 1),
             tree_lens (ts_trees s TK_D) (dcodes - 1),
             blockbits).
Proof.
  intros lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD blockbits
         Hwf Hl Hd Hc Hbc Hbl Hcllen Hlens Hblc HV7 Hab Hmcbl
         HBL8 Hnn0 Htail
         HLmc HLnn HLg HL15 HDmc HDnn HDg HD15 HbL HbD HVL HVD.
  split.
  - exact (send_all_trees_stream lcodes dcodes blcodes s blt maxcbl blc cl
             bitsL bitsD Hwf Hl Hd Hc Hbc Hbl HBL8 Hlens Hblc HV7 Hab Hmcbl
             HLmc HLnn HLg HL15 HDmc HDnn HDg HD15 HbL HbD).
  - (* the code-length vector agreement, at the spelling the header uses *)
    assert (Hcl : cl = scatter_cl (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes
                                     (ts_trees s TK_BL))).
    { rewrite Hbl.
      exact (cl_is_the_scattered_vector blt maxcbl blc cl blcodes
               Hbc Hcllen Hlens Hnn0 Htail). }
    exact (dynamic_header_roundtrip lcodes dcodes blcodes (ts_trees s TK_BL) cl
             (ts_trees s TK_L) (ts_trees s TK_D) bitsL bitsD blockbits
             Hl Hd Hc Hbc Hcl HV7 HBL8 HbL HbD
             (send_tree_items_wf (ts_trees s TK_L) (lcodes - 1) HLmc HLg HL15)
             (send_tree_items_wf (ts_trees s TK_D) (dcodes - 1) HDmc HDg HD15)
             (send_tree_items_lens (ts_trees s TK_L) (lcodes - 1) HLmc HLg HL15)
             (send_tree_items_lens (ts_trees s TK_D) (dcodes - 1) HDmc HDg HD15)
             HVL HVD).
Qed.

Print Assumptions lensof_det.
Print Assumptions cl_is_the_scattered_vector.
Print Assumptions dynamic_header_on_the_wire.
