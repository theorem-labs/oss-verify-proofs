(** * ZRStrictHdr — the dynamic header round trip, STRICT twin.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-21; strict-freeze
    round 3, pin Gap7Strict ).  GAP7 strict supply, stage 2/W1.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [LdDynRT.dynamic_header_roundtrip] proves the LAX parse of the bits
    [send_all_trees] writes.  [decode_dynamic_tables_strict] is the lax
    text plus the machine's builder-accept guards (and two length
    bounds), so its round trip is the SAME composition of the exported
    segment lemmas with the guard booleans rewritten true at the two
    gate sites.  The three [build_accepts_b] facts arrive as premises —
    their discharge (kraft facts + the EnoughFits residue through g1's
    characterization bridge) happens at the walk level, not here.

    Mirrors LdDynRT verbatim where the texts coincide, including the
    opacity seal on the bit primitives. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  LdDynSeam LdDynSplit LdDynHdr LdDynCl LdDynEmit LdDynRT LdDynV Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Same seal as LdDynRT: [cbn] must not unfold the bit primitives. *)
Local Opaque write_bits read_bits read_3bit_vals scatter_cl read_lengths.

(** ** The round trip, strict *)

Theorem dynamic_header_roundtrip_strict :
  forall lcodes dcodes blcodes bl cl tL tD bitsL bitsD rest,
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= 19 ->
  cl = scatter_cl (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes bl) ->
  ValidLengths cl 7%nat ->
  (forall r, 0 <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  cl_bits cl (send_tree_items tL (lcodes - 1)) = Some bitsL ->
  cl_bits cl (send_tree_items tD (dcodes - 1)) = Some bitsD ->
  CLWf [] (send_tree_items tL (lcodes - 1)) ->
  CLWf [] (send_tree_items tD (dcodes - 1)) ->
  cl_lens (send_tree_items tL (lcodes - 1)) = tree_lens tL (lcodes - 1) ->
  cl_lens (send_tree_items tD (dcodes - 1)) = tree_lens tD (dcodes - 1) ->
  ValidLengths (tree_lens tL (lcodes - 1)) 15%nat ->
  ValidLengths (tree_lens tD (dcodes - 1)) 15%nat ->
  (* the strict guards: the machine's builder accepts all three lists *)
  build_accepts_b CT_CODES cl 7 = true ->
  build_accepts_b CT_LENS (tree_lens tL (lcodes - 1)) 9 = true ->
  build_accepts_b CT_DISTS (tree_lens tD (dcodes - 1)) 6 = true ->
  lcodes <= 286 ->
  dcodes <= 30 ->
  decode_dynamic_tables_strict
    (hdr_bits lcodes dcodes blcodes
       ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes bl
       ++ bitsL ++ bitsD ++ rest)
  = Some (tree_lens tL (lcodes - 1), tree_lens tD (dcodes - 1), rest).
Proof.
  intros lcodes dcodes blcodes bl cl tL tD bitsL bitsD rest
         Hl Hd Hc Hbc Hcl HV7 HBL8 HbL HbD HwL HwD HlensL HlensD HVL HVD
         HaCL HaL HaD Hlc286 Hdc30.
  destruct (header_decode lcodes dcodes blcodes
              (sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes bl
                 ++ bitsL ++ bitsD ++ rest) Hl Hd Hc) as [H1 [H2 H3]].
  unfold decode_dynamic_tables_strict.
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
  (* both gate booleans at the CL site *)
  rewrite (vl_true cl 7%nat HV7), HaCL.
  cbn [andb].
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
  (* the six-way final gate: lax validity, the strict bounds, the
     builder accepts *)
  assert (E286 : (length (tree_lens tL (lcodes - 1)) <=? 286)%nat = true).
  { apply Nat.leb_le. rewrite tree_lens_length. lia. }
  assert (E30 : (length (tree_lens tD (dcodes - 1)) <=? 30)%nat = true).
  { apply Nat.leb_le. rewrite tree_lens_length. lia. }
  rewrite (vl_true _ _ HVL), (vl_true _ _ HVD), E286, E30, HaL, HaD.
  reflexivity.
Qed.

(** ** The wire wrapper, strict (mirror of
    [LdDynV.dynamic_header_on_the_wire]'s decode half; the stream half
    is unchanged and stays with the lax wrapper) *)

Theorem dynamic_header_decode_strict :
  forall lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD blockbits,
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= 19 ->
  ts_trees s TK_BL = gen_codes blt maxcbl blc ->
  length cl = 19%nat ->
  LensOf blt cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  (forall r, 0 <= r < blcodes ->
   0 <= t_len (ts_trees s TK_BL) (bl_order r) < 8) ->
  (forall j, 0 <= j <= 18 -> 0 <= t_len blt (bl_order j)) ->
  (forall j, blcodes <= j <= 18 -> t_len blt (bl_order j) = 0) ->
  0 <= lcodes - 1 <= 285 ->
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  0 <= dcodes - 1 <= 285 ->
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= t_len (ts_trees s TK_D) i <= 15) ->
  cl_bits cl (send_tree_items (ts_trees s TK_L) (lcodes - 1)) = Some bitsL ->
  cl_bits cl (send_tree_items (ts_trees s TK_D) (dcodes - 1)) = Some bitsD ->
  ValidLengths (tree_lens (ts_trees s TK_L) (lcodes - 1)) 15%nat ->
  ValidLengths (tree_lens (ts_trees s TK_D) (dcodes - 1)) 15%nat ->
  (forall i, 0 <= t_len (ts_trees s TK_L) i) ->
  t_len (ts_trees s TK_L) (lcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= t_len (ts_trees s TK_D) i) ->
  t_len (ts_trees s TK_D) (dcodes - 1 + 1) = 65535 ->
  build_accepts_b CT_CODES cl 7 = true ->
  build_accepts_b CT_LENS (tree_lens (ts_trees s TK_L) (lcodes - 1)) 9
    = true ->
  build_accepts_b CT_DISTS (tree_lens (ts_trees s TK_D) (dcodes - 1)) 6
    = true ->
  lcodes <= 286 ->
  dcodes <= 30 ->
  decode_dynamic_tables_strict
    (hdr_bits lcodes dcodes blcodes
       ++ sat_bits (Z.to_nat BL_CODES + 1) 0 blcodes (ts_trees s TK_BL)
       ++ bitsL ++ bitsD ++ blockbits)
  = Some (tree_lens (ts_trees s TK_L) (lcodes - 1),
          tree_lens (ts_trees s TK_D) (dcodes - 1),
          blockbits).
Proof.
  intros lcodes dcodes blcodes s blt maxcbl blc cl bitsL bitsD blockbits
         Hl Hd Hc Hbc Hbl Hcllen Hlens Hblc HV7 Hab Hmcbl
         HBL8 Hnn0 Htail HLmc HL15 HDmc HD15 HbL HbD HVL HVD
         HLnn HLg HDnn HDg
         HaCL HaL HaD Hlc286 Hdc30.
  assert (Hcl : cl = scatter_cl (sat_vals (Z.to_nat BL_CODES + 1) 0 blcodes
                                   (ts_trees s TK_BL))).
  { rewrite Hbl.
    exact (cl_is_the_scattered_vector blt maxcbl blc cl blcodes
             Hbc Hcllen Hlens Hnn0 Htail). }
  exact (dynamic_header_roundtrip_strict lcodes dcodes blcodes
           (ts_trees s TK_BL) cl
           (ts_trees s TK_L) (ts_trees s TK_D) bitsL bitsD blockbits
           Hl Hd Hc Hbc Hcl HV7 HBL8
           HbL HbD
           (send_tree_items_wf (ts_trees s TK_L) (lcodes - 1) HLmc HLg HL15)
           (send_tree_items_wf (ts_trees s TK_D) (dcodes - 1) HDmc HDg HD15)
           (send_tree_items_lens (ts_trees s TK_L) (lcodes - 1) HLmc HLg HL15)
           (send_tree_items_lens (ts_trees s TK_D) (dcodes - 1) HDmc HDg HD15)
           HVL HVD HaCL HaL HaD Hlc286 Hdc30).
Qed.

Print Assumptions dynamic_header_roundtrip_strict.
Print Assumptions dynamic_header_decode_strict.
