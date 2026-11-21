(** * CoverEnd — the END-TO-END composition: zlib's own two scans, through
      [build_bl_tree]'s tree, out to [send_tree]'s bytes and back.

    OWNER: huffman-id.

    WHY THIS FILE EXISTS.  CoverChain.v and ScanBase.v discharge
    [send_tree_roundtrip]'s coverage hypothesis, and I reported that to the
    consuming lane.  A discharged hypothesis is not the same thing as a USABLE
    one: what makes it usable is that the OTHER hypotheses of the consumer are
    satisfiable at the same instantiation.  The lesson I had just written down
    was "write the composition", so this file writes it rather than asserting it.

    WHAT IT FOUND: the plug fits, and two of the consumer's hypotheses come free
    at this instantiation rather than being owed:

      forall i, 0 <= t_len t i     free from [DlNn tL] via [BuildChain.dl_setlen],
                                   because the tree sent is [scan_tree]'s OUTPUT
                                   and every write into the length array is a u16
      t_len t (maxc + 1) = 65535   free BY CONSTRUCTION -- [scan_tree] performs
                                   that store itself ([Trees.v:733]) and returns
                                   the guarded tree, so the sentinel hypothesis is
                                   discharged by the call-site SHAPE

    That second one is worth stating plainly because it was carried as an
    assumption for a long time on both sides of the seam: nobody has to prove the
    0xffff guard, because the function that needs it writes it.

    WHAT REMAINS, and none of it is mine: the heap facts ([bt_init]/[bt_force2]
    results), the representation facts about [cl] ([LensOf], [BlcOf],
    [ValidLengths], [AbsentBeyond], and the length bound that is [LensOf]'s
    anti-vacuity clause), and SEAM D -- that the caller SENDS at the [maxc] it
    SCANNED at.  SEAM D is visible here as the fact that [maxcL] appears in both
    the [scan_tree] and the [send_tree] position of one theorem; a caller whose
    [lcodes - 1] differs from its [ts_maxcode s TK_L] cannot instantiate it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens SendGoWf
  HuffCover ScanCount BuildChain BtTerm SendTreeRT CoverChain ScanBase.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The two hypotheses that come free on a scanned tree.  Stated separately so
    the freeness is checkable rather than buried in the capstone's proof. *)
Lemma scanned_tree_dlnn : forall t maxc bl,
  DlNn t -> forall i, 0 <= t_len (fst (scan_tree t maxc bl)) i.
Proof.
  intros t maxc bl Hnn i. unfold scan_tree. cbn [fst]. apply dl_setlen. exact Hnn.
Qed.

Lemma scanned_tree_guard : forall t maxc bl,
  t_len (fst (scan_tree t maxc bl)) (maxc + 1) = 65535.
Proof.
  intros t maxc bl. unfold scan_tree. cbn [fst].
  rewrite t_len_setlen_same. reflexivity.
Qed.

Lemma scanned_tree_lens15 : forall t maxc bl,
  0 <= maxc ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  forall i, 0 <= i <= maxc -> 0 <= t_len (fst (scan_tree t maxc bl)) i <= 15.
Proof.
  intros t maxc bl Hmc H15 i Hi. unfold scan_tree. cbn [fst].
  rewrite t_len_setlen_other by lia. apply H15. lia.
Qed.

(** ** THE END-TO-END STATEMENT

    Run zlib's [build_bl_tree] scans over the literal and distance trees, build
    the code-length tree, emit the literal tree's code lengths with [send_tree],
    and [DeflateSpec.read_lengths] -- the model of inflate's CODELENS phase --
    reads back exactly those code lengths, with the rest of the stream untouched.

    The code-length tree [gen_codes] runs on is THE SAME TERM as the one coverage
    is derived from: [ts_trees (build_tree TK_BL st2) TK_BL].  Writing it once
    rather than as two hypotheses is the point -- a version with a separate [blt]
    and a [LensOf blt cl] hypothesis would let the coverage argument and the
    emission argument silently be about different trees. *)
Theorem send_tree_roundtrip_from_scan :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         maxcbl blc rest
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  (* the two trees zlib is about to describe *)
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  DlNn tL ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (* [init_block] leaves the bl_tree's frequencies at zero ([Trees.v:347]) *)
  (forall s', t_freq (ts_trees st TK_BL) s' = 0) ->
  (* [build_bl_tree]'s two scans, into the SAME table ([Trees.v:806-810]) *)
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  (* the code-length tree's representation as a list, and its codes *)
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  read_lengths cl (length (tree_lens (fst p1) maxcL))
    (bw_stream (send_tree (fst p1) maxcL
        (gen_codes (ts_trees (build_tree TK_BL st2) TK_BL) maxcbl blc) bw_init)
     ++ rest)
  = Some (tree_lens (fst p1) maxcL, rest).
Proof.
  intros st st2 cl tL maxcL tD maxcD p1 p2 maxcbl blc rest
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         HmcL HmcD HnnL H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn2 Hinit Hforce
         HL Hlen Hblc HV Hab Hmcbl.
  (* coverage first, while [p1]/[p2] are still the variables the chain expects *)
  destruct (cover_both_streams_final st st2 cl tL maxcL tD maxcD p1 p2
              t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              HmcL HmcD H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn2 Hinit Hforce HL Hlen)
    as [[bits Hbits] _].
  (* now substitute, so no conversion-based tactic has to decide whether
     [send_tree_items (fst p1) maxcL] and its expansion are convertible -- that
     decision unfolds [send_items] at literal fuel 289 over a symbolic tree. *)
  subst p2. subst p1.
  apply (send_tree_roundtrip (fst (scan_tree tL maxcL (ts_trees st TK_BL))) maxcL
           cl (ts_trees (build_tree TK_BL st2) TK_BL) maxcbl blc bits rest).
  - exact HmcL.
  - apply scanned_tree_dlnn. exact HnnL.
  - apply scanned_tree_guard.
  - apply scanned_tree_lens15; [lia | exact H15L].
  - exact HL.
  - exact Hblc.
  - exact HV.
  - exact Hab.
  - exact Hmcbl.
  - exact Hbits.
Qed.

Print Assumptions scanned_tree_dlnn.
Print Assumptions scanned_tree_guard.
Print Assumptions scanned_tree_lens15.
Print Assumptions send_tree_roundtrip_from_scan.
