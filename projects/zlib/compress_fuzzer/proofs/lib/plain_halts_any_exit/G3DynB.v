(** * G3DynB — the DYNAMIC arm of one emitted block, assembled.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3 dynamic arm,
    part 2: G3DynA's per-build packs + LdDynV's wire theorem + CbFold's
    [compress_block_decodes], discharging exactly the [dyn_bw] seam
    hypothesis G3Block/G3Event consume.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The interim premises (R1/R2/R3, an earlier development run re-exports pending) ride
    through from G3DynA; everything else here is Qed-closed. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import BtFrame.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream Huff DeflateSpec Trees CbEmit CbFold
  HuffGenCodes KraftDlNn ClStream SendItems SendGo SendGoLens HuffCover
  CoverChain ScanBase LdDynCl LdDynHdr LdDynRT LdDynEmit LdDynSeam LdDynV DynCodes
  DynLitCoded BuildChain BuildTree BtSized BtTerm BtCensus4 BtCensus5
  BtItem6 BtItem6b BtClPack BtBlSide BtLive Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import G3DynA SwTally
  Gap7Strict ZRStrictHdr ZRStrictSupply.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Token-occurrence positivity for the frequency ties *)

Lemma count_L_in_lit : forall toks b,
  In (TLit b) toks -> 1 <= count_L b toks.
Proof.
  induction toks as [|t r IH]; intros b Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - cbn [count_L]. rewrite Z.eqb_refl.
    pose proof (count_L_nonneg b r). lia.
  - destruct t as [c|len dist]; cbn [count_L];
      pose proof (IH b Hin);
      destruct (Z.eqb _ b); lia.
Qed.

Lemma count_L_in_match : forall toks len dist,
  In (TMatch len dist) toks ->
  1 <= count_L (length_code (len - 3) + LITERALS + 1) toks.
Proof.
  induction toks as [|t r IH]; intros len dist Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - cbn [count_L]. rewrite Z.eqb_refl.
    pose proof (count_L_nonneg (length_code (len - 3) + LITERALS + 1) r).
    lia.
  - destruct t as [c|len' dist']; cbn [count_L];
      pose proof (IH len dist Hin);
      destruct (Z.eqb _ _); lia.
Qed.

Lemma count_D_in_match : forall toks len dist,
  In (TMatch len dist) toks ->
  1 <= count_D (d_code (dist - 1)) toks.
Proof.
  induction toks as [|t r IH]; intros len dist Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - cbn [count_D]. rewrite Z.eqb_refl.
    pose proof (count_D_nonneg (d_code (dist - 1)) r). lia.
  - destruct t as [c|len' dist']; cbn [count_D];
      pose proof (IH len dist Hin);
      try (destruct (Z.eqb _ _)); lia.
Qed.

(** ** 2. Transfers across the sentinel write *)

Lemma tree_lens_ext : forall t t' maxc,
  (forall i, 0 <= i <= maxc -> t_len t' i = t_len t i) ->
  tree_lens t' maxc = tree_lens t maxc.
Proof.
  intros t t' maxc He.
  unfold tree_lens.
  apply map_ext_in.
  intros a Ha. apply in_seq in Ha.
  f_equal. apply He. lia.
Qed.

Lemma tree_codes_upto_ext : forall t t' L n,
  (forall i, (i < n)%nat -> t_len t' (Z.of_nat i) = t_len t (Z.of_nat i)) ->
  (forall i, (i < n)%nat -> t_code t' (Z.of_nat i) = t_code t (Z.of_nat i)) ->
  tree_codes_upto t L n -> tree_codes_upto t' L n.
Proof.
  intros t t' L n Hl Hc H i cw Hi Hcf.
  destruct (H i cw Hi Hcf) as (H1 & H2 & H3).
  rewrite (Hl i Hi), (Hc i Hi).
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.

(** ** 3. [sat_ranks] keeps the writer well-formed *)

Lemma sat_ranks_wf : forall fuel rank blcodes bl b,
  (forall r, rank <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  bw_wf b ->
  bw_wf (sat_ranks fuel rank blcodes bl b).
Proof.
  induction fuel as [|f IH]; intros rank blcodes bl b H8 Hwf;
    cbn [sat_ranks].
  - exact Hwf.
  - destruct (Z.leb_spec blcodes rank) as [Hle|Hgt]; [exact Hwf|].
    apply IH.
    + intros r Hr. apply H8. lia.
    + destruct (bw_send_bits_stream (t_len bl (bl_order rank)) 3 b Hwf
                  ltac:(unfold Buf_size; lia)
                  ltac:(destruct (H8 rank ltac:(lia));
                        change (2 ^ 3) with 8; lia))
        as [_ W]. exact W.
Qed.

(** ** 4. THE SEAM: [dyn_bw] emits one decodable BTYPE-2 block *)

Theorem dyn_arm_dec_blk : forall ts0 toks last acc out mbi s2,
  (mbi, s2) = build_bl_tree (build_tree TK_D (build_tree TK_L ts0)) ->
  bw_wf (ts_bw ts0) ->
  last = 0 \/ last = 1 ->
  BufToks (ts_symbuf ts0) 0 (ts_symnext ts0) toks ->
  FreqInv toks ts0 ->
  cEnc toks ->
  resolve acc toks = Some out ->
  (* entry facts (walk-threaded) *)
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts0 b = 0) ->
  (forall i, 0 <= i < 19 -> t_freq (ts_trees ts0 TK_BL) i = 0) ->
  (forall i, 0 <= t_len (ts_trees ts0 TK_BL) i) ->
  (* interim premises, pending an earlier development run's R1/R2/R3 re-exports *)
  (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree TK_L ts0) b = 0) ->
  (forall i, 0 <= t_len (ts_trees (build_tree TK_L ts0) TK_L) i) ->
  (forall b, b < 0 \/ 15 < b ->
   ts_blcount (build_tree TK_D (build_tree TK_L ts0)) b = 0) ->
  (forall i, 0 <= t_len
     (ts_trees (build_tree TK_D (build_tree TK_L ts0)) TK_D) i) ->
  1 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts0)) TK_D ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s2 b = 0) ->
  (forall i, 0 <= t_len (ts_trees s2 TK_BL) i) ->
  exists delta,
    bw_stream (dyn_bw last mbi s2) = bw_stream (ts_bw ts0) ++ delta
    /\ bw_wf (dyn_bw last mbi s2)
    /\ (forall suffix,
         dec_blk (delta ++ suffix) acc = Some (Z.eqb last 1, out, suffix))
    /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
        forall suffix,
         dec_blk_strict (delta ++ suffix) acc
         = Some (Z.eqb last 1, out, suffix)).
Proof.
  intros ts0 toks last acc out mbi s2
         Epair Hwf Hl Hbuf Hfrq Henc Hres
         Hblc0 Hblf0 Hbln0
         HR1L HR2L HR1D HR2D HR3D HR1B HR2B.
  destruct Hfrq as [HfL HfD].
  set (s1L := build_tree TK_L ts0) in *.
  set (s1D := build_tree TK_D s1L) in *.
  assert (Embi : mbi = fst (build_bl_tree s1D))
    by (rewrite <- Epair; reflexivity).
  assert (Es2 : s2 = snd (build_bl_tree s1D))
    by (rewrite <- Epair; reflexivity).
  (* END_BLOCK is live at the flush state *)
  assert (Heob : t_freq (ts_trees ts0 TK_L) END_BLOCK <> 0).
  { rewrite (HfL END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)).
    rewrite Z.eqb_refl.
    pose proof (count_L_nonneg END_BLOCK toks). lia. }
  (* ---- the three builds ---- *)
  destruct (inst_L ts0 Hblc0 Heob HR1L HR2L)
    as (LmcR & LVL & Lrng & Leob & Llive & Lcodes).
  cbv zeta in LmcR, LVL, Lrng, Leob, Llive, Lcodes.
  fold s1L in LmcR, LVL, Lrng, Leob, Llive, Lcodes.
  destruct (inst_D s1L HR1L HR1D HR2D HR3D)
    as (DmcR & DVL & Drng & Dlive & Dcodes).
  cbv zeta in DmcR, DVL, Drng, Dlive, Dcodes.
  fold s1D in DmcR, DVL, Drng, Dlive, Dcodes.
  (* frames *)
  assert (FL_D : ts_trees s1D TK_L = ts_trees s1L TK_L)
    by (apply build_tree_tree_other; unfold TK_L, TK_D; lia).
  assert (FLmc_D : ts_maxcode s1D TK_L = ts_maxcode s1L TK_L)
    by (apply build_tree_maxcode_other; unfold TK_L, TK_D; lia).
  assert (FBL_L : ts_trees s1L TK_BL = ts_trees ts0 TK_BL)
    by (apply build_tree_tree_other; unfold TK_L, TK_BL; lia).
  assert (FBL_D : ts_trees s1D TK_BL = ts_trees s1L TK_BL)
    by (apply build_tree_tree_other; unfold TK_D, TK_BL; lia).
  assert (FD_L : ts_trees s1L TK_D = ts_trees ts0 TK_D)
    by (apply build_tree_tree_other; unfold TK_L, TK_D; lia).
  (* ---- the BL build + scans ---- *)
  destruct (inst_BL s1D HR1D
              ltac:(intros i Hi; rewrite FBL_D, FBL_L;
                    exact (Hblf0 i Hi))
              ltac:(intro i; rewrite FBL_D, FBL_L; apply Hbln0)
              ltac:(rewrite FLmc_D; exact LmcR)
              DmcR
              ltac:(intro i; rewrite FL_D; apply HR2L)
              HR2D
              ltac:(intros i Hi; rewrite FL_D; apply Lrng;
                    rewrite FLmc_D in Hi; exact Hi)
              ltac:(intros i Hi; apply Drng; exact Hi)
              ltac:(rewrite FL_D; exact Leob)
              ltac:(rewrite <- Es2; exact HR1B)
              ltac:(rewrite <- Es2; exact HR2B))
    as (Bmbi & Bcllen & BV7 & Bfits & Btail & Bpack & BbitsL & BbitsD
        & BgL & BgD & BmL & BmD & BLnn & BLrng & BDnn & BDrng
        & BLcode & BLlen & BDcode & BDlen & Bsb & Bsn & Bbw).
  cbv zeta in Bmbi, Bcllen, BV7, Bfits, Btail, Bpack, BbitsL, BbitsD,
    BgL, BgD, BmL, BmD, BLnn, BLrng, BDnn, BDrng,
    BLcode, BLlen, BDcode, BDlen, Bsb, Bsn, Bbw.
  rewrite <- Es2 in *.
  rewrite <- Embi in *.
  destruct Bpack as (blt0 & maxcbl & blc & Etree & PLens & PBlc & PAb
                     & Pmcbl).
  (* the whole-state frames back to ts0 *)
  destruct (build_tree_frame TK_L ts0) as (FsbL & FsnL & FbwL & _).
  destruct (build_tree_frame TK_D s1L) as (FsbD & FsnD & FbwD & _).
  fold s1L in FsbL, FsnL, FbwL.
  fold s1D in FsbD, FsnD, FbwD.
  assert (Ebw2 : ts_bw s2 = ts_bw ts0) by (rewrite Bbw, FbwD, FbwL;
    reflexivity).
  assert (Esb2 : ts_symbuf s2 = ts_symbuf ts0) by (rewrite Bsb, FsbD, FsbL;
    reflexivity).
  assert (Esn2 : ts_symnext s2 = ts_symnext ts0) by (rewrite Bsn, FsnD,
    FsnL; reflexivity).
  set (mcL := ts_maxcode s1L TK_L) in *.
  set (mcD := ts_maxcode s1D TK_D) in *.
  destruct BbitsL as (bitsL & HbL0).
  destruct BbitsD as (bitsD & HbD0).
  set (cl := tree_lens (ts_trees s2 TK_BL) 18) in *.
  (* the header writer *)
  set (b0 := bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2)).
  destruct (bw_send_bits_stream (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2)
              ltac:(rewrite Ebw2; exact Hwf)
              ltac:(unfold Buf_size; lia)
              ltac:(destruct Hl as [->| ->];
                    [ change (Z.shiftl DYN_TREES 1 + 0) with 4
                    | change (Z.shiftl DYN_TREES 1 + 1) with 5 ];
                    change (2 ^ 3) with 8; lia))
    as [S0 W0].
  fold b0 in S0, W0.
  (* normalise the two send maxcodes *)
  assert (EmcS : ts_maxcode s2 TK_L + 1 - 1 = mcL)
    by (rewrite BmL, FLmc_D; lia).
  assert (EmcSD : ts_maxcode s2 TK_D + 1 - 1 = mcD)
    by (rewrite BmD; lia).
  (* pointwise transfer: the guarded trees agree with the built ones on
     the coding window *)
  assert (TLen : forall i, i <= mcL ->
            t_len (ts_trees s2 TK_L) i = t_len (ts_trees s1L TK_L) i).
  { intros i Hi. rewrite <- FL_D. apply BLlen.
    rewrite FLmc_D. lia. }
  assert (TCode : forall i,
            t_code (ts_trees s2 TK_L) i = t_code (ts_trees s1L TK_L) i).
  { intro i. rewrite <- FL_D. apply BLcode. }
  assert (TLenD : forall i, i <= mcD ->
            t_len (ts_trees s2 TK_D) i = t_len (ts_trees s1D TK_D) i).
  { intros i Hi. apply BDlen. lia. }
  assert (TCodeD : forall i,
            t_code (ts_trees s2 TK_D) i = t_code (ts_trees s1D TK_D) i).
  { intro i. apply BDcode. }
  assert (EllL : tree_lens (ts_trees s2 TK_L) mcL
                 = tree_lens (ts_trees s1L TK_L) mcL)
    by (apply tree_lens_ext; intros i Hi; apply TLen; lia).
  assert (EllD : tree_lens (ts_trees s2 TK_D) mcD
                 = tree_lens (ts_trees s1D TK_D) mcD)
    by (apply tree_lens_ext; intros i Hi; apply TLenD; lia).
  (* item 6 at the send trees *)
  assert (HVL' : ValidLengths (tree_lens (ts_trees s2 TK_L) mcL) 15%nat)
    by (rewrite EllL; exact LVL).
  assert (HVD' : ValidLengths (tree_lens (ts_trees s2 TK_D) mcD) 15%nat)
    by (rewrite EllD; exact DVL).
  (* the pre-codes BL facts, transferred through gen_codes *)
  assert (Tblt0 : forall x, t_len blt0 x = t_len (ts_trees s2 TK_BL) x).
  { intro x. rewrite Etree, gen_codes_len. reflexivity. }
  (* ---- the wire, for every block payload ---- *)
  assert (Hwire : forall blockbits,
      bw_stream (send_all_trees (ts_maxcode s2 TK_L + 1)
                   (ts_maxcode s2 TK_D + 1) (mbi + 1) (set_bw b0 s2))
        = bw_stream b0
            ++ hdr_bits (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
                 (mbi + 1)
            ++ sat_bits (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                 (ts_trees s2 TK_BL)
            ++ bitsL ++ bitsD
      /\ decode_dynamic_tables
           (hdr_bits (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
              (mbi + 1)
              ++ sat_bits (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                   (ts_trees s2 TK_BL)
              ++ bitsL ++ bitsD ++ blockbits)
         = Some (tree_lens (ts_trees s2 TK_L) mcL,
                 tree_lens (ts_trees s2 TK_D) mcD,
                 blockbits)).
  { intro blockbits.
    pose proof (dynamic_header_on_the_wire
                  (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
                  (mbi + 1) (set_bw b0 s2) blt0 maxcbl blc cl
                  bitsL bitsD blockbits
                  W0
                  ltac:(rewrite BmL, FLmc_D; lia)
                  ltac:(rewrite BmD; lia)
                  ltac:(lia) ltac:(lia)
                  Etree Bcllen PLens PBlc BV7 PAb Pmcbl
                  ltac:(intros r Hr; apply Bfits; lia)
                  ltac:(intros j Hj; rewrite Tblt0; apply HR2B)
                  ltac:(intros j Hj; rewrite Tblt0; apply Btail; lia)
                  ltac:(rewrite EmcS; rewrite BmL, FLmc_D in *; lia)
                  BLnn
                  ltac:(replace (ts_maxcode s2 TK_L + 1 - 1 + 1)
                          with (ts_maxcode s1D TK_L + 1)
                          by (rewrite BmL; lia);
                        exact BgL)
                  ltac:(intros i Hi; apply BLrng;
                        rewrite <- FLmc_D in EmcS; lia)
                  ltac:(rewrite EmcSD; rewrite BmD in *; lia)
                  BDnn
                  ltac:(replace (ts_maxcode s2 TK_D + 1 - 1 + 1)
                          with (mcD + 1) by lia;
                        exact BgD)
                  ltac:(intros i Hi; apply BDrng; lia)
                  ltac:(replace (ts_maxcode s2 TK_L + 1 - 1)
                          with (ts_maxcode s1D TK_L) by
                          (rewrite <- FLmc_D in EmcS; lia);
                        exact HbL0)
                  ltac:(replace (ts_maxcode s2 TK_D + 1 - 1)
                          with mcD by lia;
                        exact HbD0)
                  ltac:(rewrite EmcS; exact HVL')
                  ltac:(rewrite EmcSD; exact HVD'))
      as [Sw Dec].
    rewrite EmcS, EmcSD in Dec.
    split; [exact Sw | exact Dec]. }
  (* the STRICT parse of the same header bits (GAP7 freeze r3): guarded
     by the two frozen statements; the guards facts derive from the
     walk-threaded premises via [dyn_strict_guards] *)
  assert (Hwires : build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
      forall blockbits,
      decode_dynamic_tables_strict
        (hdr_bits (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
           (mbi + 1)
           ++ sat_bits (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                (ts_trees s2 TK_BL)
           ++ bitsL ++ bitsD ++ blockbits)
      = Some (tree_lens (ts_trees s2 TK_L) mcL,
              tree_lens (ts_trees s2 TK_D) mcD,
              blockbits)).
  { intros HBK EFR blockbits.
    assert (Es2g : s2 = snd (build_bl_tree s1D))
      by (rewrite <- Epair; reflexivity).
    pose proof HR1B as HR1B'. rewrite Es2g in HR1B'.
    pose proof HR2B as HR2B'. rewrite Es2g in HR2B'.
    destruct (dyn_strict_guards ts0 HBK EFR Heob Hblc0 Hblf0 Hbln0
                HR1L HR2L HR1D HR2D HR3D HR1B' HR2B')
      as (HaCL & HaL & HaD & Hb286 & Hb30).
    fold s1L in HaCL, HaL, HaD, Hb286, Hb30.
    fold s1D in HaCL, HaL, HaD, Hb286, Hb30.
    rewrite <- Es2g in HaCL, HaL, HaD, Hb286, Hb30.
    pose proof (dynamic_header_decode_strict
                  (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
                  (mbi + 1) (set_bw b0 s2) blt0 maxcbl blc cl
                  bitsL bitsD blockbits
                  ltac:(rewrite BmL, FLmc_D; lia)
                  ltac:(rewrite BmD; lia)
                  ltac:(lia) ltac:(lia)
                  Etree Bcllen PLens PBlc BV7 PAb Pmcbl
                  ltac:(intros r Hr; apply Bfits; lia)
                  ltac:(intros j Hj; rewrite Tblt0; apply HR2B)
                  ltac:(intros j Hj; rewrite Tblt0; apply Btail; lia)
                  ltac:(rewrite EmcS; rewrite BmL, FLmc_D in *; lia)
                  ltac:(intros i Hi; apply BLrng;
                        rewrite <- FLmc_D in EmcS; lia)
                  ltac:(rewrite EmcSD; rewrite BmD in *; lia)
                  ltac:(intros i Hi; apply BDrng; lia)
                  ltac:(replace (ts_maxcode s2 TK_L + 1 - 1)
                          with (ts_maxcode s1D TK_L) by
                          (rewrite <- FLmc_D in EmcS; lia);
                        exact HbL0)
                  ltac:(replace (ts_maxcode s2 TK_D + 1 - 1)
                          with mcD by lia;
                        exact HbD0)
                  ltac:(rewrite EmcS; exact HVL')
                  ltac:(rewrite EmcSD; exact HVD')
                  BLnn
                  ltac:(replace (ts_maxcode s2 TK_L + 1 - 1 + 1)
                          with (ts_maxcode s1D TK_L + 1)
                          by (rewrite BmL; lia);
                        exact BgL)
                  BDnn
                  ltac:(replace (ts_maxcode s2 TK_D + 1 - 1 + 1)
                          with (mcD + 1) by lia;
                        exact BgD)
                  HaCL
                  ltac:(rewrite EmcS; exact HaL)
                  ltac:(rewrite EmcSD; exact HaD)
                  Hb286 Hb30)
      as Dec.
    rewrite EmcS, EmcSD in Dec.
    exact Dec. }
  (* ---- the compressed body ---- *)
  set (bwT := send_all_trees (ts_maxcode s2 TK_L + 1)
                (ts_maxcode s2 TK_D + 1) (mbi + 1) (set_bw b0 s2)) in *.
  assert (WT : bw_wf bwT).
  { unfold bwT, send_all_trees. cbv zeta.
    assert (Ebt : ts_trees (set_bw b0 s2) = ts_trees s2) by reflexivity.
    assert (Ebbw : ts_bw (set_bw b0 s2) = b0) by reflexivity.
    rewrite Ebt, Ebbw.
    set (w1 := bw_send_bits (ts_maxcode s2 TK_L + 1 - 257) 5 b0).
    set (w2 := bw_send_bits (ts_maxcode s2 TK_D + 1 - 1) 5 w1).
    set (w3 := bw_send_bits (mbi + 1 - 4) 4 w2).
    set (w4 := sat_ranks (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                 (ts_trees s2 TK_BL) w3).
    assert (W1 : bw_wf w1).
    { destruct (bw_send_bits_stream (ts_maxcode s2 TK_L + 1 - 257) 5 b0 W0
                  ltac:(unfold Buf_size; lia)
                  ltac:(change (2 ^ 5) with 32; lia)) as [_ W].
      exact W. }
    assert (W2 : bw_wf w2).
    { destruct (bw_send_bits_stream (ts_maxcode s2 TK_D + 1 - 1) 5 w1 W1
                  ltac:(unfold Buf_size; lia)
                  ltac:(change (2 ^ 5) with 32; lia)) as [_ W].
      exact W. }
    assert (W3 : bw_wf w3).
    { destruct (bw_send_bits_stream (mbi + 1 - 4) 4 w2 W2
                  ltac:(unfold Buf_size; lia)
                  ltac:(change (2 ^ 4) with 16; lia)) as [_ W].
      exact W. }
    assert (W4 : bw_wf w4).
    { apply sat_ranks_wf; [|exact W3].
      intros r Hr. apply Bfits. lia. }
    rewrite Etree.
    destruct (send_tree_stream_at_any_writer (ts_trees s2 TK_L)
                (ts_maxcode s2 TK_L + 1 - 1) cl blt0 maxcbl blc bitsL w4
                ltac:(lia)
                BLnn
                ltac:(replace (ts_maxcode s2 TK_L + 1 - 1 + 1)
                        with (ts_maxcode s1D TK_L + 1)
                        by (rewrite BmL; lia);
                      exact BgL)
                ltac:(intros i Hi; apply BLrng; lia)
                PLens PBlc BV7 PAb Pmcbl
                ltac:(replace (ts_maxcode s2 TK_L + 1 - 1)
                        with (ts_maxcode s1D TK_L) by (rewrite BmL; lia);
                      exact HbL0)
                W4) as [_ W5].
    destruct (send_tree_stream_at_any_writer (ts_trees s2 TK_D)
                (ts_maxcode s2 TK_D + 1 - 1) cl blt0 maxcbl blc bitsD
                (send_tree (ts_trees s2 TK_L) (ts_maxcode s2 TK_L + 1 - 1)
                   (gen_codes blt0 maxcbl blc) w4)
                ltac:(lia)
                BDnn
                ltac:(replace (ts_maxcode s2 TK_D + 1 - 1 + 1)
                        with (mcD + 1) by lia;
                      exact BgD)
                ltac:(intros i Hi; apply BDrng; lia)
                PLens PBlc BV7 PAb Pmcbl
                ltac:(replace (ts_maxcode s2 TK_D + 1 - 1)
                        with mcD by lia;
                      exact HbD0)
                W5) as [_ W6].
    exact W6. }
  (* the token-side facts at the send trees *)
  assert (LensPtL : forall k, (k < length (tree_lens (ts_trees s2 TK_L)
                                 mcL))%nat ->
            t_len (ts_trees s2 TK_L) (Z.of_nat k)
            = Z.of_nat (nth k (tree_lens (ts_trees s2 TK_L) mcL) 0%nat))
    by (exact (lensof_self (ts_trees s2 TK_L) mcL BLnn)).
  assert (LensPtD : forall k, (k < length (tree_lens (ts_trees s2 TK_D)
                                 mcD))%nat ->
            t_len (ts_trees s2 TK_D) (Z.of_nat k)
            = Z.of_nat (nth k (tree_lens (ts_trees s2 TK_D) mcD) 0%nat))
    by (exact (lensof_self (ts_trees s2 TK_D) mcD BDnn)).
  assert (LlenV : length (tree_lens (ts_trees s2 TK_L) mcL)
                  = Z.to_nat (mcL + 1))
    by apply BtClPack.tree_lens_length.
  assert (DlenV : length (tree_lens (ts_trees s2 TK_D) mcD)
                  = Z.to_nat (mcD + 1))
    by apply BtClPack.tree_lens_length.
  (* live symbol -> in-range coded length at the SEND tree *)
  assert (LiveL : forall v, 0 <= v < 286 ->
            t_freq (ts_trees ts0 TK_L) v <> 0 ->
            1 <= t_len (ts_trees s2 TK_L) v <= 15 /\ v <= mcL).
  { intros v Hv Hf.
    destruct (Llive v Hv Hf) as [Hr Hle].
    split; [|exact Hle].
    rewrite (TLen v Hle). exact Hr. }
  assert (LiveD : forall v, 0 <= v < 30 ->
            t_freq (ts_trees ts0 TK_D) v <> 0 ->
            1 <= t_len (ts_trees s2 TK_D) v <= 15 /\ v <= mcD).
  { intros v Hv Hf.
    assert (Hf1 : t_freq (ts_trees s1L TK_D) v <> 0)
      by (rewrite FD_L; exact Hf).
    destruct (Dlive v Hv Hf1) as [Hr Hle].
    split; [|exact Hle].
    rewrite (TLenD v Hle). exact Hr. }
  (* code_for existence via the canonical-code supply *)
  assert (CodeL : forall v, 0 <= v <= mcL ->
            1 <= t_len (ts_trees s2 TK_L) v <= 15 ->
            exists cw, code_for (tree_lens (ts_trees s2 TK_L) mcL) 15%nat
                         (Z.to_nat v) = Some cw).
  { intros v Hv Hr.
    destruct (dyn_coded_upto (ts_trees s2 TK_L)
                (tree_lens (ts_trees s2 TK_L) mcL)
                (length (tree_lens (ts_trees s2 TK_L) mcL))
                LensPtL ltac:(lia) (Z.to_nat v)
                ltac:(rewrite LlenV; lia)
                ltac:(rewrite Z2Nat.id by lia; exact Hr))
      as [cw Hcw].
    exists cw. exact Hcw. }
  assert (CodeD : forall v, 0 <= v <= mcD ->
            1 <= t_len (ts_trees s2 TK_D) v <= 15 ->
            exists cw, code_for (tree_lens (ts_trees s2 TK_D) mcD) 15%nat
                         (Z.to_nat v) = Some cw).
  { intros v Hv Hr.
    destruct (dyn_coded_upto (ts_trees s2 TK_D)
                (tree_lens (ts_trees s2 TK_D) mcD)
                (length (tree_lens (ts_trees s2 TK_D) mcD))
                LensPtD ltac:(lia) (Z.to_nat v)
                ltac:(rewrite DlenV; lia)
                ltac:(rewrite Z2Nat.id by lia; exact Hr))
      as [cw Hcw].
    exists cw. exact Hcw. }
  (* the per-token pack *)
  assert (Htoks : Forall (tok_ok (tree_lens (ts_trees s2 TK_L) mcL)
                          (tree_lens (ts_trees s2 TK_D) mcD)
                          (Z.to_nat (mcL + 1)) (Z.to_nat (mcD + 1))) toks).
  { rewrite Forall_forall.
    intros t Hin.
    assert (Ht := proj1 (Forall_forall _ _) Henc t Hin).
    destruct t as [b|len dist]; cbn [tok_enc] in Ht; cbn [tok_ok].
    - split; [exact Ht|].
      assert (Hf : t_freq (ts_trees ts0 TK_L) b <> 0).
      { rewrite (HfL b ltac:(unfold L_CODES; lia)).
        pose proof (count_L_in_lit toks b Hin).
        destruct (Z.eqb b END_BLOCK); lia. }
      destruct (LiveL b ltac:(lia) Hf) as [Hr Hle].
      exact (CodeL b ltac:(lia) Hr).
    - destruct Ht as [Hlen Hdist].
      unfold MIN_MATCH, MAX_MATCH in Hlen.
      assert (Hlc : 0 <= len - 3 < 256) by lia.
      pose proof (lcode_range (len - 3) Hlc) as (Hli & _ & _).
      assert (HD : DcodeRange (dist - 1)) by (apply DcodeRange_all; lia).
      pose proof HD as (Hdcr & _ & _).
      set (sL := length_code (len - 3) + LITERALS + 1) in *.
      set (sD := d_code (dist - 1)) in *.
      assert (HfL' : t_freq (ts_trees ts0 TK_L) sL <> 0).
      { rewrite (HfL sL ltac:(unfold sL, LITERALS, L_CODES in *; lia)).
        pose proof (count_L_in_match toks len dist Hin).
        fold sL in H.
        destruct (Z.eqb sL END_BLOCK) eqn:E;
          [apply Z.eqb_eq in E; unfold sL, LITERALS, END_BLOCK in *; lia
          |lia]. }
      assert (HfD' : t_freq (ts_trees ts0 TK_D) sD <> 0).
      { rewrite (HfD sD ltac:(unfold sD, D_CODES in *; lia)).
        pose proof (count_D_in_match toks len dist Hin).
        fold sD in H. lia. }
      destruct (LiveL sL ltac:(unfold sL, LITERALS in *; lia) HfL')
        as [HrL HleL].
      destruct (LiveD sD ltac:(unfold sD in *; lia) HfD') as [HrD HleD].
      split; [lia|].
      split; [lia|].
      split; [exact HD|].
      split; [unfold sL, LITERALS in *; lia|].
      split; [unfold sD in *; lia|].
      split.
      + exact (CodeL sL ltac:(unfold sL, LITERALS in *; lia) HrL).
      + exact (CodeD sD ltac:(unfold sD in *; lia) HrD).
  }
  (* codes at the send trees *)
  assert (CodesL : tree_codes_upto (ts_trees s2 TK_L)
                     (tree_lens (ts_trees s2 TK_L) mcL)
                     (Z.to_nat (mcL + 1))).
  { rewrite EllL.
    apply (tree_codes_upto_ext (ts_trees s1L TK_L)).
    - intros i Hi. apply TLen. lia.
    - intros i Hi. apply TCode.
    - apply Lcodes. }
  assert (CodesD : tree_codes_upto (ts_trees s2 TK_D)
                     (tree_lens (ts_trees s2 TK_D) mcD)
                     (Z.to_nat (mcD + 1))).
  { rewrite EllD.
    apply (tree_codes_upto_ext (ts_trees s1D TK_D)).
    - intros i Hi. apply TLenD. lia.
    - intros i Hi. apply TCodeD.
    - apply Dcodes. }
  (* END_BLOCK's codeword *)
  assert (Heobcw : exists cw,
            code_for (tree_lens (ts_trees s2 TK_L) mcL) 15%nat 256%nat
            = Some cw).
  { destruct (LiveL END_BLOCK ltac:(unfold END_BLOCK; lia) Heob)
      as [Hr Hle].
    destruct (CodeL END_BLOCK ltac:(unfold END_BLOCK in *; lia) Hr)
      as [cw Hcw].
    exists cw.
    replace 256%nat with (Z.to_nat END_BLOCK)
      by (unfold END_BLOCK; reflexivity).
    exact Hcw. }
  (* ---- the compressed body decodes ---- *)
  destruct (compress_block_decodes (ts_symbuf s2) (ts_symnext s2)
              (ts_trees s2 TK_L) (ts_trees s2 TK_D)
              (tree_lens (ts_trees s2 TK_L) mcL)
              (tree_lens (ts_trees s2 TK_D) mcD)
              (Z.to_nat (mcL + 1)) (Z.to_nat (mcD + 1))
              bwT toks acc out
              CodesL CodesD
              ltac:(rewrite BmL, FLmc_D in *; lia)
              WT
              ltac:(rewrite Esb2, Esn2; exact Hbuf)
              Htoks
              Heobcw HVL' HVD' Henc Hres)
    as (cbd & Scb & Wcb & Hdec).
  (* ---- assemble ---- *)
  exists (zwrite 3 (Z.shiftl DYN_TREES 1 + last)
          ++ (hdr_bits (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
                (mbi + 1)
              ++ sat_bits (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                   (ts_trees s2 TK_BL)
              ++ bitsL ++ bitsD)
          ++ cbd).
  assert (Sdyn : bw_stream (dyn_bw last mbi s2)
                 = bw_stream (ts_bw ts0)
                   ++ zwrite 3 (Z.shiftl DYN_TREES 1 + last)
                   ++ (hdr_bits (ts_maxcode s2 TK_L + 1)
                         (ts_maxcode s2 TK_D + 1) (mbi + 1)
                       ++ sat_bits (Z.to_nat BL_CODES + 1) 0 (mbi + 1)
                            (ts_trees s2 TK_BL)
                       ++ bitsL ++ bitsD)
                   ++ cbd).
  { unfold dyn_bw.
    fold b0. fold bwT.
    rewrite Scb.
    rewrite (proj1 (Hwire [])).
    rewrite S0, Ebw2.
    rewrite <- !app_assoc. reflexivity. }
  split.
  { rewrite Sdyn. rewrite <- !app_assoc. reflexivity. }
  split.
  { unfold dyn_bw. fold b0. fold bwT. exact Wcb. }
  split.
  { intro suffix.
    destruct (Hdec suffix) as (syms & Hsyms & Hlz).
    rewrite <- !app_assoc.
    destruct Hl as [-> | ->]; unfold dec_blk.
    - change (zwrite 3 (Z.shiftl DYN_TREES 1 + 0))
        with [false; false; true].
      change (read_bits 1%nat ([false; false; true] ++ ?r))
        with (Some (0, [false; true] ++ r)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([false; true] ++ ?r)) with (Some (2, r)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite (proj2 (Hwire (cbd ++ suffix))).
      cbv beta iota.
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity.
    - change (zwrite 3 (Z.shiftl DYN_TREES 1 + 1))
        with [true; false; true].
      change (read_bits 1%nat ([true; false; true] ++ ?r))
        with (Some (1, [false; true] ++ r)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([false; true] ++ ?r)) with (Some (2, r)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite (proj2 (Hwire (cbd ++ suffix))).
      cbv beta iota.
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity. }
  { intros HBK EFR suffix.
    destruct (Hdec suffix) as (syms & Hsyms & Hlz).
    rewrite <- !app_assoc.
    destruct Hl as [-> | ->]; unfold dec_blk_strict.
    - change (zwrite 3 (Z.shiftl DYN_TREES 1 + 0))
        with [false; false; true].
      change (read_bits 1%nat ([false; false; true] ++ ?r))
        with (Some (0, [false; true] ++ r)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([false; true] ++ ?r)) with (Some (2, r)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite (Hwires HBK EFR (cbd ++ suffix)).
      cbv beta iota.
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity.
    - change (zwrite 3 (Z.shiftl DYN_TREES 1 + 1))
        with [true; false; true].
      change (read_bits 1%nat ([true; false; true] ++ ?r))
        with (Some (1, [false; true] ++ r)).
      cbv beta iota zeta.
      change (read_bits 2%nat ([false; true] ++ ?r)) with (Some (2, r)).
      cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite (Hwires HBK EFR (cbd ++ suffix)).
      cbv beta iota.
      rewrite Hsyms. cbv beta iota.
      rewrite Hlz. reflexivity. }
Qed.

Print Assumptions dyn_arm_dec_blk.
