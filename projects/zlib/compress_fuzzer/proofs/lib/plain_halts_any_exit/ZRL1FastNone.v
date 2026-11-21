(** * ZRL1FastNone — the buf=None per-event budget at the FAST path (1,-15).

    OWNER: l1-adversary (zlib z-repro campaign, 2026-08-23; the project owner
    commission: settle the l1_raw deflateBound face).

    THE GAP: deflate_fast (level 1) has NO TOO_FAR filter (ds_body-only),
    so ZReproG6N's [Forall tok_far_ok] premise is undischargeable on the
    fast path and its ledger (2*cost <= 13*extent + 5) is FALSE there
    (len-3 far match: 2*25 = 50 > 13*3 + 5 = 44).

    THE REPLACEMENT: [tr_flush_block] emits the MIN of the static and
    dynamic arms when buf = None.  So the budget follows from EITHER
    counter being under 8*slen + 21 — the disjunction [zr_l1_min_fits].
    That disjunction is THE one open Case-B lemma of the face (falsifier
    verdict 2026-08-23: no counterexample in ~720 adversarial inputs;
    empirically Case B = static expands via len-3-far density and the
    dynamic tree compresses the shared length symbol 257).  This file
    does NOT prove it; it reduces the whole (1,-15) buf=None face to it.

    Structure mirrors ZReproG6N section-by-section:
      - [zr_l1_min_fits]            — the frozen hole (Case A \/ Case B).
      - [tr_flush_block_len_none_fast]   — G6N's theorem, Hfar premise
        replaced by the disjunction; conclusion identical.
      - [flush_block_only_acct_none_fast] — the per-EVENT budget.
      - [flush_from_acct_full_fast]  — the blockstart dichotomy wrapper:
        the face's per-event budget from ONE conditional premise.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees DeflateSpec CbEmit CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BuildTree SendGo SendGoWf SendItems ClStream HuffCover ScanCount.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  BtFrame SwWin SwEv SwStep G3Event G3DynA ZReproG6A ZReproG6C ZReproG6D
  ZReproG6I ZReproG6K ZReproG6L ZReproG6F ZReproG6G ZReproG6H ZReproG6N.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The frozen hole: Case A (static fits) OR Case B (dynamic fits).

   Stated at [tr_flush_block]'s huffman dispatch state — the counters
   AFTER build_tree L, build_tree D, build_bl_tree — because that is
   where the mathematics lives (integer Huffman + tree description).
   The threshold 8*slen + 21 is G6N's: it leaves 19 bits of the 40-bit
   budget for the 3-bit block header, the <= 6 bl-padding, and ceil8.
   ========================================================================== *)

Definition zr_l1_min_fits (ts : TSt) (slen : Z) : Prop :=
  ts_statlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
    <= 8 * slen + 21
  \/ ts_optlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
     <= 8 * slen + 21.

(* ==========================================================================
   2.  The tr-level theorem: G6N's [tr_flush_block_len_none] with the
       TOO_FAR premise replaced by [zr_l1_min_fits].
   ========================================================================== *)

Theorem tr_flush_block_len_none_fast : forall ts toks slen last level dtype,
  bwv (ts_bw ts) ->
  last = 0 \/ last = 1 ->
  0 < level ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  zr_l1_min_fits ts slen ->
  let ts' := snd (tr_flush_block None slen last level 0 dtype ts) in
  zbits (ts_bw ts) <= zbits (ts_bw ts')
  /\ ceil8 (zbits (ts_bw ts'))
     <= ceil8 (zbits (ts_bw ts)) + 8 * slen + 40
  /\ bwv (ts_bw ts')
  /\ (last = 1 -> bw_valid (ts_bw ts') = 0).
Proof.
  intros ts toks slen last level dtype
         Hbwv Hl Hlevel Hbuf Henc Hntoks Hext Hsld
         Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD Hmin.
  destruct (dispatch_counters ts toks Hol0 Hsl0 Hbl0 HFI Henc Hntoks HblZ
              HnnL HnnD)
    as (OL & SL & EOL & ESL & HOLr & HSLr & Hmbir & HmcLr & HmcDr
        & HgL & HgD & Hlen15L & Hlen15D & HnnL' & HnnD' & HLenBL
        & Hwtok & HeobW & HDYN & HSTA & HSLup).
  (* the frozen hole, transported to the named counters — BEFORE the
     dispatch state is destructed away *)
  unfold zr_l1_min_fits in Hmin.
  rewrite ESL, EOL in Hmin.
  pose proof (zbits_nonneg (ts_bw ts)) as Hzn.
  unfold tr_flush_block. cbv zeta.
  rewrite (proj2 (Z.ltb_lt 0 level) Hlevel).
  cbv iota.
  destruct (build_bl_tree (build_tree TK_D (build_tree TK_L ts)))
    as [mbi s2p] eqn:EP.
  cbn [fst snd].
  cbn [fst snd] in EOL, ESL, Hmbir, HmcLr, HmcDr, HgL, HgD, Hlen15L,
    Hlen15D, HnnL', HnnD', HLenBL, Hwtok, HeobW, HDYN, HSTA, HSLup.
  assert (HF : TFrame s2p ts).
  { assert (Es2 : s2p = snd (build_bl_tree (build_tree TK_D
                              (build_tree TK_L ts))))
      by (rewrite EP; reflexivity).
    rewrite Es2.
    eapply tframe_trans; [apply build_bl_tree_frame|].
    eapply tframe_trans; apply build_tree_frame. }
  destruct HF as (Fsb & Fsn & Fbw & Fm).
  assert (Estatlenb : u64 (ts_statlen s2p + 3 + 7) / 8 = (SL + 10) / 8).
  { rewrite ESL. f_equal. unfold u64. rewrite Z.mod_small by lia. ring. }
  assert (Eoptlenb : u64 (ts_optlen s2p + 3 + 7) / 8 = (OL + 10) / 8).
  { rewrite EOL. f_equal. unfold u64. rewrite Z.mod_small by lia. ring. }
  assert (HSLd : 8 * ((SL + 10) / 8) <= SL + 10).
  { pose proof (Z.mul_div_le (SL + 10) 8 ltac:(lia)). lia. }
  assert (HOLd : 8 * ((OL + 10) / 8) <= OL + 10).
  { pose proof (Z.mul_div_le (OL + 10) 8 ltac:(lia)). lia. }
  assert (HSLge : SL + 3 <= 8 * ((SL + 10) / 8)).
  { pose proof (Z.mod_pos_bound (SL + 10) 8 ltac:(lia)).
    pose proof (Z.div_mod (SL + 10) 8 ltac:(lia)). lia. }
  assert (HOLge : OL + 3 <= 8 * ((OL + 10) / 8)).
  { pose proof (Z.mod_pos_bound (OL + 10) 8 ltac:(lia)).
    pose proof (Z.div_mod (OL + 10) 8 ltac:(lia)). lia. }
  (* the huffman-body bit costs — verbatim from G6N (no ledger needed) *)
  assert (HstaticBody :
      zbits (ts_bw ts)
        <= zbits (compress_block (ts_symbuf s2p) (ts_symnext s2p)
                    static_ltree static_dtree
                    (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                       (ts_bw s2p)))
      /\ zbits (compress_block (ts_symbuf s2p) (ts_symnext s2p)
               static_ltree static_dtree
               (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 (ts_bw s2p)))
         <= zbits (ts_bw ts) + 3 + SL
      /\ bwv (compress_block (ts_symbuf s2p) (ts_symnext s2p)
                static_ltree static_dtree
                (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                   (ts_bw s2p)))).
  { rewrite Fbw, Fsb, Fsn.
    destruct (zbits_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 (ts_bw ts)
                Hbwv ltac:(unfold Buf_size; lia)) as [Z0 V0].
    destruct (compress_block_len (ts_symbuf ts) (ts_symnext ts)
                static_ltree static_dtree
                (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 (ts_bw ts))
                toks V0 Hbuf Henc static_ltree_LenB static_dtree_LenB)
      as [Z1 V1].
    pose proof (toks_cost_nonneg static_ltree static_dtree toks
                  static_ltree_LenB static_dtree_LenB Henc) as Htcnn.
    pose proof (static_ltree_LenB 256 ltac:(lia)) as Heobnn.
    (* the static counter decomposes as cost + EOB: dispatch's HSTA *)
    split; [|split; [|exact V1]]; rewrite Z1, Z0; unfold END_BLOCK in *; lia. }
  assert (HdynBody :
      zbits (ts_bw ts) <= zbits (dyn_bw last mbi s2p)
      /\ zbits (dyn_bw last mbi s2p) <= zbits (ts_bw ts) + 3 + OL + 6
      /\ bwv (dyn_bw last mbi s2p)).
  { unfold dyn_bw.
    destruct (zbits_send_bits (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2p)
                ltac:(rewrite Fbw; exact Hbwv)
                ltac:(unfold Buf_size; lia)) as [Z0 V0].
    set (b0 := bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2p)) in *.
    assert (V0' : bwv (ts_bw (set_bw b0 s2p)))
      by (rewrite ts_bw_set_bw; exact V0).
    destruct (send_all_trees_len (ts_maxcode s2p TK_L + 1)
                (ts_maxcode s2p TK_D + 1) (mbi + 1) (set_bw b0 s2p) V0')
      as [Z2 V2].
    { cbn [ts_maxcode set_bw].
      replace (ts_maxcode s2p TK_L + 1 - 1) with (ts_maxcode s2p TK_L)
        by ring. lia. }
    { cbn [ts_maxcode set_bw].
      replace (ts_maxcode s2p TK_D + 1 - 1) with (ts_maxcode s2p TK_D)
        by ring. lia. }
    { lia. }
    { cbn [ts_maxcode ts_trees set_bw].
      replace (ts_maxcode s2p TK_L + 1 - 1) with (ts_maxcode s2p TK_L)
        by ring. exact HgL. }
    { cbn [ts_maxcode ts_trees set_bw].
      replace (ts_maxcode s2p TK_D + 1 - 1) with (ts_maxcode s2p TK_D)
        by ring. exact HgD. }
    { cbn [ts_maxcode ts_trees set_bw].
      intros i Hi.
      replace (ts_maxcode s2p TK_L + 1 - 1) with (ts_maxcode s2p TK_L) in Hi
        by ring.
      apply Hlen15L. exact Hi. }
    { cbn [ts_maxcode ts_trees set_bw].
      intros i Hi.
      replace (ts_maxcode s2p TK_D + 1 - 1) with (ts_maxcode s2p TK_D) in Hi
        by ring.
      apply Hlen15D. exact Hi. }
    { cbn [ts_trees set_bw]. exact HnnL'. }
    { cbn [ts_trees set_bw]. exact HnnD'. }
    { cbn [ts_trees set_bw]. exact HLenBL. }
    set (b3 := send_all_trees (ts_maxcode s2p TK_L + 1)
                 (ts_maxcode s2p TK_D + 1) (mbi + 1) (set_bw b0 s2p)) in *.
    assert (V2' : bwv b3) by (unfold b3; exact V2).
    destruct (compress_block_len_tok (ts_symbuf s2p) (ts_symnext s2p)
                (ts_trees s2p TK_L) (ts_trees s2p TK_D) b3 toks
                V2' ltac:(rewrite Fsb, Fsn; exact Hbuf) Henc Hwtok HeobW)
      as [Z1 V1].
    pose proof (toks_cost_nonneg_tok (ts_trees s2p TK_L) (ts_trees s2p TK_D)
                  toks Henc Hwtok) as Htcnn.
    assert (HBLnnL : 0 <= wsum (fun sy =>
              hid_zcount sy (items_syms (send_tree_items (ts_trees s2p TK_L)
                               (ts_maxcode s2p TK_L)))
              * (t_len (ts_trees s2p TK_BL) sy + extra_blbits sy)) 0 19).
    { apply wsum_nonneg. intros sy Hsy.
      assert (Hsy' : 0 <= sy < 19) by lia.
      pose proof (hid_nonneg sy (items_syms (send_tree_items
                    (ts_trees s2p TK_L) (ts_maxcode s2p TK_L)))).
      pose proof (HLenBL sy Hsy'). pose proof (extra_blbits_range sy Hsy').
      apply Z.mul_nonneg_nonneg; lia. }
    assert (HBLnnD : 0 <= wsum (fun sy =>
              hid_zcount sy (items_syms (send_tree_items (ts_trees s2p TK_D)
                               (ts_maxcode s2p TK_D)))
              * (t_len (ts_trees s2p TK_BL) sy + extra_blbits sy)) 0 19).
    { apply wsum_nonneg. intros sy Hsy.
      assert (Hsy' : 0 <= sy < 19) by lia.
      pose proof (hid_nonneg sy (items_syms (send_tree_items
                    (ts_trees s2p TK_D) (ts_maxcode s2p TK_D)))).
      pose proof (HLenBL sy Hsy'). pose proof (extra_blbits_range sy Hsy').
      apply Z.mul_nonneg_nonneg; lia. }
    split; [|split; [|exact V1]];
      rewrite Z1, Z2, ts_bw_set_bw, Z0, Fbw;
      cbn [ts_trees ts_maxcode set_bw];
      replace (ts_maxcode s2p TK_L + 1 - 1) with (ts_maxcode s2p TK_L) by ring;
      replace (ts_maxcode s2p TK_D + 1 - 1) with (ts_maxcode s2p TK_D) by ring;
      lia. }
  (* --- the None dispatch: no stored arm, the two huffman bodies --- *)
  rewrite Estatlenb, Eoptlenb.
  replace (Z.eqb 0 Z_FIXED) with false by reflexivity.
  rewrite !orb_false_r.
  set (SLB := (SL + 10) / 8) in *.
  set (OLB := (OL + 10) / 8) in *.
  set (optlenb := if Z.leb SLB OLB then SLB else OLB) in *.
  assert (HSLdB : 8 * SLB <= SL + 10) by (unfold SLB; lia).
  assert (HOLdB : 8 * OLB <= OL + 10) by (unfold OLB; lia).
  assert (HSLgeB : SL + 3 <= 8 * SLB) by (unfold SLB; lia).
  assert (HOLgeB : OL + 3 <= 8 * OLB) by (unfold OLB; lia).
  cbv iota.
  destruct (Z.eqb_spec SLB optlenb) as [Estat|Edyn].
  + (* STATIC arm: chosen means SLB <= OLB, so Case B also caps SL *)
    assert (HSLBle : SLB <= OLB).
    { unfold optlenb in Estat.
      destruct (Z.leb_spec SLB OLB) as [Hle|Hgt]; [exact Hle | lia]. }
    assert (HSL28 : SL <= 8 * slen + 28).
    { destruct Hmin as [HA|HB]; lia. }
    cbn [ts_bw set_bw].
    destruct HstaticBody as (HsMono & HsB & HsV).
    set (b4 := compress_block (ts_symbuf s2p) (ts_symnext s2p)
                 static_ltree static_dtree
                 (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                    (ts_bw s2p))) in *.
    assert (Hmono4 : zbits (ts_bw ts) <= zbits (ts_bw (set_bw b4 s2p)))
      by (cbn [ts_bw set_bw]; exact HsMono).
    assert (Hstep4 : ceil8 (zbits (ts_bw (set_bw b4 s2p)))
                     <= ceil8 (zbits (ts_bw ts)) + (8 * slen + 40)).
    { cbn [ts_bw set_bw].
      eapply Z.le_trans; [apply ceil8_mono; exact HsB|].
      replace (zbits (ts_bw ts) + 3 + SL)
        with (zbits (ts_bw ts) + (3 + SL)) by ring.
      eapply Z.le_trans; [apply ceil8_add_le; lia|].
      assert (Hc : ceil8 (3 + SL) <= 3 + SL + 7)
        by (pose proof (ceil8_lt (3 + SL)); lia).
      lia. }
    destruct (g6_flush_tail (set_bw b4 s2p) last (8 * slen + 40)
                (ts_bw ts) Hl ltac:(cbn [ts_bw set_bw]; exact HsV)
                ltac:(lia) Hmono4 Hstep4) as (T1 & T2 & T3 & T4).
    split; [exact T1|]. split; [lia|]. split; [exact T3 | exact T4].
  + (* DYNAMIC arm: chosen strictly under the static counter *)
    cbn [ts_bw set_bw].
    destruct HdynBody as (HdMono & HdB & HdV).
    assert (Hdynb : OL <= 8 * slen + 21).
    { assert (Hob : optlenb = OLB /\ OLB < SLB).
      { unfold optlenb in *.
        destruct (Z.leb_spec SLB OLB) as [Hle|Hgt].
        - exfalso. apply Edyn. reflexivity.
        - split; [reflexivity | exact Hgt]. }
      destruct Hob as [_ HOLBlt].
      destruct Hmin as [HA|HB]; lia. }
    change (compress_block (ts_symbuf s2p) (ts_symnext s2p)
              (ts_trees s2p TK_L) (ts_trees s2p TK_D)
              (send_all_trees (ts_maxcode s2p TK_L + 1)
                 (ts_maxcode s2p TK_D + 1) (mbi + 1)
                 (set_bw (bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3
                    (ts_bw s2p)) s2p)))
      with (dyn_bw last mbi s2p).
    assert (Hmono4 : zbits (ts_bw ts)
                     <= zbits (ts_bw (set_bw (dyn_bw last mbi s2p) s2p)))
      by (cbn [ts_bw set_bw]; exact HdMono).
    assert (Hstep4 : ceil8 (zbits (ts_bw (set_bw (dyn_bw last mbi s2p) s2p)))
                     <= ceil8 (zbits (ts_bw ts)) + (8 * slen + 40)).
    { cbn [ts_bw set_bw].
      eapply Z.le_trans; [apply ceil8_mono; exact HdB|].
      replace (zbits (ts_bw ts) + 3 + OL + 6)
        with (zbits (ts_bw ts) + (3 + OL + 6)) by ring.
      eapply Z.le_trans; [apply ceil8_add_le; lia|].
      assert (Hc : ceil8 (3 + OL + 6) <= 3 + OL + 6 + 7)
        by (pose proof (ceil8_lt (3 + OL + 6)); lia).
      lia. }
    destruct (g6_flush_tail (set_bw (dyn_bw last mbi s2p) s2p) last
                (8 * slen + 40) (ts_bw ts) Hl
                ltac:(cbn [ts_bw set_bw]; exact HdV)
                ltac:(lia) Hmono4 Hstep4) as (T1 & T2 & T3 & T4).
    split; [exact T1|]. split; [lia|]. split; [exact T3 | exact T4].
Qed.

(* ==========================================================================
   3.  The per-EVENT budget at a NEGATIVE block start, fast path.
   ========================================================================== *)

Theorem flush_block_only_acct_none_fast : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g ->
  dg_strategy g = 0 ->
  dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  ls_blockstart (d_ls (fe_s ev)) < 0 ->
  32506 < fe_end ev - fe_start ev ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  zr_l1_min_fits (d_ts (fe_s ev)) (fe_end ev - fe_start ev) ->
  let s' := flush_block_only (fe_last ev) (fe_s ev) in
  tot_bits (fe_s ev) <= tot_bits s'
  /\ ceil8 (tot_bits s')
     <= ceil8 (tot_bits (fe_s ev)) + 8 * (fe_end ev - fe_start ev) + 40
  /\ bwv (zbw s')
  /\ zs_availout (d_strm s')
     = zs_availout (d_strm (fe_s ev))
       - (zlen (zs_out (d_strm s')) - zlen (zs_out (d_strm (fe_s ev))))
  /\ zlen (zs_out (d_strm (fe_s ev))) <= zlen (zs_out (d_strm s'))
  /\ 0 <= zs_availout (d_strm s').
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hbs Hsld
         Hol0 Hsl0 Hbl0 HblZ HnnL HnnD Hmin s'.
  destruct HE as (Ecfg & Ewrap & Hbuf & Hfreq & Henc & Hsn & Hspan & Hend
                  & Hres & Hspan_eq & Hwin & Hlast01).
  set (s := fe_s ev) in *.
  assert (Hlen : Z.of_nat (length (fe_toks ev)) <= 16383).
  { pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext. lia. }
  set (l := d_ls s) in *.
  set (bs := ls_blockstart l) in *.
  set (slen := ls_strstart l - bs) in *.
  assert (Hlevg : 0 < dg_level (d_cfg s)) by (rewrite Ecfg; exact Hlev).
  assert (Hstratg : dg_strategy (d_cfg s) = 0) by (rewrite Ecfg; exact Hstrat).
  set (buf := if Z.leb 0 bs
              then Some (win_take (ls_window l) bs slen) else None) in *.
  assert (Ebuf : buf = None)
    by (unfold buf; replace (Z.leb 0 bs) with false
          by (symmetry; apply Z.leb_gt; lia); reflexivity).
  (* the tokens tile exactly the block's bytes *)
  assert (Hext0 : toks_ext (fe_toks ev) = fe_end ev - fe_start ev).
  { pose proof (resolve_length (fe_toks ev)
                  (firstn (Z.to_nat (fe_start ev)) done)
                  (firstn (Z.to_nat (fe_end ev)) done) Henc Hres) as RL.
    rewrite !g6_zlen_firstn in RL by lia.
    lia. }
  assert (Hspan2 : fe_end ev - fe_start ev = slen)
    by (unfold slen, bs, l; exact Hspan_eq).
  assert (Hext' : toks_ext (fe_toks ev) = slen).
  { rewrite Hext0. exact Hspan2. }
  rewrite Hspan2 in Hmin, Hsld.
  set (r := tr_flush_block None slen (fe_last ev) (dg_level (d_cfg s))
              0 (zs_datatype (d_strm s)) (d_ts s)) in *.
  destruct (tr_flush_block_len_none_fast (d_ts s) (fe_toks ev) slen
              (fe_last ev) (dg_level (d_cfg s)) (zs_datatype (d_strm s))
              Hbwv ltac:(lia) Hlevg Hbuf Henc Hlen Hext'
              ltac:(lia)
              Hol0 Hsl0 Hbl0 Hfreq HblZ HnnL HnnD Hmin)
    as (Hmono & Hstep & Hwf & _).
  fold r in Hmono, Hstep, Hwf.
  unfold s', flush_block_only. cbv zeta.
  fold l. fold bs. fold slen. fold buf.
  rewrite Ebuf. rewrite Hstratg.
  change (tr_flush_block None slen (fe_last ev) (dg_level (d_cfg s))
            0 (zs_datatype (d_strm s)) (d_ts s))
    with r.
  set (s2 := setD_ls (setL_blockstart (ls_strstart l) l)
               (setD_ts (snd r)
                  (setD_strm (setZ_datatype (fst r) (d_strm s)) s))) in *.
  assert (E2ts : ts_bw (d_ts s2) = ts_bw (snd r))
    by (unfold s2, setD_ls, setD_ts, setD_strm; reflexivity).
  assert (E2out : zs_out (d_strm s2) = zs_out (d_strm s))
    by (unfold s2, setD_ls, setD_ts, setD_strm, setZ_datatype; reflexivity).
  assert (E2avo : zs_availout (d_strm s2) = zs_availout (d_strm s))
    by (unfold s2, setD_ls, setD_ts, setD_strm, setZ_datatype; reflexivity).
  assert (E2zbw : zbw s2 = ts_bw (snd r)) by (unfold zbw; exact E2ts).
  destruct (flush_pending_acct s2
              ltac:(rewrite E2zbw; unfold bwv in *; exact Hwf)
              ltac:(rewrite E2avo; exact Havo))
    as (Fcons & Fbwv & Favo & Fmono & Favo0 & _ & _ & _ & _ & _ & _).
  assert (Hts2 : tot_bits s2 = 8 * zlen (zs_out (d_strm s)) + zbits (ts_bw (snd r))).
  { unfold tot_bits. rewrite E2out, E2zbw. reflexivity. }
  assert (Hts : tot_bits s = 8 * zlen (zs_out (d_strm s)) + zbits (ts_bw (d_ts s)))
    by (unfold tot_bits, zbw; reflexivity).
  pose proof (zlen_nonneg (zs_out (d_strm s))) as HQnn.
  split; [|split; [|split; [|split; [|split]]]].
  - rewrite Fcons, Hts2, Hts. lia.
  - rewrite Fcons, Hts2, Hts.
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s))) (zbits (ts_bw (snd r)))).
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s))) (zbits (ts_bw (d_ts s)))).
    rewrite !(ceil8_add_mul _ (zlen (zs_out (d_strm s)))).
    rewrite Hspan2. lia.
  - exact Fbwv.
  - rewrite Favo, E2avo, E2out. reflexivity.
  - rewrite <- E2out at 1. exact Fmono.
  - exact Favo0.
Qed.

(* ==========================================================================
   4.  The dichotomy wrapper: the whole (1,-15) per-event budget from ONE
       conditional premise (span floor is the walk's slide fact; min-fits
       is THE open Case-B lemma).
   ========================================================================== *)

Theorem flush_from_acct_full_fast : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  (ls_blockstart (d_ls (fe_s ev)) < 0 ->
     32506 < fe_end ev - fe_start ev
     /\ zr_l1_min_fits (d_ts (fe_s ev)) (fe_end ev - fe_start ev)) ->
  EvStepBudget ev.
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hol Hsl Hbl
         HblZ HnnL HnnD Hneg.
  destruct (Z.le_gt_cases 0 (ls_blockstart (d_ls (fe_s ev)))) as [Hge|Hlt].
  - exact (flush_from_acct g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo
             Hge Hol Hsl Hbl HblZ HnnL HnnD).
  - destruct (Hneg Hlt) as [Hsld Hmin].
    destruct (flush_block_only_acct_none_fast g wrap done ev HE Hlev Hstrat
                Hsend Hbwv Havo Hlt Hsld Hol Hsl Hbl HblZ HnnL HnnD Hmin)
      as (Hm & Hc & Hbwv' & Havorel & Hgrow & _).
    destruct HE as (_ & _ & _ & _ & _ & _ & Hspan & _).
    unfold EvStepBudget, cb_tot.
    unfold tot_bits, zbw in Hm, Hc.
    repeat split.
    + exact Hm.
    + exact Hc.
    + lia.
    + exact Havorel.
    + exact Hgrow.
Qed.

Print Assumptions tr_flush_block_len_none_fast.
Print Assumptions flush_block_only_acct_none_fast.
Print Assumptions flush_from_acct_full_fast.
