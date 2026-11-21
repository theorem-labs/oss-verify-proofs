(** * ZReproG6H — G6 bound-fit, part H: one flush event fits the budget.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    [tr_flush_block_len]: whichever arm the level>=1, strategy-0
    dispatcher takes at a walk snapshot, the bit writer grows by at most
    [8*stored_len + 40] bits of [ceil8] potential.
      * STORED   — part B's exact cost (align + 32 + bytes), 40 on the nose.
      * STATIC   — the stored guard's failure caps the byte cost at
                   [stored_len + 3]; part G's SL dominates the arm's data
                   bits EXACTLY (static trees are [LenB], so part C's
                   walk applies directly).
      * DYNAMIC  — same shape through OL + 6.  The dispatch trees are the
                   GUARDED scanned trees (a 65535 sentinel at maxc+1), so
                   part C's global-[LenB] [compress_block_len] does NOT
                   apply; the per-token-width variant here does, using the
                   [tok_widths_ok] window part G exports.

    Then [flush_block_only_acct] threads it through part A's
    [flush_pending] conservation.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin CbEmit CbFold ClStream
  SendItems SendGo SendGoWf ScanCount ScanBase HuffCover Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  BtFrame G3DynA ZReproG6A ZReproG6B ZReproG6C ZReproG6D ZReproG6E
  ZReproG6F ZReproG6G.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Static-table lengths fit the LenB window (for the static arm).
   ========================================================================== *)

Definition g6_stl15_at (v : Z) : bool :=
  (0 <=? t_len static_ltree v) && (t_len static_ltree v <=? 15).

Lemma g6_stl15_all : forallb g6_stl15_at (zseq 286 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma static_ltree_LenB : LenB static_ltree 286.
Proof.
  intros v Hv.
  pose proof (forallb_zseq' g6_stl15_at 286 286 v
                ltac:(vm_compute; reflexivity) g6_stl15_all Hv) as H.
  unfold g6_stl15_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition g6_std15_at (v : Z) : bool :=
  (0 <=? t_len static_dtree v) && (t_len static_dtree v <=? 15).

Lemma g6_std15_all : forallb g6_std15_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma static_dtree_LenB : LenB static_dtree 30.
Proof.
  intros v Hv.
  pose proof (forallb_zseq' g6_std15_at 30 30 v
                ltac:(vm_compute; reflexivity) g6_std15_all Hv) as H.
  unfold g6_std15_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ==========================================================================
   2.  The per-token-widths compress_block bit walk (guarded trees).
   ========================================================================== *)

Lemma cb_step_len_tok : forall sym symnext lt dt st,
  bwv (c_bw st) ->
  tok_enc (tok_at sym (c_sx st)) ->
  tok_widths_ok lt dt (tok_at sym (c_sx st)) ->
  zbits (c_bw (cb_out (cb_step sym symnext lt dt st)))
    = zbits (c_bw st) + tok_cost lt dt (tok_at sym (c_sx st))
  /\ bwv (c_bw (cb_out (cb_step sym symnext lt dt st))).
Proof.
  intros sym symnext lt dt st Hb He Hw.
  unfold tok_at, cb_dist, cb_lc in He, Hw |- *.
  unfold cb_step, cb_out. cbv zeta.
  set (dist := Z.land (sym (c_sx st)) 255
               + Z.shiftl (Z.land (sym (c_sx st + 1)) 255) 8) in *.
  set (lc := sym (c_sx st + 2)) in *.
  destruct (Z.eqb_spec dist 0) as [E|E].
  - cbn [tok_cost].
    cbn [tok_widths_ok] in Hw.
    destruct (zbits_send_code lc lt (c_bw st) Hb
                ltac:(unfold Buf_size; lia)) as [Hz Hv].
    destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw c_sx];
      split; assumption.
  - cbn [tok_enc] in He. destruct He as [[Hl0 Hl1] [Hd0 Hd1]].
    unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1.
    cbn [tok_widths_ok] in Hw.
    replace (lc + 3 - 3) with lc in Hw by ring.
    destruct Hw as [HwL HwD].
    cbn [tok_cost]. cbv zeta.
    replace (lc + 3 - 3) with lc by ring.
    destruct (lcode_range lc ltac:(lia)) as [Hc _].
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
    pose proof (extra_lbits_range (length_code lc) Hc) as Hel.
    pose proof (extra_dbits_range (d_code (dist - 1)) Hdc) as Hed.
    destruct (zbits_send_code (length_code lc + LITERALS + 1) lt (c_bw st) Hb
                ltac:(unfold Buf_size; lia)) as [Z1 V1].
    set (b1 := send_code (length_code lc + LITERALS + 1) lt (c_bw st)) in *.
    assert (S2 : zbits (if Z.eqb (extra_lbits (length_code lc)) 0 then b1
                        else bw_send_bits (lc - base_length (length_code lc))
                               (extra_lbits (length_code lc)) b1)
                 = zbits b1 + extra_lbits (length_code lc)
             /\ bwv (if Z.eqb (extra_lbits (length_code lc)) 0 then b1
                     else bw_send_bits (lc - base_length (length_code lc))
                            (extra_lbits (length_code lc)) b1)).
    { destruct (Z.eqb_spec (extra_lbits (length_code lc)) 0) as [E2|E2].
      - rewrite E2. split; [lia | exact V1].
      - apply zbits_send_bits; [exact V1 | unfold Buf_size; lia]. }
    destruct S2 as [Z2 V2].
    set (b2 := if Z.eqb (extra_lbits (length_code lc)) 0 then b1
               else bw_send_bits (lc - base_length (length_code lc))
                      (extra_lbits (length_code lc)) b1) in *.
    destruct (zbits_send_code (d_code (dist - 1)) dt b2 V2
                ltac:(unfold Buf_size; lia)) as [Z3 V3].
    set (b3 := send_code (d_code (dist - 1)) dt b2) in *.
    assert (S4 : zbits (if Z.eqb (extra_dbits (d_code (dist - 1))) 0 then b3
                        else bw_send_bits (dist - 1 - base_dist (d_code (dist - 1)))
                               (extra_dbits (d_code (dist - 1))) b3)
                 = zbits b3 + extra_dbits (d_code (dist - 1))
             /\ bwv (if Z.eqb (extra_dbits (d_code (dist - 1))) 0 then b3
                     else bw_send_bits (dist - 1 - base_dist (d_code (dist - 1)))
                            (extra_dbits (d_code (dist - 1))) b3)).
    { destruct (Z.eqb_spec (extra_dbits (d_code (dist - 1))) 0) as [E4|E4].
      - rewrite E4. split; [lia | exact V3].
      - apply zbits_send_bits; [exact V3 | unfold Buf_size; lia]. }
    destruct S4 as [Z4 V4].
    destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw c_sx];
      (split; [rewrite Z4, Z3, Z2, Z1; ring | exact V4]).
Qed.

Lemma cb_loop_len_tok : forall toks t sym symnext lt dt st0,
  bwv (c_bw st0) ->
  BufToks sym (c_sx st0) symnext (t :: toks) ->
  cEnc (t :: toks) ->
  Forall (tok_widths_ok lt dt) (t :: toks) ->
  exists st',
    cb_loop (S (length toks)) sym symnext lt dt st0 = Some st'
    /\ zbits (c_bw st') = zbits (c_bw st0) + toks_cost lt dt (t :: toks)
    /\ bwv (c_bw st').
Proof.
  induction toks as [|t2 toks IH];
    intros t sym symnext lt dt st0 Hb Hbuf He Hw;
    inversion He as [|? ? Ht Hr]; subst;
    inversion Hw as [|? ? Htw Hrw]; subst;
    pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext;
    destruct (buftoks_cons_inv _ _ _ _ _ Hbuf) as [Etok Htail].
  - cbn [length] in Hext.
    assert (Hw0 : tok_widths_ok lt dt (tok_at sym (c_sx st0)))
      by (rewrite <- Etok; exact Htw).
    assert (He0 : tok_enc (tok_at sym (c_sx st0)))
      by (rewrite <- Etok; exact Ht).
    destruct (cb_step_len_tok sym symnext lt dt st0 Hb He0 Hw0) as [Hz Hv].
    exists (cb_out (cb_step sym symnext lt dt st0)).
    split; [apply cb_loop_one; lia|].
    split; [|exact Hv].
    rewrite Hz, <- Etok. cbn [toks_cost]. ring.
  - cbn [length] in Hext.
    assert (Hw0 : tok_widths_ok lt dt (tok_at sym (c_sx st0)))
      by (rewrite <- Etok; exact Htw).
    assert (He0 : tok_enc (tok_at sym (c_sx st0)))
      by (rewrite <- Etok; exact Ht).
    destruct (cb_step_len_tok sym symnext lt dt st0 Hb He0 Hw0) as [Hz Hv].
    assert (Hlt3 : c_sx st0 + 3 < symnext) by (cbn [length] in Hext; lia).
    destruct (IH t2 sym symnext lt dt
                 (cb_out (cb_step sym symnext lt dt st0)) Hv
                 ltac:(rewrite cb_step_sx; exact Htail) Hr Hrw)
      as [st' [Hloop [Hz' Hv']]].
    exists st'.
    split.
    { cbn [length].
      rewrite (cb_loop_step_cont _ sym symnext lt dt st0 Hlt3).
      exact Hloop. }
    split; [|exact Hv'].
    rewrite Hz', Hz, <- Etok. cbn [toks_cost]. ring.
Qed.

Theorem compress_block_len_tok : forall sym symnext lt dt b toks,
  bwv b ->
  BufToks sym 0 symnext toks ->
  cEnc toks ->
  Forall (tok_widths_ok lt dt) toks ->
  0 <= t_len lt END_BLOCK <= 15 ->
  zbits (compress_block sym symnext lt dt b)
    = zbits b + toks_cost lt dt toks + t_len lt END_BLOCK
  /\ bwv (compress_block sym symnext lt dt b).
Proof.
  intros sym symnext lt dt b toks Hb Hbuf He Hw Heob.
  assert (Heob' : 0 <= t_len lt END_BLOCK <= Buf_size)
    by (unfold Buf_size; lia).
  pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext.
  unfold compress_block. cbv zeta.
  destruct toks as [|t toks].
  - cbn [length] in Hext.
    replace (Z.eqb symnext 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota.
    destruct (zbits_send_code END_BLOCK lt b Hb Heob') as [Hz Hv].
    split; [rewrite Hz; cbn [toks_cost]; ring | exact Hv].
  - cbn [length] in Hext.
    replace (Z.eqb symnext 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv beta iota.
    destruct (cb_loop_len_tok toks t sym symnext lt dt
                {| c_sx := 0; c_bw := b |} Hb Hbuf He Hw)
      as [st' [Hloop [Hz' Hv']]].
    rewrite (cb_loop_fuel_mono (S (length toks)) (Z.to_nat symnext + 1)
               sym symnext lt dt _ st' ltac:(lia) Hloop).
    cbv beta iota.
    destruct (zbits_send_code END_BLOCK lt (c_bw st') Hv' Heob') as [Hz Hv].
    split; [|exact Hv].
    rewrite Hz, Hz'. cbn [c_bw]. ring.
Qed.

(* ==========================================================================
   3.  The dispatcher's bit cost, arm by arm.
   ========================================================================== *)

(* ==========================================================================
   2b.  Token-cost nonnegativity from per-token widths (for monotonicity).
   ========================================================================== *)

Lemma tok_cost_nonneg_tok : forall lt dt t,
  tok_enc t -> tok_widths_ok lt dt t -> 0 <= tok_cost lt dt t.
Proof.
  intros lt dt t He Hw.
  destruct t as [b | len dist]; cbn [tok_cost tok_widths_ok] in *.
  - lia.
  - destruct He as [[Hl0 Hl1] [Hd0 Hd1]].
    unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1.
    destruct Hw as [HwL HwD].
    destruct (lcode_range (len - 3) ltac:(lia)) as [Hc _].
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
    pose proof (extra_lbits_range (length_code (len - 3)) Hc).
    pose proof (extra_dbits_range (d_code (dist - 1)) Hdc).
    lia.
Qed.

Lemma toks_cost_nonneg_tok : forall lt dt toks,
  cEnc toks -> Forall (tok_widths_ok lt dt) toks ->
  0 <= toks_cost lt dt toks.
Proof.
  intros lt dt toks He Hw.
  induction toks as [|t r IH]; cbn [toks_cost]; [lia|].
  inversion He as [|? ? Ht Hr]; subst.
  inversion Hw as [|? ? Htw Hrw]; subst.
  pose proof (tok_cost_nonneg_tok lt dt t Ht Htw).
  pose proof (IH Hr Hrw). lia.
Qed.

(* ==========================================================================
   3.  The init_block + windup tail (shared by every arm).
   ========================================================================== *)

Lemma g6_flush_tail : forall s4 last budget b0,
  last = 0 \/ last = 1 ->
  bwv (ts_bw s4) ->
  0 <= budget ->
  zbits b0 <= zbits (ts_bw s4) ->
  ceil8 (zbits (ts_bw s4)) <= ceil8 (zbits b0) + budget ->
  zbits b0 <= zbits (ts_bw (if Z.eqb last 0 then init_block s4
                            else set_bw (bw_windup (ts_bw (init_block s4)))
                                   (init_block s4)))
  /\ ceil8 (zbits (ts_bw (if Z.eqb last 0 then init_block s4
                          else set_bw (bw_windup (ts_bw (init_block s4)))
                                 (init_block s4))))
     <= ceil8 (zbits b0) + budget
  /\ bwv (ts_bw (if Z.eqb last 0 then init_block s4
                 else set_bw (bw_windup (ts_bw (init_block s4)))
                        (init_block s4)))
  /\ (last = 1 -> bw_valid (ts_bw (if Z.eqb last 0 then init_block s4
                                   else set_bw (bw_windup (ts_bw (init_block s4)))
                                          (init_block s4))) = 0).
Proof.
  intros s4 last budget b0 Hl Hbwv Hbud Hmono Hstep.
  assert (Einit : ts_bw (init_block s4) = ts_bw s4) by reflexivity.
  pose proof (ceil8_ge (zbits b0)) as Hge0.
  pose proof (ceil8_ge (zbits (ts_bw s4))) as Hge4.
  destruct Hl; subst last; cbn [Z.eqb]; cbv iota.
  - (* last = 0 *)
    rewrite Einit.
    split; [exact Hmono|].
    split; [exact Hstep|].
    split; [exact Hbwv|].
    intro Hc; discriminate Hc.
  - (* last = 1: windup pads to the byte ceiling *)
    cbn [ts_bw set_bw]. rewrite Einit.
    destruct (zbits_windup (ts_bw s4) Hbwv) as (Hwz & Hwv & Hwbwv & _).
    split.
    { rewrite Hwz. lia. }
    split.
    { rewrite Hwz.
      rewrite (ceil8_aligned (ceil8 (zbits (ts_bw s4))) (ceil8_mod _)).
      exact Hstep. }
    split; [exact Hwbwv|].
    intros _. exact Hwv.
Qed.

(* ==========================================================================
   4.  Per-block budget, stored option available.
   ========================================================================== *)

Theorem tr_flush_block_len : forall ts toks dat stored_len last level dtype,
  bwv (ts_bw ts) ->
  last = 0 \/ last = 1 ->
  0 < level ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  zlen dat = stored_len ->
  0 <= stored_len ->
  let ts' := snd (tr_flush_block (Some dat) stored_len last level 0 dtype ts) in
  zbits (ts_bw ts) <= zbits (ts_bw ts')
  /\ ceil8 (zbits (ts_bw ts'))
     <= ceil8 (zbits (ts_bw ts)) + 8 * stored_len + 40
  /\ bwv (ts_bw ts')
  /\ (last = 1 -> bw_valid (ts_bw ts') = 0).
Proof.
  intros ts toks dat stored_len last level dtype
         Hbwv Hl Hlevel Hbuf Henc Hntoks Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD
         Hdat Hsl0'.
  destruct (dispatch_counters ts toks Hol0 Hsl0 Hbl0 HFI Henc Hntoks HblZ
              HnnL HnnD)
    as (OL & SL & EOL & ESL & HOLr & HSLr & Hmbir & HmcLr & HmcDr
        & HgL & HgD & Hlen15L & Hlen15D & HnnL' & HnnD' & HLenBL
        & Hwtok & HeobW & HDYN & HSTA & _).
  pose proof (zbits_nonneg (ts_bw ts)) as Hzn.
  unfold tr_flush_block. cbv zeta.
  rewrite (proj2 (Z.ltb_lt 0 level) Hlevel).
  cbv iota.
  destruct (build_bl_tree (build_tree TK_D (build_tree TK_L ts)))
    as [mbi s2p] eqn:EP.
  cbn [fst snd].
  cbn [fst snd] in EOL, ESL, Hmbir, HmcLr, HmcDr, HgL, HgD, Hlen15L,
    Hlen15D, HnnL', HnnD', HLenBL, Hwtok, HeobW, HDYN, HSTA.
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
  (* the huffman-body bit costs *)
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
    (* nonneg pieces for the monotonicity clause *)
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
  (* --- the guard, and the two possible arm bodies --- *)
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
  destruct (Z.leb_spec (stored_len + 4) optlenb) as [Hg|Hg].
  - (* STORED arm chosen *)
    cbv iota.
    destruct (tr_stored_block_fits dat stored_len last s2p
                ltac:(rewrite Fbw; exact Hbwv) ltac:(symmetry; exact Hdat))
      as (Hal & Hstep & Hmono).
    set (s4 := tr_stored_block dat stored_len last s2p) in *.
    destruct (tr_stored_block_len dat stored_len last s2p
                ltac:(rewrite Fbw; exact Hbwv)) as (_ & Hval & Hwf).
    fold s4 in Hval, Hwf.
    rewrite Fbw in Hstep, Hmono.
    destruct (g6_flush_tail s4 last (8 * stored_len + 40) (ts_bw ts) Hl Hwf
                ltac:(lia) Hmono
                ltac:(rewrite Hal; lia)) as (T1 & T2 & T3 & T4).
    split; [exact T1|]. split; [lia|]. split; [exact T3 | exact T4].
  - (* huffman arm chosen: the stored guard FAILED, so optlenb <= stored_len + 3 *)
    cbv iota.
    assert (Hoptb : optlenb <= stored_len + 3) by lia.
    destruct (Z.eqb_spec SLB optlenb) as [Estat|Edyn].
    + (* STATIC arm *)
      cbn [ts_bw set_bw].
      destruct HstaticBody as (HsMono & HsB & HsV).
      set (b4 := compress_block (ts_symbuf s2p) (ts_symnext s2p)
                   static_ltree static_dtree
                   (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                      (ts_bw s2p))) in *.
      assert (Hstatb : SL <= 8 * stored_len + 21).
      { assert (SLB <= stored_len + 3) by lia. lia. }
      assert (Hmono4 : zbits (ts_bw ts) <= zbits (ts_bw (set_bw b4 s2p)))
        by (cbn [ts_bw set_bw]; exact HsMono).
      assert (Hstep4 : ceil8 (zbits (ts_bw (set_bw b4 s2p)))
                       <= ceil8 (zbits (ts_bw ts)) + (8 * stored_len + 40)).
      { cbn [ts_bw set_bw].
        eapply Z.le_trans; [apply ceil8_mono; exact HsB|].
        replace (zbits (ts_bw ts) + 3 + SL)
          with (zbits (ts_bw ts) + (3 + SL)) by ring.
        eapply Z.le_trans; [apply ceil8_add_le; lia|].
        assert (Hc : ceil8 (3 + SL) <= 3 + SL + 7)
          by (pose proof (ceil8_lt (3 + SL)); lia).
        lia. }
      destruct (g6_flush_tail (set_bw b4 s2p) last (8 * stored_len + 40)
                  (ts_bw ts) Hl ltac:(cbn [ts_bw set_bw]; exact HsV)
                  ltac:(lia) Hmono4 Hstep4) as (T1 & T2 & T3 & T4).
      split; [exact T1|]. split; [lia|]. split; [exact T3 | exact T4].
    + (* DYNAMIC arm *)
      cbn [ts_bw set_bw].
      destruct HdynBody as (HdMono & HdB & HdV).
      assert (Hdynb : OL <= 8 * stored_len + 21).
      { assert (Hob : optlenb = OLB).
        { unfold optlenb in *.
          destruct (Z.leb_spec SLB OLB) as [Hle|Hgt].
          - exfalso. apply Edyn. reflexivity.
          - reflexivity. }
        rewrite Hob in Hoptb. lia. }
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
                       <= ceil8 (zbits (ts_bw ts)) + (8 * stored_len + 40)).
      { cbn [ts_bw set_bw].
        eapply Z.le_trans; [apply ceil8_mono; exact HdB|].
        replace (zbits (ts_bw ts) + 3 + OL + 6)
          with (zbits (ts_bw ts) + (3 + OL + 6)) by ring.
        eapply Z.le_trans; [apply ceil8_add_le; lia|].
        assert (Hc : ceil8 (3 + OL + 6) <= 3 + OL + 6 + 7)
          by (pose proof (ceil8_lt (3 + OL + 6)); lia).
        lia. }
      destruct (g6_flush_tail (set_bw (dyn_bw last mbi s2p) s2p) last
                  (8 * stored_len + 40) (ts_bw ts) Hl
                  ltac:(cbn [ts_bw set_bw]; exact HdV)
                  ltac:(lia) Hmono4 Hstep4) as (T1 & T2 & T3 & T4).
      split; [exact T1|]. split; [lia|]. split; [exact T3 | exact T4].
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions compress_block_len_tok.
Print Assumptions tr_flush_block_len.
Unset Printing All.
