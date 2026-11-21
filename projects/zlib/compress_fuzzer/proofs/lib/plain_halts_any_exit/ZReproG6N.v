(** * ZReproG6N — the buf=None per-event budget (slow path, strategy 0).

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    THE GAP THIS CLOSES: [flush_block_only] passes [buf = None] when
    [block_start < 0] (a window slide crossed the block), so the stored
    fallback is unavailable and parts H/J's [8*stored_len + 40] budget —
    proved through the stored-guard arithmetic — does not cover the event.

    THE LEDGER (crc-capstone's LP, this file's integer dual): with the
    slow path's TOO_FAR filter, a tallied len-3 match has [dist <= 4096],
    so its static cost is at most 22 bits over 24; longer matches carry
    only more slack; only literals overrun, by at most 1 bit each.
    Per token: [2*cost <= 13*extent + 5], TIGHT at literals (18 = 18)
    and near len-3 matches (44 = 44).  Summed, with the memLevel-8 token
    cap [<= 16383] and the slide span floor [>= dg_max_dist + 1 = 32507],
    the whole static emission fits [8*span] with ~7800 bits to spare
    (threshold: span >= 27317) — so the block fits the SAME
    [8*span + 40] budget as the buf-present case, and the walk-side
    interface needs only the TOO_FAR fact and the slide span floor.

    Exhaustively pre-verified against the zlib tables (256 literals x
    every length/dist-class combination under the filter): zero
    violations, tightest row = near len-3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees DeflateSpec CbEmit CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BuildTree SendGo SendGoWf SendItems ClStream HuffCover ScanCount.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  BtFrame SwWin SwEv SwStep G3Event G3DynA ZReproG6A ZReproG6C ZReproG6D
  ZReproG6I ZReproG6K ZReproG6L ZReproG6F ZReproG6G ZReproG6H.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Token extent and the TOO_FAR predicate.
   ========================================================================== *)

(** Bytes of input a token covers: a literal one, a match its length. *)
Definition tok_ext (t : Tok) : Z :=
  match t with
  | TLit _ => 1
  | TMatch len _ => len
  end.

Fixpoint toks_ext (ts : list Tok) : Z :=
  match ts with
  | [] => 0
  | t :: r => tok_ext t + toks_ext r
  end.

(** The slow path's strategy-0 filter ([Deflate.v ds_body]): a len-3
    match farther than TOO_FAR is discarded before tallying. *)
Definition tok_far_ok (t : Tok) : Prop :=
  match t with
  | TLit _ => True
  | TMatch len dist => len = 3 -> dist <= TOO_FAR
  end.

Lemma tok_ext_pos : forall t, tok_enc t -> 1 <= tok_ext t.
Proof.
  intros t He. destruct t as [b | len dist]; cbn [tok_ext].
  - lia.
  - destruct He as [Hl _]. unfold MIN_MATCH in Hl. lia.
Qed.

Lemma toks_ext_nonneg : forall ts, cEnc ts -> 0 <= toks_ext ts.
Proof.
  induction ts as [|t r IH]; intro He; cbn [toks_ext].
  - lia.
  - inversion He as [|? ? Ht Hr]; subst.
    pose proof (tok_ext_pos t Ht). pose proof (IH Hr). lia.
Qed.

(* ==========================================================================
   2.  Resolve length: the token stream's extent IS the byte span.
       (Derives the extent equation from EvOk's resolve clause — no
       walk export needed.)
   ========================================================================== *)

Lemma g6n_copy_n_zlen : forall n dist out,
  zlen (copy_n n dist out) = zlen out + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros dist out; cbn [copy_n].
  - lia.
  - rewrite IH, g6_zlen_app, g6_zlen1. lia.
Qed.

Lemma resolve_length : forall toks pre post,
  cEnc toks ->
  resolve pre toks = Some post ->
  zlen post = zlen pre + toks_ext toks.
Proof.
  induction toks as [|t r IH]; intros pre post He Hres; cbn [resolve] in Hres.
  - injection Hres as <-. cbn [toks_ext]. lia.
  - inversion He as [|? ? Ht Hr]; subst.
    cbn [toks_ext].
    destruct t as [b | len dist]; cbn [resolve_tok] in Hres.
    + rewrite (IH _ _ Hr Hres), g6_zlen_app, g6_zlen1.
      cbn [tok_ext]. lia.
    + destruct ((1 <=? dist) && (dist <=? zlen pre)) eqn:Eg;
        [|discriminate Hres].
      rewrite (IH _ _ Hr Hres), g6n_copy_n_zlen.
      cbn [tok_ext].
      destruct Ht as [Hl _]. unfold MIN_MATCH, MAX_MATCH in Hl.
      rewrite Z2Nat.id by lia. lia.
Qed.

(* ==========================================================================
   3.  The per-token static-cost dual: 2*cost <= 13*extent + 5.
   ========================================================================== *)

(** Literals: at most 9 static bits (codes 144-255). *)
Definition g6n_lit_at (b : Z) : bool := t_len static_ltree b <=? 9.

Lemma g6n_lit_all : forallb g6n_lit_at (zseq 256 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** Static dtree: every code exactly 5 bits. *)
Definition g6n_d5_at (dc : Z) : bool := t_len static_dtree dc =? 5.

Lemma g6n_d5_all : forallb g6n_d5_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** Distance extras cap at 13. *)
Definition g6n_dex_at (dc : Z) : bool := extra_dbits dc <=? 13.

Lemma g6n_dex_all : forallb g6n_dex_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** A distance code with extra > 10 starts at base >= 4097 — so a
    TOO_FAR-filtered distance has extra <= 10. *)
Definition g6n_dfar_at (dc : Z) : bool :=
  (extra_dbits dc <=? 10) || (4097 <=? znth dist_base dc).

Lemma g6n_dfar_all : forallb g6n_dfar_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** Per length code c >= 1 (len >= 4): the whole match cost, at the
    WORST distance (5 + 13), fits 13 * (the code's minimum length) + 5;
    and that minimum is >= 4. *)
Definition g6n_len_at (c : Z) : bool :=
  if c =? 0 then true
  else (2 * (t_len static_ltree (c + LITERALS + 1) + extra_lbits c + 5 + 13)
          <=? 13 * znth length_base c + 5)
       && (4 <=? znth length_base c).

Lemma g6n_len_all : forallb g6n_len_at (zseq 29 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g6n_tok_bound : forall t,
  tok_enc t -> tok_far_ok t ->
  2 * tok_cost static_ltree static_dtree t <= 13 * tok_ext t + 5.
Proof.
  intros t He Hf. destruct t as [b | len dist].
  - (* literal: 2*9 <= 13 + 5, tight *)
    cbn [tok_cost tok_ext]. cbn [tok_enc] in He.
    pose proof (forallb_zseq' g6n_lit_at 256 256 b
                  ltac:(vm_compute; reflexivity) g6n_lit_all He) as H.
    unfold g6n_lit_at in H. apply Z.leb_le in H. lia.
  - cbn [tok_cost tok_ext]. cbn [tok_enc] in He. cbn [tok_far_ok] in Hf.
    destruct He as [Hlen Hdist].
    unfold MIN_MATCH, MAX_MATCH in Hlen.
    (* the distance side *)
    destruct (DcodeRange_all (dist - 1) ltac:(lia)) as (Hdc & Hdwin & _).
    set (dc := d_code (dist - 1)) in *.
    pose proof (forallb_zseq' g6n_d5_at 30 30 dc
                  ltac:(vm_compute; reflexivity) g6n_d5_all Hdc) as H5.
    unfold g6n_d5_at in H5. apply Z.eqb_eq in H5.
    pose proof (forallb_zseq' g6n_dex_at 30 30 dc
                  ltac:(vm_compute; reflexivity) g6n_dex_all Hdc) as H13.
    unfold g6n_dex_at in H13. apply Z.leb_le in H13.
    (* the length side *)
    destruct (lcode_range (len - 3) ltac:(lia)) as (Hlc & Hlwin & _).
    set (c := length_code (len - 3)) in *.
    destruct (Z.eqb_spec c 0) as [E0 | Ene].
    + (* code 0 covers exactly len = 3: the filter caps the distance *)
      rewrite E0 in Hlwin.
      change (znth length_base 0) with 3 in Hlwin.
      change (znth length_extra 0) with 0 in Hlwin.
      change (2 ^ 0) with 1 in Hlwin.
      assert (E3 : len = 3) by lia.
      assert (Hfar : dist <= 4096)
        by (apply Hf; exact E3).
      pose proof (forallb_zseq' g6n_dfar_at 30 30 dc
                    ltac:(vm_compute; reflexivity) g6n_dfar_all Hdc) as HF.
      unfold g6n_dfar_at in HF. apply orb_true_iff in HF.
      assert (H10 : extra_dbits dc <= 10).
      { destruct HF as [HF | HF]; apply Z.leb_le in HF; lia. }
      rewrite E0.
      change (t_len static_ltree (0 + LITERALS + 1)) with 7.
      change (extra_lbits 0) with 0.
      lia.
    + (* code >= 1: len >= base >= 4 and the worst-case row closes it *)
      assert (Hc1 : 1 <= c < 29) by lia.
      pose proof (forallb_zseq' g6n_len_at 29 29 c
                    ltac:(vm_compute; reflexivity) g6n_len_all
                    ltac:(lia)) as HL.
      unfold g6n_len_at in HL.
      replace (c =? 0) with false in HL
        by (symmetry; apply Z.eqb_neq; lia).
      apply andb_true_iff in HL as [HL1 HL2].
      apply Z.leb_le in HL1. apply Z.leb_le in HL2.
      lia.
Qed.

Theorem g6n_toks_bound : forall toks,
  cEnc toks ->
  Forall tok_far_ok toks ->
  2 * toks_cost static_ltree static_dtree toks
  <= 13 * toks_ext toks + 5 * Z.of_nat (length toks).
Proof.
  induction toks as [|t r IH]; intros He Hf.
  - cbn. lia.
  - inversion He as [|? ? Het Her]; subst.
    inversion Hf as [|? ? Hft Hfr]; subst.
    cbn [toks_cost toks_ext length].
    pose proof (g6n_tok_bound t Het Hft).
    pose proof (IH Her Hfr).
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* ==========================================================================
   4.  The H-sibling: one buf=None flush fits the SAME budget.
   ========================================================================== *)

Theorem tr_flush_block_len_none : forall ts toks slen last level dtype,
  bwv (ts_bw ts) ->
  last = 0 \/ last = 1 ->
  0 < level ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  Forall tok_far_ok toks ->
  toks_ext toks = slen ->
  32506 < slen ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  let ts' := snd (tr_flush_block None slen last level 0 dtype ts) in
  zbits (ts_bw ts) <= zbits (ts_bw ts')
  /\ ceil8 (zbits (ts_bw ts'))
     <= ceil8 (zbits (ts_bw ts)) + 8 * slen + 40
  /\ bwv (ts_bw ts')
  /\ (last = 1 -> bw_valid (ts_bw ts') = 0).
Proof.
  intros ts toks slen last level dtype
         Hbwv Hl Hlevel Hbuf Henc Hntoks Hfar Hext Hsld
         Hol0 Hsl0 Hbl0 HFI HblZ HnnL HnnD.
  destruct (dispatch_counters ts toks Hol0 Hsl0 Hbl0 HFI Henc Hntoks HblZ
              HnnL HnnD)
    as (OL & SL & EOL & ESL & HOLr & HSLr & Hmbir & HmcLr & HmcDr
        & HgL & HgD & Hlen15L & Hlen15D & HnnL' & HnnD' & HLenBL
        & Hwtok & HeobW & HDYN & HSTA & HSLup).
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
  (* THE LEDGER: the static counter is under the per-token budget *)
  assert (Hcost2 : 2 * toks_cost static_ltree static_dtree toks
                   <= 13 * slen + 5 * 16383).
  { pose proof (g6n_toks_bound toks Henc Hfar) as HB.
    rewrite Hext in HB. lia. }
  assert (Heob : 0 <= t_len static_ltree END_BLOCK <= 15).
  { unfold END_BLOCK. apply static_ltree_LenB. lia. }
  assert (Hstatb : SL <= 8 * slen + 21) by lia.
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
  + (* STATIC arm *)
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
      lia. }
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
   5.  The J-sibling: the per-EVENT budget at a NEGATIVE block start.
   ========================================================================== *)

Theorem flush_block_only_acct_none : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g ->
  dg_strategy g = 0 ->
  dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  ls_blockstart (d_ls (fe_s ev)) < 0 ->
  Forall tok_far_ok (fe_toks ev) ->
  32506 < fe_end ev - fe_start ev ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
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
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hbs Hfar Hsld
         Hol0 Hsl0 Hbl0 HblZ HnnL HnnD s'.
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
  assert (Hext' : toks_ext (fe_toks ev) = slen).
  { rewrite Hext0. unfold slen, bs, l. exact Hspan_eq. }
  set (r := tr_flush_block None slen (fe_last ev) (dg_level (d_cfg s))
              0 (zs_datatype (d_strm s)) (d_ts s)) in *.
  destruct (tr_flush_block_len_none (d_ts s) (fe_toks ev) slen (fe_last ev)
              (dg_level (d_cfg s)) (zs_datatype (d_strm s))
              Hbwv ltac:(lia) Hlevg Hbuf Henc Hlen Hfar Hext'
              ltac:(lia)
              Hol0 Hsl0 Hbl0 Hfreq HblZ HnnL HnnD)
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
  assert (Hspan2 : fe_end ev - fe_start ev = slen)
    by (unfold slen, bs, l; exact Hspan_eq).
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
   6.  The dichotomy wrapper: the blockstart premise goes INTERNAL.
   ========================================================================== *)

Theorem flush_from_acct_full : forall g wrap done ev,
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
  Forall tok_far_ok (fe_toks ev) ->
  (ls_blockstart (d_ls (fe_s ev)) < 0 -> 32506 < fe_end ev - fe_start ev) ->
  EvStepBudget ev.
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hol Hsl Hbl
         HblZ HnnL HnnD Hfar Hsld.
  destruct (Z.le_gt_cases 0 (ls_blockstart (d_ls (fe_s ev)))) as [Hge|Hlt].
  - exact (flush_from_acct g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo
             Hge Hol Hsl Hbl HblZ HnnL HnnD).
  - destruct (flush_block_only_acct_none g wrap done ev HE Hlev Hstrat Hsend
                Hbwv Havo Hlt Hfar (Hsld Hlt) Hol Hsl Hbl HblZ HnnL HnnD)
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

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions resolve_length.
Print Assumptions g6n_toks_bound.
Print Assumptions tr_flush_block_len_none.
Print Assumptions flush_block_only_acct_none.
Print Assumptions flush_from_acct_full.
Unset Printing All.
