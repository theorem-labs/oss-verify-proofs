(** * SwTally — the slow-path walk, part W3a: geometry pack, the rolling
      hash, token/frequency bookkeeping of the tally macros, and the two
      per-state predicates the lazy loop carries ([SyncOK], [MatchCand]).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3 of the Q5
    plan; design in WALK-DESIGN.md.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHAT LIVES HERE.
      * [GeomOk2]: SwWin's [GeomOk] extended with exactly the section
        hypotheses CresChain's discharged lemmas take (powers of two, masks,
        the hash-shift cover).  All four z-repro configs satisfy it at
        (wbits, hbits) = (15, 15), by computation through [defl_init2].
      * [h3_roll]: the rolling-hash identity, an instance of CresChain's
        [update_hash_forget].  This is what re-establishes [SyncOK] after
        each insert.
      * [count_L]/[count_D] + [FreqInv]: the tally macros bump exactly the
        frequency of the token they append.  [FreqInv] quantifies ONLY over
        the C-cleared ranges [0, L_CODES) / [0, D_CODES): the slots above
        hold [build_tree]'s internal-node leftovers between blocks
        (Trees.v §5's comment), and nothing reads them before writing.
        This is the freq half of the G1 interface
        (G1-INTERFACE.md, "SETTING").
      * [tr_tally_lit_step]/[tr_tally_dist_step]: the full effect of one
        tally — the [BufToks] snoc, the frequency bump, the flush flag, and
        the frame of everything untouched.
      * [SyncOK]/[MatchCand]: the [ins_h] synchronisation and the deferred
        lazy-match candidate, in INPUT coordinates (slide-stable). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Huff DeflateSpec ZBitsOut Trees Deflate CbEmit CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import SwWin.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac tsimp :=
  cbn [ts_trees ts_maxcode ts_blcount ts_heap ts_heaplen ts_heapmax ts_depth
       ts_symbuf ts_symnext ts_optlen ts_statlen ts_matches ts_bw
       set_trees set_maxcode set_blcount set_heap set_heaplen set_heapmax
       set_depth set_symbuf set_symnext set_optlen set_statlen set_matches
       set_bw set_tree set_max
       t_freq t_setfreq tr_fc tr_dl fst snd].

(** ** 1. The geometry pack *)

Record GeomOk2 (g : DeflGeom) (wbits hbits : Z) : Prop := mkGeomOk2 {
  g2_geom  : GeomOk g;
  g2_wb0   : 0 <= wbits;
  g2_hb0   : 0 <= hbits;
  g2_hb8   : 8 <= hbits;
  g2_ws    : dg_w_size g = 2 ^ wbits;
  g2_wm    : dg_w_mask g = dg_w_size g - 1;
  g2_hs    : dg_hash_size g = 2 ^ hbits;
  g2_hm    : dg_hash_mask g = dg_hash_size g - 1;
  g2_sh0   : 0 <= dg_hash_shift g;
  g2_cover : hbits <= 3 * dg_hash_shift g;
  g2_u16   : 2 * dg_w_size g <= 65536;
  (* the sym_buf capacity: a 3-multiple (the flush flag tests EQUALITY, so
     a non-multiple would let symnext step past it), small enough that the
     u16-truncated frequencies are exact *)
  g2_se_lo  : 3 <= dg_sym_end g;
  g2_se_hi  : dg_sym_end g <= 196599;
  g2_se_mod : (dg_sym_end g) mod 3 = 0
}.

(** All four z-repro configs, through [defl_init2], at (15, 15). *)
Example swtally_geom2_zr :
  match defl_init2 (-1) 8 15 8 0, defl_init2 1 8 (-15) 8 0,
        defl_init2 9 8 31 8 0, defl_init2 0 8 15 8 0 with
  | Some g1, Some g2, Some g3, Some g4 =>
      GeomOk2 g1 15 15 /\ GeomOk2 g2 15 15
      /\ GeomOk2 g3 15 15 /\ GeomOk2 g4 15 15
  | _, _, _, _ => False
  end.
Proof.
  vm_compute.
  repeat split; vm_compute;
    first [reflexivity | intros H; discriminate H].
Qed.

(** ** 2. The rolling hash *)

Lemma h3_roll : forall g wbits hbits w p,
  GeomOk2 g wbits hbits ->
  update_hash g (h3 g w p) (w (p + 3)) = h3 g w (p + 1).
Proof.
  intros g wbits hbits w p Hg.
  unfold h3.
  replace (p + 1 + 1) with (p + 2) by lia.
  replace (p + 1 + 2) with (p + 3) by lia.
  apply (update_hash_forget g hbits (g2_hb0 _ _ _ Hg) (g2_sh0 _ _ _ Hg)).
  - rewrite (g2_hm _ _ _ Hg), (g2_hs _ _ _ Hg). reflexivity.
  - exact (g2_cover _ _ _ Hg).
Qed.

(** ** 3. Token counting and the frequency invariant *)

Fixpoint count_L (i : Z) (toks : list Tok) : Z :=
  match toks with
  | [] => 0
  | TLit b :: r =>
      (if Z.eqb b i then 1 else 0) + count_L i r
  | TMatch len dist :: r =>
      (if Z.eqb (length_code (len - 3) + LITERALS + 1) i then 1 else 0)
      + count_L i r
  end.

Fixpoint count_D (i : Z) (toks : list Tok) : Z :=
  match toks with
  | [] => 0
  | TLit _ :: r => count_D i r
  | TMatch len dist :: r =>
      (if Z.eqb (d_code (dist - 1)) i then 1 else 0) + count_D i r
  end.

Lemma count_L_app : forall i t1 t2,
  count_L i (t1 ++ t2) = count_L i t1 + count_L i t2.
Proof.
  intros i t1 t2. induction t1 as [|[b|len dist] r IH]; cbn [count_L app];
    lia.
Qed.

Lemma count_D_app : forall i t1 t2,
  count_D i (t1 ++ t2) = count_D i t1 + count_D i t2.
Proof.
  intros i t1 t2. induction t1 as [|[b|len dist] r IH]; cbn [count_D app];
    lia.
Qed.

Lemma count_L_nonneg : forall i toks, 0 <= count_L i toks.
Proof.
  intros i toks. induction toks as [|[b|len dist] r IH]; cbn [count_L];
    try destruct (Z.eqb _ i); lia.
Qed.

Lemma count_D_nonneg : forall i toks, 0 <= count_D i toks.
Proof.
  intros i toks. induction toks as [|[b|len dist] r IH]; cbn [count_D];
    try destruct (Z.eqb _ i); lia.
Qed.

Lemma count_L_le_len : forall i toks,
  count_L i toks <= Z.of_nat (length toks).
Proof.
  intros i toks. induction toks as [|[b|len dist] r IH];
    cbn [count_L length]; try destruct (Z.eqb _ i); lia.
Qed.

Lemma count_D_le_len : forall i toks,
  count_D i toks <= Z.of_nat (length toks).
Proof.
  intros i toks. induction toks as [|[b|len dist] r IH];
    cbn [count_D length]; try destruct (Z.eqb _ i); lia.
Qed.

(** The tally macros bump only in-range indices; [FreqInv] therefore
    characterises exactly the C-cleared ranges.  Frequencies pass through
    [u16] at every write ([t_setfreq], zlib's [ush] slot), so the invariant
    is honest only while the token count stays far below 65535 — the walk
    carries [symnext <= sym_end = 49149], comfortably inside. *)
Definition FreqInv (toks : list Tok) (ts : TSt) : Prop :=
  (forall i, 0 <= i < L_CODES ->
     t_freq (ts_trees ts TK_L) i
     = count_L i toks + (if Z.eqb i END_BLOCK then 1 else 0))
  /\ (forall i, 0 <= i < D_CODES ->
     t_freq (ts_trees ts TK_D) i = count_D i toks).

Lemma tree_zero_freq_spec : forall n i0 t j,
  t_freq (tree_zero_freq n i0 t) j
  = if (Z.leb i0 j) && (Z.ltb j (i0 + Z.of_nat n))
    then 0 else t_freq t j.
Proof.
  induction n as [|n IH]; intros i0 t j; cbn [tree_zero_freq].
  - destruct (Z.leb_spec i0 j) as [H1|H1];
      destruct (Z.ltb_spec j (i0 + Z.of_nat 0)) as [H2|H2];
      cbn [andb]; try reflexivity; lia.
  - rewrite IH.
    destruct (Z.eq_dec j i0) as [->|Hne].
    + destruct (Z.leb_spec (i0 + 1) i0) as [H1|H1]; [lia|].
      destruct (Z.ltb_spec i0 (i0 + 1 + Z.of_nat n)) as [H2|H2]; [|lia].
      cbn [andb].
      destruct (Z.leb_spec i0 i0) as [H3|H3]; [|lia].
      destruct (Z.ltb_spec i0 (i0 + Z.of_nat (S n))) as [H4|H4]; [|lia].
      cbn [andb].
      unfold t_setfreq, t_freq. cbn [tr_fc].
      now rewrite zset_same.
    + assert (Hz : t_freq (t_setfreq t i0 0) j = t_freq t j).
      { unfold t_setfreq, t_freq. cbn [tr_fc].
        now rewrite zset_other by lia. }
      rewrite Hz.
      destruct (Z.leb_spec (i0 + 1) j) as [H1|H1];
        destruct (Z.ltb_spec j (i0 + 1 + Z.of_nat n)) as [H2|H2];
        destruct (Z.leb_spec i0 j) as [H3|H3];
        destruct (Z.ltb_spec j (i0 + Z.of_nat (S n))) as [H4|H4];
        cbn [andb]; try reflexivity; lia.
Qed.

(** [init_block] establishes the invariant for the empty token list. *)
Lemma freqinv_init_block : forall ts, FreqInv [] (init_block ts).
Proof.
  intros ts. unfold init_block. cbv zeta.
  split; intros i Hi; tsimp.
  - (* TK_L: two set_tree layers above it (TK_D, TK_BL), then the write *)
    unfold TK_BL, TK_D, TK_L in *. cbn [Z.eqb Pos.eqb].
    unfold t_setfreq, t_freq. cbn [tr_fc].
    destruct (Z.eq_dec i END_BLOCK) as [->|Hne].
    + rewrite zset_same.
      unfold END_BLOCK. cbn [Z.eqb Pos.eqb count_L]. reflexivity.
    + rewrite zset_other by congruence.
      change (t_freq (tree_zero_freq (Z.to_nat L_CODES) 0 (ts_trees ts 0)) i)
        with (t_freq (tree_zero_freq (Z.to_nat L_CODES) 0 (ts_trees ts 0)) i).
      rewrite tree_zero_freq_spec.
      replace ((0 <=? i) && (i <? 0 + Z.of_nat (Z.to_nat L_CODES)))
        with true
        by (symmetry; apply andb_true_iff; split;
            [apply Z.leb_le; lia
            | apply Z.ltb_lt; unfold L_CODES in *; lia]).
      cbn [count_L].
      replace (Z.eqb i END_BLOCK) with false
        by (symmetry; apply Z.eqb_neq; exact Hne).
      reflexivity.
  - unfold TK_BL, TK_D, TK_L in *. cbn [Z.eqb Pos.eqb].
    rewrite tree_zero_freq_spec.
    replace ((0 <=? i) && (i <? 0 + Z.of_nat (Z.to_nat D_CODES)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia
          | apply Z.ltb_lt; unfold D_CODES in *; lia]).
    reflexivity.
Qed.

(** ** 4. What everything else in [TSt] does across a tally: nothing *)

Definition TallyFrame (ts ts' : TSt) : Prop :=
  ts_trees ts' TK_BL = ts_trees ts TK_BL
  /\ ts_maxcode ts' = ts_maxcode ts
  /\ ts_blcount ts' = ts_blcount ts
  /\ ts_heap ts' = ts_heap ts
  /\ ts_heaplen ts' = ts_heaplen ts
  /\ ts_heapmax ts' = ts_heapmax ts
  /\ ts_depth ts' = ts_depth ts
  /\ ts_optlen ts' = ts_optlen ts
  /\ ts_statlen ts' = ts_statlen ts
  /\ ts_matches ts' = ts_matches ts
  /\ ts_bw ts' = ts_bw ts.

(** ** 5. The two tally steps *)

Lemma tr_tally_lit_step : forall c sym_end ts toks,
  0 <= ts_symnext ts ->
  Z.of_nat (length toks) <= 65533 ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  FreqInv toks ts ->
  BufToks (ts_symbuf (snd (tr_tally_lit c sym_end ts))) 0
          (ts_symnext (snd (tr_tally_lit c sym_end ts)))
          (toks ++ [TLit (u8 c)])
  /\ ts_symnext (snd (tr_tally_lit c sym_end ts)) = ts_symnext ts + 3
  /\ FreqInv (toks ++ [TLit (u8 c)]) (snd (tr_tally_lit c sym_end ts))
  /\ fst (tr_tally_lit c sym_end ts) = Z.eqb (ts_symnext ts + 3) sym_end
  /\ TallyFrame ts (snd (tr_tally_lit c sym_end ts)).
Proof.
  intros c sym_end ts toks Hsn Hlen Hbuf [HfL HfD].
  unfold t_freq, TK_L, TK_D in HfL, HfD.
  assert (Hu8 : 0 <= u8 c < 256)
    by (unfold u8; apply Z.mod_pos_bound; lia).
  unfold tr_tally_lit. cbv zeta. tsimp.
  set (sn := ts_symnext ts) in *.
  set (sb' := zset (zset (zset (ts_symbuf ts) sn 0) (sn + 1) 0)
                (sn + 2) (u8 c)).
  assert (Hagree : forall i, 0 <= i < sn -> sb' i = ts_symbuf ts i).
  { intros i Hi. unfold sb'. rewrite !zset_other by lia. reflexivity. }
  assert (Htok : tok_at sb' sn = TLit (u8 c)).
  { unfold tok_at, cb_dist, cb_lc, sb'.
    rewrite (zset_other _ (sn + 2) _ (sn + 1)) by lia.
    rewrite (zset_same _ (sn + 1)).
    rewrite (zset_other _ (sn + 2) _ sn) by lia.
    rewrite (zset_other _ (sn + 1) _ sn) by lia.
    rewrite (zset_same _ sn).
    cbn [Z.land].
    rewrite zset_same.
    reflexivity. }
  repeat split.
  - (* BufToks *)
    rewrite <- Htok.
    apply buftoks_snoc.
    apply (buftoks_stable (ts_symbuf ts)); [exact Hbuf|].
    intros i Hi. apply Hagree. lia.
  - (* FreqInv, L side *)
    intros i Hi. tsimp.
    unfold TK_L. cbn [Z.eqb Pos.eqb].
    unfold t_setfreq, t_freq. cbn [tr_fc].
    rewrite count_L_app. cbn [count_L].
    destruct (Z.eq_dec (u8 c) i) as [E|Hne].
    + rewrite E, zset_same, (HfL i Hi), Z.eqb_refl.
      pose proof (count_L_nonneg i toks).
      pose proof (count_L_le_len i toks).
      destruct (Z.eqb i END_BLOCK); rewrite u16_id by lia; lia.
    + rewrite zset_other by congruence.
      rewrite (HfL i Hi).
      replace (Z.eqb (u8 c) i) with false
        by (symmetry; apply Z.eqb_neq; exact Hne).
      lia.
  - (* FreqInv, D side: TK_D untouched *)
    intros i Hi. tsimp.
    unfold TK_D, TK_L. cbn [Z.eqb Pos.eqb].
    rewrite count_D_app. cbn [count_D].
    unfold t_freq.
    rewrite (HfD i Hi). lia.
Qed.

Lemma tr_tally_dist_step : forall distance length0 sym_end ts toks,
  0 <= ts_symnext ts ->
  Z.of_nat (length toks) <= 65533 ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  FreqInv toks ts ->
  1 <= u16 distance ->
  BufToks (ts_symbuf (snd (tr_tally_dist distance length0 sym_end ts))) 0
          (ts_symnext (snd (tr_tally_dist distance length0 sym_end ts)))
          (toks ++ [TMatch (u8 length0 + 3) (u16 distance)])
  /\ ts_symnext (snd (tr_tally_dist distance length0 sym_end ts))
       = ts_symnext ts + 3
  /\ FreqInv (toks ++ [TMatch (u8 length0 + 3) (u16 distance)])
             (snd (tr_tally_dist distance length0 sym_end ts))
  /\ fst (tr_tally_dist distance length0 sym_end ts)
       = Z.eqb (ts_symnext ts + 3) sym_end
  /\ TallyFrame ts (snd (tr_tally_dist distance length0 sym_end ts)).
Proof.
  intros distance length0 sym_end ts toks Hsn Hlen Hbuf [HfL HfD] Hd1.
  unfold t_freq, TK_L, TK_D in HfL, HfD.
  assert (Hu8 : 0 <= u8 length0 < 256)
    by (unfold u8; apply Z.mod_pos_bound; lia).
  assert (Hu16 : 0 <= u16 distance < 65536)
    by (unfold u16; apply Z.mod_pos_bound; lia).
  unfold tr_tally_dist. cbv zeta. tsimp.
  set (sn := ts_symnext ts) in *.
  set (dd := u16 distance) in *.
  set (sb' := zset (zset (zset (ts_symbuf ts) sn (u8 dd))
                     (sn + 1) (u8 (Z.shiftr dd 8)))
                (sn + 2) (u8 length0)).
  assert (Hlow : Z.land (u8 dd) 255 = dd mod 256).
  { unfold u8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    now rewrite Z.mod_mod by lia. }
  assert (Hhigh : Z.land (u8 (Z.shiftr dd 8)) 255 = dd / 256).
  { unfold u8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    rewrite Z.mod_mod by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 8) with 256.
    apply Z.mod_small.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hre : Z.land (u8 dd) 255
                + Z.shiftl (Z.land (u8 (Z.shiftr dd 8)) 255) 8 = dd).
  { rewrite Hlow, Hhigh, Z.shiftl_mul_pow2 by lia.
    change (2 ^ 8) with 256.
    pose proof (Z_div_mod_eq_full dd 256). lia. }
  assert (Hagree : forall i, 0 <= i < sn -> sb' i = ts_symbuf ts i).
  { intros i Hi. unfold sb'. rewrite !zset_other by lia. reflexivity. }
  assert (Htok : tok_at sb' sn = TMatch (u8 length0 + 3) dd).
  { unfold tok_at, cb_dist, cb_lc, sb'.
    rewrite (zset_other _ (sn + 2) _ (sn + 1)) by lia.
    rewrite (zset_same _ (sn + 1)).
    rewrite (zset_other _ (sn + 2) _ sn) by lia.
    rewrite (zset_other _ (sn + 1) _ sn) by lia.
    rewrite (zset_same _ sn).
    rewrite zset_same.
    rewrite Hre.
    replace (Z.eqb dd 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    reflexivity. }
  repeat split.
  - rewrite <- Htok.
    apply buftoks_snoc.
    apply (buftoks_stable (ts_symbuf ts)); [exact Hbuf|].
    intros i Hi. apply Hagree. lia.
  - (* FreqInv, L side: index length_code(len) + 257 *)
    intros i Hi. tsimp.
    unfold TK_D, TK_L. cbn [Z.eqb Pos.eqb].
    unfold t_setfreq, t_freq. cbn [tr_fc].
    rewrite count_L_app. cbn [count_L].
    replace (u8 length0 + 3 - 3) with (u8 length0) by lia.
    destruct (Z.eq_dec (length_code (u8 length0) + LITERALS + 1) i)
      as [E|Hne].
    + rewrite E, zset_same, (HfL i Hi), Z.eqb_refl.
      pose proof (count_L_nonneg i toks).
      pose proof (count_L_le_len i toks).
      destruct (Z.eqb i END_BLOCK); rewrite u16_id by lia; lia.
    + rewrite zset_other by congruence.
      rewrite (HfL i Hi).
      replace (Z.eqb (length_code (u8 length0) + LITERALS + 1) i) with false
        by (symmetry; apply Z.eqb_neq; exact Hne).
      lia.
  - (* FreqInv, D side: index d_code (dist - 1) *)
    intros i Hi. tsimp.
    unfold TK_D, TK_L. cbn [Z.eqb Pos.eqb].
    unfold t_setfreq, t_freq. cbn [tr_fc].
    rewrite count_D_app. cbn [count_D].
    destruct (Z.eq_dec (d_code (dd - 1)) i) as [E|Hne].
    + rewrite E, zset_same, (HfD i Hi), Z.eqb_refl.
      pose proof (count_D_nonneg i toks).
      pose proof (count_D_le_len i toks).
      rewrite u16_id by lia. lia.
    + rewrite zset_other by congruence.
      rewrite (HfD i Hi).
      replace (Z.eqb (d_code (dd - 1)) i) with false
        by (symmetry; apply Z.eqb_neq; exact Hne).
      lia.
Qed.

(** ** 6. The two lazy-loop predicates (design doc C3 and M) *)

(** [ins_h] is synchronised with [strstart] whenever the loop is entitled to
    use it: the pending-insert counter is drained and three bytes of
    lookahead exist.  Everywhere else the loop never reads it. *)
Definition SyncOK (g : DeflGeom) (l : LSt) : Prop :=
  ls_insert l = 0 -> MIN_MATCH <= ls_lookahead l ->
  update_hash g (ls_insh l) (ls_window l (ls_strstart l + 2))
  = h3 g (ls_window l) (ls_strstart l).

(** The deferred lazy candidate, in INPUT coordinates so that a window slide
    (which moves [matchstart] and [strstart] together, SwWin's [StepPres])
    preserves it verbatim.  [done] is [zs_done] — the consumed input. *)
Definition MatchCand (g : DeflGeom) (slid : Z) (l : LSt) (done : list Z)
  : Prop :=
  MIN_MATCH <= ls_matchlen l ->
  ls_matchavail l = 1
  /\ 0 <= slid + ls_matchstart l
  /\ 1 <= ls_strstart l - 1 - ls_matchstart l <= dg_max_dist g
  /\ ls_matchlen l <= MAX_MATCH
  /\ ls_matchlen l <= ls_lookahead l + 1
  /\ (forall k, 0 <= k < ls_matchlen l ->
        nth (Z.to_nat (slid + ls_matchstart l + k)) done 0
        = nth (Z.to_nat (slid + (ls_strstart l - 1) + k)) done 0).

Print Assumptions tr_tally_lit_step.
Print Assumptions tr_tally_dist_step.
Print Assumptions h3_roll.
