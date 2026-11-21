(** * BuildChain — the composition, written out: from "positive frequency" to
      "code length in [1, max_length]" across all of [build_tree]'s stages.

    OWNER: huffman-id.  The step I twice reported as remaining.

    WHY IT IS WRITTEN AS A SHAPE LEMMA.  Every stage is taken as a parameter with
    its defining equation, and the final state [s1] is described by its THREE
    RELEVANT PROJECTIONS ([ts_trees], [ts_heap], [ts_heapmax]) rather than by
    [build_tree]'s stack of eight record setters.  That decouples the composition
    from the setter stack completely: instantiating it for [build_tree] is then
    three projection facts, not one giant unfold.  The same shape worked for
    [BtStep.step_shape_covers], and for the same reason — it makes every index
    side condition explicit instead of burying it in a [cbv zeta] normal form.

    WHAT THIS BUYS.  Writing the composition is what found both real gaps in this
    layer (the leftover-is-the-root gap, and the global-[LenBound] gap that
    GbRange.v fixes).  So this file is not bookkeeping: it is the check that the
    pieces actually meet, and it is the third time I have run it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes GenBitlen BtCover PqDown BtForce2 BtStep BtRoot GbVisit GbRange.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [t_dad] and [t_len] alias the same [tr_dl] slot.  This is the ONLY property of the tree
    the range theorem needs (see GbRange.v).

    CORRECTED 2026-08-19, by kraftsum's census, and the correction matters because a consumer
    read my earlier prose as making [DlNn] free.  It said nonnegativity holds "because every
    write into [tr_dl] is a [u16]".  That is HALF the reason.  Censusing every writer of
    [tr_dl] in [Trees.v] gives FOUR ingredients and only two are about masking:

      tzero               (:217)      [tr_dl = zzero]                   all zeros
      t_setfreq/t_setcode (:227/229)  [tr_dl] passed THROUGH             a FRAME fact, not u16
      t_setdad/t_setlen   (:231/233)  [zset (tr_dl t) i (u16 v)]         the u16 argument
      static_ltree/dtree  (:235/236)  [mkTree _ (zlist static_*_len)]    LITERAL DATA

    The two static trees are LITERAL DATA, so their nonnegativity is a COMPUTATION rather than
    a consequence of masking — [forallb (Z.leb 0)] over [static_ltree_len]'s 288 entries and
    [static_dtree_len]'s 30, both true, measured by kraftsum.  So the conclusion stood and the
    stated reason covered half of it.

    The [u16] half is meanwhile STRONGER than the old prose claimed: [u16 (-1) = 65535], so
    [dl_setlen] and [dl_setdad] below need no hypothesis on [v] at all — which is why their
    proofs discharge by [Z.mod_pos_bound] with no side condition. The lemmas were already
    unconditional; only the prose undersold them.

    DISCHARGED, not merely explained: kraftsum's [KraftDlNn] proves [DlNnSt ts_new] outright
    (at the fresh state [ts_trees] is [fun _ => tzero]) plus [DlNnSt s -> DlNn t ->
    DlNnSt (set_tree k t s)] as the per-[set_tree] step, so [BtItem4.item4_L_positive]'s entry
    premise is closed at [ts_new] and carried by that step. Their file, not this one. *)
Definition DlNn (t : Tree) : Prop := forall i, 0 <= t_len t i.

Lemma dl_setlen : forall t i v, DlNn t -> DlNn (t_setlen t i v).
Proof.
  intros t i v H j. destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite t_len_setlen_same'. unfold u16. apply Z.mod_pos_bound. lia.
  - rewrite t_len_setlen_other' by exact Hne. apply H.
Qed.

Lemma dl_setfreq : forall t i v j, t_len (t_setfreq t i v) j = t_len t j.
Proof. intros. reflexivity. Qed.

(** ** Nonnegativity across the three tree-mutating stages *)

Lemma bt_init_dl : forall fuel n elems t hp dep hlen maxc,
  DlNn t ->
  match bt_init fuel n elems t hp dep hlen maxc with
  | (t', _, _, _, _) => DlNn t'
  end.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc H.
  - cbn [bt_init]. exact H.
  - cbn [bt_init].
    destruct (Z.leb elems n); [exact H|].
    destruct (Z.eqb (t_freq t n) 0).
    + apply IH. apply dl_setlen. exact H.
    + apply IH. exact H.
Qed.

Lemma bt_force2_dl : forall fuel stree t hp dep hlen maxc ol sl,
  DlNn t ->
  match bt_force2 fuel stree t hp dep hlen maxc ol sl with
  | (t', _, _, _, _, _, _) => DlNn t'
  end.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl H.
  - cbn [bt_force2]. exact H.
  - cbn [bt_force2].
    destruct (Z.leb 2 hlen); [exact H|].
    apply IH. intro j. rewrite dl_setfreq. apply H.
Qed.

Lemma bt_step_dl : forall st st',
  DlNn (b_tree st) ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  DlNn (b_tree st').
Proof.
  intros st st' H Hst.
  unfold bt_step in Hst. cbv zeta in Hst.
  destruct (Z.leb 2 (b_hlen st - 1));
    destruct Hst as [Hst|Hst]; try discriminate;
    inversion Hst; subst; cbn [b_tree];
    apply dl_setlen; apply dl_setlen; intro j; rewrite dl_setfreq; apply H.
Qed.

Lemma bt_loop_dl : forall fuel st,
  DlNn (b_tree st) ->
  match bt_loop fuel st with
  | Some stf => DlNn (b_tree stf)
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st H.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + apply IH. exact (bt_step_dl st st' H (or_introl Est)).
    + exact (bt_step_dl st st' H (or_intror Est)).
Qed.

(** ** The gap invariant survives to the exit state

    Needed only for [0 <= heap_max - 1], which [gen_bitlen] wants.  It comes free
    from [BtStep.bt_step_gap]. *)
Lemma bt_loop_gap_out : forall fuel st,
  2 <= b_hlen st -> Gap st ->
  match bt_loop fuel st with
  | Some stf => Gap stf
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st Hlen Hgap.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (left; exact Est).
      apply IH; [| exact (bt_step_gap st st' Hlen Hgap Hor)].
      unfold bt_step in Est. cbv zeta in Est.
      destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [|discriminate].
      apply Z.leb_le in E2. inversion Est. subst. cbn [b_hlen]. lia.
    + exact (bt_step_gap st st' Hlen Hgap (or_intror Est)).
Qed.

(** ** THE COMPOSITION

    [s1] is given by its three relevant projections, so the eight record setters
    in [build_tree]'s tail never appear.  [fuelinit] is left general because
    [build_tree] calls [bt_init] at [Z.to_nat L_CODES + 2], not at the specialised
    fuel of [BtCover.bt_init_covers_all]. *)
Theorem build_chain :
  forall k s s0 fuelinit t0 hp0 dep0 hlen0 maxc0
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1 hp2 stf s1,
  1 <= sd_max_length k <= 15 ->
  DlNn (ts_trees s k) ->
  0 <= s0 < sd_elems k ->
  t_freq (ts_trees s k) s0 <> 0 ->
  sd_elems k <= Z.of_nat fuelinit ->
  bt_init fuelinit 0 (sd_elems k) (ts_trees s k) (ts_heap s) (ts_depth s) 0 (-1)
    = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  2 <= hlen1 -> hlen1 <= L_CODES ->
  hp2 = bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1; b_heap := hp2; b_dep := dep1;
             b_hlen := hlen1; b_hmax := HEAP_SIZE; b_node := sd_elems k |}
    = Some stf ->
  ts_trees s1 k = b_tree stf ->
  ts_heap s1 = zset (b_heap stf) (b_hmax stf - 1) (b_heap stf SMALLEST) ->
  ts_heapmax s1 = b_hmax stf - 1 ->
  1 <= t_len (ts_trees (gen_bitlen k s1) k) s0 <= sd_max_length k.
Proof.
  intros k s s0 fuelinit t0 hp0 dep0 hlen0 maxc0
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1 hp2 stf s1
         Hm Hnn Hs0 Hfr Hfuel E0 E2 Hl2 HlL Ehp2 Eloop Etr Ehp Ehm.

  (* stage 1: bt_init covers, and keeps the length array nonnegative *)
  pose proof (bt_init_covers fuelinit 0 (sd_elems k) (ts_trees s k)
                (ts_heap s) (ts_depth s) 0 (-1)) as Hc0.
  pose proof (bt_init_dl fuelinit 0 (sd_elems k) (ts_trees s k)
                (ts_heap s) (ts_depth s) 0 (-1) Hnn) as Hd0.
  rewrite E0 in Hc0, Hd0.
  destruct Hc0 as [Hcov0 [_ Hmono0]]; [lia | lia |].
  assert (Hin0 : InHeap hp0 1 hlen0 s0) by (apply Hcov0; [lia | exact Hfr]).

  (* stage 2: bt_force2 keeps membership and nonnegativity *)
  pose proof (bt_force2_preserves 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                (ts_optlen s) (ts_statlen s) s0 Hmono0 Hin0) as Hin1.
  pose proof (bt_force2_dl 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                (ts_optlen s) (ts_statlen s) Hd0) as Hd1.
  rewrite E2 in Hin1, Hd1.

  (* stage 3: heapify keeps membership *)
  assert (Hhalf : hlen1 / 2 <= hlen1)
    by (apply Z.div_le_upper_bound; lia).
  pose proof (bt_heapify_preserves (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                (hlen1 / 2) s0 Hhalf Hin1) as Hin2.
  rewrite <- Ehp2 in Hin2.

  (* stage 4: the combine loop parks it, and the gap survives *)
  pose proof (combine_loop_parks_every_symbol (Z.to_nat HEAP_SIZE) hlen1 hp2
                dep1 t1 (sd_elems k) s0 (sd_elems k) Hl2 HlL
                (Z.le_refl _) Hs0 Hin2) as Hpark.
  pose proof (bt_loop_dl (Z.to_nat HEAP_SIZE)
                {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                   b_hlen := hlen1; b_hmax := HEAP_SIZE;
                   b_node := sd_elems k |}) as Hdf.
  cbn [b_tree] in Hdf. specialize (Hdf Hd1).
  pose proof (bt_loop_gap_out (Z.to_nat HEAP_SIZE)
                {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                   b_hlen := hlen1; b_hmax := HEAP_SIZE;
                   b_node := sd_elems k |}) as Hgf.
  cbn [b_hlen] in Hgf.
  assert (Hg0 : Gap {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                       b_hlen := hlen1; b_hmax := HEAP_SIZE;
                       b_node := sd_elems k |})
    by (apply gap_at_entry; exact HlL).
  specialize (Hgf Hl2 Hg0).
  rewrite Eloop in Hpark, Hdf, Hgf.

  (* the exit gap gives [heap_max >= 3], hence [0 <= heap_max - 1] *)
  pose proof (bt_loop_root (Z.to_nat HEAP_SIZE)
                {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                   b_hlen := hlen1; b_hmax := HEAP_SIZE;
                   b_node := sd_elems k |} (sd_elems k)) as Hroot.
  cbn [b_hlen b_node] in Hroot.
  specialize (Hroot Hl2 (Z.le_refl _)). rewrite Eloop in Hroot.
  destruct Hroot as [Hlen1' _].
  unfold Gap in Hgf. rewrite Hlen1' in Hgf.

  (* the parked window is EXACTLY what gen_bitlen walks: the tail's single write
     lands at [heap_max - 1], strictly below the walk's first index *)
  destruct Hpark as [j [Hj Heq]].
  assert (Hheapj : ts_heap s1 j = s0).
  { rewrite Ehp. rewrite zset_other by lia. exact Heq. }
  rewrite <- Hheapj.
  apply gen_bitlen_range_at.
  - exact Hm.
  - rewrite Etr. exact Hdf.
  - rewrite Ehm. lia.
  - rewrite Ehm. lia.
Qed.

(** ** The code-length tree's instance, which is what HuffCover consumes *)
Corollary build_chain_bl : forall s s0 fuelinit t0 hp0 dep0 hlen0 maxc0
                                  t1 hp1 dep1 hlen1 maxc1 ol1 sl1 hp2 stf s1,
  DlNn (ts_trees s TK_BL) ->
  0 <= s0 < sd_elems TK_BL ->
  t_freq (ts_trees s TK_BL) s0 <> 0 ->
  sd_elems TK_BL <= Z.of_nat fuelinit ->
  bt_init fuelinit 0 (sd_elems TK_BL) (ts_trees s TK_BL) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  2 <= hlen1 -> hlen1 <= L_CODES ->
  hp2 = bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1; b_heap := hp2; b_dep := dep1;
             b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems TK_BL |} = Some stf ->
  ts_trees s1 TK_BL = b_tree stf ->
  ts_heap s1 = zset (b_heap stf) (b_hmax stf - 1) (b_heap stf SMALLEST) ->
  ts_heapmax s1 = b_hmax stf - 1 ->
  1 <= t_len (ts_trees (gen_bitlen TK_BL s1) TK_BL) s0 <= 7.
Proof.
  intros. rewrite <- bl_max_length_is_7.
  eapply build_chain; try eassumption.
  rewrite bl_max_length_is_7. lia.
Qed.

(** And the final [gen_codes] does not disturb it: it writes CODES, and
    [HuffGenCodes.gen_codes_len] says lengths are untouched.  So the range
    survives [build_tree]'s last line. *)
Corollary range_survives_gen_codes : forall t maxc blc s0 m,
  1 <= t_len t s0 <= m ->
  1 <= t_len (gen_codes t maxc blc) s0 <= m.
Proof. intros t maxc blc s0 m H. rewrite gen_codes_len. exact H. Qed.

Print Assumptions bt_init_dl.
Print Assumptions bt_loop_dl.
Print Assumptions bt_loop_gap_out.
Print Assumptions build_chain.
Print Assumptions build_chain_bl.
Print Assumptions range_survives_gen_codes.
