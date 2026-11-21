(** * BtTerm — the combine loop terminates, so (B) is UNCONDITIONAL.

    OWNER: huffman-id.  The last hypothesis of [build_tree_range].

    [bt_loop]'s fuel is [Z.to_nat HEAP_SIZE] = 573, and [Trees.v] calls the [None]
    branch "unreachable: the fuel is a static over-estimate".  That comment is now
    a theorem.  The measure is [heap_len]: every trip decreases it by exactly one
    and the loop stops at [heap_len - 1 < 2], so it runs at most [heap_len - 1]
    trips.  With [heap_len <= L_CODES = 286] against fuel 573 the margin is better
    than 2x — unlike the two constants I pinned earlier tonight (the three
    unrolled [send_code] copies, and [HEAP_SIZE = 2*L_CODES+1]), both of which
    were exactly tight.  Worth saying which kind you have: this one has room. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  GenBitlen BtCover PqDown BtForce2 BtStep BtRoot BuildChain BuildTree BtSized.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Each trip drops [heap_len] by one and the loop halts below 2, so fuel
    [>= heap_len - 1] suffices. *)
Lemma bt_loop_terminates : forall fuel st,
  2 <= b_hlen st -> b_hlen st - 1 <= Z.of_nat fuel ->
  bt_loop fuel st <> None.
Proof.
  induction fuel as [|f IH]; intros st H2 Hf.
  - cbn [bt_loop]. change (Z.of_nat 0) with 0 in Hf. exfalso. lia.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est; [|discriminate].
    apply IH.
    + unfold bt_step in Est. cbv zeta in Est.
      destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [|discriminate].
      apply Z.leb_le in E2. inversion Est. subst. cbn [b_hlen]. lia.
    + unfold bt_step in Est. cbv zeta in Est.
      destruct (Z.leb 2 (b_hlen st - 1)); [|discriminate].
      inversion Est. subst. cbn [b_hlen].
      rewrite Nat2Z.inj_succ in Hf. lia.
Qed.

(** ** (B), UNCONDITIONAL

    No sizing hypothesis ([BtSized.bt_sized] discharges it), no termination
    hypothesis (above).  What is left are facts about the INPUT tree and the
    symbol, which is where hypotheses belong. *)
Theorem build_tree_range_final :
  forall k s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  1 <= sd_max_length k <= 15 ->
  DlNn (ts_trees s k) ->
  0 <= s0 < sd_elems k ->
  t_freq (ts_trees s k) s0 <> 0 ->
  0 <= sd_elems k -> sd_elems k <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  1 <= t_len (ts_trees (build_tree k s) k) s0 <= sd_max_length k.
Proof.
  intros k s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         Hm Hnn Hs0 Hfr He0 HeL E0 E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; eassumption).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                      (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop.
  - eapply build_tree_range_sized; eassumption.
  - (* the [None] branch is unreachable, and now provably so *)
    exfalso. revert Eloop. apply bt_loop_terminates.
    + cbn [b_hlen]. lia.
    + cbn [b_hlen]. rewrite Z2Nat.id by (unfold HEAP_SIZE; lia).
      unfold HEAP_SIZE, L_CODES in *. lia.
Qed.

(** The code-length tree's instance: HuffCover's [CLCovers], unconditional. *)
Corollary build_tree_bl_final :
  forall s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  DlNn (ts_trees s TK_BL) ->
  0 <= s0 < sd_elems TK_BL ->
  t_freq (ts_trees s TK_BL) s0 <> 0 ->
  0 <= sd_elems TK_BL -> sd_elems TK_BL <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees s TK_BL)
          (ts_heap s) (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  1 <= t_len (ts_trees (build_tree TK_BL s) TK_BL) s0 <= 7.
Proof.
  intros. rewrite <- bl_max_length_is_7.
  eapply build_tree_range_final; try eassumption.
  rewrite bl_max_length_is_7. lia.
Qed.

(** ** (B), FINISHED

    Every positive-frequency symbol comes out of [build_tree] with a code length
    in [1, max_length] — [1, 7] for the code-length tree, which is exactly what
    [HuffCover.CLCovers] requires.  The surviving hypotheses are: the input
    tree's length array is nonnegative (free, the [u16] writes give it), the
    symbol is in range with nonzero frequency (the statement's own subject), and
    the element count is at most [L_CODES] (true of every tree kind).

    No sizing assumption.  No termination assumption.  Nothing about the heap. *)

Print Assumptions bt_loop_terminates.
Print Assumptions build_tree_range_final.
Print Assumptions build_tree_bl_final.
