(** * BuildTree — (B) at [build_tree] itself: the plumbing, written.

    OWNER: huffman-id.  The step I twice reported as remaining and twice declined
    to claim.  TL's instruction was to finish it "to your own standard"
    ("plumbing not written is not proved"), so here it is written.

    WHAT WAS ACTUALLY LEFT.  [BuildChain.build_chain] does the mathematics: it
    threads a positive-frequency symbol through every stage and out the far side
    with a length in [1, max_length].  It describes the post-loop state by its
    THREE RELEVANT PROJECTIONS rather than by [build_tree]'s stack of eight record
    setters, precisely so that this file could be short.  All that remains is:

      - discharge those three projections against the real setter stack
        ([set_statlen]/[set_optlen]/[set_heapmax]/[set_heaplen]/[set_depth]/
         [set_heap]/[set_max]/[set_tree]) — each is "every setter but the
        relevant one preserves this field";
      - observe that [build_tree]'s last line wraps the result in [gen_codes],
        which writes CODES and leaves lengths alone
        ([HuffGenCodes.gen_codes_len]).

    THE TWO SIDE CONDITIONS I STILL DO NOT PROVE, carried as hypotheses and named
    rather than buried:
      [Hsize]  2 <= heap_len <= L_CODES after [bt_force2] — a counting argument
               about [bt_init]'s appends. [bt_force2] exists to force [>= 2]; at
               most [elems <= L_CODES] symbols are ever heaped.
      [Eloop]  the combine loop returns [Some] within its static fuel.
    Both are true of real states and neither is about code lengths, which is why
    they are hypotheses of a theorem about code lengths rather than lemmas of it.

    So (B) is now: PROVED, modulo two named counting/termination facts. That is a
    different sentence from "proved", and I am writing it out rather than
    rounding, because three times in this lane a step I called obvious carried
    real content. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes GenBitlen BtCover PqDown BtForce2 BtStep BtRoot GbVisit GbRange
  BuildChain.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The three projections through [build_tree]'s setter stack

    Each is the same one-line observation — every setter but the relevant one
    rebuilds the record with the field unchanged — but they are stated separately
    because that is how [build_chain] consumes them, and because a single fused
    lemma would hide which setter is doing the work. *)

Definition s1_of (k maxc1 : Z) (stf : BtSt) (ol1 sl1 : Z) (s : TSt) : TSt :=
  set_statlen sl1
    (set_optlen ol1
      (set_heapmax (b_hmax stf - 1)
        (set_heaplen (b_hlen stf)
          (set_depth (b_dep stf)
            (set_heap (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf SMALLEST))
              (set_max k maxc1 (set_tree k (b_tree stf) s))))))).

(** ONE SETTER AT A TIME, and this is not a style preference.

    [unfold set_statlen, set_optlen, ...] over the eight nested setters costs
    18 GB and does not terminate: each [set_X v s] is [mkTSt] applied to THIRTEEN
    projections of [s], so unfolding a stack of eight multiplies out to ~13^8
    subterms. Unfolding them ONE AT A TIME keeps every intermediate at thirteen
    small projections, and each lemma below is a single [reflexivity].

    The general shape, worth carrying: **a record setter written as
    "rebuild with all N fields" is exponential to unfold in a stack and linear to
    rewrite through.** Always give yourself the per-field rewrite lemmas before
    touching a setter stack of any depth. *)

Lemma tr_statlen : forall v s, ts_trees (set_statlen v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_optlen : forall v s, ts_trees (set_optlen v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_heapmax : forall v s, ts_trees (set_heapmax v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_heaplen : forall v s, ts_trees (set_heaplen v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_depth : forall v s, ts_trees (set_depth v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_heap : forall v s, ts_trees (set_heap v s) = ts_trees s.
Proof. reflexivity. Qed.
Lemma tr_max : forall k v s, ts_trees (set_max k v s) = ts_trees s.
Proof. reflexivity. Qed.

Lemma hp_statlen : forall v s, ts_heap (set_statlen v s) = ts_heap s.
Proof. reflexivity. Qed.
Lemma hp_optlen : forall v s, ts_heap (set_optlen v s) = ts_heap s.
Proof. reflexivity. Qed.
Lemma hp_heapmax : forall v s, ts_heap (set_heapmax v s) = ts_heap s.
Proof. reflexivity. Qed.
Lemma hp_heaplen : forall v s, ts_heap (set_heaplen v s) = ts_heap s.
Proof. reflexivity. Qed.
Lemma hp_depth : forall v s, ts_heap (set_depth v s) = ts_heap s.
Proof. reflexivity. Qed.
Lemma hp_heap : forall v s, ts_heap (set_heap v s) = v.
Proof. reflexivity. Qed.

Lemma hm_statlen : forall v s, ts_heapmax (set_statlen v s) = ts_heapmax s.
Proof. reflexivity. Qed.
Lemma hm_optlen : forall v s, ts_heapmax (set_optlen v s) = ts_heapmax s.
Proof. reflexivity. Qed.
Lemma hm_heapmax : forall v s, ts_heapmax (set_heapmax v s) = v.
Proof. reflexivity. Qed.

Lemma set_tree_same : forall k t s, ts_trees (set_tree k t s) k = t.
Proof.
  intros. unfold set_tree, set_trees. cbn [ts_trees].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma s1_trees : forall k maxc1 stf ol1 sl1 s,
  ts_trees (s1_of k maxc1 stf ol1 sl1 s) k = b_tree stf.
Proof.
  intros. unfold s1_of.
  rewrite tr_statlen, tr_optlen, tr_heapmax, tr_heaplen, tr_depth, tr_heap,
          tr_max.
  apply set_tree_same.
Qed.

Lemma s1_heap : forall k maxc1 stf ol1 sl1 s,
  ts_heap (s1_of k maxc1 stf ol1 sl1 s)
  = zset (b_heap stf) (b_hmax stf - 1) (b_heap stf SMALLEST).
Proof.
  intros. unfold s1_of.
  rewrite hp_statlen, hp_optlen, hp_heapmax, hp_heaplen, hp_depth.
  apply hp_heap.
Qed.

Lemma s1_heapmax : forall k maxc1 stf ol1 sl1 s,
  ts_heapmax (s1_of k maxc1 stf ol1 sl1 s) = b_hmax stf - 1.
Proof.
  intros. unfold s1_of.
  rewrite hm_statlen, hm_optlen. apply hm_heapmax.
Qed.

(** ** (B) at [build_tree] *)
Theorem build_tree_range :
  forall k s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  1 <= sd_max_length k <= 15 ->
  DlNn (ts_trees s k) ->
  0 <= s0 < sd_elems k ->
  t_freq (ts_trees s k) s0 <> 0 ->
  sd_elems k <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  2 <= hlen1 -> hlen1 <= L_CODES ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  1 <= t_len (ts_trees (build_tree k s) k) s0 <= sd_max_length k.
Proof.
  intros k s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hm Hnn Hs0 Hfr Hel E0 E2 Hl2 HlL Eloop.
  (* Reduce ONLY what is needed.  [cbv iota zeta] here costs 11 GB: [iota]
     includes FIX reduction, so it unfolds [bt_force2] at its literal fuel 3 and
     normalises the whole goal.  [cbv beta match] reduces the tuple match on a
     constructor and nothing else; the single [cbv zeta] up front is for the two
     small outer lets ([elems], [stree]) so the rewrites can see [sd_elems k]. *)
  unfold build_tree. cbv zeta.
  rewrite E0. cbv beta match.
  rewrite E2. cbv beta match.
  rewrite Eloop. cbv beta match.
  (* the last line writes CODES; lengths are untouched *)
  rewrite set_tree_same, gen_codes_len.
  (* and the rest is [build_chain], with the three projections discharged *)
  eapply build_chain with
    (fuelinit := (Z.to_nat L_CODES + 2)%nat)
    (t0 := t0) (hp0 := hp0) (dep0 := dep0) (hlen0 := hlen0) (maxc0 := maxc0)
    (t1 := t1) (hp1 := hp1) (dep1 := dep1) (hlen1 := hlen1) (maxc1 := maxc1)
    (ol1 := ol1) (sl1 := sl1) (stf := stf)
    (hp2 := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2)).
  - exact Hm.
  - exact Hnn.
  - exact Hs0.
  - exact Hfr.
  - (* the fuel is generous: [L_CODES + 2] steps for at most [L_CODES] symbols *)
    rewrite Nat2Z.inj_add, Z2Nat.id by (unfold L_CODES; lia).
    change (Z.of_nat 2) with 2. lia.
  - exact E0.
  - exact E2.
  - exact Hl2.
  - exact HlL.
  - reflexivity.
  - exact Eloop.
  - apply s1_trees.
  - apply s1_heap.
  - apply s1_heapmax.
Qed.

(** The code-length tree's instance — HuffCover's [CLCovers], at [build_bl_tree]'s
    own [build_tree] call. *)
Corollary build_tree_bl_range :
  forall s s0 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  DlNn (ts_trees s TK_BL) ->
  0 <= s0 < sd_elems TK_BL ->
  t_freq (ts_trees s TK_BL) s0 <> 0 ->
  sd_elems TK_BL <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees s TK_BL)
          (ts_heap s) (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  2 <= hlen1 -> hlen1 <= L_CODES ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems TK_BL |}
    = Some stf ->
  1 <= t_len (ts_trees (build_tree TK_BL s) TK_BL) s0 <= 7.
Proof.
  intros. rewrite <- bl_max_length_is_7.
  eapply build_tree_range; try eassumption.
  rewrite bl_max_length_is_7. lia.
Qed.

(** WHAT (B) NOW IS, stated once so nobody has to reconstruct it:

      every positive-frequency symbol comes out of [build_tree] with a code
      length in [1, max_length] — [1, 7] for the code-length tree — PROVIDED
      the heap length after [bt_force2] is in [2, L_CODES] and the combine loop
      terminates within its static fuel.

    Those two provisos are counting and termination facts about the heap, not
    facts about lengths.  Everything about LENGTHS is proved. *)

Print Assumptions s1_trees.
Print Assumptions s1_heap.
Print Assumptions s1_heapmax.
Print Assumptions build_tree_range.
Print Assumptions build_tree_bl_range.
