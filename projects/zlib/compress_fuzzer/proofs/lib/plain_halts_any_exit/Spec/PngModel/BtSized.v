(** * BtSized — the counting argument, so [build_tree_range]'s sizing hypothesis
      is discharged rather than assumed.

    OWNER: huffman-id.  The second half of "finish (B)'s plumbing".

    [BuildTree.build_tree_range] carried [2 <= hlen1 <= L_CODES] as a hypothesis.
    It is a counting fact about how many times [bt_init] and [bt_force2] append,
    and it splits into four one-line inductions:

      UPPER  [bt_init] appends at most once per symbol and advances [n] each
             trip, so [hlen' <= hlen + (elems - n)]; from [n = 0], [hlen = 0]
             that is [hlen0 <= elems <= L_CODES].
      UPPER  [bt_force2] appends only while [hlen < 2], so it cannot push [hlen]
             past 2 — any bound [B >= 2] survives.
      LOWER  [bt_force2] appends UNTIL [hlen >= 2], so with fuel to spare it
             leaves [hlen >= 2].  That is the whole purpose of the function
             ([trees.c:653-659], "force at least two codes of non-zero
             frequency") and the fuel it is called with (3) is more than the 2 it
             can ever need.
      LOWER  [bt_init]'s [hlen] is monotone and starts at 0, so [hlen0 >= 0].

    NOTHING HERE IS ABOUT LENGTHS, which is why it was a hypothesis of a theorem
    about lengths rather than a lemma of one — but it is cheap, and a hypothesis
    that is cheap to discharge should be discharged rather than carried. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtCover BuildChain BuildTree.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** [bt_init] appends at most once per symbol *)
Lemma bt_init_hlen_ub : forall fuel n elems t hp dep hlen maxc,
  n <= elems ->
  match bt_init fuel n elems t hp dep hlen maxc with
  | (_, _, _, hlen', _) => hlen' <= hlen + (elems - n)
  end.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc Hn.
  - cbn [bt_init]. lia.
  - cbn [bt_init].
    destruct (Z.leb elems n) eqn:Eend; [apply Z.leb_le in Eend; lia|].
    apply Z.leb_gt in Eend.
    destruct (Z.eqb (t_freq t n) 0).
    + specialize (IH (n + 1) elems (t_setlen t n 0) hp dep hlen maxc).
      destruct (bt_init f (n + 1) elems (t_setlen t n 0) hp dep hlen maxc)
        as [[[[t' hp'] dep'] hlen'] maxc'].
      specialize (IH ltac:(lia)). lia.
    + specialize (IH (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                     (hlen + 1) n).
      destruct (bt_init f (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                        (hlen + 1) n) as [[[[t' hp'] dep'] hlen'] maxc'].
      specialize (IH ltac:(lia)). lia.
Qed.

(** ** [bt_force2] cannot push [heap_len] past 2 *)
Lemma bt_force2_hlen_ub : forall fuel stree t hp dep hlen maxc ol sl B,
  2 <= B -> hlen <= B ->
  match bt_force2 fuel stree t hp dep hlen maxc ol sl with
  | (_, _, _, hlen', _, _, _) => hlen' <= B
  end.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl B HB Hh.
  - cbn [bt_force2]. exact Hh.
  - cbn [bt_force2].
    destruct (Z.leb 2 hlen) eqn:E2; [exact Hh|].
    apply Z.leb_gt in E2.
    apply IH; [exact HB | lia].
Qed.

(** ** ...and it appends UNTIL [heap_len] reaches 2

    This is the function's entire purpose, and the fuel it is called with (3)
    exceeds the 2 appends it can ever need. *)
Lemma bt_force2_hlen_lb : forall fuel stree t hp dep hlen maxc ol sl,
  2 <= hlen + Z.of_nat fuel ->
  match bt_force2 fuel stree t hp dep hlen maxc ol sl with
  | (_, _, _, hlen', _, _, _) => 2 <= hlen'
  end.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl Hf.
  - cbn [bt_force2]. change (Z.of_nat 0) with 0 in Hf. lia.
  - cbn [bt_force2].
    destruct (Z.leb 2 hlen) eqn:E2; [apply Z.leb_le in E2; exact E2|].
    apply Z.leb_gt in E2.
    apply IH. rewrite Nat2Z.inj_succ in Hf. lia.
Qed.

(** ** The sizing fact, assembled *)
Theorem bt_sized :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  0 <= sd_elems k -> sd_elems k <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  2 <= hlen1 <= L_CODES.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         He0 HeL E0 E2.
  (* [hlen0] is between 0 and [elems] *)
  pose proof (bt_init_hlen_ub (Z.to_nat L_CODES + 2) 0 (sd_elems k)
                (ts_trees s k) (ts_heap s) (ts_depth s) 0 (-1) He0) as Hub0.
  pose proof (bt_init_covers (Z.to_nat L_CODES + 2) 0 (sd_elems k)
                (ts_trees s k) (ts_heap s) (ts_depth s) 0 (-1)) as Hc0.
  rewrite E0 in Hub0, Hc0.
  destruct Hc0 as [_ [_ Hmono0]].
  { rewrite Nat2Z.inj_add, Z2Nat.id by (unfold L_CODES; lia).
    change (Z.of_nat 2) with 2. lia. }
  { lia. }
  (* [bt_force2] then lands it in [2, L_CODES] *)
  pose proof (bt_force2_hlen_ub 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                (ts_optlen s) (ts_statlen s) L_CODES) as Hub1.
  pose proof (bt_force2_hlen_lb 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                (ts_optlen s) (ts_statlen s)) as Hlb1.
  rewrite E2 in Hub1, Hlb1.
  split.
  - apply Hlb1. change (Z.of_nat 3) with 3. lia.
  - apply Hub1; [unfold L_CODES; lia | lia].
Qed.

(** ** (B) with the sizing hypothesis DISCHARGED

    What remains of [build_tree_range]'s hypotheses is exactly one: that the
    combine loop returns [Some] within its static fuel.  Termination, and nothing
    else. *)
Theorem build_tree_range_sized :
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
         Hm Hnn Hs0 Hfr HeL E0 E2 Eloop.
  assert (Hsz : 2 <= hlen1 <= L_CODES).
  { eapply bt_sized; try eassumption. lia. }
  eapply build_tree_range; try eassumption; lia.
Qed.

(** So (B) now reads: every positive-frequency symbol comes out of [build_tree]
    with a code length in [1, max_length], PROVIDED the combine loop terminates
    within its static fuel.  One hypothesis, and it is a termination fact about a
    loop whose fuel [Trees.v] itself documents as a static over-estimate. *)

Print Assumptions bt_init_hlen_ub.
Print Assumptions bt_force2_hlen_ub.
Print Assumptions bt_force2_hlen_lb.
Print Assumptions bt_sized.
Print Assumptions build_tree_range_sized.
