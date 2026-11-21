(** * ZRTreeFacts — the per-build tree-state facts the dynamic arm eats.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  ThreadSeam
    discharge, part 1: at one [build_tree k s] call,

      * blcount support ([b < 0 \/ 15 < b -> 0]) at the OUTPUT, from the
        entry support — via an earlier development run's parked census
        ([BtCensus5.build_tree_parked] + [BtItem6.gen_bitlen_out]'s
        window conjunct), replaying [build_tree_out]'s assembly;
      * global length nonnegativity ([DlNn]) at the output — the
        [BuildChain] stage lemmas plus fresh [gb_pass1]/[gb_pass2]
        inductions (every length write is a [t_setlen] and [t_setlen]
        stores [u16]).

    These discharge the [ZR_DynEntry] R-facts at flush sites once the
    invariant is threaded along the walk (part 2). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream Deflate Trees
  BuildTree BuildChain KraftInit GenBitlen HuffGenCodes
  BtWin BtCensus2 BtSized BtTerm BtCensus4 BtCensus5 BtItem6 BtItem6b
  BtBlSide.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(* ==========================================================================
   1.  [DlNn] through [gen_bitlen]'s two passes.
   ========================================================================== *)

Lemma gb_pass1_dl : forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov,
  DlNn t ->
  match gb_pass1 fuel k hp maxc maxlen base extra stree h t blc ol sl ov with
  | (t', _, _, _, _) => DlNn t'
  end.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov H;
    cbn [gb_pass1].
  - exact H.
  - destruct (Z.leb HEAP_SIZE h); [exact H|].
    cbv zeta.
    destruct (Z.ltb maxc (hp h)).
    + apply IH. apply dl_setlen. exact H.
    + apply IH. apply dl_setlen. exact H.
Qed.

Lemma gb_pass2_dl : forall fuel hp maxc t blc bits n h ol,
  DlNn t ->
  match gb_pass2 fuel hp maxc t blc bits n h ol with
  | (t', _) => DlNn t'
  end.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol H;
    cbn [gb_pass2].
  - exact H.
  - destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1); [exact H | apply IH; exact H].
    + cbv zeta.
      destruct (Z.ltb maxc (hp (h - 1))); [apply IH; exact H|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits); [apply IH; exact H|].
      apply IH. apply dl_setlen. exact H.
Qed.

Local Ltac tprj :=
  cbn [ts_trees ts_blcount ts_maxcode ts_heap ts_heapmax ts_optlen
       ts_statlen ts_symbuf ts_symnext ts_heaplen ts_depth
       set_statlen set_optlen set_blcount set_heapmax set_heaplen
       set_depth set_heap set_max set_maxcode set_trees].

Lemma gen_bitlen_dl : forall k s,
  DlNn (ts_trees s k) ->
  DlNn (ts_trees (gen_bitlen k s) k).
Proof.
  intros k s H.
  unfold gen_bitlen. cbv zeta.
  pose proof (gb_pass1_dl (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                (sd_extra k) (sd_stree k) (ts_heapmax s + 1)
                (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
                (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                (ts_optlen s) (ts_statlen s) 0
                (dl_setlen _ _ _ H)) as H1.
  destruct (gb_pass1 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as [[[[t2 blc1] ol1] sl1] ov].
  destruct (Z.eqb ov 0).
  - tprj. rewrite set_tree_same. exact H1.
  - pose proof (gb_pass2_dl (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                  (ts_heap s) (ts_maxcode s k) t2
                  (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                  (sd_max_length k)
                  (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                     (sd_max_length k))
                  HEAP_SIZE ol1 H1) as H2.
    destruct (gb_pass2 _ _ _ _ _ _ _ _ _) as [t3 ol2].
    tprj. rewrite set_tree_same. exact H2.
Qed.

(* ==========================================================================
   2.  [DlNn] through the whole [build_tree].
   ========================================================================== *)

Theorem build_tree_dl : forall k s,
  DlNn (ts_trees s k) ->
  DlNn (ts_trees (build_tree k s) k).
Proof.
  intros k s H.
  unfold build_tree. cbv zeta.
  pose proof (bt_init_dl (Z.to_nat L_CODES + 2) 0 (sd_elems k)
                (ts_trees s k) (ts_heap s) (ts_depth s) 0 (-1) H) as H0.
  destruct (bt_init _ _ _ _ _ _ _ _)
    as [[[[t0 hp0] dep0] hlen0] maxc0].
  pose proof (bt_force2_dl 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                (ts_optlen s) (ts_statlen s) H0) as H1.
  destruct (bt_force2 _ _ _ _ _ _ _ _ _)
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1].
  pose proof (bt_loop_dl (Z.to_nat HEAP_SIZE)
                {| b_tree := t1;
                   b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1
                               hlen1 (hlen1 / 2);
                   b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                   b_node := sd_elems k |}
                ltac:(cbn [b_tree]; exact H1)) as H2.
  destruct (bt_loop _ _) as [stf|]; [|exact H].
  assert (Hs1 : DlNn (ts_trees
      (set_statlen sl1 (set_optlen ol1
         (set_heapmax (b_hmax stf - 1) (set_heaplen (b_hlen stf)
           (set_depth (b_dep stf)
             (set_heap (zset (b_heap stf) (b_hmax stf - 1)
                          (b_heap stf SMALLEST))
               (set_max k maxc1 (set_tree k (b_tree stf) s)))))))) k)).
  { tprj. rewrite set_tree_same. exact H2. }
  pose proof (gen_bitlen_dl k _ Hs1) as H3.
  tprj. rewrite set_tree_same.
  intro i. rewrite gen_codes_len. exact (H3 i).
Qed.

Print Assumptions build_tree_dl.

(* ==========================================================================
   3.  blcount support through the whole [build_tree].
   ========================================================================== *)

Lemma wsum_le : forall (f : Z -> Z) n lo,
  (forall x, 0 <= f x <= 1) ->
  0 <= wsum f lo n <= Z.of_nat n.
Proof.
  intros f n; induction n as [|n IH]; intros lo Hf; cbn [wsum].
  - lia.
  - pose proof (Hf lo). pose proof (IH (lo + 1) Hf).
    rewrite Nat2Z.inj_succ. lia.
Qed.

Theorem build_tree_blc_support : forall k s,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (sd_elems k - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree k s) b = 0.
Proof.
  intros k s Hel HM HKe Hblc b Hb.
  unfold build_tree. cbv zeta.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop.
  2:{ apply Hblc. exact Hb. }
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as (Hpk & Hio & Hsz & Hcen & _).
  assert (Hhl : hlen1 <= sd_elems k).
  { rewrite (io_total _ _ _ _ _ Hio).
    unfold live_total.
    pose proof (wsum_le (fun x => ind (live_b t1 maxc1 x))
                  (Z.to_nat (sd_elems k)) 0
                  (fun x => ind_0_1 (live_b t1 maxc1 x))) as W.
    rewrite Z2Nat.id in W by lia. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length k) by lia.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
  assert (Hmf0 : 0 <= b_hmax stf - 1)
    by (unfold HEAP_SIZE in Hhm; unfold L_CODES in Hsz; lia).
  rewrite bc_settree.
  fold (s1_of k maxc1 stf ol1 sl1 s).
  destruct (gen_bitlen_out k (s1_of k maxc1 stf ol1 sl1 s)
              (sd_elems k) maxc1 (sd_max_length k) t1 (b_tree stf)
              (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1))
              (b_hmax stf - 1) (b_node stf) hlen1
              Hpk HM Hmf0 eq_refl
              (s1_heap k maxc1 stf ol1 sl1 s)
              (s1_heapmax k maxc1 stf ol1 sl1 s)
              (s1_trees k maxc1 stf ol1 sl1 s)
              (s1_maxcode k maxc1 stf ol1 sl1 s)
              ltac:(intros b0 Hb0; rewrite s1_blcount; apply Hblc; exact Hb0)
              Hcen ltac:(lia) HK)
    as [_ [_ [G3 [_ [_ _]]]]].
  apply G3. lia.
Qed.

Print Assumptions build_tree_blc_support.

(* ==========================================================================
   4.  Cross-tree and scan frames.
   ========================================================================== *)

(** [set_tree_other] / [build_tree_tree_other] come from [BtBlSide]. *)

(** [scan_go] never writes a length. *)
Lemma scan_go_len : forall fuel t maxc n prevlen nextlen count maxcnt mincnt bl j,
  t_len (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl) j
  = t_len bl j.
Proof.
  induction fuel as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl j;
    cbn [scan_go].
  - reflexivity.
  - destruct (Z.ltb maxc n); [reflexivity|].
    destruct ((Z.ltb (count + 1) maxcnt)
              && (Z.eqb nextlen (t_len t (n + 1)))).
    + apply IH.
    + cbv zeta. rewrite IH.
      repeat first
        [ rewrite dl_setfreq
        | match goal with
          | |- t_len (if ?c then _ else _) _ = _ => destruct c
          end
        | reflexivity ].
Qed.

Print Assumptions scan_go_len.

(* ==========================================================================
   5.  Frequency frames through the build stages and code assignment.
   ========================================================================== *)

Lemma t_freq_setfreq_other : forall t i v j, j <> i ->
  t_freq (t_setfreq t i v) j = t_freq t j.
Proof.
  intros t i v j Hj. unfold t_setfreq, t_freq. cbn [tr_fc].
  apply zset_other. exact Hj.
Qed.

Lemma t_freq_setfreq_same : forall t i v, t_freq (t_setfreq t i v) i = u16 v.
Proof.
  intros t i v. unfold t_setfreq, t_freq. cbn [tr_fc]. apply zset_same.
Qed.

Lemma t_freq_setcode_other : forall t i v j, j <> i ->
  t_freq (t_setcode t i v) j = t_freq t j.
Proof.
  intros t i v j Hj. unfold t_setcode, t_freq. cbn [tr_fc].
  apply zset_other. exact Hj.
Qed.

Lemma bt_init_freq : forall fuel n elems t hp dep hlen maxc j,
  t_freq (match bt_init fuel n elems t hp dep hlen maxc with
          | (t', _, _, _, _) => t' end) j = t_freq t j.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc j;
    cbn [bt_init].
  - reflexivity.
  - destruct (Z.leb elems n); [reflexivity|].
    destruct (Z.eqb (t_freq t n) 0).
    + rewrite IH. reflexivity.
    + apply IH.
Qed.

Lemma bt_force2_freq_other : forall fuel stree t hp dep hlen maxc ol sl j,
  -1 <= maxc ->
  (j < 0 \/ 2 < j) ->
  t_freq (match bt_force2 fuel stree t hp dep hlen maxc ol sl with
          | (t', _, _, _, _, _, _) => t' end) j = t_freq t j.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl j Hm Hj;
    cbn [bt_force2].
  - reflexivity.
  - destruct (Z.leb 2 hlen); [reflexivity|].
    cbv zeta.
    destruct (Z.ltb maxc 2) eqn:E.
    + apply Z.ltb_lt in E.
      rewrite IH by lia.
      apply t_freq_setfreq_other. lia.
    + apply Z.ltb_ge in E.
      rewrite IH by lia.
      apply t_freq_setfreq_other. lia.
Qed.

Lemma gb_pass1_freq : forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov j,
  t_freq (match gb_pass1 fuel k hp maxc maxlen base extra stree h t blc ol sl ov with
          | (t', _, _, _, _) => t' end) j = t_freq t j.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov j;
    cbn [gb_pass1].
  - reflexivity.
  - destruct (Z.leb HEAP_SIZE h); [reflexivity|].
    cbv zeta.
    destruct (Z.ltb maxc (hp h)); rewrite IH; reflexivity.
Qed.

Lemma gb_pass2_freq : forall fuel hp maxc t blc bits n h ol j,
  t_freq (match gb_pass2 fuel hp maxc t blc bits n h ol with
          | (t', _) => t' end) j = t_freq t j.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol j;
    cbn [gb_pass2].
  - reflexivity.
  - destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1); [reflexivity | apply IH].
    + cbv zeta.
      destruct (Z.ltb maxc (hp (h - 1))); [apply IH|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits); [apply IH|].
      rewrite IH. reflexivity.
Qed.

Lemma gen_bitlen_freq : forall k s j,
  t_freq (ts_trees (gen_bitlen k s) k) j = t_freq (ts_trees s k) j.
Proof.
  intros k s j.
  unfold gen_bitlen. cbv zeta.
  pose proof (gb_pass1_freq (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                (sd_extra k) (sd_stree k) (ts_heapmax s + 1)
                (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
                (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                (ts_optlen s) (ts_statlen s) 0 j) as F1.
  destruct (gb_pass1 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as [[[[t2 blc1] ol1] sl1] ov].
  destruct (Z.eqb ov 0).
  - tprj. rewrite set_tree_same. exact F1.
  - pose proof (gb_pass2_freq (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                  (ts_heap s) (ts_maxcode s k) t2
                  (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                  (sd_max_length k)
                  (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                     (sd_max_length k))
                  HEAP_SIZE ol1 j) as F2.
    destruct (gb_pass2 _ _ _ _ _ _ _ _ _) as [t3 ol2].
    tprj. rewrite set_tree_same.
    rewrite F2. exact F1.
Qed.

Lemma gc_assign_freq_other : forall fuel n maxc t nc j,
  (j < n \/ maxc < j) ->
  t_freq (gc_assign fuel n maxc t nc) j = t_freq t j.
Proof.
  induction fuel as [|f IH]; intros n maxc t nc j Hj; cbn [gc_assign].
  - reflexivity.
  - destruct (Z.ltb maxc n) eqn:E; [reflexivity|].
    apply Z.ltb_ge in E.
    cbv zeta.
    destruct (Z.eqb (t_len t n) 0).
    + apply IH. lia.
    + rewrite IH by lia.
      apply t_freq_setcode_other. lia.
Qed.

Lemma gen_codes_freq_other : forall t maxc blc j,
  (j < 0 \/ maxc < j) ->
  t_freq (gen_codes t maxc blc) j = t_freq t j.
Proof.
  intros t maxc blc j Hj. unfold gen_codes. cbv zeta.
  apply gc_assign_freq_other. exact Hj.
Qed.

Lemma tree_zero_freq_other : forall n i0 t j,
  (j < i0 \/ i0 + Z.of_nat n <= j) ->
  t_freq (tree_zero_freq n i0 t) j = t_freq t j.
Proof.
  induction n as [|n IH]; intros i0 t j Hj; cbn [tree_zero_freq].
  - reflexivity.
  - rewrite Nat2Z.inj_succ in Hj.
    rewrite IH by lia.
    apply t_freq_setfreq_other. lia.
Qed.

Lemma tree_zero_freq_zero : forall n i0 t j,
  i0 <= j < i0 + Z.of_nat n ->
  t_freq (tree_zero_freq n i0 t) j = 0.
Proof.
  induction n as [|n IH]; intros i0 t j Hj; cbn [tree_zero_freq].
  - cbn [Z.of_nat] in Hj. lia.
  - rewrite Nat2Z.inj_succ in Hj.
    destruct (Z.eq_dec j i0) as [-> | Hne].
    + rewrite tree_zero_freq_other by lia.
      rewrite t_freq_setfreq_same. reflexivity.
    + apply IH. lia.
Qed.

Print Assumptions gen_bitlen_freq.

Lemma tree_zero_freq_len : forall n i0 t j,
  t_len (tree_zero_freq n i0 t) j = t_len t j.
Proof.
  induction n as [|n IH]; intros i0 t j; cbn [tree_zero_freq].
  - reflexivity.
  - rewrite IH. apply dl_setfreq.
Qed.

(* ==========================================================================
   6.  The forced maxcode: [bt_force2] guarantees at least two heap
       entries, so the census puts [maxc1 >= 1] — and [build_tree]
       publishes exactly [maxc1].
   ========================================================================== *)

Lemma live_b_false_high : forall t maxc x, maxc < x -> live_b t maxc x = false.
Proof.
  intros t maxc x Hx. unfold live_b.
  rewrite (proj2 (Z.leb_gt x maxc)) by lia.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma wsum_live_window : forall t maxc n lo,
  wsum (fun x => ind (live_b t maxc x)) lo n <= Z.max 0 (maxc + 1 - lo).
Proof.
  intros t maxc n; induction n as [|n IH]; intro lo; cbn [wsum].
  - lia.
  - pose proof (IH (lo + 1)).
    destruct (Z.le_gt_cases lo maxc) as [Hle | Hgt].
    + pose proof (ind_0_1 (live_b t maxc lo)). lia.
    + rewrite (live_b_false_high t maxc lo Hgt). cbn [ind]. lia.
Qed.

Theorem build_tree_maxc_ge1 : forall k s,
  3 <= sd_elems k <= L_CODES ->
  1 <= ts_maxcode (build_tree k s) k.
Proof.
  intros k s Hel.
  unfold build_tree. cbv zeta.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; try eassumption; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as (_ & Hio & _ & _ & _).
  assert (Hmc1 : 1 <= maxc1).
  { pose proof (io_total _ _ _ _ _ Hio) as Htot.
    pose proof (wsum_live_window t1 maxc1 (Z.to_nat (sd_elems k)) 0) as W.
    unfold live_total in Htot. lia. }
  fold (s1_of k maxc1 stf ol1 sl1 s).
  rewrite mc_settree.
  rewrite gen_bitlen_maxcode.
  rewrite s1_maxcode.
  exact Hmc1.
Qed.

Print Assumptions build_tree_maxc_ge1.
