(** * BtBlSide — the 0xffff guards survive to [send_all_trees], and
      [bbl_scan]'s result is characterized.

    OWNER: an earlier development run.  LdDynV item 4's sentinel hypotheses
    ([t_len t (maxc+1) = 65535]) and item 3's zero-tail live here, as facts at
    [build_bl_tree]'s output.  The load-bearing frames: [build_tree k] and
    [gen_bitlen k] never write ANOTHER kind's tree, so the guards written by
    the two [scan_tree]s are still in place after the BL tree is built. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtItem6b BuildTree.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Tree frames across kinds *)

Lemma set_tree_other : forall k t s j, j <> k ->
  ts_trees (set_tree k t s) j = ts_trees s j.
Proof.
  intros k t s j Hj. unfold set_tree, set_trees. cbn [ts_trees].
  replace (Z.eqb j k) with false by (symmetry; apply Z.eqb_neq; exact Hj).
  reflexivity.
Qed.

Lemma gen_bitlen_tree_other : forall k s j, j <> k ->
  ts_trees (gen_bitlen k s) j = ts_trees s j.
Proof.
  intros k s j Hj. unfold gen_bitlen.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
              (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
              (sd_extra k) (sd_stree k) (ts_heapmax s + 1)
              (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
              (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
              (ts_optlen s) (ts_statlen s) 0)
    as [[[[t2 blc1] ol1] sl1] ov].
  destruct (Z.eqb ov 0).
  - cbn [ts_trees set_statlen set_optlen set_blcount].
    apply set_tree_other. exact Hj.
  - destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                (ts_heap s) (ts_maxcode s k) t2
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                (sd_max_length k)
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                   (sd_max_length k))
                HEAP_SIZE ol1) as [t3 ol2].
    cbn [ts_trees set_statlen set_optlen set_blcount].
    apply set_tree_other. exact Hj.
Qed.

Lemma s1stack_tree_other : forall k maxc1 stf ol1 sl1 s j, j <> k ->
  ts_trees
    (set_statlen sl1
      (set_optlen ol1
        (set_heapmax (b_hmax stf - 1)
          (set_heaplen (b_hlen stf)
            (set_depth (b_dep stf)
              (set_heap (zset (b_heap stf) (b_hmax stf - 1)
                              (b_heap stf SMALLEST))
                (set_max k maxc1 (set_tree k (b_tree stf) s)))))))) j
  = ts_trees s j.
Proof.
  intros k maxc1 stf ol1 sl1 s j Hj.
  cbn [ts_trees set_statlen set_optlen set_heapmax set_heaplen set_depth
       set_heap].
  unfold set_max, set_maxcode. cbn [ts_trees].
  apply set_tree_other. exact Hj.
Qed.

Lemma build_tree_tree_other : forall k s j, j <> k ->
  ts_trees (build_tree k s) j = ts_trees s j.
Proof.
  intros k s j Hj. unfold build_tree.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0].
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1].
  cbv zeta.
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|]; [|reflexivity].
  rewrite set_tree_other by exact Hj.
  rewrite gen_bitlen_tree_other by exact Hj.
  apply s1stack_tree_other. exact Hj.
Qed.

Lemma build_tree_maxcode_other : forall k s j, j <> k ->
  ts_maxcode (build_tree k s) j = ts_maxcode s j.
Proof.
  intros k s j Hj. unfold build_tree.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0].
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1].
  cbv zeta.
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|]; [|reflexivity].
  rewrite mc_settree, gen_bitlen_maxcode.
  rewrite mc_statlen, mc_optlen, mc_heapmax, mc_heaplen, mc_depth, mc_heap.
  unfold set_max, set_maxcode. cbn [ts_maxcode].
  replace (Z.eqb j k) with false by (symmetry; apply Z.eqb_neq; exact Hj).
  rewrite mc_settree. reflexivity.
Qed.

(** ** The [scan_tree] guard *)

Lemma scan_tree_guard : forall t maxc bl,
  t_len (fst (scan_tree t maxc bl)) (maxc + 1) = 65535.
Proof.
  intros t maxc bl. unfold scan_tree. cbn [fst].
  unfold t_setlen, t_len. cbn [tr_dl].
  rewrite zset_same. reflexivity.
Qed.

Lemma scan_tree_len_other : forall t maxc bl i, i <> maxc + 1 ->
  t_len (fst (scan_tree t maxc bl)) i = t_len t i.
Proof.
  intros t maxc bl i Hi. unfold scan_tree. cbn [fst].
  unfold t_setlen, t_len. cbn [tr_dl].
  apply zset_other. exact Hi.
Qed.

(** The guards written by [build_bl_tree]'s two scans are still present in
    its output — the BL build touches only the BL tree. *)
Lemma build_bl_tree_guards : forall s,
  let s' := snd (build_bl_tree s) in
  t_len (ts_trees s' TK_L) (ts_maxcode s TK_L + 1) = 65535
  /\ t_len (ts_trees s' TK_D) (ts_maxcode s TK_D + 1) = 65535
  /\ ts_maxcode s' TK_L = ts_maxcode s TK_L
  /\ ts_maxcode s' TK_D = ts_maxcode s TK_D.
Proof.
  intro s. unfold build_bl_tree. cbv zeta. cbn [snd].
  cbn [ts_maxcode set_optlen].
  rewrite (build_tree_maxcode_other TK_BL _ TK_L)
    by (unfold TK_L, TK_BL; lia).
  rewrite (build_tree_maxcode_other TK_BL _ TK_D)
    by (unfold TK_D, TK_BL; lia).
  cbn [ts_maxcode set_tree set_trees].
  rewrite !tr_optlen.
  split; [|split; [|split]].
  - rewrite (build_tree_tree_other TK_BL _ TK_L)
      by (unfold TK_L, TK_BL; lia).
    rewrite (set_tree_other TK_BL _ _ TK_L) by (unfold TK_L, TK_BL; lia).
    rewrite (set_tree_other TK_D _ _ TK_L) by (unfold TK_L, TK_D; lia).
    rewrite (set_tree_other TK_BL _ _ TK_L) by (unfold TK_L, TK_BL; lia).
    rewrite set_tree_same.
    (* the D-scan reads the ALREADY-GUARDED L tree; its guard write is on the
       D tree, so the L guard is intact *)
    apply scan_tree_guard.
  - rewrite (build_tree_tree_other TK_BL _ TK_D)
      by (unfold TK_D, TK_BL; lia).
    rewrite (set_tree_other TK_BL _ _ TK_D) by (unfold TK_D, TK_BL; lia).
    rewrite set_tree_same.
    cbn [ts_maxcode set_tree set_trees].
    apply scan_tree_guard.
  - reflexivity.
  - reflexivity.
Qed.

(** ** [bbl_scan] *)

Lemma bbl_scan_spec : forall fuel (bl : Tree) (i : Z),
  i < Z.of_nat fuel -> 2 <= i ->
  2 <= bbl_scan fuel bl i <= i
  /\ (forall j, bbl_scan fuel bl i < j <= i -> t_len bl (bl_order j) = 0)
  /\ (3 <= bbl_scan fuel bl i -> t_len bl (bl_order (bbl_scan fuel bl i)) <> 0).
Proof.
  induction fuel as [|f IH]; intros bl i Hf Hi.
  - cbn [Z.of_nat] in Hf. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    cbn [bbl_scan].
    destruct (Z.ltb i 3) eqn:E3.
    + apply Z.ltb_lt in E3.
      split; [lia|]. split; [intros j Hj; lia | intro; lia].
    + apply Z.ltb_ge in E3.
      destruct (negb (Z.eqb (t_len bl (bl_order i)) 0)) eqn:En.
      * apply negb_true_iff, Z.eqb_neq in En.
        split; [lia|]. split; [intros j Hj; lia | intro; exact En].
      * apply negb_false_iff, Z.eqb_eq in En.
        destruct (IH bl (i - 1) ltac:(lia) ltac:(lia)) as [Hr [Hz Hnz]].
        split; [lia|]. split; [|exact Hnz].
        intros j Hj.
        destruct (Z.eq_dec j i) as [->|Hne]; [exact En|].
        apply Hz. lia.
Qed.

Print Assumptions build_tree_tree_other.
Print Assumptions build_tree_maxcode_other.
Print Assumptions build_bl_tree_guards.
Print Assumptions bbl_scan_spec.
