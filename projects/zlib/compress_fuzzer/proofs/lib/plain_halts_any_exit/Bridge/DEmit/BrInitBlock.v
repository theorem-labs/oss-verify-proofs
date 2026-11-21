(** * Bridge.DEmit.BrInitBlock — pair D4 of PAIRS.md: [init_block], S5 vs RT.

    Both clear the frequencies of the [L_CODES] / [D_CODES] / [BL_CODES]
    leaves (S5 with [arr_fill], RT with [tree_zero_freq]), set
    [freq[END_BLOCK] = 1], and zero [opt_len], [static_len], [sym_next],
    [matches].  The internal-node slots above [elems] are left alone on both
    sides. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  Shapes                                                                *)
(* ------------------------------------------------------------------------- *)

(** S5's [init_block] as a setter chain, unfolded only down to the setters
    (never through them: the [arr_fill]s must stay folded). *)
Ltac ib_unfold := unfold DT.init_block, DS.set_Freq, DS.set_tree_fc, DS.tree_fc; cbv zeta.

Lemma rt_init_block_facts : forall ts,
  let ts' := RT.init_block ts in
  RT.ts_trees ts' RT.TK_L
    = RT.t_setfreq (RT.tree_zero_freq (Z.to_nat RT.L_CODES) 0 (RT.ts_trees ts RT.TK_L)) RT.END_BLOCK 1
  /\ RT.ts_trees ts' RT.TK_D = RT.tree_zero_freq (Z.to_nat RT.D_CODES) 0 (RT.ts_trees ts RT.TK_D)
  /\ RT.ts_trees ts' RT.TK_BL = RT.tree_zero_freq (Z.to_nat RT.BL_CODES) 0 (RT.ts_trees ts RT.TK_BL)
  /\ RT.ts_maxcode ts' = RT.ts_maxcode ts /\ RT.ts_blcount ts' = RT.ts_blcount ts
  /\ RT.ts_heap ts' = RT.ts_heap ts /\ RT.ts_heaplen ts' = RT.ts_heaplen ts
  /\ RT.ts_heapmax ts' = RT.ts_heapmax ts /\ RT.ts_depth ts' = RT.ts_depth ts
  /\ RT.ts_symbuf ts' = RT.ts_symbuf ts /\ RT.ts_symnext ts' = 0
  /\ RT.ts_optlen ts' = 0 /\ RT.ts_statlen ts' = 0 /\ RT.ts_matches ts' = 0
  /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof.
  intros ts. unfold RT.init_block. cbv zeta.
  cbn [RT.ts_trees RT.ts_maxcode RT.ts_blcount RT.ts_heap RT.ts_heaplen RT.ts_heapmax RT.ts_depth
       RT.ts_symbuf RT.ts_symnext RT.ts_optlen RT.ts_statlen RT.ts_matches RT.ts_bw
       RT.set_matches RT.set_symnext RT.set_statlen RT.set_optlen RT.set_tree RT.set_trees].
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Clearing frequencies                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma tzf_fc : forall n i t j,
  RT.tr_fc (RT.tree_zero_freq n i t) j = if (i <=? j) && (j <? i + Z.of_nat n) then 0 else RT.tr_fc t j.
Proof.
  induction n as [|n IH]; intros i t j; cbn [RT.tree_zero_freq].
  - replace (i + Z.of_nat 0) with i by lia. destruct (Z.leb_spec i j), (Z.ltb_spec j i); cbn; try lia; reflexivity.
  - rewrite IH. unfold RT.t_setfreq. cbn [RT.tr_fc]. unfold Base.zset.
    destruct (Z.eqb_spec j i) as [->|N].
    + replace ((i + 1 <=? i) && (i <? i + 1 + Z.of_nat n)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((i <=? i) && (i <? i + Z.of_nat (S n))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      reflexivity.
    + replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
      destruct (Z.leb_spec (i + 1) j), (Z.leb_spec i j), (Z.ltb_spec j (i + Z.of_nat (S n))); cbn; try lia; reflexivity.
Qed.

Lemma tzf_dl : forall n i t, RT.tr_dl (RT.tree_zero_freq n i t) = RT.tr_dl t.
Proof. induction n as [|n IH]; intros i t; cbn [RT.tree_zero_freq]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(** Rewrite with these rather than [unfold t_setfreq; cbn [tr_dl]]: on a
    [tree_zero_freq] argument the latter makes the kernel check at [Qed]
    run for minutes. *)
Lemma tsf_fc : forall t i v, RT.tr_fc (RT.t_setfreq t i v) = Base.zset (RT.tr_fc t) i (Base.u16 v).
Proof. reflexivity. Qed.
Lemma tsf_dl : forall t i v, RT.tr_dl (RT.t_setfreq t i v) = RT.tr_dl t.
Proof. reflexivity. Qed.

Lemma fill_rel : forall a t n hi,
  arr_rel a (RT.tr_fc t) 0 hi -> hi <= arr_len a -> 0 <= n ->
  arr_rel (arr_fill a 0 n 0) (RT.tr_fc (RT.tree_zero_freq (Z.to_nat n) 0 t)) 0 hi.
Proof.
  intros a t n hi H Hhi Hn j Hj. rewrite arr_get_fill, tzf_fc. unfold arr_inb.
  rewrite Z2Nat.id by lia. replace (Z.max 0 n) with n by lia.
  destruct (Z.leb_spec 0 j); [|lia]. destruct (Z.ltb_spec j (0 + n)); destruct (Z.ltb_spec j (arr_len a)); cbn; try lia.
  all: first [reflexivity | apply H; exact Hj].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Ltac ib_fields :=
  autorewrite with s5f_matches s5f_sym_next s5f_static_len s5f_opt_len s5f_bl_tree_fc s5f_dyn_dtree_fc s5f_dyn_ltree_fc.

(** S5's [init_block], field by field (each proved by unfolding it down to
    its setters only: the kernel then never has to compare unfolded
    [arr_fill]s, which it cannot do in reasonable time). *)
Lemma ib_s5_fields : forall s,
  let s' := DT.init_block s in
  DS.ds_dyn_ltree_fc s' = arr_set (arr_fill (DS.ds_dyn_ltree_fc s) 0 DS.L_CODES 0) DS.END_BLOCK (wrap16 1)
  /\ DS.ds_dyn_ltree_dl s' = DS.ds_dyn_ltree_dl s
  /\ DS.ds_dyn_dtree_fc s' = arr_fill (DS.ds_dyn_dtree_fc s) 0 DS.D_CODES 0
  /\ DS.ds_dyn_dtree_dl s' = DS.ds_dyn_dtree_dl s
  /\ DS.ds_bl_tree_fc s' = arr_fill (DS.ds_bl_tree_fc s) 0 DS.BL_CODES 0
  /\ DS.ds_bl_tree_dl s' = DS.ds_bl_tree_dl s
  /\ DS.ds_bl_count s' = DS.ds_bl_count s /\ DS.ds_heap s' = DS.ds_heap s /\ DS.ds_depth s' = DS.ds_depth s
  /\ DS.ds_l_max_code s' = DS.ds_l_max_code s /\ DS.ds_d_max_code s' = DS.ds_d_max_code s
  /\ DS.ds_bl_max_code s' = DS.ds_bl_max_code s
  /\ DS.ds_heap_len s' = DS.ds_heap_len s /\ DS.ds_heap_max s' = DS.ds_heap_max s
  /\ DS.ds_opt_len s' = 0 /\ DS.ds_static_len s' = 0 /\ DS.ds_matches s' = 0 /\ DS.ds_sym_next s' = 0.
Proof.
  intros s. cbv zeta. ib_unfold. ib_fields.
  repeat (split; [reflexivity|]). reflexivity.
Qed.

Section Pair.
Variables (s : DS.deflate_state) (ts : RT.TSt).
Hypothesis H : trel s ts.
Hypothesis Hl : TM.tree_lens s.


(* One lemma per conjunct of [trel]: kept separate because the kernel
   checks the whole-goal version far too slowly. *)
Lemma ib_c1 : arr_rel (DS.ds_dyn_ltree_fc (DT.init_block s))
                      (RT.tr_fc (RT.ts_trees (RT.init_block ts) RT.TK_L)) 0 DS.HEAP_SIZE.
Proof.
  destruct (rt_init_block_facts ts) as (R1 & _). destruct (ib_s5_fields s) as (S1 & _). destruct H as (T1 & _). destruct Hl as (L1 & _).
  rewrite S1, R1, tsf_fc, <- wrap16_u16.
  apply arr_rel_set.
  - apply fill_rel; [exact T1 | unfold DS.HEAP_SIZE; lia | unfold RT.L_CODES; lia].
  - rewrite arr_len_fill. unfold DS.HEAP_SIZE in *. lia.
Qed.

Lemma ib_c2 : arr_rel (DS.ds_dyn_ltree_dl (DT.init_block s))
                      (RT.tr_dl (RT.ts_trees (RT.init_block ts) RT.TK_L)) 0 DS.HEAP_SIZE.
Proof.
  destruct (rt_init_block_facts ts) as (R1 & _). destruct (ib_s5_fields s) as (_ & S2 & _). destruct H as (_ & T2 & _).
  rewrite S2, R1, tsf_dl, tzf_dl. exact T2.
Qed.

Lemma ib_c3 : arr_rel (DS.ds_dyn_dtree_fc (DT.init_block s))
                      (RT.tr_fc (RT.ts_trees (RT.init_block ts) RT.TK_D)) 0 (2 * DS.D_CODES + 1).
Proof.
  destruct (rt_init_block_facts ts) as (_ & R2 & _). destruct (ib_s5_fields s) as (_ & _ & S3 & _). destruct H as (_ & _ & T3 & _).
  destruct Hl as (_ & _ & L3 & _).
  rewrite S3, R2. apply fill_rel; [exact T3 | unfold DS.D_CODES; lia | unfold RT.D_CODES; lia].
Qed.

Lemma ib_c4 : arr_rel (DS.ds_dyn_dtree_dl (DT.init_block s))
                      (RT.tr_dl (RT.ts_trees (RT.init_block ts) RT.TK_D)) 0 (2 * DS.D_CODES + 1).
Proof.
  destruct (rt_init_block_facts ts) as (_ & R2 & _). destruct (ib_s5_fields s) as (_ & _ & _ & S4 & _). destruct H as (_ & _ & _ & T4 & _).
  rewrite S4, R2, tzf_dl. exact T4.
Qed.

Lemma ib_c5 : arr_rel (DS.ds_bl_tree_fc (DT.init_block s))
                      (RT.tr_fc (RT.ts_trees (RT.init_block ts) RT.TK_BL)) 0 (2 * DS.BL_CODES + 1).
Proof.
  destruct (rt_init_block_facts ts) as (_ & _ & R3 & _). destruct (ib_s5_fields s) as (_ & _ & _ & _ & S5 & _). destruct H as (_ & _ & _ & _ & T5 & _).
  destruct Hl as (_ & _ & _ & _ & L5 & _).
  rewrite S5, R3. apply fill_rel; [exact T5 | unfold DS.BL_CODES; lia | unfold RT.BL_CODES; lia].
Qed.

Lemma ib_c6 : arr_rel (DS.ds_bl_tree_dl (DT.init_block s))
                      (RT.tr_dl (RT.ts_trees (RT.init_block ts) RT.TK_BL)) 0 (2 * DS.BL_CODES + 1).
Proof.
  destruct (rt_init_block_facts ts) as (_ & _ & R3 & _). destruct (ib_s5_fields s) as (_ & _ & _ & _ & _ & S6 & _).
  destruct H as (_ & _ & _ & _ & _ & T6 & _).
  rewrite S6, R3, tzf_dl. exact T6.
Qed.

Lemma ib_rest :
  arr_rel (DS.ds_bl_count (DT.init_block s)) (RT.ts_blcount (RT.init_block ts)) 0 (DS.MAX_BITS + 1)
  /\ arr_rel (DS.ds_heap (DT.init_block s)) (RT.ts_heap (RT.init_block ts)) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_depth (DT.init_block s)) (RT.ts_depth (RT.init_block ts)) 0 DS.HEAP_SIZE
  /\ DS.ds_l_max_code (DT.init_block s) = RT.ts_maxcode (RT.init_block ts) RT.TK_L
  /\ DS.ds_d_max_code (DT.init_block s) = RT.ts_maxcode (RT.init_block ts) RT.TK_D
  /\ DS.ds_bl_max_code (DT.init_block s) = RT.ts_maxcode (RT.init_block ts) RT.TK_BL
  /\ DS.ds_heap_len (DT.init_block s) = RT.ts_heaplen (RT.init_block ts)
  /\ DS.ds_heap_max (DT.init_block s) = RT.ts_heapmax (RT.init_block ts)
  /\ DS.ds_opt_len (DT.init_block s) = RT.ts_optlen (RT.init_block ts)
  /\ DS.ds_static_len (DT.init_block s) = RT.ts_statlen (RT.init_block ts)
  /\ DS.ds_matches (DT.init_block s) = RT.ts_matches (RT.init_block ts).
Proof.
  destruct (rt_init_block_facts ts) as (_ & _ & _ & R4 & R5 & R6 & R7 & R8 & R9 & _ & _ & R12 & R13 & R14 & _).
  destruct (ib_s5_fields s) as (_ & _ & _ & _ & _ & _ & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & _).
  destruct H as (_ & _ & _ & _ & _ & _ & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & _).
  rewrite S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, R4, R5, R6, R7, R8, R12, R13, R14.
  exact (conj T7 (conj T8 (conj T9 (conj T10 (conj T11 (conj T12 (conj T13 (conj T14
          (conj eq_refl (conj eq_refl eq_refl)))))))))).
Qed.

End Pair.

Theorem br_init_block : forall s ts,
  trel s ts -> TM.tree_lens s ->
  trel (DT.init_block s) (RT.init_block ts)
  /\ DS.ds_sym_next (DT.init_block s) = RT.ts_symnext (RT.init_block ts)
  /\ RT.ts_symnext (RT.init_block ts) = 0
  /\ RT.ts_symbuf (RT.init_block ts) = RT.ts_symbuf ts /\ RT.ts_bw (RT.init_block ts) = RT.ts_bw ts.
Proof.
  intros s ts H Hl.
  destruct (rt_init_block_facts ts) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & R11 & _ & _ & _ & R15).
  destruct (ib_s5_fields s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S18).
  split; [|split; [rewrite S18, R11; reflexivity | split; [exact R11 | split; [exact R10 | exact R15]]]].
  exact (conj (ib_c1 s ts H Hl) (conj (ib_c2 s ts H) (conj (ib_c3 s ts H Hl) (conj (ib_c4 s ts H)
          (conj (ib_c5 s ts H Hl) (conj (ib_c6 s ts H) (ib_rest s ts H))))))).
Qed.

Print Assumptions br_init_block.
