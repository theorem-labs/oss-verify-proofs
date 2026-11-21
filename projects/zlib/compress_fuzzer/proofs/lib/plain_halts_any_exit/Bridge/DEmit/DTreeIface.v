(** * Bridge.DEmit.DTreeIface — group D's tree pairs, as D22 ([BrFbPre], [BrFbEmit]) uses them.

    Pairs D26 (build_tree + pqdownheap), D27 (gen_bitlen), D28 (gen_codes,
    bi_reverse), D29 (scan_tree, send_tree), D30 (build_bl_tree,
    send_all_trees), D33 (detect_data_type) and D4 (init_block).  Each
    statement here is proved in its own file and re-exported:
    [BrBuildTree] (with [BrBuildTree0]-[BrBuildTree4]), [BrScanTree],
    [BrSendTree], [BrBlTree], [BrSendAll], [BrDetect], [BrInitBlock].
    Internal to group D (not consumed by other groups).

    The side conditions are S5's OWN safety predicates for the same calls
    ([GenBitlenModel.bt_safe], [RefSendTree4.send_tree_safe],
    [SendModel.sbs_ok]): S5's closed [FB_CALL] supplies all of them at a
    flush (inside [flush_ok]), and they give exactly what the bridge needs
    beyond the relation: every array index S5 touches is inside its array,
    every loop ends before its fuel runs out, and every emitting
    [send_bits] has room.

    [scan_tree]/[send_tree] also need [max_code < L_CODES]: RT's loops are
    fuelled [L_CODES + 3] steps where S5's run to [max_code]
    ([BrScanTree.scan_cex] computes a disagreement at [max_code = 400]);
    [br_build_tree_mc] gives the bound for every tree [build_tree] made. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel GenBitlenModel SendModel
  FlushBlockModel RefSendTree4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrSbs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Export DTreeDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require
  BrBuildTree BrScanTree BrSendTree BrBlTree BrSendAll BrDetect BrInitBlock.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  D26-D28: build_tree (with pqdownheap, gen_bitlen, gen_codes)          *)
(* ------------------------------------------------------------------------- *)

Theorem br_build_tree : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t ->
  trel (DT.build_tree s t) (RT.build_tree (tk_of t) ts).
Proof. exact BrBuildTree.br_build_tree. Qed.

Theorem br_build_tree_mc : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t ->
  -1 <= DS.max_code (DT.build_tree s t) t < DS.sd_elems t.
Proof. exact BrBuildTree.br_build_tree_mc. Qed.

Theorem br_build_tree_lens : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t -> TM.tree_lens (DT.build_tree s t).
Proof. exact BrBuildTree.br_build_tree_lens. Qed.

Lemma rt_build_tree_frame : forall k ts,
  let ts' := RT.build_tree k ts in
  RT.ts_symbuf ts' = RT.ts_symbuf ts /\ RT.ts_symnext ts' = RT.ts_symnext ts
  /\ RT.ts_matches ts' = RT.ts_matches ts /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof. exact BrBuildTree.rt_build_tree_frame. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  D29: scan_tree / send_tree                                            *)
(* ------------------------------------------------------------------------- *)

Theorem br_scan_tree : forall s ts t mc,
  trel s ts -> TM.tree_lens s -> scan_ok s t mc -> mc < DS.L_CODES ->
  trel (DT.scan_tree s t mc) (scan_ts (tk_of t) mc ts).
Proof. exact BrScanTree.br_scan_tree'. Qed.

Theorem br_send_tree : forall s b ts t mc,
  bw_rel s b -> trel s ts -> TM.tree_lens s -> scan_ok s t mc -> mc < DS.L_CODES -> bl_lens_ok s ->
  DS.ds_pending_out s = 0 ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s)) s t mc ->
  bw_rel (DT.send_tree s t mc) (RT.send_tree (RT.ts_trees ts (tk_of t)) mc (RT.ts_trees ts RT.TK_BL) b)
  /\ DS.ds_pending_out (DT.send_tree s t mc) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_tree s t mc)) = arr_len (DS.ds_pending_buf s).
Proof. exact BrSendTree.br_send_tree'. Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  D30: build_bl_tree / send_all_trees                                   *)
(* ------------------------------------------------------------------------- *)

Theorem br_build_bl_tree : forall s ts,
  trel s ts -> TM.tree_lens s ->
  scan_ok s DS.TL (DS.ds_l_max_code s) -> DS.ds_l_max_code s < DS.L_CODES ->
  scan_ok s DS.TD (DS.ds_d_max_code s) ->
  GBM.bt_safe (let s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s) in
               DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1)) DS.TB ->
  snd (DT.build_bl_tree s) = fst (RT.build_bl_tree ts)
  /\ trel (fst (DT.build_bl_tree s)) (snd (RT.build_bl_tree ts))
  /\ TM.tree_lens (fst (DT.build_bl_tree s)).
Proof. exact BrBlTree.br_build_bl_tree. Qed.

(** [lc]/[dc]/[bc] are the counts the dynamic block header announces; the
    three room conditions are those of S5's [RefFlushBlk12.dyn_ok] (the
    block's 3-bit header call is the first of its [hd_calls], already sent
    when [send_all_trees] starts). *)
Theorem br_send_all_trees : forall s b ts lc dc bc,
  bw_rel s b -> trel s ts -> TM.tree_lens s -> DS.ds_pending_out s = 0 ->
  lc = DS.ds_l_max_code s + 1 -> dc = DS.ds_d_max_code s + 1 -> 0 <= bc <= 19 -> lc <= DS.L_CODES ->
  scan_ok s DS.TL (lc - 1) -> scan_ok s DS.TD (dc - 1) -> bl_lens_ok s ->
  SM.sbs_ok (arr_len (DS.ds_pending_buf s)) s (FBM.sat_calls s lc dc bc) ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s)) (SM.sbs_run s (FBM.sat_calls s lc dc bc)) DS.TL (lc - 1) ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s))
    (DT.send_tree (SM.sbs_run s (FBM.sat_calls s lc dc bc)) DS.TL (lc - 1)) DS.TD (dc - 1) ->
  bw_rel (DT.send_all_trees s lc dc bc) (RT.send_all_trees lc dc bc (RT.set_bw b ts))
  /\ DS.ds_pending_out (DT.send_all_trees s lc dc bc) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_all_trees s lc dc bc)) = arr_len (DS.ds_pending_buf s).
Proof. exact BrSendAll.br_send_all_trees'. Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  D33: detect_data_type; D4: init_block                                 *)
(* ------------------------------------------------------------------------- *)

Theorem br_detect_data_type : forall s ts,
  trel s ts -> DT.detect_data_type s = RT.detect_data_type (RT.ts_trees ts RT.TK_L).
Proof. exact BrDetect.br_detect_data_type. Qed.

Theorem br_init_block : forall s ts,
  trel s ts -> TM.tree_lens s ->
  trel (DT.init_block s) (RT.init_block ts)
  /\ DS.ds_sym_next (DT.init_block s) = RT.ts_symnext (RT.init_block ts)
  /\ RT.ts_symnext (RT.init_block ts) = 0
  /\ RT.ts_symbuf (RT.init_block ts) = RT.ts_symbuf ts /\ RT.ts_bw (RT.init_block ts) = RT.ts_bw ts.
Proof. exact BrInitBlock.br_init_block. Qed.

Print Assumptions br_build_tree.
Print Assumptions br_build_bl_tree.
Print Assumptions br_send_all_trees.
Print Assumptions br_send_tree.
Print Assumptions br_detect_data_type.
Print Assumptions br_init_block.
