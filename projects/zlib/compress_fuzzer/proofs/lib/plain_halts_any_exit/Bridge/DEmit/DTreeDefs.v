(** * Bridge.DEmit.DTreeDefs — the definitions group D's tree pairs share.

    The trees are compared on RT's [TSt] alone: [trel] is [IRelDefl.tree_rel]
    with the [TSt] in place of [d_ts t] ([tree_rel_trel]).  [DTreeIface]
    states the tree pairs over these and re-exports their proofs.

    Ownership: group D (a worker). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel GenBitlenModel SendModel
  FlushBlockModel RefSendTree4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module GBM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.GenBitlenModel.
Module FBM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.FlushBlockModel.
Module ST4 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.
Module SM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.SendModel.

Definition trel (s : DS.deflate_state) (ts : RT.TSt) : Prop :=
  let L := RT.ts_trees ts RT.TK_L in
  let D := RT.ts_trees ts RT.TK_D in
  let B := RT.ts_trees ts RT.TK_BL in
  arr_rel (DS.ds_dyn_ltree_fc s) (RT.tr_fc L) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_dyn_ltree_dl s) (RT.tr_dl L) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_dyn_dtree_fc s) (RT.tr_fc D) 0 (2 * DS.D_CODES + 1)
  /\ arr_rel (DS.ds_dyn_dtree_dl s) (RT.tr_dl D) 0 (2 * DS.D_CODES + 1)
  /\ arr_rel (DS.ds_bl_tree_fc s) (RT.tr_fc B) 0 (2 * DS.BL_CODES + 1)
  /\ arr_rel (DS.ds_bl_tree_dl s) (RT.tr_dl B) 0 (2 * DS.BL_CODES + 1)
  /\ arr_rel (DS.ds_bl_count s) (RT.ts_blcount ts) 0 (DS.MAX_BITS + 1)
  /\ arr_rel (DS.ds_heap s) (RT.ts_heap ts) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_depth s) (RT.ts_depth ts) 0 DS.HEAP_SIZE
  /\ DS.ds_l_max_code s = RT.ts_maxcode ts RT.TK_L
  /\ DS.ds_d_max_code s = RT.ts_maxcode ts RT.TK_D
  /\ DS.ds_bl_max_code s = RT.ts_maxcode ts RT.TK_BL
  /\ DS.ds_heap_len s = RT.ts_heaplen ts /\ DS.ds_heap_max s = RT.ts_heapmax ts
  /\ DS.ds_opt_len s = RT.ts_optlen ts /\ DS.ds_static_len s = RT.ts_statlen ts
  /\ DS.ds_matches s = RT.ts_matches ts.

Lemma tree_rel_trel : forall s t, tree_rel s t <-> trel s (RD.d_ts t).
Proof. intros s t. split; intros H; exact H. Qed.

(** S5's tree ids as RT's tree kinds. *)
Definition tk_of (t : DS.tree_id) : Z :=
  match t with DS.TL => RT.TK_L | DS.TD => RT.TK_D | DS.TB => RT.TK_BL end.

(** RT's [scan_tree] returns the guarded tree and the new [bl_tree];
    [build_bl_tree] installs both. *)
Definition scan_ts (k mc : Z) (ts : RT.TSt) : RT.TSt :=
  let p := RT.scan_tree (RT.ts_trees ts k) mc (RT.ts_trees ts RT.TK_BL) in
  RT.set_tree RT.TK_BL (snd p) (RT.set_tree k (fst p) ts).

(** The code lengths [scan_tree]/[send_tree] walk are at most 15 up to
    [mc] (so every [bl_tree] index they touch is below 19), and the guard
    slot [mc + 1] is inside the array. *)
Definition scan_ok (s : DS.deflate_state) (t : DS.tree_id) (mc : Z) : Prop :=
  t <> DS.TB /\ 0 <= mc /\ mc + 1 < TM.tsize t
  /\ (forall i, 0 <= i <= mc -> 0 <= DS.Len s t i <= 15).

(** The bit-length tree's code lengths are usable [send_bits] lengths. *)
Definition bl_lens_ok (s : DS.deflate_state) : Prop :=
  forall i, 0 <= i < DS.BL_CODES -> 0 <= DS.Len s DS.TB i <= 16.
