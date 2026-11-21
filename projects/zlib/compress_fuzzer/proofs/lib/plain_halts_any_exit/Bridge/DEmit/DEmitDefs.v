(** * Bridge.DEmit.DEmitDefs — the definitions group D's pair statements use.

    Split out of [DEmitIface] (which re-exports this file) so that group D's
    proof files can import the definitions and [DEmitIface] can in turn
    import the proofs: no file of the interface is changed in meaning, and a
    consumer that does [Require Import DEmitIface] sees exactly the same
    names.  See [DEmitIface] for what each definition is for.

    Ownership: group D (a worker).  Reviewer: the part C lead. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk TreeModel DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [DL] (S5's DeflateLz) and [bs_of] (S5 block state -> RT's) come from
   [IRelDefl], shared with group M. *)
Module DT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.
Module DB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module TM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.TreeModel.
Module DO := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateOverlay.

(* ------------------------------------------------------------------------- *)
(* 1.  The side conditions                                                   *)
(* ------------------------------------------------------------------------- *)

(** The emission-side invariant.  Field for field, the fields of
    [RefDeflSafeFB.fb_entry] that do not mention the window, [strstart],
    [lookahead] or [block_start], plus [ec_pout]/[ec_pending] (the queue is
    empty: zlib drains it before the deflate loop runs and after every flush
    that leaves [avail_out > 0]) and [ec_room] (RT's [total_out] is a plain
    [Z], S5's wraps at 2^64; [total_out + avail_out] is constant across a
    flush). *)
Record em_core (s : DS.deflate_state) : Prop := {
  ec_level : 1 <= DS.ds_level s <= 9;
  ec_strategy : 0 <= DS.ds_strategy s <= 4;
  ec_dt : - 2 ^ 31 <= DS.cs_data_type (DS.ds_strm s) < 2 ^ 31;
  ec_lbs : 2048 <= DS.ds_lit_bufsize s <= 32768;
  ec_lbs2 : exists k, DS.ds_lit_bufsize s = 2 ^ k;
  ec_pbl : arr_len (DS.ds_pending_buf s) = DS.ds_lit_bufsize s * 4;
  ec_symend : DS.ds_sym_end s = (DS.ds_lit_bufsize s - 1) * 3;
  ec_pending : DS.ds_pending s = 0;
  ec_pout : DS.ds_pending_out s = 0;
  ec_biv : 0 <= DS.ds_bi_valid s <= 7;
  ec_bib : 0 <= DS.ds_bi_buf s < 2 ^ 16;
  ec_pbb : forall i, 0 <= i < arr_len (DS.ds_pending_buf s) -> 0 <= arr_get (DS.ds_pending_buf s) i < 256;
  ec_tout : 0 <= DS.cs_total_out (DS.ds_strm s);
  ec_aout : 0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32;
  ec_room : DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s)
            + arr_len (DS.ds_pending_buf s) < 2 ^ 64;
  ec_sn : DS.ds_sym_next s = 3 * DO.nsym s;
  ec_nsym : 0 <= DO.nsym s <= DS.ds_lit_bufsize s - 1;
  ec_syms : forall j, 0 <= j < DO.nsym s -> DO.sym_okb s j;
  ec_hist : DO.freq_hist s;
  ec_optlen : DS.ds_opt_len s = 0;
  ec_statlen : DS.ds_static_len s = 0;
  ec_tl : TM.tree_lens s;
  ec_fc : forall t i, 0 <= arr_get (DS.tree_fc s t) i < 65536;
  ec_dl : forall t i, 0 <= arr_get (DS.tree_dl s t) i < 65536;
  ec_depth : forall i, 0 <= arr_get (DS.ds_depth s) i < 256;
  ec_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (DS.ds_bl_count s) i < 65536 }.

(** Between two trips of the deflate loops: room for one more symbol
    ([sym_next < sym_end]). *)
Definition em_inv (s : DS.deflate_state) : Prop :=
  em_core s /\ DO.nsym s < DS.ds_lit_bufsize s - 1.

(** The window/[strstart] facts a flush needs (the rest of [fb_entry]),
    on RT's side, over [d_cfg] and [d_ls] only. *)
Definition fb_lz (t : RD.DSt) : Prop :=
  256 <= RC.dg_w_size (RD.d_cfg t) <= 32768
  /\ RD.ls_windowsize (RD.d_ls t) = 2 * RC.dg_w_size (RD.d_cfg t)
  /\ 0 <= RD.ls_strstart (RD.d_ls t) <= RD.ls_windowsize (RD.d_ls t)
  /\ 0 <= RD.ls_lookahead (RD.d_ls t) <= RD.ls_windowsize (RD.d_ls t)
  /\ 0 <= RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t) < 2 ^ 32
  /\ - 2 ^ 63 <= RD.ls_blockstart (RD.d_ls t)
  /\ (forall i, 0 <= i < RD.ls_windowsize (RD.d_ls t) -> 0 <= RD.ls_window (RD.d_ls t) i < 256).

(** The fields [em_core] reads. *)
Definition em_view (s : DS.deflate_state) :=
  (DS.ds_level s, DS.ds_strategy s, DS.ds_lit_bufsize s, DS.ds_sym_end s,
   DS.ds_pending_buf s, DS.ds_pending s, DS.ds_pending_out s, DS.ds_bi_buf s, DS.ds_bi_valid s,
   DS.ds_sym_next s, DS.ds_opt_len s, DS.ds_static_len s,
   (DS.ds_dyn_ltree_fc s, DS.ds_dyn_ltree_dl s, DS.ds_dyn_dtree_fc s, DS.ds_dyn_dtree_dl s,
    DS.ds_bl_tree_fc s, DS.ds_bl_tree_dl s, DS.ds_bl_count s, DS.ds_heap s, DS.ds_depth s),
   (DS.cs_avail_out (DS.ds_strm s), DS.cs_total_out (DS.ds_strm s), DS.cs_data_type (DS.ds_strm s))).

(** Destruct both states down to their fields and identify the viewed ones;
    every [em_core] field statement then converts (only projections differ). *)
Local Ltac em_view_subst :=
  intros s s'; destruct s, s';
  repeat match goal with c : DS.cstrm |- _ => destruct c end;
  intros E; unfold em_view in E; cbn in E; injection E; intros; subst.

Lemma em_core_frame : forall s s', em_view s' = em_view s -> em_core s -> em_core s'.
Proof.
  em_view_subst. match goal with H : em_core _ |- _ => destruct H end. constructor; assumption.
Qed.

Lemma em_inv_frame : forall s s', em_view s' = em_view s -> em_inv s -> em_inv s'.
Proof.
  intros s s' E [H Hn]. split; [exact (em_core_frame s s' E H)|].
  clear H. revert s s' E Hn. em_view_subst. assumption.
Qed.

Lemma em_inv_core : forall s, em_inv s -> em_core s.
Proof. intros s [H _]. exact H. Qed.
