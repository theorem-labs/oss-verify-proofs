(** * Bridge.DEmit.BrSbs — a run of [send_bits] calls, S5 vs RT.

    S5's own proofs describe every block body (the tree header, the
    [send_tree] loops' codes, [compress_block] over the pristine symbols,
    see [RiskIface.ov_compress_block]) as [SendModel.sbs_run] over a list of
    [(value, length)] calls, with [SendModel.sbs_ok] as the room condition:
    room for two bytes only when a call actually emits ([sb_room]).  This
    file relates that to RT's bit writer run over the same calls
    ([rt_sbs]).  [br_send_bits_sb] is [BrBits.br_send_bits] with S5's
    weaker room premise. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.
Module SM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.SendModel.

(** RT's run of the same calls. *)
Fixpoint rt_sbs (b : ZBitsOut.BW) (cs : list (Z * Z)) : ZBitsOut.BW :=
  match cs with
  | [] => b
  | (v, l) :: r => rt_sbs (ZBitsOut.bw_send_bits v l b) r
  end.

Lemma rt_sbs_app : forall a c b, rt_sbs b (a ++ c) = rt_sbs (rt_sbs b a) c.
Proof. induction a as [|[v l] a IH]; intros; [reflexivity|]. cbn. apply IH. Qed.

Lemma send_bits_frame : forall s v l,
  DS.ds_pending_out (DT.send_bits s v l) = DS.ds_pending_out s
  /\ arr_len (DS.ds_pending_buf (DT.send_bits s v l)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s v l. split; [|apply SM.sb_pbl].
  rewrite SM.send_bits_shape. unfold SM.upd4.
  autorewrite with s5f_bi_valid s5f_bi_buf s5f_pending s5f_pending_buf. reflexivity.
Qed.

Theorem br_send_bits_sb : forall s b v l,
  bw_rel s b -> DS.ds_pending_out s = 0 -> 0 <= l <= 16 ->
  SM.sb_room (arr_len (DS.ds_pending_buf s)) s l ->
  bw_rel (DT.send_bits s v l) (ZBitsOut.bw_send_bits v l b)
  /\ DS.ds_pending_out (DT.send_bits s v l) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_bits s v l)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s b v l Hrel Hpo Hl Hroom.
  destruct (send_bits_frame s v l) as [F1 F2]. rewrite F1, F2. split; [|split; [exact Hpo | reflexivity]].
  unfold SM.sb_room in Hroom.
  destruct (Z.ltb_spec (DS.Buf_size - l) (DS.ds_bi_valid s)) as [C|C].
  - apply br_send_bits; [exact Hrel|]. split; [exact Hpo|]. apply Hroom. exact C.
  - destruct Hrel as (Hp & Hb & Hv).
    unfold DT.send_bits, ZBitsOut.bw_send_bits. cbv zeta.
    change ZBitsOut.Buf_size with DS.Buf_size. rewrite <- Hv.
    replace (DS.Buf_size - l <? DS.ds_bi_valid s) with false by (symmetry; apply Z.ltb_ge; exact C).
    unfold bw_rel, pend_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
    autorewrite with s5f_bi_valid s5f_bi_buf. rewrite <- Hb, !wrap16_u16.
    split; [exact Hp|]. split; reflexivity.
Qed.

Theorem br_sbs_run : forall cs s b,
  bw_rel s b -> DS.ds_pending_out s = 0 -> SM.sbs_ok (arr_len (DS.ds_pending_buf s)) s cs ->
  bw_rel (SM.sbs_run s cs) (rt_sbs b cs)
  /\ DS.ds_pending_out (SM.sbs_run s cs) = 0
  /\ arr_len (DS.ds_pending_buf (SM.sbs_run s cs)) = arr_len (DS.ds_pending_buf s).
Proof.
  induction cs as [|[v l] cs IH]; intros s b Hb Hpo Hok; cbn [SM.sbs_run rt_sbs SM.sbs_ok] in *.
  - split; [exact Hb|]. split; [exact Hpo | reflexivity].
  - destruct Hok as (Hl & Hr & Hok).
    destruct (br_send_bits_sb s b v l Hb Hpo Hl Hr) as (Hb1 & Hpo1 & Hlen1).
    rewrite <- Hlen1 in Hok.
    destruct (IH _ _ Hb1 Hpo1 Hok) as (R1 & R2 & R3).
    split; [exact R1|]. split; [exact R2|]. rewrite R3. exact Hlen1.
Qed.

Print Assumptions br_sbs_run.
