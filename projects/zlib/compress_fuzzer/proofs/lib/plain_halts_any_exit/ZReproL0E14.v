(* the zlib 1.4 twin of ZReproL0E, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from ZReproL0E), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * ZReproL0E — the (0,15) pump FACE: flush transfer for the one-shot read.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  Residual (ii)
    of the Q2 close-out.  [ZReproL0C.zr_inflate_l0_stream] runs the whole
    inflate walk at [Z_FINISH]; [ZR_PumpSucceeds] quantifies the flush over
    [ZR_Flush1] ([Z_NO_FLUSH] or [Z_FINISH]).  Rather than replaying the
    walk, this file proves the TRANSFER: for any flush that is neither
    [Z_BLOCK] nor [Z_TREES], the step machine is flush-blind (its only
    [InfCtx] reads are [n_flush =? Z_BLOCK/Z_TREES] tests — measured:
    Inflate.v:1289/1408/1435/1449 are the only [n_flush] sites in the step
    cone, and [n_walloc]/[n_wfresh] are read only by [inf_leave]), and at
    the leave the two flushes can differ only in (a) the [updatewindow]
    branch, which touches window fields the result projections never read,
    and (b) the [Z_BUF_ERROR] rewrite, dead on a [Z_STREAM_END] return.
    So a [Z_STREAM_END] answer at [Z_FINISH] IS a [Z_STREAM_END] answer at
    [Z_NO_FLUSH], byte-for-byte on the output.

    Why the face excludes [Z_BLOCK]/[Z_TREES]: at those flushes the TYPE
    arm leaves the loop at the first block boundary with [Z_OK], and the
    one-shot read's [Z_STREAM_END] gate fails — the face would be FALSE
    there.  The negative control at the bottom pins that.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool Setoid.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  GtAdlerChunk GtAdlerLoop ZRepro ZReproL0 ZReproL0B ZReproL0C.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14 ZRepro14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Flush-blindness of the step machine.
   ========================================================================== *)




Lemma zr_CODELENS_ctx14 : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_CODELENS14 c1 q = inf_CODELENS14 c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_CODELENS14.
  now rewrite (zr_eqb_nT c1), (zr_eqb_nT c2) by assumption.
Qed.

Lemma zr_LENLENS_ctx14 : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_LENLENS14 c1 q = inf_LENLENS14 c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_LENLENS14. cbv zeta.
  match goal with |- context [ll_go ?a ?b ?c ?d ?e] =>
    destruct (ll_go a b c d e) end; cbv beta iota; [|reflexivity].
  match goal with |- context [ll_zero ?a ?b ?c] =>
    destruct (ll_zero a b c) end; cbv beta iota.
  match goal with |- context [inf_table ?a ?b ?c ?d ?e ?f] =>
    destruct (inf_table a b c d e f) as [[[[rc bc] nx] cd]|] end;
    cbv beta iota; [|reflexivity].
  destruct (negb (rc =? 0)); cbv beta iota;
    [reflexivity | apply zr_CODELENS_ctx14; assumption].
Qed.

Lemma zr_TABLE_ctx14 : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_TABLE14 c1 q = inf_TABLE14 c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_TABLE14. cbv zeta.
  match goal with |- context [inf_nb ?a ?b] =>
    destruct (inf_nb a b) end; cbv beta iota; [|reflexivity].
  match goal with |- context [if ?b then _ else _] =>
    destruct b end; cbv beta iota;
    [reflexivity | apply zr_LENLENS_ctx14; assumption].
Qed.






Lemma zr_HEAD_ctx14 : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_HEAD14 c1 q = inf_HEAD14 c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_HEAD14. cbv zeta.
  match goal with |- context [if ?b then _ else _] =>
    destruct b end; cbv beta iota;
    [apply zr_TYPEDO_ctx; assumption | reflexivity].
Qed.

Lemma zr_step_ctx14 : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_step14 c1 q = inf_step14 c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_step14.
  (* bullets keyed to Mode's constructor order (Inflate.v:200-206) *)
  destruct (q_mode q);
    [ apply zr_HEAD_ctx14; assumption
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity
    | apply zr_DICTID_ctx; assumption
    | apply zr_DICT_ctx; assumption
    | apply zr_TYPE_ctx; assumption
    | apply zr_TYPEDO_ctx; assumption
    | apply zr_STORED_ctx; assumption
    | reflexivity | reflexivity
    | apply zr_TABLE_ctx14; assumption
    | apply zr_LENLENS_ctx14; assumption
    | apply zr_CODELENS_ctx14; assumption
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity ].
Qed.

Lemma zr_loop_ctx14 : forall c1 c2 n q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_loop14 n c1 q = inf_loop14 n c2 q.
Proof.
  intros c1 c2 n q H1 H2. revert q.
  induction n as [|n IH]; intro q; [reflexivity|].
  cbn [inf_loop14]. rewrite (zr_step_ctx14 c1 c2 q H1 H2).
  destruct (inf_step14 c2 q); try reflexivity. apply IH.
Qed.

(* ==========================================================================
   2.  Leave observations.
   ========================================================================== *)

(** [uw] with the allocation flag set never fails, and touches only the
    window: the header record and bit count survive. *)

(** The tail's output buffer is whatever came in. *)

(** The tail's return code, as a closed formula over the fields it reads:
    the flush enters ONLY through the [=? Z_FINISH] disjunct of the
    Z_BUF_ERROR condition, and that condition is guarded by
    [q_ret Q =? Z_OK]. *)

(** Every branch of [inf_leave] (window update taken or not) lands on the
    same return formula and leaves the output buffer alone — provided the
    window allocation flag is live, which kills the Z_MEM_ERROR arm. *)

(** The transfer at the leave: a Z_STREAM_END verdict moves across
    contexts, with the output buffer intact. *)

(* ==========================================================================
   3.  The call-level transfer.
   ========================================================================== *)

Lemma zr_inf_call_transfer14 : forall f s z inb cap r4 u4 st4 z4 out4,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inf_call14 Z_FINISH s z inb cap = Some (r4, u4, st4, z4, out4) ->
  r4 = Z_STREAM_END ->
  exists u1 st1 z1,
    zr_inf_call14 f s z inb cap = Some (r4, u1, st1, z1, out4).
Proof.
  intros f s z inb cap r4 u4 st4 z4 out4 HB HT H4 HSE.
  assert (OKf : zr_cflush_ok {| n_flush := f; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush]; assumption).
  assert (OK4 : zr_cflush_ok {| n_flush := Z_FINISH; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush];
        unfold Z_FINISH, Z_BLOCK, Z_TREES; lia).
  unfold zr_inf_call14, inflate_model14 in H4 |- *.
  cbv beta iota zeta
      delta [inf_ctx inf_st0 g_st g_state_null g_z g_inbuf g_next_in
             g_avail_in g_in_null g_outbuf g_next_out g_avail_out
             g_out_null g_flush g_walloc g_wfresh orb andb negb]
      in H4 |- *.
  rewrite (zr_loop_ctx14 {| n_flush := f; n_walloc := true;
                          n_wfresh := zzero |}
                       {| n_flush := Z_FINISH; n_walloc := true;
                          n_wfresh := zzero |})
    by assumption.
  destruct (inf_loop14 _ _ _) as [step|] eqn:EL;
    [| cbv beta iota in H4; discriminate ].
  (* NOTE: this destruct substitutes into H4 as well (measured — the
     hypothesis already carries [Some step]/[None] afterwards). *)
  destruct step as [q'|q'|q' r'|m'|];
    cbv beta iota in H4;
    try discriminate.
  - (* InfLeave: transfer the leave observations *)
    destruct (inf_leave {| n_flush := Z_FINISH; n_walloc := true;
                           n_wfresh := zzero |} q') as [q2 r2] eqn:E4.
    cbv beta iota delta [r_ret r_q] in H4.
    injection H4 as <- <- <- <- <-.
    destruct (zr_leave_obs {| n_flush := f; n_walloc := true;
                              n_wfresh := zzero |}
                           {| n_flush := Z_FINISH; n_walloc := true;
                              n_wfresh := zzero |} q'
                eq_refl eq_refl
                ltac:(rewrite E4; cbn [snd]; exact HSE))
      as [R1 O1].
    destruct (inf_leave {| n_flush := f; n_walloc := true;
                           n_wfresh := zzero |} q') as [q1 r1] eqn:E1.
    rewrite ?E4 in O1.
    cbn [fst snd] in R1, O1.
    cbv beta iota delta [r_ret r_q].
    do 3 eexists.
    rewrite R1, HSE, O1. reflexivity.
  - (* InfRet: flush-free result *)
    injection H4 as <- <- <- <- <-.
    do 3 eexists. reflexivity.
Qed.

(* ==========================================================================
   4.  The faces: the transfer at [zr_inflate], and the pump face.
   ========================================================================== *)

Theorem zr_inflate_transfer14 : forall f wb cap enc y,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inflate14 Z_FINISH wb cap enc = Some y ->
  zr_inflate14 f wb cap enc = Some y.
Proof.
  intros f wb cap enc y HB HT H.
  unfold zr_inflate14 in H |- *.
  destruct (inflateInit2 z_fresh state_fresh wb) as [[z s]|]; [|discriminate].
  destruct (zr_inf_call14 Z_FINISH s z enc cap)
    as [[[[[r4 u4] st4] z4] out4]|] eqn:EC; [|discriminate].
  destruct (Z.eqb r4 Z_STREAM_END) eqn:ER; [|discriminate].
  apply Z.eqb_eq in ER.
  destruct (zr_inf_call_transfer14 f s z enc cap r4 u4 st4 z4 out4
              HB HT EC ER) as (u1 & st1 & z1 & EC1).
  rewrite EC1. rewrite <- H. now rewrite (proj2 (Z.eqb_eq _ _) ER).
Qed.


(* ==========================================================================
   5.  Controls.  Positive: the NO_FLUSH one-shot read computes end-to-end
       on an emitted stream.  Negative: at Z_BLOCK the loop leaves at the
       first block boundary with Z_OK and the one-shot gate fails — the
       face's ZR_Flush1 restriction is load-bearing, not decorative.
   ========================================================================== *)



