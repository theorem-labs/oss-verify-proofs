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
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Flush-blindness of the step machine.
   ========================================================================== *)

Definition zr_cflush_ok (c : InfCtx) : Prop :=
  n_flush c <> Z_BLOCK /\ n_flush c <> Z_TREES.

Lemma zr_eqb_nB : forall c, zr_cflush_ok c -> (n_flush c =? Z_BLOCK) = false.
Proof. intros c [H _]. apply Z.eqb_neq. exact H. Qed.

Lemma zr_eqb_nT : forall c, zr_cflush_ok c -> (n_flush c =? Z_TREES) = false.
Proof. intros c [_ H]. apply Z.eqb_neq. exact H. Qed.

Lemma zr_CODELENS_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_CODELENS c1 q = inf_CODELENS c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_CODELENS.
  now rewrite (zr_eqb_nT c1), (zr_eqb_nT c2) by assumption.
Qed.

Lemma zr_LENLENS_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_LENLENS c1 q = inf_LENLENS c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_LENLENS. cbv zeta.
  match goal with |- context [ll_go ?a ?b ?c ?d ?e] =>
    destruct (ll_go a b c d e) end; cbv beta iota; [|reflexivity].
  match goal with |- context [ll_zero ?a ?b ?c] =>
    destruct (ll_zero a b c) end; cbv beta iota.
  match goal with |- context [inf_table ?a ?b ?c ?d ?e ?f] =>
    destruct (inf_table a b c d e f) as [[[[rc bc] nx] cd]|] end;
    cbv beta iota; [|reflexivity].
  destruct (negb (rc =? 0)); cbv beta iota;
    [reflexivity | apply zr_CODELENS_ctx; assumption].
Qed.

Lemma zr_TABLE_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_TABLE c1 q = inf_TABLE c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_TABLE. cbv zeta.
  match goal with |- context [inf_nb ?a ?b] =>
    destruct (inf_nb a b) end; cbv beta iota; [|reflexivity].
  match goal with |- context [if ?b then _ else _] =>
    destruct b end; cbv beta iota;
    [reflexivity | apply zr_LENLENS_ctx; assumption].
Qed.

Lemma zr_STORED_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_STORED c1 q = inf_STORED c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_STORED.
  now rewrite (zr_eqb_nT c1), (zr_eqb_nT c2) by assumption.
Qed.

Lemma zr_TYPEDO_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_TYPEDO c1 q = inf_TYPEDO c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_TYPEDO.
  now rewrite (zr_eqb_nT c1), (zr_eqb_nT c2) by assumption.
Qed.

Lemma zr_TYPE_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_TYPE c1 q = inf_TYPE c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_TYPE.
  rewrite (zr_eqb_nB c1), (zr_eqb_nB c2),
          (zr_eqb_nT c1), (zr_eqb_nT c2) by assumption.
  cbn [orb]. cbv beta iota. apply zr_TYPEDO_ctx; assumption.
Qed.

Lemma zr_DICT_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_DICT c1 q = inf_DICT c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_DICT.
  match goal with |- context [if ?b then _ else _] =>
    destruct b end; cbv beta iota;
    [reflexivity | apply zr_TYPE_ctx; assumption].
Qed.

Lemma zr_DICTID_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_DICTID c1 q = inf_DICTID c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_DICTID.
  match goal with |- context [inf_nb ?a ?b] =>
    destruct (inf_nb a b) end; cbv beta iota;
    [apply zr_DICT_ctx; assumption | reflexivity].
Qed.

Lemma zr_HEAD_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_HEAD c1 q = inf_HEAD c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_HEAD. cbv zeta.
  match goal with |- context [if ?b then _ else _] =>
    destruct b end; cbv beta iota;
    [apply zr_TYPEDO_ctx; assumption | reflexivity].
Qed.

Lemma zr_step_ctx : forall c1 c2 q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_step c1 q = inf_step c2 q.
Proof.
  intros c1 c2 q H1 H2. unfold inf_step.
  (* bullets keyed to Mode's constructor order (Inflate.v:200-206) *)
  destruct (q_mode q);
    [ apply zr_HEAD_ctx; assumption
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity
    | apply zr_DICTID_ctx; assumption
    | apply zr_DICT_ctx; assumption
    | apply zr_TYPE_ctx; assumption
    | apply zr_TYPEDO_ctx; assumption
    | apply zr_STORED_ctx; assumption
    | reflexivity | reflexivity
    | apply zr_TABLE_ctx; assumption
    | apply zr_LENLENS_ctx; assumption
    | apply zr_CODELENS_ctx; assumption
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity ].
Qed.

Lemma zr_loop_ctx : forall c1 c2 n q,
  zr_cflush_ok c1 -> zr_cflush_ok c2 ->
  inf_loop n c1 q = inf_loop n c2 q.
Proof.
  intros c1 c2 n q H1 H2. revert q.
  induction n as [|n IH]; intro q; [reflexivity|].
  cbn [inf_loop]. rewrite (zr_step_ctx c1 c2 q H1 H2).
  destruct (inf_step c2 q); try reflexivity. apply IH.
Qed.

(* ==========================================================================
   2.  Leave observations.
   ========================================================================== *)

(** [uw] with the allocation flag set never fails, and touches only the
    window: the header record and bit count survive. *)
Lemma zr_uw_some : forall fresh s o copy,
  exists s', uw true fresh s o copy = Some s'
             /\ s_hdr s' = s_hdr s /\ s_bits s' = s_bits s.
Proof.
  intros fresh s o copy. unfold uw. cbv zeta.
  destruct (w_alloc (s_win s)); cbv beta iota;
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           end;
    eexists; (split; [reflexivity | split; reflexivity]).
Qed.

(** The tail's output buffer is whatever came in. *)
Lemma zr_tail_ob : forall c Q wrote,
  q_ob (fst (inf_leave_tail c Q wrote)) = q_ob Q.
Proof.
  intros c Q wrote. unfold inf_leave_tail. cbv zeta.
  (* lazy kernel conversion projects through the setter tower with
     sharing; strong reduction (unfold+cbn) materializes it 8^depth *)
  match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

(** The tail's return code, as a closed formula over the fields it reads:
    the flush enters ONLY through the [=? Z_FINISH] disjunct of the
    Z_BUF_ERROR condition, and that condition is guarded by
    [q_ret Q =? Z_OK]. *)
Lemma zr_tail_ret : forall c Q wrote,
  snd (inf_leave_tail c Q wrote)
  = if ((q_in Q - br_have (q_br Q) =? 0) && (wrote =? 0)
        || (n_flush c =? Z_FINISH)) && (q_ret Q =? Z_OK)
    then Z_BUF_ERROR else q_ret Q.
Proof.
  intros c Q wrote. unfold inf_leave_tail. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

(** Every branch of [inf_leave] (window update taken or not) lands on the
    same return formula and leaves the output buffer alone — provided the
    window allocation flag is live, which kills the Z_MEM_ERROR arm. *)
Lemma zr_leave_shape : forall c q0,
  n_walloc c = true ->
  snd (inf_leave c q0)
  = (let Q := q_restore q0 in
     let wrote := q_out Q - o_left (q_ob Q) in
     if ((q_in Q - br_have (q_br Q) =? 0) && (wrote =? 0)
         || (n_flush c =? Z_FINISH)) && (q_ret Q =? Z_OK)
     then Z_BUF_ERROR else q_ret Q)
  /\ q_ob (fst (inf_leave c q0)) = q_ob (q_restore q0).
Proof.
  intros c q0 HW.
  unfold inf_leave. cbv zeta. rewrite HW.
  set (Q := q_restore q0).
  set (wrote := q_out Q - o_left (q_ob Q)).
  destruct (negb _ || _).
  - destruct (zr_uw_some (n_wfresh c) (q_st Q) (q_ob Q) wrote)
      as [st' [EU _]].
    rewrite EU.
    rewrite zr_tail_ret, zr_tail_ob.
    unfold qset_st. cbn [q_in q_br q_ret q_ob].
    split; reflexivity.
  - rewrite zr_tail_ret, zr_tail_ob.
    split; reflexivity.
Qed.

(** The transfer at the leave: a Z_STREAM_END verdict moves across
    contexts, with the output buffer intact. *)
Lemma zr_leave_obs : forall c1 c2 q0,
  n_walloc c1 = true -> n_walloc c2 = true ->
  snd (inf_leave c2 q0) = Z_STREAM_END ->
  snd (inf_leave c1 q0) = Z_STREAM_END
  /\ q_ob (fst (inf_leave c1 q0)) = q_ob (fst (inf_leave c2 q0)).
Proof.
  intros c1 c2 q0 HW1 HW2 H2.
  destruct (zr_leave_shape c1 q0 HW1) as [R1 O1].
  destruct (zr_leave_shape c2 q0 HW2) as [R2 O2].
  rewrite R2 in H2. rewrite R1, O1, O2. cbv zeta in *.
  split; [|reflexivity].
  destruct (q_ret (q_restore q0) =? Z_OK) eqn:EOK.
  - exfalso. apply Z.eqb_eq in EOK.
    rewrite andb_true_r in H2.
    destruct (_ || _) in H2;
      unfold Z_BUF_ERROR, Z_STREAM_END, Z_OK in *; lia.
  - rewrite andb_false_r in *. exact H2.
Qed.

(* ==========================================================================
   3.  The call-level transfer.
   ========================================================================== *)

Lemma zr_inf_call_transfer : forall f s z inb cap r4 u4 st4 z4 out4,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inf_call Z_FINISH s z inb cap = Some (r4, u4, st4, z4, out4) ->
  r4 = Z_STREAM_END ->
  exists u1 st1 z1,
    zr_inf_call f s z inb cap = Some (r4, u1, st1, z1, out4).
Proof.
  intros f s z inb cap r4 u4 st4 z4 out4 HB HT H4 HSE.
  assert (OKf : zr_cflush_ok {| n_flush := f; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush]; assumption).
  assert (OK4 : zr_cflush_ok {| n_flush := Z_FINISH; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush];
        unfold Z_FINISH, Z_BLOCK, Z_TREES; lia).
  unfold zr_inf_call, inflate_model in H4 |- *.
  cbv beta iota zeta
      delta [inf_ctx inf_st0 g_st g_state_null g_z g_inbuf g_next_in
             g_avail_in g_in_null g_outbuf g_next_out g_avail_out
             g_out_null g_flush g_walloc g_wfresh orb andb negb]
      in H4 |- *.
  rewrite (zr_loop_ctx {| n_flush := f; n_walloc := true;
                          n_wfresh := zzero |}
                       {| n_flush := Z_FINISH; n_walloc := true;
                          n_wfresh := zzero |})
    by assumption.
  destruct (inf_loop _ _ _) as [step|] eqn:EL;
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

Theorem zr_inflate_transfer : forall f wb cap enc y,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inflate Z_FINISH wb cap enc = Some y ->
  zr_inflate f wb cap enc = Some y.
Proof.
  intros f wb cap enc y HB HT H.
  unfold zr_inflate in H |- *.
  destruct (inflateInit2 z_fresh state_fresh wb) as [[z s]|]; [|discriminate].
  destruct (zr_inf_call Z_FINISH s z enc cap)
    as [[[[[r4 u4] st4] z4] out4]|] eqn:EC; [|discriminate].
  destruct (Z.eqb r4 Z_STREAM_END) eqn:ER; [|discriminate].
  apply Z.eqb_eq in ER.
  destruct (zr_inf_call_transfer f s z enc cap r4 u4 st4 z4 out4
              HB HT EC ER) as (u1 & st1 & z1 & EC1).
  rewrite EC1. rewrite <- H. now rewrite (proj2 (Z.eqb_eq _ _) ER).
Qed.

Theorem ZRepro_Pump_l0_zlib_holds : ZRepro_Pump_l0_zlib.
Proof.
  unfold ZRepro_Pump_l0_zlib, ZR_PumpSucceeds.
  intros x enc flush cap Hx Hdef HF Hcap Hcap32.
  rewrite zr_deflate_l0_shape in Hdef. injection Hdef as <-.
  exists (map u8 x).
  destruct HF as [-> | ->].
  - apply zr_inflate_transfer;
      [ unfold Z_NO_FLUSH, Z_BLOCK; lia
      | unfold Z_NO_FLUSH, Z_TREES; lia
      | exact (zr_inflate_l0_stream x cap Hcap) ].
  - exact (zr_inflate_l0_stream x cap Hcap).
Qed.

(* ==========================================================================
   5.  Controls.  Positive: the NO_FLUSH one-shot read computes end-to-end
       on an emitted stream.  Negative: at Z_BLOCK the loop leaves at the
       first block boundary with Z_OK and the one-shot gate fails — the
       face's ZR_Flush1 restriction is load-bearing, not decorative.
   ========================================================================== *)

Example zr_l0e_control_noflush :
  zr_inflate Z_NO_FLUSH 15 3 (zr_l0_stream [72; 105]) = Some [72; 105].
Proof. vm_compute. reflexivity. Qed.

Example zr_l0e_control_zblock_fails :
  zr_inflate Z_BLOCK 15 3 (zr_l0_stream [72; 105]) = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions ZRepro_Pump_l0_zlib_holds.
Print Assumptions zr_inflate_transfer.
