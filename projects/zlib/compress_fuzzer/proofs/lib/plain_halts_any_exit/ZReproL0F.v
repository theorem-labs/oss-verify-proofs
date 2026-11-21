(** * ZReproL0F — flush-blindness of the one-shot read, both directions.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  Q6 stage-1
    piece.  ZReproL0E's [zr_inflate_transfer] moves a Z_FINISH answer to
    any admissible flush; Q6's soundness leg needs the OTHER direction
    (the face's success premise arrives at an arbitrary [ZR_Flush1]
    flush, and the walk is authored once, at Z_FINISH).  Rather than a
    mirrored proof, this file states the SYMMETRIC form — the one-shot
    read is flush-blind across ALL flushes avoiding Z_BLOCK/Z_TREES —
    and both directions are instances.  The proof is ZReproL0E's
    call-transfer with the fixed Z_FINISH context generalised; every
    ingredient ([zr_loop_ctx], [zr_leave_obs]) was already
    context-generic.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  GtAdlerChunk GtAdlerLoop ZRepro ZReproL0 ZReproL0B ZReproL0C ZReproL0E.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma zr_inf_call_blind : forall f1 f2 s z inb cap r4 u4 st4 z4 out4,
  f1 <> Z_BLOCK -> f1 <> Z_TREES -> f2 <> Z_BLOCK -> f2 <> Z_TREES ->
  zr_inf_call f2 s z inb cap = Some (r4, u4, st4, z4, out4) ->
  r4 = Z_STREAM_END ->
  exists u1 st1 z1,
    zr_inf_call f1 s z inb cap = Some (r4, u1, st1, z1, out4).
Proof.
  intros f1 f2 s z inb cap r4 u4 st4 z4 out4 HB1 HT1 HB2 HT2 H4 HSE.
  assert (OKf : zr_cflush_ok {| n_flush := f1; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush]; assumption).
  assert (OK4 : zr_cflush_ok {| n_flush := f2; n_walloc := true;
                                n_wfresh := zzero |})
    by (split; cbn [n_flush]; assumption).
  unfold zr_inf_call, inflate_model in H4 |- *.
  cbv beta iota zeta
      delta [inf_ctx inf_st0 g_st g_state_null g_z g_inbuf g_next_in
             g_avail_in g_in_null g_outbuf g_next_out g_avail_out
             g_out_null g_flush g_walloc g_wfresh orb andb negb]
      in H4 |- *.
  rewrite (zr_loop_ctx {| n_flush := f1; n_walloc := true;
                          n_wfresh := zzero |}
                       {| n_flush := f2; n_walloc := true;
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
    destruct (inf_leave {| n_flush := f2; n_walloc := true;
                           n_wfresh := zzero |} q') as [q2 r2] eqn:E4.
    cbv beta iota delta [r_ret r_q] in H4.
    injection H4 as <- <- <- <- <-.
    destruct (zr_leave_obs {| n_flush := f1; n_walloc := true;
                              n_wfresh := zzero |}
                           {| n_flush := f2; n_walloc := true;
                              n_wfresh := zzero |} q'
                eq_refl eq_refl
                ltac:(rewrite E4; cbn [snd]; exact HSE))
      as [R1 O1].
    destruct (inf_leave {| n_flush := f1; n_walloc := true;
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

Theorem zr_inflate_flushblind : forall f1 f2 wb cap enc y,
  f1 <> Z_BLOCK -> f1 <> Z_TREES -> f2 <> Z_BLOCK -> f2 <> Z_TREES ->
  zr_inflate f2 wb cap enc = Some y ->
  zr_inflate f1 wb cap enc = Some y.
Proof.
  intros f1 f2 wb cap enc y HB1 HT1 HB2 HT2 H.
  unfold zr_inflate in H |- *.
  destruct (inflateInit2 z_fresh state_fresh wb) as [[z s]|]; [|discriminate].
  destruct (zr_inf_call f2 s z enc cap)
    as [[[[[r4 u4] st4] z4] out4]|] eqn:EC; [|discriminate].
  destruct (Z.eqb r4 Z_STREAM_END) eqn:ER; [|discriminate].
  apply Z.eqb_eq in ER.
  destruct (zr_inf_call_blind f1 f2 s z enc cap r4 u4 st4 z4 out4
              HB1 HT1 HB2 HT2 EC ER) as (u1 & st1 & z1 & EC1).
  rewrite EC1. rewrite <- H. now rewrite (proj2 (Z.eqb_eq _ _) ER).
Qed.


(** The two directions Q6 consumes, named. *)
Corollary zr_inflate_to_finish : forall f wb cap enc y,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inflate f wb cap enc = Some y ->
  zr_inflate Z_FINISH wb cap enc = Some y.
Proof.
  intros f wb cap enc y HB HT H.
  apply (zr_inflate_flushblind Z_FINISH f); auto;
    unfold Z_FINISH, Z_BLOCK, Z_TREES; lia.
Qed.

Corollary zr_inflate_from_finish : forall f wb cap enc y,
  f <> Z_BLOCK -> f <> Z_TREES ->
  zr_inflate Z_FINISH wb cap enc = Some y ->
  zr_inflate f wb cap enc = Some y.
Proof.
  intros f wb cap enc y HB HT H.
  apply (zr_inflate_flushblind f Z_FINISH); auto;
    unfold Z_FINISH, Z_BLOCK, Z_TREES; lia.
Qed.

Print Assumptions zr_inflate_flushblind.
