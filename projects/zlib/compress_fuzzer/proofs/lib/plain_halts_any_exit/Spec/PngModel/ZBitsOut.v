(** * Spec.PngModel.ZBitsOut — zlib's deflate bit writer ([trees.c]).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Source: [materials/zlib-1.3.1/trees.c] lines 144-192 and 271-286 (the
    NON-[ZLIB_DEBUG] [send_bits] macro — the build has no [-DZLIB_DEBUG]),
    plus [deflate.h:287] [put_byte].  BUG-FOR-BUG: [bi_buf] is a [ush], so
    every [|=] into it truncates to 16 bits; the model writes that [u16]
    explicitly.

    LOCAL SCRATCH COPY.  The WP-4 lane lead owns the delivered
    [Spec/PngModel/ZBitsOut.v]; this file implements the frozen interface
    ([BW], [bw_init], [bw_send_bits], [bw_put_byte], [bw_put_short],
    [bw_flush], [bw_windup]) so that [Trees.v] / [Deflate.v] can be written
    and validated against it and then simply pick up the delivered file.

    [bw_out] is the byte queue of [pending_buf] that has not yet been
    handed to [next_out]: [put_byte] appends at the tail, [flush_pending]
    ([deflate.c:915]) removes from the head.  In the C this is the range
    [[pending_out, pending_buf + pending)]; nothing in [deflate.c] or
    [trees.c] uses an ABSOLUTE [pending_buf] index (only [pending != 0],
    [pending == pending_buf_size] and the four tail bytes patched by
    [deflate_stored]), so a list is a faithful representation. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [deflate.h:55]: [#define Buf_size 16]. *)
Definition Buf_size : Z := 16.

Record BW : Type := mkBW {
  bw_out   : list Z;  (** bytes emitted so far, in order (the pending queue) *)
  bw_buf   : Z;       (** [bi_buf],   a [ush] *)
  bw_valid : Z        (** [bi_valid], [0 <= bw_valid < 16] *)
}.

Definition bw_init : BW := {| bw_out := []; bw_buf := 0; bw_valid := 0 |}.

(** [deflate.h:287]: [s->pending_buf[s->pending++] = (Bytef)(c)]. *)
Definition bw_put_byte (v : Z) (b : BW) : BW :=
  {| bw_out := bw_out b ++ [u8 v]; bw_buf := bw_buf b; bw_valid := bw_valid b |}.

(** [trees.c:144-147]: [put_byte(w & 0xff); put_byte((uch)((ush)(w) >> 8))]. *)
Definition bw_put_short (w : Z) (b : BW) : BW :=
  bw_put_byte (Z.shiftr (u16 w) 8) (bw_put_byte w b).

(** [trees.c:273-285], the non-debug macro.  Note the two [ush] casts:
    [(ush)value << bi_valid] is computed in [int] but assigned into the
    [ush] [bi_buf], so the OR result truncates to 16 bits; and
    [(ush)val >> (Buf_size - bi_valid)] shifts the 16-bit value. *)
Definition bw_send_bits (value length : Z) (b : BW) : BW :=
  let v16   := u16 value in
  let merged := u16 (Z.lor (bw_buf b) (Z.shiftl v16 (bw_valid b))) in
  if Z.ltb (Buf_size - length) (bw_valid b) then
    let b' := bw_put_short merged b in
    {| bw_out   := bw_out b';
       bw_buf   := Z.shiftr v16 (Buf_size - bw_valid b);
       bw_valid := bw_valid b + length - Buf_size |}
  else
    {| bw_out := bw_out b; bw_buf := merged; bw_valid := bw_valid b + length |}.

(** [trees.c:166-176] [bi_flush]. *)
Definition bw_flush (b : BW) : BW :=
  if Z.eqb (bw_valid b) 16 then
    let b' := bw_put_short (bw_buf b) b in
    {| bw_out := bw_out b'; bw_buf := 0; bw_valid := 0 |}
  else if Z.leb 8 (bw_valid b) then
    let b' := bw_put_byte (bw_buf b) b in
    {| bw_out := bw_out b'; bw_buf := Z.shiftr (bw_buf b) 8;
       bw_valid := bw_valid b - 8 |}
  else b.

(** [trees.c:181-192] [bi_windup]. *)
Definition bw_windup (b : BW) : BW :=
  let b' := if Z.ltb 8 (bw_valid b) then bw_put_short (bw_buf b) b
            else if Z.ltb 0 (bw_valid b) then bw_put_byte (bw_buf b) b
            else b in
  {| bw_out := bw_out b'; bw_buf := 0; bw_valid := 0 |}.

(** ** Elementary facts *)

(** Every emitter only ever appends to [bw_out]: the queue already handed
    out is never rewritten.  This is what lets a machine-level [BW_rep]
    speak about a suffix. *)

Lemma bw_put_byte_out : forall v b, bw_out (bw_put_byte v b) = bw_out b ++ [u8 v].
Proof. reflexivity. Qed.

Lemma bw_put_short_out :
  forall w b, bw_out (bw_put_short w b)
              = bw_out b ++ [u8 w; u8 (Z.shiftr (u16 w) 8)].
Proof.
  intros w b. cbn [bw_put_short bw_put_byte bw_out].
  now rewrite <- app_assoc.
Qed.

Lemma bw_send_bits_out_pre :
  forall v n b, exists t, bw_out (bw_send_bits v n b) = bw_out b ++ t.
Proof.
  intros v n b. unfold bw_send_bits.
  destruct (Z.ltb (Buf_size - n) (bw_valid b)); cbn [bw_out].
  - rewrite bw_put_short_out. eexists; reflexivity.
  - exists []. now rewrite app_nil_r.
Qed.

Lemma bw_flush_out_pre : forall b, exists t, bw_out (bw_flush b) = bw_out b ++ t.
Proof.
  intros b. unfold bw_flush.
  destruct (Z.eqb (bw_valid b) 16); cbn [bw_out].
  - rewrite bw_put_short_out. eexists; reflexivity.
  - destruct (Z.leb 8 (bw_valid b)); cbn [bw_out].
    + rewrite bw_put_byte_out. eexists; reflexivity.
    + exists []. now rewrite app_nil_r.
Qed.

Lemma bw_windup_out_pre : forall b, exists t, bw_out (bw_windup b) = bw_out b ++ t.
Proof.
  intros b. unfold bw_windup; cbn [bw_out].
  destruct (Z.ltb 8 (bw_valid b)).
  - rewrite bw_put_short_out. eexists; reflexivity.
  - destruct (Z.ltb 0 (bw_valid b)).
    + rewrite bw_put_byte_out. eexists; reflexivity.
    + exists []. now rewrite app_nil_r.
Qed.

(** [bi_windup] always leaves the buffer empty and byte-aligned — the fact
    [_tr_stored_block] relies on. *)
Lemma bw_windup_empty : forall b, bw_buf (bw_windup b) = 0 /\ bw_valid (bw_windup b) = 0.
Proof. intros b; unfold bw_windup; cbn; split; reflexivity. Qed.
