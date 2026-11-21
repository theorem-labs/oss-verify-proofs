(** * ZReproL0D — the (0,15) emitter FACE: [ZR_FramedZlib] over the shape
      theorem.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  Residual (i)
    of the Q2 close-out.  [ZReproL0B.zr_deflate_l0_shape] pins the exact
    bytes [zr_deflate 0 15] emits; this file shows those bytes satisfy the
    DECLARATIVE frame [ZR_FramedZlib] — header clauses, [BodyDecodesTo]
    via [DeflateSpec.dec_stream], trailer — inhabiting
    [ZRepro_Emitter_l0_zlib], the face [ZRepro_composes] already consumes.

    The content is the body clause: [zr_stored_body]'s blocks decode back
    to the payload under the declarative decoder.  Per block it is
    [StoredRt.decode_stored_tail] (byte-aligned stored-block decode,
    [pad = 5] after the 3 header bits — [align_byte] inside
    [decode_stored] eats exactly those five pad bits); across blocks it is
    a fuel induction on [dec_stream_fuel], fuel-normalised at the end by
    [dec_stream_fuel_indep].

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits BwStream DeflateSpec StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro ZReproL0 ZReproL0B ZReproL0C.
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Local list facts (stdlib spellings for these vary across versions).
   ========================================================================== *)

Lemma zr_forall_firstn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H; revert n; induction H as [|a l Ha Hl IH]; intro n;
    destruct n; simpl; auto.
Qed.

Lemma zr_forall_skipn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n l H; revert n; induction H as [|a l Ha Hl IH]; intro n;
    destruct n; simpl; auto.
Qed.

Lemma zr_bits_len_mod8 : forall (bs : list Z),
  (length (bytes_bits bs) mod 8 = 0)%nat.
Proof.
  intro bs. rewrite bytes_bits_length, Nat.mul_comm.
  apply Nat.mod_mul; lia.
Qed.

(* ==========================================================================
   2.  The five header bytes, as bits: the [zwrite] forms
       [decode_stored_tail] eats.
   ========================================================================== *)

(** LEN, little-endian over two bytes, IS the 16-bit LSB-first write. *)
Lemma zr_len_pair_bits : forall len rest,
  0 <= len < 65536 ->
  byte_bits (u8 len) ++ byte_bits (u8 (Z.shiftr len 8)) ++ rest
  = zwrite 16 len ++ rest.
Proof.
  intros len rest Hlen.
  rewrite app_assoc. f_equal.
  rewrite !byte_bits_zwrite.
  rewrite (zwrite_cut 8 16 len) by lia.
  f_equal.
  - symmetry. apply zwrite_mod. lia.
  - change (16 - 8) with 8. f_equal.
    apply Z.shiftr_div_pow2. lia.
Qed.

(** NLEN: the ones-complement pair the model writes ([u8 (Z.lnot len)] and
    the high byte through [u32]) is the 16-bit write of [u16 (- len - 1)],
    which is what [stored_tail] carries. *)
Lemma zr_nlen_pair_bits : forall len,
  0 <= len < 65536 ->
  byte_bits (u8 (Z.lnot len)) ++ byte_bits (u8 (Z.shiftr (u32 (Z.lnot len)) 8))
  = zwrite 16 (u16 (- len - 1)).
Proof.
  intros len Hlen.
  assert (Hln : Z.lnot len = - len - 1)
    by (pose proof (Z.add_lnot_diag len); lia).
  assert (Hu32 : u32 (Z.lnot len) = 4294967295 - len).
  { rewrite Hln. unfold u32.
    rewrite <- (Z.mod_add (- len - 1) 1 4294967296) by lia.
    replace (- len - 1 + 1 * 4294967296) with (4294967295 - len) by lia.
    apply Z.mod_small; lia. }
  assert (Hu16 : u16 (- len - 1) = 65535 - len).
  { unfold u16.
    rewrite <- (Z.mod_add (- len - 1) 1 65536) by lia.
    replace (- len - 1 + 1 * 65536) with (65535 - len) by lia.
    apply Z.mod_small; lia. }
  rewrite Hu32, Hln, Hu16.
  rewrite !byte_bits_zwrite.
  rewrite (zwrite_cut 8 16 (65535 - len)) by lia.
  f_equal.
  - rewrite <- (zwrite_mod 8 (- len - 1)) by lia. f_equal.
    replace (65535 - len) with (- len - 1 + 256 * 2 ^ 8) by lia.
    now rewrite Z.mod_add by lia.
  - change (16 - 8) with 8.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite <- (zwrite_mod 8 ((4294967295 - len) / 2 ^ 8)) by lia.
    rewrite <- (zwrite_mod 8 ((65535 - len) / 2 ^ 8)) by lia.
    f_equal.
    replace (4294967295 - len) with ((65535 - len) + 16776960 * 2 ^ 8) by lia.
    rewrite Z.div_add by lia.
    replace ((65535 - len) / 2 ^ 8 + 16776960)
      with ((65535 - len) / 2 ^ 8 + 65535 * 2 ^ 8) by lia.
    now rewrite Z.mod_add by lia.
Qed.

(** The whole header: 3 block-header bits, then exactly [stored_tail]'s
    [pad = 5] shape.  [last] is concrete (0 or 1) at every use site. *)
Lemma zr_hdr_bits : forall last len,
  last = 0 \/ last = 1 -> 0 <= len < 65536 ->
  bytes_bits (zr_stored_hdr last len)
  = zwrite 3 last ++ repeat false 5
    ++ zwrite 16 len ++ zwrite 16 (u16 (- len - 1)).
Proof.
  intros last len Hl Hlen.
  assert (B0 : byte_bits last = zwrite 3 last ++ repeat false 5)
    by (destruct Hl; subst; reflexivity).
  unfold zr_stored_hdr.
  rewrite !bytes_bits_cons, bytes_bits_nil, app_nil_r.
  rewrite zr_len_pair_bits by lia.
  rewrite zr_nlen_pair_bits by lia.
  rewrite B0.
  now rewrite <- !app_assoc.
Qed.

Lemma zr_block_bits : forall last len chunk,
  last = 0 \/ last = 1 -> len = zlen chunk -> 0 <= len < 65536 ->
  bytes_bits (zr_stored_hdr last len ++ map u8 chunk)
  = zwrite 3 last ++ stored_tail chunk len 5.
Proof.
  intros last len chunk Hl Hlen Hr.
  rewrite bytes_bits_app, zr_hdr_bits by auto.
  unfold stored_tail.
  now rewrite <- !app_assoc.
Qed.

(* ==========================================================================
   3.  One block through [dec_blk].
   ========================================================================== *)

Lemma zr_dec_blk_stored : forall last len chunk tail acc,
  last = 0 \/ last = 1 -> len = zlen chunk -> 0 <= len < 65536 ->
  Forall (fun b => 0 <= b < 256) chunk ->
  (length tail mod 8 = 0)%nat ->
  dec_blk (bytes_bits (zr_stored_hdr last len ++ map u8 chunk) ++ tail) acc
  = Some (Z.eqb last 1, acc ++ chunk, tail).
Proof.
  intros last len chunk tail acc Hl Hlen Hr Hb Ht.
  assert (Hlen' : len = Z.of_nat (length chunk)) by (rewrite Hlen; reflexivity).
  pose proof (decode_stored_tail chunk len 5%nat tail Hlen' Hr
                ltac:(lia) Ht) as DS.
  rewrite zr_block_bits by auto.
  rewrite <- app_assoc.
  assert (R1 : forall rest : list bool,
    read_bits 1%nat ([false; false; false] ++ rest)
    = Some (0, [false; false] ++ rest)) by reflexivity.
  assert (R1' : forall rest : list bool,
    read_bits 1%nat ([true; false; false] ++ rest)
    = Some (1, [false; false] ++ rest)) by reflexivity.
  assert (R2 : forall rest : list bool,
    read_bits 2%nat ([false; false] ++ rest) = Some (0, rest))
    by reflexivity.
  destruct Hl; subst last; unfold dec_blk.
  - change (zwrite 3 0) with [false; false; false].
    rewrite R1. cbv beta iota zeta.
    rewrite R2. cbv beta iota zeta.
    cbn [Z.eqb].
    rewrite DS. cbv beta iota.
    now rewrite (stored_map_u8_id chunk Hb).
  - change (zwrite 3 1) with [true; false; false].
    rewrite R1'. cbv beta iota zeta.
    rewrite R2. cbv beta iota zeta.
    cbn [Z.eqb].
    rewrite DS. cbv beta iota.
    now rewrite (stored_map_u8_id chunk Hb).
Qed.

(* ==========================================================================
   4.  The block-list induction.
   ========================================================================== *)

Lemma zr_body_dec_fuel : forall f (x : list Z) acc g,
  Forall (fun b => 0 <= b < 256) x ->
  (Z.to_nat (zlen x / 65535) < f)%nat ->
  (f <= g)%nat ->
  dec_stream_fuel g (bytes_bits (zr_stored_body f x)) acc
  = Some (acc ++ x, []).
Proof.
  induction f as [|f IH]; intros x acc g Hb Hf Hg; [lia|].
  destruct g as [|g]; [lia|].
  pose proof (zlen_nonneg x) as Hxnn.
  cbn [zr_stored_body].
  destruct (Z.leb_spec (zlen x) 65535) as [Hle|Hgt].
  - (* final block: the whole remaining input, last = 1, remainder [] *)
    cbn [dec_stream_fuel].
    rewrite <- (app_nil_r
      (bytes_bits (zr_stored_hdr 1 (zlen x) ++ map u8 x))).
    rewrite (zr_dec_blk_stored 1 (zlen x) x [] acc
               (or_intror eq_refl) eq_refl ltac:(lia) Hb eq_refl).
    cbn [Z.eqb]. cbv beta iota. reflexivity.
  - (* continuing block: a full 65535-byte chunk, last = 0, recurse *)
    assert (Hchunk : zlen (firstn (Z.to_nat 65535) x) = 65535).
    { unfold zlen in *. rewrite length_firstn. lia. }
    cbn [dec_stream_fuel].
    rewrite app_assoc, bytes_bits_app.
    rewrite (zr_dec_blk_stored 0 65535 (firstn (Z.to_nat 65535) x)
               (bytes_bits (zr_stored_body f (skipn (Z.to_nat 65535) x))) acc
               (or_introl eq_refl) (eq_sym Hchunk) ltac:(lia)
               (zr_forall_firstn _ _ _ Hb)
               (zr_bits_len_mod8 _)).
    cbn [Z.eqb]. cbv beta iota.
    assert (Hq : (zlen x - 65535) / 65535 = zlen x / 65535 - 1).
    { replace (zlen x - 65535) with (zlen x + (-1) * 65535) by lia.
      now rewrite Z.div_add by lia. }
    assert (Hqpos : 1 <= zlen x / 65535).
    { replace (zlen x) with (65536 + (zlen x - 65536)) by lia.
      apply Z.div_le_lower_bound; lia. }
    rewrite (IH (skipn (Z.to_nat 65535) x)
               (acc ++ firstn (Z.to_nat 65535) x) g
               (zr_forall_skipn _ _ _ Hb)
               ltac:(rewrite zlen_skipn_65535 by lia; rewrite Hq; lia)
               ltac:(lia)).
    now rewrite <- app_assoc, firstn_skipn.
Qed.

Theorem zr_body_decodes : forall x : list Z,
  Forall (fun b => 0 <= b < 256) x ->
  BodyDecodesTo (zr_stored_body (zr_body_fuel x) x) x.
Proof.
  intros x Hb.
  unfold BodyDecodesTo, dec_stream, dec_stream_rem, dec_stream_from.
  set (bits := bytes_bits (zr_stored_body (zr_body_fuel x) x)).
  rewrite (dec_stream_fuel_indep (S (length bits))
             (Nat.max (zr_body_fuel x) (S (length bits))) bits [])
    by lia.
  unfold bits.
  rewrite (zr_body_dec_fuel (zr_body_fuel x) x []
             (Nat.max (zr_body_fuel x)
                (S (length (bytes_bits (zr_stored_body (zr_body_fuel x) x)))))
             Hb ltac:(unfold zr_body_fuel; lia) (Nat.le_max_l _ _)).
  reflexivity.
Qed.

(* ==========================================================================
   4b.  The emitted stream is byte-valued — unconditionally (every
        payload byte passes through [u8], the header entries are 0/1 or
        [u8]-applied, the trailer is [be32]'s masked bytes).
   ========================================================================== *)

Lemma zr_u8_byte : forall v, 0 <= u8 v < 256.
Proof. intro v. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma zr_hdr_bytes_range : forall last len,
  last = 0 \/ last = 1 ->
  Forall (fun b => 0 <= b < 256) (zr_stored_hdr last len).
Proof.
  intros last len Hl. unfold zr_stored_hdr.
  apply Forall_forall. intros v Hv. cbn in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    first [ destruct Hl; subst; lia | apply zr_u8_byte ].
Qed.

Lemma zr_body_bytes : forall f (x : list Z),
  Forall (fun b => 0 <= b < 256) (zr_stored_body f x).
Proof.
  induction f as [|f IH]; intro x; cbn [zr_stored_body];
    [constructor|].
  assert (HM : forall l : list Z,
            Forall (fun b => 0 <= b < 256) (map u8 l)).
  { intro l. apply Forall_forall. intros v Hv.
    apply in_map_iff in Hv as [w [<- _]]. apply zr_u8_byte. }
  destruct (Z.leb (zlen x) 65535).
  - apply Forall_app; split;
      [ apply zr_hdr_bytes_range; right; reflexivity | apply HM ].
  - apply Forall_app; split;
      [ apply zr_hdr_bytes_range; left; reflexivity |].
    apply Forall_app; split; [ apply HM | apply IH ].
Qed.

Lemma zr_be32_bytes : forall v,
  Forall (fun b => 0 <= b < 256) (be32 v).
Proof.
  intro v. unfold be32.
  apply Forall_forall. intros w Hw. cbn in Hw.
  destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; apply zr_u8_byte.
Qed.

Lemma zr_l0_stream_bytes : forall x,
  Forall (fun b => 0 <= b < 256) (zr_l0_stream x).
Proof.
  intro x. unfold zr_l0_stream.
  apply Forall_app; split;
    [| apply Forall_app; split; [apply zr_body_bytes | apply zr_be32_bytes]].
  constructor; [lia|]. constructor; [lia|]. constructor.
Qed.

(* ==========================================================================
   5.  The face.
   ========================================================================== *)

Theorem ZRepro_Emitter_l0_zlib_holds : ZRepro_Emitter_l0_zlib.
Proof.
  unfold ZRepro_Emitter_l0_zlib, ZR_EmitterPublishes.
  intros x Hx. destruct Hx as [Hb Hcap].
  exists (zr_l0_stream x).
  split; [apply zr_deflate_l0_shape|].
  split.
  { (* the published length bound: 6 + body <= deflateBound, via
       ZReproL0B.zr_l0_room *)
    unfold zr_l0_stream.
    rewrite !zlen_app, zlen_be32.
    rewrite (zlen_body (zr_body_fuel x) x (Nat.le_refl _)).
    pose proof (zr_l0_room x) as HR.
    replace (zlen [120; 1]) with 2 by reflexivity.
    lia. }
  split.
  { (* the published byte range *)
    apply zr_l0_stream_bytes. }
  unfold ZR_FramedZlib.
  exists 120, 1, (zr_stored_body (zr_body_fuel x) x),
         (adler32_z adler_init false x).
  split; [|split; [|split]].
  - (* ZlibFramed *)
    unfold ZlibFramed, zr_l0_stream.
    rewrite (map_u8_id x Hb).
    unfold adler_init. reflexivity.
  - (* ZlibHeaderOk 120 1 — CMF/FLG of the level-0 zlib header.
       Clause 4 (FDICT clear, GAP7-F2 amendment) discharged by q5-emitter
       in the same window (lane retired; flow-lead GO 2026-08-21):
       1 & 32 = 0 by computation. *)
    unfold ZlibHeaderOk.
    assert (H7 : Z.shiftr (u8 120) 4 = 7) by reflexivity.
    split; [reflexivity | split; [rewrite H7; lia | split; reflexivity]].
  - (* BodyDecodesTo *)
    exact (zr_body_decodes x Hb).
  - (* TrailerMatchesPayload *)
    reflexivity.
Qed.

(* ==========================================================================
   6.  Controls.  The face's per-clause instruments, pinned by vm_compute:
       the declarative decoder really recovers the payload from the emitted
       body (positive), and really rejects a corrupted NLEN (negative — the
       decode instrument is not a rubber stamp).
   ========================================================================== *)

Example zr_l0d_control_decode :
  dec_stream (bytes_bits (zr_stored_body (zr_body_fuel [72; 105]) [72; 105]))
  = Some [72; 105].
Proof. vm_compute. reflexivity. Qed.

(** The same block with NLEN's high byte off by one: [decode_stored]'s
    complement check fails, the stream is rejected. *)
Example zr_l0d_control_corrupt :
  dec_stream (bytes_bits [1; 2; 0; 253; 254; 72; 105]) = None.
Proof. vm_compute. reflexivity. Qed.

(** The empty payload is one empty final block and still frames. *)
Example zr_l0d_control_empty :
  dec_stream (bytes_bits (zr_stored_body (zr_body_fuel []) [])) = Some [].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions ZRepro_Emitter_l0_zlib_holds.
Print Assumptions zr_body_decodes.
