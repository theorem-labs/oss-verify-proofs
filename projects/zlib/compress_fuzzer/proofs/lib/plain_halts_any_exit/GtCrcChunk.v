(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtCrcChunk — the crc twin of
      [GtAdlerChunk]'s §4: the encode-side CRC32 closed form (Q3 gzip
      extension, 2026-08-19).

    [Deflate.read_buf] at [wrap = 2] accumulates
    [crc32_z_at (zs_adler st) 0 dat] once per read chunk (Deflate.v §5),
    while the gzip trailer ([deflate_trailer]'s wrap-2 arm) states CRC32
    over the WHOLE payload.  They agree via the composition law below.

    Priced against the artifact before writing (the GtAdlerChunk lesson,
    both directions): unlike the adler side, NO well-formedness invariant
    is owed — crc's accumulator is a plain 32-bit word with no two-half
    packing, and the algebra was already Qed:
    [ChecksumThy.crc32_braid_eq] (the braided model equals the
    byte-at-a-time reference, alignment dropped),
    [ChecksumThy.crc32_ref_app] (the app law),
    [ChecksumThy.u32_lnot_lxor] and [crc32_ref_range] (the range facts).
    This file only assembles them at [read_buf]'s call shape.  The adler
    twin's residue (four return paths, NMAX blocking, csub canonicality)
    has no crc counterpart. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Checksum ChecksumThy Deflate.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  Init and the empty buffer                                             *)

(** gzip's initial accumulator, all three sites ([deflate.c:1033] header,
    [:661] deflateResetKeep, [inflate.c:804] HCRC exit):
    [crc32(0, Z_NULL, 0) = 0]. *)
Lemma crc32_z_gzip_init : crc32_z 0 true 0 [] = 0.
Proof. reflexivity. Qed.

Definition CrcVal (c : Z) : Prop := 0 <= c < 4294967296.

Lemma crcval_init : CrcVal 0.
Proof. unfold CrcVal; lia. Qed.

(** [crc32_ref c [] = c] for in-range [c]: unwind the pre/post
    complement.  ([crc_bytes _ [] ] is a [fold_left] over [] — the
    identity.) *)
Lemma crc32_ref_nil : forall c, CrcVal c -> crc32_ref c [] = c.
Proof.
  intros c Hc. unfold crc32_ref. cbn [crc_bytes fold_left].
  rewrite u32_lnot_lxor.
  replace (u32 c) with c by (unfold u32; symmetry; apply Z.mod_small; exact Hc).
  now rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
Qed.

Lemma bytes_nil : bytes [].
Proof. intros b Hb. destruct Hb. Qed.

Lemma crc32_z_at_nil : forall c a, CrcVal c -> crc32_z_at c a [] = c.
Proof.
  intros c a Hc. rewrite (crc32_braid_eq c a [] bytes_nil).
  now apply crc32_ref_nil.
Qed.

(** The value stays a 32-bit word — what threads the fold below. *)
Lemma crc32_z_at_val : forall c a bs, bytes bs -> CrcVal (crc32_z_at c a bs).
Proof.
  intros c a bs Hb. rewrite (crc32_braid_eq c a bs Hb).
  apply crc32_ref_range.
Qed.

(* ######################################################################### *)
(* 2.  The composition law                                                   *)

Lemma bytes_app : forall xs ys, bytes xs -> bytes ys -> bytes (xs ++ ys).
Proof.
  intros xs ys Hx Hy b Hb. apply in_app_or in Hb.
  destruct Hb; [now apply Hx | now apply Hy].
Qed.

(** [crc32(crc32(c, xs), ys) = crc32(c, xs ++ ys)] at ANY alignments —
    [read_buf] always passes 0, but the law does not care
    ([crc32_braid_eq] drops the alignment). *)
Theorem crc32_z_at_chunk : forall c a a' a'' xs ys,
  bytes xs -> bytes ys ->
  crc32_z_at (crc32_z_at c a xs) a' ys = crc32_z_at c a'' (xs ++ ys).
Proof.
  intros c a a' a'' xs ys Hx Hy.
  rewrite (crc32_braid_eq _ a' ys Hy).
  rewrite (crc32_braid_eq c a xs Hx).
  rewrite (crc32_braid_eq c a'' (xs ++ ys) (bytes_app xs ys Hx Hy)).
  now rewrite crc32_ref_app.
Qed.

(* ######################################################################### *)
(* 3.  The multi-chunk fold [read_buf] actually produces                     *)

(** The encoder's accumulation, chunk list form ([GtAdlerChunk.ad_chunks]'s
    twin at [read_buf]'s wrap-2 call shape). *)
Fixpoint crc_chunks (c : Z) (cs : list (list Z)) : Z :=
  match cs with
  | [] => c
  | x :: r => crc_chunks (crc32_z_at c 0 x) r
  end.

Lemma bytes_concat : forall cs, Forall bytes cs -> bytes (concat cs).
Proof.
  induction cs as [|x r IH]; intros HF; [exact bytes_nil|].
  inversion HF; subst. cbn [concat]. now apply bytes_app; [|apply IH].
Qed.

Theorem crc32_z_at_chunks : forall cs c,
  CrcVal c -> Forall bytes cs ->
  crc_chunks c cs = crc32_z_at c 0 (concat cs).
Proof.
  induction cs as [|x r IH]; intros c Hc HF; cbn [crc_chunks concat].
  - now rewrite (crc32_z_at_nil c 0 Hc).
  - inversion HF as [|? ? Hx Hr]; subst.
    rewrite (IH _ (crc32_z_at_val c 0 x Hx) Hr).
    apply crc32_z_at_chunk; [exact Hx | now apply bytes_concat].
Qed.

(** From the gzip init: the whole-payload closed form the trailer states. *)
Corollary crc32_z_at_chunks_from_init : forall cs,
  Forall bytes cs ->
  crc_chunks (crc32_z 0 true 0 []) cs = crc32_z_at 0 0 (concat cs).
Proof.
  intros cs HF. rewrite crc32_z_gzip_init.
  exact (crc32_z_at_chunks cs 0 crcval_init HF).
Qed.

(* ######################################################################### *)
(* 4.  The [read_buf] step, verbatim                                         *)

Lemma bytes_map_u8 : forall l, bytes (map u8 l).
Proof.
  intros l b Hb. apply in_map_iff in Hb. destruct Hb as (x & Hx & _).
  subst b. unfold u8. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia.
Qed.

(** At [wrap = 2] one [read_buf] moves the accumulator by exactly one
    [crc_chunks] step over the bytes it returns — the [len = 0] branch
    returns [dat = []] and leaves [zs_adler] alone, which the nil law
    absorbs. *)
Theorem read_buf_crc_step : forall size st,
  CrcVal (zs_adler st) ->
  zs_adler (snd (read_buf 2 size st))
  = crc32_z_at (zs_adler st) 0 (fst (read_buf 2 size st)).
Proof.
  intros size st Hc. unfold read_buf. cbv zeta.
  destruct (Z.eqb (if Z.ltb size (zlen (zs_in st)) then size else zlen (zs_in st)) 0).
  - cbn [fst snd]. now rewrite (crc32_z_at_nil _ 0 Hc).
  - reflexivity.
Qed.

Lemma read_buf_dat_bytes : forall wrap size st,
  bytes (fst (read_buf wrap size st)).
Proof.
  intros wrap size st. unfold read_buf. cbv zeta.
  destruct (Z.eqb (if Z.ltb size (zlen (zs_in st)) then size else zlen (zs_in st)) 0).
  - exact bytes_nil.
  - cbn [fst]. apply bytes_map_u8.
Qed.
