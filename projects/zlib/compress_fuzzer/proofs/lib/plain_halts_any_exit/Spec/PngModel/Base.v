(** * Spec.PngModel.Base — shared vocabulary for the C transcriptions.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Nothing here mentions
    RISC-V, the memory images, or the trusted spec; this file is the bottom
    of the [Spec/PngModel] dependency DAG and imports only Stdlib.

    The [Spec/PngModel] tree is a BUG-FOR-BUG transcription of the vendored
    zlib-1.3.1 / libpng-1.6.43 / harness C sources
    ([data/libpng4--aug14/materials], in-container
    [/harness/problem/materials]).  It is NOT a formalisation of RFC 1950/
    1951 or of the PNG specification: where the shipped C deviates from the
    standards, or from what a clean-room implementation would do, the
    transcription follows the C.  Every function here is total (fuelled
    where the C loops) and executable, so that it can be
    (i) differentially tested against the delivered binary and
    (ii) reduced by [vm_compute] inside proofs.

    Arrays.  The C code mutates fixed-size scratch arrays in place.  Rather
    than model them as lists (whose length obligations would pollute every
    loop invariant) we model an array as a TOTAL FUNCTION [zarr = Z -> Z]
    with pointwise update [zset].  That is the same shape the machine-level
    representation predicates want:

      [ARR_rep mem base a n := forall i, 0 <= i < n -> rdnk mem (base+k*i) = a i]

    is a single universally-quantified fact rather than [n] conjuncts —
    the [MuslMallocInit] lesson, and mandatory at [ENOUGH]-sized tables
    (see c5-invariants.md §3.2 and its "TBL_rep as a forall-fact" note).

    Out-of-range indices.  A [zarr] is total, so an index the C would read
    out of bounds returns whatever the model's initialiser says instead of
    being undefined.  Every such index is UNREACHABLE for the callers this
    driver makes (argued per site at the use), and the reachability
    argument is stated as a well-formedness hypothesis on the interface
    lemma rather than being enforced by the representation. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Total integer arrays *)

Definition zarr : Type := Z -> Z.

Definition zconst (v : Z) : zarr := fun _ => v.

Definition zzero : zarr := zconst 0.

(** [zset a i v] is [a] with index [i] overwritten by [v]. *)
Definition zset (a : zarr) (i v : Z) : zarr :=
  fun j => if Z.eqb j i then v else a j.

Lemma zset_same : forall a i v, zset a i v i = v.
Proof. intros; unfold zset; now rewrite Z.eqb_refl. Qed.

Lemma zset_other : forall a i v j, j <> i -> zset a i v j = a j.
Proof. intros a i v j H; unfold zset; now apply Z.eqb_neq in H as ->. Qed.

(** A read-only array given by a literal list; index [i] outside
    [0 .. length l - 1] reads [0].  Used for the static [lbase]/[lext]/
    [dbase]/[dext] tables of [inftrees.c], whose out-of-range indices are
    unreachable for every call this driver makes. *)
Definition zlist (l : list Z) : zarr :=
  fun i => nth (Z.to_nat i) l 0.

(** Materialise [n] entries of an array, low index first.  Only used by the
    differential-testing extraction; proofs speak through [zarr] directly. *)
Definition zarr_take (a : zarr) (n : Z) : list Z :=
  map (fun k => a (Z.of_nat k)) (seq 0 (Z.to_nat n)).

(** ** Machine-integer truncation

    Written explicitly at every point where the C source contains a cast,
    so that a reader can check the transcription against the C line by line
    and so that a walk can discharge the cast with a range fact rather than
    silently assuming it away. *)

Definition u8  (v : Z) : Z := v mod 256.
Definition u16 (v : Z) : Z := v mod 65536.
Definition u32 (v : Z) : Z := v mod 4294967296.

Lemma u8_id  : forall v, 0 <= v < 256   -> u8 v = v.
Proof. intros; unfold u8; now apply Z.mod_small. Qed.
Lemma u16_id : forall v, 0 <= v < 65536 -> u16 v = v.
Proof. intros; unfold u16; now apply Z.mod_small. Qed.
Lemma u32_id : forall v, 0 <= v < 4294967296 -> u32 v = v.
Proof. intros; unfold u32; now apply Z.mod_small. Qed.

(** ** zlib's decoding-table entry ([inftrees.h]'s [code])

<<
    typedef struct { unsigned char op; unsigned char bits; unsigned short val; } code;
>>

    Four bytes, little-endian, no padding (checked against the delivered
    binary: [inflate_state.codes] is [ENOUGH * 4] bytes). *)

Record Code : Set := mkCode { c_op : Z ; c_bits : Z ; c_val : Z }.

(** The constructor the transcription uses, applying the same truncations
    the C casts do. *)
Definition mkCodeT (op bits val : Z) : Code :=
  {| c_op := u8 op ; c_bits := u8 bits ; c_val := u16 val |}.

(** The 32-bit little-endian encoding of a [code], i.e. what a 4-byte load
    at the entry's address yields.  This is the abstraction function of the
    machine-level [TBL_rep]. *)
Definition code_enc (e : Code) : Z :=
  c_op e + 256 * c_bits e + 65536 * c_val e.

Lemma code_enc_range :
  forall op bits val, 0 <= code_enc (mkCodeT op bits val) < 4294967296.
Proof.
  intros op bits val. unfold code_enc, mkCodeT; cbn [c_op c_bits c_val].
  unfold u8, u16.
  pose proof (Z.mod_pos_bound op 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound bits 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound val 65536 ltac:(lia)).
  lia.
Qed.

Definition code_eqb (a b : Code) : bool :=
  Z.eqb (c_op a) (c_op b) && Z.eqb (c_bits a) (c_bits b) && Z.eqb (c_val a) (c_val b).

Lemma code_eqb_true : forall a b, code_eqb a b = true -> a = b.
Proof.
  intros [oa ba va] [ob bb vb]; unfold code_eqb; cbn.
  intros H. apply andb_prop in H as [H Hv]. apply andb_prop in H as [Ho Hb].
  apply Z.eqb_eq in Ho, Hb, Hv. now subst.
Qed.

(** ** Total tables of entries *)

Definition ztbl : Type := Z -> Code.

Definition tnone : ztbl := fun _ => mkCode 0 0 0.

Definition tset (t : ztbl) (i : Z) (e : Code) : ztbl :=
  fun j => if Z.eqb j i then e else t j.

Lemma tset_same : forall t i e, tset t i e i = e.
Proof. intros; unfold tset; now rewrite Z.eqb_refl. Qed.

Lemma tset_other : forall t i e j, j <> i -> tset t i e j = t j.
Proof. intros t i e j H; unfold tset; now apply Z.eqb_neq in H as ->. Qed.

Definition ztbl_take (t : ztbl) (n : Z) : list Code :=
  map (fun k => t (Z.of_nat k)) (seq 0 (Z.to_nat n)).

(** ** Agreement on an index range

    ONE canonical relation for "these two arrays hold the same data over
    this window", plus the kit that makes it compose.  Every window,
    table and buffer lemma in the round-trip DAG is an [arr_eq_on] /
    [tbl_eq_on] fact: the machine-level representation predicates
    ([ARR_rep]/[TBL_rep], see the header) are [arr_eq_on] between the
    model's array and the abstraction of a memory region, the decoder
    window argument is [arr_eq_on] between the window and a suffix of the
    output history, and every [zset]-heavy loop invariant is
    "[arr_eq_on] outside the written prefix".  Stating them all with the
    same relation is what lets them chain by [arr_eq_on_trans] /
    [arr_eq_on_join] instead of by a dozen incompatible
    [forall i, ... -> _ i = _ i] phrasings.

    Half-open on the right, like every other range in this tree
    ([it_wf]'s [0 <= i < codes], [zarr_take]'s [seq 0 n]), so that
    splitting at a midpoint needs no off-by-one. *)

Definition arr_eq_on (a b : zarr) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> a i = b i.

Definition tbl_eq_on (t u : ztbl) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> t i = u i.

(** *** Elimination and introduction *)

Lemma arr_eq_on_at :
  forall a b lo hi i, arr_eq_on a b lo hi -> lo <= i < hi -> a i = b i.
Proof. intros a b lo hi i H Hi; now apply H. Qed.

Lemma tbl_eq_on_at :
  forall t u lo hi i, tbl_eq_on t u lo hi -> lo <= i < hi -> t i = u i.
Proof. intros t u lo hi i H Hi; now apply H. Qed.

Lemma arr_eq_on_all :
  forall a b lo hi, (forall i, a i = b i) -> arr_eq_on a b lo hi.
Proof. intros a b lo hi H i _; apply H. Qed.

Lemma tbl_eq_on_all :
  forall t u lo hi, (forall i, t i = u i) -> tbl_eq_on t u lo hi.
Proof. intros t u lo hi H i _; apply H. Qed.

(** *** Equivalence *)

Lemma arr_eq_on_refl : forall a lo hi, arr_eq_on a a lo hi.
Proof. intros a lo hi i _; reflexivity. Qed.

Lemma arr_eq_on_sym :
  forall a b lo hi, arr_eq_on a b lo hi -> arr_eq_on b a lo hi.
Proof. intros a b lo hi H i Hi; symmetry; now apply H. Qed.

Lemma arr_eq_on_trans :
  forall a b c lo hi,
    arr_eq_on a b lo hi -> arr_eq_on b c lo hi -> arr_eq_on a c lo hi.
Proof. intros a b c lo hi H1 H2 i Hi; rewrite H1 by exact Hi; now apply H2. Qed.

Lemma tbl_eq_on_refl : forall t lo hi, tbl_eq_on t t lo hi.
Proof. intros t lo hi i _; reflexivity. Qed.

Lemma tbl_eq_on_sym :
  forall t u lo hi, tbl_eq_on t u lo hi -> tbl_eq_on u t lo hi.
Proof. intros t u lo hi H i Hi; symmetry; now apply H. Qed.

Lemma tbl_eq_on_trans :
  forall t u w lo hi,
    tbl_eq_on t u lo hi -> tbl_eq_on u w lo hi -> tbl_eq_on t w lo hi.
Proof. intros t u w lo hi H1 H2 i Hi; rewrite H1 by exact Hi; now apply H2. Qed.

(** *** The empty range, narrowing, splitting and joining *)

Lemma arr_eq_on_empty : forall a b lo hi, hi <= lo -> arr_eq_on a b lo hi.
Proof. intros a b lo hi H i Hi; lia. Qed.

Lemma tbl_eq_on_empty : forall t u lo hi, hi <= lo -> tbl_eq_on t u lo hi.
Proof. intros t u lo hi H i Hi; lia. Qed.

Lemma arr_eq_on_narrow :
  forall a b lo hi lo' hi',
    lo <= lo' -> hi' <= hi -> arr_eq_on a b lo hi -> arr_eq_on a b lo' hi'.
Proof. intros a b lo hi lo' hi' H1 H2 H i Hi; apply H; lia. Qed.

Lemma tbl_eq_on_narrow :
  forall t u lo hi lo' hi',
    lo <= lo' -> hi' <= hi -> tbl_eq_on t u lo hi -> tbl_eq_on t u lo' hi'.
Proof. intros t u lo hi lo' hi' H1 H2 H i Hi; apply H; lia. Qed.

Lemma arr_eq_on_join :
  forall a b lo mid hi,
    arr_eq_on a b lo mid -> arr_eq_on a b mid hi -> arr_eq_on a b lo hi.
Proof.
  intros a b lo mid hi H1 H2 i Hi.
  destruct (Z_lt_le_dec i mid); [apply H1 | apply H2]; lia.
Qed.

Lemma tbl_eq_on_join :
  forall t u lo mid hi,
    tbl_eq_on t u lo mid -> tbl_eq_on t u mid hi -> tbl_eq_on t u lo hi.
Proof.
  intros t u lo mid hi H1 H2 i Hi.
  destruct (Z_lt_le_dec i mid); [apply H1 | apply H2]; lia.
Qed.

Lemma arr_eq_on_split :
  forall a b lo mid hi,
    lo <= mid <= hi -> arr_eq_on a b lo hi ->
    arr_eq_on a b lo mid /\ arr_eq_on a b mid hi.
Proof.
  intros a b lo mid hi Hm H; split;
    (eapply arr_eq_on_narrow; [| | exact H]; lia).
Qed.

Lemma tbl_eq_on_split :
  forall t u lo mid hi,
    lo <= mid <= hi -> tbl_eq_on t u lo hi ->
    tbl_eq_on t u lo mid /\ tbl_eq_on t u mid hi.
Proof.
  intros t u lo mid hi Hm H; split;
    (eapply tbl_eq_on_narrow; [| | exact H]; lia).
Qed.

(** Extend a range by one index at either end. *)
Lemma arr_eq_on_snoc :
  forall a b lo hi, arr_eq_on a b lo hi -> a hi = b hi -> arr_eq_on a b lo (hi + 1).
Proof.
  intros a b lo hi H He i Hi.
  destruct (Z.eq_dec i hi) as [->|Hne]; [exact He | apply H; lia].
Qed.

Lemma arr_eq_on_cons :
  forall a b lo hi, a lo = b lo -> arr_eq_on a b (lo + 1) hi -> arr_eq_on a b lo hi.
Proof.
  intros a b lo hi He H i Hi.
  destruct (Z.eq_dec i lo) as [->|Hne]; [exact He | apply H; lia].
Qed.

Lemma tbl_eq_on_snoc :
  forall t u lo hi, tbl_eq_on t u lo hi -> t hi = u hi -> tbl_eq_on t u lo (hi + 1).
Proof.
  intros t u lo hi H He i Hi.
  destruct (Z.eq_dec i hi) as [->|Hne]; [exact He | apply H; lia].
Qed.

Lemma tbl_eq_on_cons :
  forall t u lo hi, t lo = u lo -> tbl_eq_on t u (lo + 1) hi -> tbl_eq_on t u lo hi.
Proof.
  intros t u lo hi He H i Hi.
  destruct (Z.eq_dec i lo) as [->|Hne]; [exact He | apply H; lia].
Qed.

(** *** [zset] / [tset] congruences

    Three shapes, and the round-trip lanes want all three: a write OUTSIDE
    the window is invisible to it; the SAME write on both sides preserves
    it; and a write INSIDE that stores the value the other side already
    holds preserves it (the "one more entry agrees" step of every
    table-filling loop). *)

Lemma arr_eq_on_zset_out_l :
  forall a b lo hi i v,
    ~ (lo <= i < hi) -> arr_eq_on a b lo hi -> arr_eq_on (zset a i v) b lo hi.
Proof.
  intros a b lo hi i v Hout H j Hj.
  rewrite zset_other by lia. now apply H.
Qed.

Lemma arr_eq_on_zset_out_r :
  forall a b lo hi i v,
    ~ (lo <= i < hi) -> arr_eq_on a b lo hi -> arr_eq_on a (zset b i v) lo hi.
Proof.
  intros a b lo hi i v Hout H j Hj.
  rewrite zset_other by lia. now apply H.
Qed.

(** The self form: writing outside a window leaves the window alone.  This
    is the one every loop invariant reaches for. *)
Lemma arr_eq_on_zset_out :
  forall a lo hi i v, ~ (lo <= i < hi) -> arr_eq_on (zset a i v) a lo hi.
Proof.
  intros a lo hi i v Hout j Hj. rewrite zset_other by lia. reflexivity.
Qed.

Lemma arr_eq_on_zset :
  forall a b lo hi i v,
    arr_eq_on a b lo hi -> arr_eq_on (zset a i v) (zset b i v) lo hi.
Proof.
  intros a b lo hi i v H j Hj.
  destruct (Z.eq_dec j i) as [->|Hne].
  - now rewrite !zset_same.
  - rewrite !zset_other by exact Hne. now apply H.
Qed.

Lemma arr_eq_on_zset_in :
  forall a b lo hi i v,
    arr_eq_on a b lo hi -> b i = v -> arr_eq_on (zset a i v) b lo hi.
Proof.
  intros a b lo hi i v H Hv j Hj.
  destruct (Z.eq_dec j i) as [->|Hne].
  - now rewrite zset_same.
  - rewrite zset_other by exact Hne. now apply H.
Qed.

Lemma tbl_eq_on_tset_out_l :
  forall t u lo hi i e,
    ~ (lo <= i < hi) -> tbl_eq_on t u lo hi -> tbl_eq_on (tset t i e) u lo hi.
Proof.
  intros t u lo hi i e Hout H j Hj.
  rewrite tset_other by lia. now apply H.
Qed.

Lemma tbl_eq_on_tset_out_r :
  forall t u lo hi i e,
    ~ (lo <= i < hi) -> tbl_eq_on t u lo hi -> tbl_eq_on t (tset u i e) lo hi.
Proof.
  intros t u lo hi i e Hout H j Hj.
  rewrite tset_other by lia. now apply H.
Qed.

Lemma tbl_eq_on_tset_out :
  forall t lo hi i e, ~ (lo <= i < hi) -> tbl_eq_on (tset t i e) t lo hi.
Proof.
  intros t lo hi i e Hout j Hj. rewrite tset_other by lia. reflexivity.
Qed.

Lemma tbl_eq_on_tset :
  forall t u lo hi i e,
    tbl_eq_on t u lo hi -> tbl_eq_on (tset t i e) (tset u i e) lo hi.
Proof.
  intros t u lo hi i e H j Hj.
  destruct (Z.eq_dec j i) as [->|Hne].
  - now rewrite !tset_same.
  - rewrite !tset_other by exact Hne. now apply H.
Qed.

Lemma tbl_eq_on_tset_in :
  forall t u lo hi i e,
    tbl_eq_on t u lo hi -> u i = e -> tbl_eq_on (tset t i e) u lo hi.
Proof.
  intros t u lo hi i e H He j Hj.
  destruct (Z.eq_dec j i) as [->|Hne].
  - now rewrite tset_same.
  - rewrite tset_other by exact Hne. now apply H.
Qed.

(** *** The bridge to [zarr_take] / [ztbl_take]

    The differential harness reads a prefix as a list; agreement on
    [0 .. n) is exactly equality of those lists, so a proof can move
    between the two views without a second induction. *)

Lemma arr_eq_on_take :
  forall a b n, arr_eq_on a b 0 (Z.of_nat n) -> zarr_take a (Z.of_nat n) = zarr_take b (Z.of_nat n).
Proof.
  intros a b n H. unfold zarr_take. rewrite Nat2Z.id.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

Lemma tbl_eq_on_take :
  forall t u n, tbl_eq_on t u 0 (Z.of_nat n) -> ztbl_take t (Z.of_nat n) = ztbl_take u (Z.of_nat n).
Proof.
  intros t u n H. unfold ztbl_take. rewrite Nat2Z.id.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

(** ** zlib's public return codes and flush values ([zlib.h:168-189])

    INTEGRATION NOTE (WP-4 seam).  [Deflate.v] and [Inflate.v] transcribe
    two different C files that both [#include <zlib.h>], and each lane
    independently wrote out the nine constants below with identical values.
    A file that [Require Import]s both — [Codec.v] does — would silently
    take whichever came last, so the nine live here, at the one node both
    lanes already depend on.  Each file keeps the constants only IT uses
    ([Z_PARTIAL_FLUSH], [Z_FULL_FLUSH], [Z_HUFFMAN_ONLY], [Z_RLE],
    [PRESET_DICT] in [Deflate.v]; [Z_NEED_DICT], [Z_DATA_ERROR],
    [Z_MEM_ERROR], [Z_VERSION_ERROR], [Z_TREES], [DEF_WBITS] in
    [Inflate.v]), because those never collided. *)

Definition Z_OK           : Z := 0.
Definition Z_STREAM_END   : Z := 1.
Definition Z_STREAM_ERROR : Z := -2.
Definition Z_BUF_ERROR    : Z := -5.

Definition Z_NO_FLUSH     : Z := 0.
Definition Z_SYNC_FLUSH   : Z := 2.
Definition Z_FINISH       : Z := 4.
Definition Z_BLOCK        : Z := 5.

(** [zlib.h:206] [#define Z_DEFLATED 8]. *)
Definition Z_DEFLATED     : Z := 8.
