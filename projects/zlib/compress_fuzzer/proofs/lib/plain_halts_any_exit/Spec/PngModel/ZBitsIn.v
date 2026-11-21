(** * Spec.PngModel.ZBitsIn — zlib's INFLATE bit reader ([inflate.c]'s macros).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Source: [materials/zlib-1.3.1/inflate.c:459-505] — the six macros
    [INITBITS], [PULLBYTE], [NEEDBITS], [BITS], [DROPBITS], [BYTEBITS] that
    every arm of [inflate]'s mode machine is written in terms of, together
    with the [LOAD]/[RESTORE] pair ([inflate.c:441-457]) that moves them
    between [z_stream]/[inflate_state] and the C locals.

    NAMING.  The WP-4 lane's frozen interface for the reader is [BR] +
    [br_initbits]/[br_pullbyte]/[br_needbits]/[br_bits_of]/[br_dropbits]/
    [br_bytebits], and it was to be delivered in [Spec/PngModel/ZBits.v].
    That filename was taken first by the deflate lane's bit WRITER ([BW],
    from [trees.c]), so the reader lives here.  The signatures below are
    EXACTLY the frozen ones; if the lane lead's [ZBits.v] later carries the
    reader too, deleting this file and repointing one [Require Import] line
    in [InflateFast.v] and [Inflate.v] is the whole migration.

    BUG-FOR-BUG.  [hold] is an [unsigned long] (64-bit on riscv64 LP64) and
    [bits] an [unsigned].  Neither ever wraps on a path [inflate] can take:
    the largest request is [NEEDBITS(32)] ([inflate.c:1145] and [:1197]),
    which pulls only while [bits < 32], so [bits <= 39] and
    [hold < 2^47] < 2^64 always.  The model therefore writes the plain
    integer arithmetic the C computes, and [br_wf] below records the range
    invariant that makes "plain" and "truncated" agree.  The one place the
    C's unsigned-ness IS observable is [br_dropbits] with [n > br_bits]
    (which would wrap [bits] to a huge value); [inflate] never does that —
    every [DROPBITS(n)] is preceded by a [NEEDBITS] or a table entry whose
    [bits] field the caller has just checked against [bits]. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The reader's whole state: the input byte array, how much of it is left,
    where the next unread byte is, and the LSB-first accumulator.

    [br_in] is the array [strm->next_in] points into, indexed ABSOLUTELY
    (index 0 = the base of the buffer, not [next_in]); [br_next] is the
    index of [next_in] itself and [br_have] is [strm->avail_in].  Holding
    the base array rather than a suffix list is what makes [PULLBYTE]'s
    [*next++] a pointwise read, and it is the shape the machine-level
    [BR_rep] wants ([c5-invariants.md] §3.1). *)
Record BR : Type := mkBR {
  br_in   : zarr;  (** input bytes, indexed from 0 *)
  br_have : Z;     (** [strm->avail_in]: bytes remaining *)
  br_next : Z;     (** index of the next unread byte *)
  br_hold : Z;     (** [hold], the accumulator, LSB-first *)
  br_bits : Z      (** [bits], valid bits in [br_hold] *)
}.

(** [inflate.c:465-469] [INITBITS()]: [hold = 0; bits = 0]. *)
Definition br_initbits (b : BR) : BR :=
  {| br_in := br_in b; br_have := br_have b; br_next := br_next b;
     br_hold := 0; br_bits := 0 |}.

(** [inflate.c:473-480] [PULLBYTE()]:
<<
    if (have == 0) goto inf_leave;
    have--;
    hold += (unsigned long)( *next++ ) << bits;
    bits += 8;
>>
    [None] is the [goto inf_leave]. *)
Definition br_pullbyte (b : BR) : option BR :=
  if Z.eqb (br_have b) 0 then None
  else Some {| br_in   := br_in b;
               br_have := br_have b - 1;
               br_next := br_next b + 1;
               br_hold := br_hold b + Z.shiftl (br_in b (br_next b)) (br_bits b);
               br_bits := br_bits b + 8 |}.

(** [inflate.c:484-488] [NEEDBITS(n)]: [while (bits < n) PULLBYTE();].

    Fuel [Z.to_nat n]: every trip adds 8 to [bits], so from [bits >= 0] at
    most [ceil(n/8) <= n] trips are needed whenever [n >= 1], and for
    [n <= 0] the guard is false on entry.  Exhausting the fuel is therefore
    unreachable and [None] means exactly the C's [goto inf_leave]. *)
Fixpoint br_needbits_go (f : nat) (n : Z) (b : BR) {struct f} : option BR :=
  match f with
  | O => if Z.ltb (br_bits b) n then None else Some b
  | S k =>
      if Z.ltb (br_bits b) n
      then match br_pullbyte b with
           | None => None
           | Some b' => br_needbits_go k n b'
           end
      else Some b
  end.

Definition br_needbits (n : Z) (b : BR) : option BR :=
  br_needbits_go (Z.to_nat n) n b.

(** [inflate.c:491] [BITS(n)]: [((unsigned)hold & ((1U << n) - 1))]. *)
Definition br_bits_of (n : Z) (b : BR) : Z :=
  Z.land (br_hold b) (Z.shiftl 1 n - 1).

(** [inflate.c:494-498] [DROPBITS(n)]: [hold >>= n; bits -= n]. *)
Definition br_dropbits (n : Z) (b : BR) : BR :=
  {| br_in := br_in b; br_have := br_have b; br_next := br_next b;
     br_hold := Z.shiftr (br_hold b) n; br_bits := br_bits b - n |}.

(** [inflate.c:501-505] [BYTEBITS()]: [hold >>= bits & 7; bits -= bits & 7]. *)
Definition br_bytebits (b : BR) : BR :=
  br_dropbits (Z.land (br_bits b) 7) b.

(** ** Well-formedness

    The invariant [inflate] maintains across every arm, and the one a
    machine-level [BR_rep] carries.  [br_bits <= 39] is the bound
    [NEEDBITS(32)] can reach; [br_hold < 2^br_bits] says the accumulator
    holds exactly [br_bits] valid bits and nothing above them, which is
    what makes [+] and [|] agree in [br_pullbyte]. *)
Definition br_wf (b : BR) : Prop :=
  0 <= br_bits b <= 39
  /\ 0 <= br_hold b < Z.shiftl 1 (br_bits b)
  /\ 0 <= br_have b
  /\ (forall i, 0 <= br_in b i < 256).

(** ** Elementary facts

    Small and cheap; the substantial bit-window theory belongs to the
    machine-level walk. *)

Lemma br_initbits_bits : forall b, br_bits (br_initbits b) = 0.
Proof. reflexivity. Qed.

Lemma br_initbits_hold : forall b, br_hold (br_initbits b) = 0.
Proof. reflexivity. Qed.

(** [PULLBYTE] consumes exactly one byte of input and adds exactly 8 bits. *)
Lemma br_pullbyte_step :
  forall b b', br_pullbyte b = Some b' ->
    br_have b' = br_have b - 1
    /\ br_next b' = br_next b + 1
    /\ br_bits b' = br_bits b + 8
    /\ br_in b' = br_in b.
Proof.
  intros b b' H; unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  inversion H; subst; cbn; repeat split.
Qed.

(** [PULLBYTE] fails exactly when the input is exhausted. *)
Lemma br_pullbyte_none : forall b, br_pullbyte b = None <-> br_have b = 0.
Proof.
  intros b; unfold br_pullbyte; split; intros H.
  - destruct (Z.eqb (br_have b) 0) eqn:E; [now apply Z.eqb_eq in E|discriminate].
  - now apply Z.eqb_eq in H as ->.
Qed.

(** [NEEDBITS] never loses bits and never rewinds the input, and on success
    it delivers what it promised.  The three facts every arm's proof needs
    before it may call [br_bits_of n]. *)
Lemma br_needbits_go_ok :
  forall f n b b', br_needbits_go f n b = Some b' -> n <= br_bits b'.
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [br_needbits_go] in H.
  - destruct (Z.ltb (br_bits b) n) eqn:E; [discriminate|].
    apply Z.ltb_ge in E. now inversion H; subst.
  - destruct (Z.ltb (br_bits b) n) eqn:E.
    + destruct (br_pullbyte b) as [b1|]; [now apply (IH n b1)|discriminate].
    + apply Z.ltb_ge in E. now inversion H; subst.
Qed.

Lemma br_needbits_ok : forall n b b', br_needbits n b = Some b' -> n <= br_bits b'.
Proof. intros n b b'; apply br_needbits_go_ok. Qed.

Lemma br_needbits_go_mono :
  forall f n b b', br_needbits_go f n b = Some b' ->
    br_in b' = br_in b
    /\ br_have b' <= br_have b
    /\ br_next b <= br_next b'
    /\ br_have b + br_next b = br_have b' + br_next b'.
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [br_needbits_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|].
    inversion H; subst; repeat split; lia.
  - destruct (Z.ltb (br_bits b) n).
    + destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      apply br_pullbyte_step in Hp as (H1 & H2 & _ & H4).
      apply IH in H as (G1 & G2 & G3 & G4).
      rewrite G1, H4. repeat split; lia.
    + inversion H; subst; repeat split; lia.
Qed.

Lemma br_needbits_mono :
  forall n b b', br_needbits n b = Some b' ->
    br_in b' = br_in b /\ br_have b' <= br_have b /\ br_next b <= br_next b'
    /\ br_have b + br_next b = br_have b' + br_next b'.
Proof. intros n b b'; apply br_needbits_go_mono. Qed.

(** [DROPBITS] is exactly the inverse bookkeeping. *)
Lemma br_dropbits_bits : forall n b, br_bits (br_dropbits n b) = br_bits b - n.
Proof. reflexivity. Qed.

Lemma br_dropbits_have : forall n b, br_have (br_dropbits n b) = br_have b.
Proof. reflexivity. Qed.

(** [BYTEBITS] lands on a byte boundary and never removes 8 or more bits. *)
Lemma br_bytebits_aligned :
  forall b, 0 <= br_bits b -> (br_bits (br_bytebits b)) mod 8 = 0.
Proof.
  intros b Hb. cbn [br_bytebits br_dropbits br_bits].
  replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8.
  rewrite Zminus_mod, Z.mod_mod by lia.
  now rewrite Z.sub_diag, Zmod_0_l.
Qed.

(** [BITS(n)] really is the low [n] bits. *)
Lemma br_bits_of_range :
  forall n b, 0 <= n -> 0 <= br_hold b -> 0 <= br_bits_of n b < Z.shiftl 1 n.
Proof.
  intros n b Hn Hh. unfold br_bits_of.
  rewrite Z.shiftl_1_l.
  assert (H2 : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (br_hold b) (2 ^ n) H2). lia.
Qed.

(** ** The list view of the unread input -- the L0 refinement bridge

    L0's declarative bit view is a [list bool] over a [list Z] of bytes,
    but [br_in] is a [zarr], a TOTAL FUNCTION, so there is no byte list to
    hand it.  [br_bytes] is that view: the [br_have] bytes still unread,
    starting at [br_next].

    Why the list lives on THIS side of the bridge rather than L0 taking a
    function-plus-length (wp2-fpstep's argument, 2026-08-16, and it is the
    right one).  L0's largest obligation set is the suffix-invariance
    ([_append]) family, and [bytes_bits (xs ++ ys) = bytes_bits xs ++
    bytes_bits ys] is a one-line [flat_map] fact over lists but an
    index-shifting argument with no [++] to induct on over a [zarr].  The
    encoder half has no [zarr] at all -- it produces a byte list -- so a
    [zarr]-based L0 would force the encoder to convert merely to STATE
    things, inverting the layering.  And [zarr]'s [zset] closure chains
    reduce super-linearly (measured: 0.03 s at 64 B, 5.4 s at 4 KB, 736 s
    at 16 KB), so keeping them below the bridge confines that cost to the
    transcription, where it is already priced in, instead of baking it
    into every lane's statements permanently.

    The unconsumed bit stream of [b] is

      (the low [br_bits b] bits of [br_hold b]) ++ bytes_bits (br_bytes b)

    and the point of the three lemmas below is that this is a refinement
    with a pleasant shape: [br_pullbyte] moves one byte out of the list
    and into [hold], leaving the CONCATENATION unchanged -- so the noisy
    buffering operation is a no-op at spec level -- while [br_dropbits],
    the operation that actually consumes, does not touch the list at all
    and advances only the [hold] side. *)

Definition br_bytes (b : BR) : list Z :=
  map (fun k => br_in b (br_next b + Z.of_nat k)) (seq 0 (Z.to_nat (br_have b))).

Lemma br_bytes_length : forall b, length (br_bytes b) = Z.to_nat (br_have b).
Proof. intro b; unfold br_bytes; rewrite length_map, length_seq; reflexivity. Qed.

(** [br_pullbyte] pops the head of the list; nothing else about it moves. *)
Lemma br_bytes_pullbyte :
  forall b b', 0 <= br_have b -> br_pullbyte b = Some b' ->
    br_bytes b = br_in b (br_next b) :: br_bytes b'.
Proof.
  intros b b' Hnn H.
  pose proof (br_pullbyte_step b b' H) as (Hh & Hn & _ & Hi).
  assert (Hpos : 0 < br_have b).
  { unfold br_pullbyte in H.
    destruct (Z.eqb_spec (br_have b) 0); [discriminate|lia]. }
  unfold br_bytes. rewrite Hh, Hn, Hi.
  replace (Z.to_nat (br_have b)) with (S (Z.to_nat (br_have b - 1))) by lia.
  cbn [seq map]. f_equal.
  - f_equal; lia.
  - rewrite <- seq_shift, map_map. apply map_ext; intro k. f_equal. lia.
Qed.

(** [br_dropbits] -- and hence [br_bytebits] -- leaves the list alone. *)
Lemma br_bytes_dropbits : forall n b, br_bytes (br_dropbits n b) = br_bytes b.
Proof. reflexivity. Qed.

Lemma br_bytes_bytebits : forall b, br_bytes (br_bytebits b) = br_bytes b.
Proof. intro b; apply br_bytes_dropbits. Qed.

Lemma br_bytes_range :
  forall b, (forall i, 0 <= br_in b i < 256) ->
    Forall (fun x => 0 <= x < 256) (br_bytes b).
Proof.
  intros b Hr. apply Forall_forall. intros x Hx.
  unfold br_bytes in Hx. apply in_map_iff in Hx as [k [Hk _]].
  subst x. apply Hr.
Qed.
