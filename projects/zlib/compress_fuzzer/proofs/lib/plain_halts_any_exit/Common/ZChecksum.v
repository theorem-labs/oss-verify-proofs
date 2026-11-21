(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common/ZChecksum — the functional model for zlib's two checksums.

    TRUST BOUNDARY: image-INDEPENDENT proof library.  Pure Gallina: no
    binary, no register, no memory.  This is the model the [crc32_z] and
    [adler32_z] walks state their postconditions against, and the model the
    PNG chunk-framing layer of [RoundTrip.v] will reuse.

    ** The finding that shapes this file

    zlib 1.3.1 computes CRC-32 with a BRAIDED implementation (N = 5 lanes of
    W = 4 bytes, so 20 bytes per round) driven by two static tables,
    [crc_table] (256 words) and [crc_braid_table] (4 x 256 words).  Read
    naively that is a GF(2)[x]/p development: zlib BUILDS the braid table as
    [multmodp (i << 24) (x2nmodp ((N*W + 3 - k) << 3, 0))], i.e. polynomial
    multiplication modulo the CRC polynomial, and the obvious plan is to
    formalise the quotient ring, the [multmodp] ladder and the [x2nmodp]
    exponentiation, then prove the braid identity by algebra.  That plan is
    what makes crc32_z look research-grade.

    It is not necessary.  Everything collapses to ONE operator:

      [xt c]  — multiply by x in the reflected representation, i.e.
                [c >> 1] with the polynomial folded in when the low bit is
                set.  This is the innermost line of zlib's own table
                generator.

    With [xtn n = xt iterated n times], all four facts below hold, and each
    was CHECKED NUMERICALLY against the bytes in the reference image before
    a line of Rocq was written (the tables live at 0x580b8 and 0x58538):

      crc_table[n]          = xtn 8 n
      crc_step c b          = xtn 8 (c XOR b)                (b < 256)
      crc_braid_table[k][i] = xtn ((23-k)*8) (i << 24)        (N=5, W=4)
      xt (a XOR b)          = xt a XOR xt b                   (linearity)

    So there is no ring to build: the braid identity is linear algebra over
    [Z.lxor] plus exponent bookkeeping, and [braid_round c w] is exactly
    [xtn 160 (c XOR w)] — absorb the lane's four bytes, then advance past the
    other sixteen.  [braid_round_xtn] below is that theorem, and it is what
    turns crc32_z from a research item into a mechanical walk.

    ** What is here

    - [xt]/[xtn] and their algebra (linearity, additivity, range, the
      shift laws that let a byte be pulled out of a word);
    - the byte-wise CRC model ([crc_step], [crc32_fold], [crc32_model]);
    - the braided model ([absorb4], [braid_tab], [braid_round]) and the two
      theorems relating it to the byte-wise one;
    - the Adler-32 model, in BOTH the mathematical form (reduce every byte)
      and the deferred form the machine actually runs (reduce once per NMAX
      block), plus the congruence between them;
    - the magic-division statement the compiled modulo reduction needs.

    Table CONTENTS are not checked here — that is image-specific and lives
    in [RefZSum.v]/[AgentZSum.v] as [chk_rom] facts against this file's
    functions. *)

From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.

Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* =========================================================================
   1.  The operator
   ========================================================================= *)

(** The reflected CRC-32 polynomial, zlib's [0xedb88320]. *)
Definition POLY : Z := 3988292384.

(** Multiply by x, reflected.  Verbatim the body of zlib's table loop. *)
Definition xt (c : Z) : Z := Z.lxor (Z.shiftr c 1) (if Z.odd c then POLY else 0).

(** Iterated.  [xtn (S n) c = xtn n (xt c)] — the step is applied FIRST, so
    that induction on [n] peels the operator off the argument side, which is
    the direction every proof below wants. *)
Fixpoint xtn (n : nat) (c : Z) : Z :=
  match n with O => c | S k => xtn k (xt c) end.

Lemma xtn_O : forall c, xtn 0 c = c. Proof. reflexivity. Qed.
Lemma xtn_S : forall n c, xtn (S n) c = xtn n (xt c). Proof. reflexivity. Qed.

Lemma xtn_add : forall m n c, xtn (m + n) c = xtn n (xtn m c).
Proof.
  induction m as [|m IH]; intros n c; cbn; [reflexivity | apply IH].
Qed.

Lemma xtn_S_out : forall n c, xtn (S n) c = xt (xtn n c).
Proof.
  intros n c. replace (S n) with (n + 1)%nat by lia.
  rewrite xtn_add. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Linearity
   ------------------------------------------------------------------------- *)

Lemma odd_lxor : forall a b, Z.odd (Z.lxor a b) = xorb (Z.odd a) (Z.odd b).
Proof.
  intros a b. rewrite <- !Z.bit0_odd. rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma shiftr_lxor : forall a b n,
  Z.shiftr (Z.lxor a b) n = Z.lxor (Z.shiftr a n) (Z.shiftr b n).
Proof.
  intros a b n. apply Z.bits_inj'. intros m Hm.
  rewrite Z.lxor_spec, !Z.shiftr_spec, Z.lxor_spec by lia. reflexivity.
Qed.

Lemma xt_xor : forall a b, xt (Z.lxor a b) = Z.lxor (xt a) (xt b).
Proof.
  intros a b. unfold xt. rewrite shiftr_lxor, odd_lxor.
  destruct (Z.odd a), (Z.odd b); cbn [xorb];
    apply Z.bits_inj'; intros m Hm;
    rewrite ?Z.lxor_spec, ?Z.bits_0; btauto.
Qed.

Lemma xtn_xor : forall n a b, xtn n (Z.lxor a b) = Z.lxor (xtn n a) (xtn n b).
Proof.
  induction n as [|n IH]; intros a b; cbn; [reflexivity|].
  rewrite xt_xor. apply IH.
Qed.

Lemma xt_0 : xt 0 = 0. Proof. reflexivity. Qed.

Lemma xtn_0 : forall n, xtn n 0 = 0.
Proof. induction n as [|n IH]; cbn; [reflexivity | rewrite xt_0; exact IH]. Qed.

(* -------------------------------------------------------------------------
   Range: 32 bits in, 32 bits out
   ------------------------------------------------------------------------- *)

(** A 32-bit bound survives [lxor].  Used for [xt]'s range and for the
    byte-wise fold's. *)
Lemma lxor_bound32 : forall a b,
  0 <= a < 4294967296 -> 0 <= b < 4294967296 -> 0 <= Z.lxor a b < 4294967296.
Proof.
  intros a b Ha Hb.
  assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact Hn|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|Hz]; [rewrite E; lia|].
  replace 4294967296 with (2 ^ 32) by reflexivity.
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 32 ltac:(lia))).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [E|Ha0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 a 32 ltac:(lia))). cbn. lia.
  - destruct (Z.eq_dec b 0) as [E|Hb0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 b 32 ltac:(lia))). cbn. lia.
Qed.

Lemma xt_range : forall c, 0 <= c < 4294967296 -> 0 <= xt c < 4294967296.
Proof.
  intros c Hc. unfold xt.
  assert (H1 : 0 <= Z.shiftr c 1 < 4294967296).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with c; [apply Z.div_le_upper_bound; lia | lia]. }
  destruct (Z.odd c).
  - apply lxor_bound32; [exact H1 | unfold POLY; lia].
  - rewrite Z.lxor_0_r. exact H1.
Qed.

Lemma xtn_range : forall n c, 0 <= c < 4294967296 -> 0 <= xtn n c < 4294967296.
Proof.
  induction n as [|n IH]; intros c Hc; cbn; [exact Hc | apply IH, xt_range, Hc].
Qed.

(* -------------------------------------------------------------------------
   The shift law: [xt] on an even value is a plain shift, so [k] steps
   cancel a [<< k].  This is what lets a byte be pulled out of a word.
   ------------------------------------------------------------------------- *)

Lemma xt_even : forall v, 0 <= v -> Z.odd v = false -> xt v = Z.shiftr v 1.
Proof. intros v _ Hv. unfold xt. rewrite Hv. apply Z.lxor_0_r. Qed.

Lemma odd_shiftl_S : forall b k, 0 <= b -> Z.odd (Z.shiftl b (Z.of_nat (S k))) = false.
Proof.
  intros b k Hb. rewrite <- Z.bit0_odd, Z.shiftl_spec_low by lia. reflexivity.
Qed.

Lemma shiftr_shiftl_S : forall b k, 0 <= b ->
  Z.shiftr (Z.shiftl b (Z.of_nat (S k))) 1 = Z.shiftl b (Z.of_nat k).
Proof.
  intros b k Hb. rewrite Z.shiftr_shiftl_l by lia.
  f_equal. lia.
Qed.

(** [k] applications of [xt] cancel a shift of [k + m], leaving [<< m]. *)
Lemma xtn_shiftl : forall k m b, 0 <= b ->
  xtn k (Z.shiftl b (Z.of_nat (k + m))) = Z.shiftl b (Z.of_nat m).
Proof.
  induction k as [|k IH]; intros m b Hb; cbn [xtn].
  - f_equal.
  - replace (S k + m)%nat with (S (k + m)) by lia.
    rewrite xt_even by
      (first [ apply Z.shiftl_nonneg; exact Hb | apply odd_shiftl_S; exact Hb ]).
    rewrite shiftr_shiftl_S by exact Hb. apply IH. exact Hb.
Qed.

Corollary xtn_shiftl_exact : forall k b, 0 <= b ->
  xtn k (Z.shiftl b (Z.of_nat k)) = b.
Proof.
  intros k b Hb.
  replace (Z.of_nat k) with (Z.of_nat (k + 0)) by (f_equal; lia).
  rewrite (xtn_shiftl k 0 b Hb). cbn [Z.of_nat]. apply Z.shiftl_0_r.
Qed.

(** and hence, at any exponent at least [k], a shifted byte costs [k] fewer
    steps. *)
Lemma xtn_shifted_byte : forall n k b, 0 <= b -> (k <= n)%nat ->
  xtn n (Z.shiftl b (Z.of_nat k)) = xtn (n - k) b.
Proof.
  intros n k b Hb Hk.
  replace n with (k + (n - k))%nat at 1 by lia.
  rewrite xtn_add, xtn_shiftl_exact by exact Hb. reflexivity.
Qed.

(* =========================================================================
   2.  Byte-wise CRC-32
   ========================================================================= *)

Definition byteZ (c : Z) (k : nat) : Z :=
  Z.land (Z.shiftr c (8 * Z.of_nat k)) 255.

Lemma byteZ_range : forall c k, 0 <= byteZ c k < 256.
Proof.
  intros c k. unfold byteZ.
  replace 255 with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. apply Z.mod_pos_bound. lia.
Qed.

(** zlib's [crc_table]. *)
Definition crc_tab (n : Z) : Z := xtn 8 n.

(** One byte absorbed: [(c >> 8) XOR crc_table[(c XOR b) & 0xff]].  The
    identity below is what removes the table from the algebra. *)
Definition crc_step (c b : Z) : Z := xtn 8 (Z.lxor c b).

Definition crc_fold (c : Z) (bs : list Z) : Z := fold_left crc_step bs c.

(** The exported entry point: zlib's [crc32_z] complements in and out. *)
Definition MASK32 : Z := 4294967295.
Definition crc32_model (init : Z) (bs : list Z) : Z :=
  Z.lxor (crc_fold (Z.lxor init MASK32) bs) MASK32.

Lemma crc_fold_nil : forall c, crc_fold c [] = c. Proof. reflexivity. Qed.
Lemma crc_fold_cons : forall c b bs, crc_fold c (b :: bs) = crc_fold (crc_step c b) bs.
Proof. reflexivity. Qed.
Lemma crc_fold_app : forall bs cs c, crc_fold c (bs ++ cs) = crc_fold (crc_fold c bs) cs.
Proof. intros bs cs c. unfold crc_fold. apply fold_left_app. Qed.

Lemma crc_fold_range : forall bs c, 0 <= c < 4294967296 ->
  (forall b, In b bs -> 0 <= b < 256) -> 0 <= crc_fold c bs < 4294967296.
Proof.
  induction bs as [|b bs IH]; intros c Hc Hb; [exact Hc|].
  rewrite crc_fold_cons. apply IH.
  - unfold crc_step. apply xtn_range. apply lxor_bound32; [exact Hc|].
    assert (Hb0 : 0 <= b < 256) by (apply Hb; left; reflexivity). lia.
  - intros x Hx. apply Hb. right. exact Hx.
Qed.

(* =========================================================================
   3.  The braided CRC, and why it is the same thing
   ========================================================================= *)

(** A four-byte little-endian word. *)
Definition wordLE (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor b0 (Z.lxor (Z.shiftl b1 8) (Z.lxor (Z.shiftl b2 16) (Z.shiftl b3 24))).

(** Splitting a 32-bit value into its four bytes, as [xtn] sees it. *)
(** The split proved by a cleaner route: [xtn] on a word equals the XOR of
    [xtn] on its shifted bytes, and [xtn_shifted_byte] discharges each
    shift.  Stating it over [wordLE] rather than over [byteZ] avoids all
    bit-extraction reasoning, and [wordLE] is the form both the walk and the
    braid table present anyway. *)
Lemma xtn_wordLE : forall n b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 -> (24 <= n)%nat ->
  xtn n (wordLE b0 b1 b2 b3)
  = Z.lxor (xtn n b0)
      (Z.lxor (xtn (n - 8) b1) (Z.lxor (xtn (n - 16) b2) (xtn (n - 24) b3))).
Proof.
  intros n b0 b1 b2 b3 H0 H1 H2 H3 Hn. unfold wordLE.
  rewrite !xtn_xor.
  replace 8 with (Z.of_nat 8) by reflexivity.
  replace 16 with (Z.of_nat 16) by reflexivity.
  replace 24 with (Z.of_nat 24) by reflexivity.
  rewrite (xtn_shifted_byte n 8 b1) by (assumption || lia).
  rewrite (xtn_shifted_byte n 16 b2) by (assumption || lia).
  rewrite (xtn_shifted_byte n 24 b3) by (assumption || lia).
  reflexivity.
Qed.

(** Absorbing a whole little-endian word is four [crc_step]s — and it is
    [xtn 32] of the XOR, with no table in sight. *)
Theorem crc_step4 : forall c b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  crc_step (crc_step (crc_step (crc_step c b0) b1) b2) b3
  = xtn 32 (Z.lxor c (wordLE b0 b1 b2 b3)).
Proof.
  intros c b0 b1 b2 b3 H0 H1 H2 H3. unfold crc_step.
  rewrite (xtn_xor 32 c (wordLE b0 b1 b2 b3)).
  rewrite (xtn_wordLE 32 b0 b1 b2 b3) by (assumption || lia).
  cbn [Nat.sub].
  rewrite !xtn_xor, <- !xtn_add.
  cbn [Nat.add].
  rewrite !Z.lxor_assoc. reflexivity.
Qed.

(** zlib's [crc_braid_table[k][i]], N = 5 lanes of W = 4 bytes.  The
    exponent is [(N*W + 3 - k) * 8 = (23 - k) * 8]: the byte's own position
    within the word, plus the 20-byte stride the lane skips. *)
Definition braid_tab (k : nat) (i : Z) : Z := xtn ((23 - k) * 8) (Z.shiftl i 24).

(** and equivalently, with the [<< 24] cancelled. *)
Lemma braid_tab_alt : forall k i, 0 <= i -> (k <= 3)%nat ->
  braid_tab k i = xtn ((23 - k) * 8 - 24) i.
Proof.
  intros k i Hi Hk. unfold braid_tab.
  replace 24 with (Z.of_nat 24) by reflexivity.
  rewrite (xtn_shifted_byte ((23 - k) * 8) 24 i) by (assumption || lia).
  reflexivity.
Qed.

(** One lane's round: the four table lookups zlib XORs together.  The four
    bytes are arguments rather than extracted here, because the machine has
    them in four separate registers ([zext.b] and [srliw] produce them) and
    because it keeps every bit-extraction obligation on the walk's side of
    the interface, where the register facts already live. *)
Definition braid_round4 (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor (braid_tab 0 b0)
    (Z.lxor (braid_tab 1 b1) (Z.lxor (braid_tab 2 b2) (braid_tab 3 b3))).

(** THE BRAID THEOREM.  A lane round absorbs the lane's four bytes and
    advances the result past the other sixteen bytes of the block:
    [xtn 160 = xtn 128 . xtn 32], absorb four then skip sixteen.  Everything
    the braided main loop does is this, five times per round.

    Note what this does NOT need: no polynomial type, no [multmodp], no
    [x2nmodp], no quotient ring.  The whole content is [xtn_wordLE] plus
    exponent arithmetic — which is why crc32_z is a mechanical walk and not
    a research item. *)
Theorem braid_round4_xtn : forall b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  braid_round4 b0 b1 b2 b3 = xtn 160 (wordLE b0 b1 b2 b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold braid_round4.
  rewrite !braid_tab_alt by (assumption || lia).
  rewrite (xtn_wordLE 160 b0 b1 b2 b3) by (assumption || lia).
  cbn [Nat.sub Nat.mul]. reflexivity.
Qed.

(** Absorbing a four-byte word, named for the walk. *)
Definition absorb4 (c w : Z) : Z := xtn 32 (Z.lxor c w).

Lemma braid_round4_absorb : forall c b0 b1 b2 b3,
  0 <= b0 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  xtn 128 (absorb4 c (wordLE b0 b1 b2 b3))
  = xtn 160 (Z.lxor c (wordLE b0 b1 b2 b3)).
Proof.
  intros. unfold absorb4. rewrite <- xtn_add. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The two bridges the walk needs between a 32-bit register value and its
   four bytes.  Both are stated over [byteZ], which is exactly what the
   machine's [zext.b] / [srliw] pair computes.
   ------------------------------------------------------------------------- *)

Lemma testbit_high : forall v n m, 0 <= v < 2 ^ n -> 0 <= n <= m ->
  Z.testbit v m = false.
Proof.
  intros v n m Hv Hm.
  destruct (Z.eq_dec v 0) as [E|Hv0]; [rewrite E; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 v < n) by (apply (proj1 (Z.log2_lt_pow2 v n ltac:(lia))); lia).
  lia.
Qed.

Lemma land_shiftl_disj : forall x y k, 0 <= x < 2 ^ k -> 0 <= k -> 0 <= y ->
  Z.land x (Z.shiftl y k) = 0.
Proof.
  intros x y k Hx Hk Hy. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec m k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r y (m - k)) by lia. apply Bool.andb_false_r.
  - rewrite (testbit_high x k m Hx) by lia. reflexivity.
Qed.

Lemma wordLE_sum : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  wordLE b0 b1 b2 b3 = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold wordLE.
  assert (S3 : Z.shiftl b3 24 = 16777216 * b3)
    by (rewrite Z.shiftl_mul_pow2 by lia; cbn; ring).
  assert (S2 : Z.shiftl b2 16 = 65536 * b2)
    by (rewrite Z.shiftl_mul_pow2 by lia; cbn; ring).
  assert (S1 : Z.shiftl b1 8 = 256 * b1)
    by (rewrite Z.shiftl_mul_pow2 by lia; cbn; ring).
  assert (A : Z.lxor (Z.shiftl b2 16) (Z.shiftl b3 24) = 65536 * b2 + 16777216 * b3).
  { rewrite <- Z.add_nocarry_lxor; [rewrite S2, S3; ring|].
    rewrite S2. replace (65536 * b2) with (Z.shiftl b2 16) by (rewrite S2; ring).
    apply land_shiftl_disj; [rewrite S2; cbn; lia | lia | lia]. }
  assert (B : Z.lxor (Z.shiftl b1 8) (Z.lxor (Z.shiftl b2 16) (Z.shiftl b3 24))
              = 256 * b1 + (65536 * b2 + 16777216 * b3)).
  { rewrite A, <- Z.add_nocarry_lxor; [rewrite S1; ring|].
    replace (65536 * b2 + 16777216 * b3) with (Z.shiftl (b2 + 256 * b3) 16)
      by (rewrite Z.shiftl_mul_pow2 by lia; cbn; ring).
    rewrite S1. apply land_shiftl_disj; [cbn; lia | lia | lia]. }
  rewrite B, <- Z.add_nocarry_lxor; [ring|].
  replace (256 * b1 + (65536 * b2 + 16777216 * b3))
    with (Z.shiftl (b1 + 256 * b2 + 65536 * b3) 8)
    by (rewrite Z.shiftl_mul_pow2 by lia; cbn; ring).
  apply land_shiftl_disj; [cbn; lia | lia | lia].
Qed.

(** A 32-bit value IS the little-endian word of its own four bytes. *)
Lemma wordLE_bytes : forall v, 0 <= v < 4294967296 ->
  wordLE (byteZ v 0) (byteZ v 1) (byteZ v 2) (byteZ v 3) = v.
Proof.
  intros v Hv.
  assert (Hb : forall k, byteZ v k = (v / 2 ^ (8 * Z.of_nat k)) mod 256).
  { intro k. unfold byteZ. replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
    reflexivity. }
  rewrite wordLE_sum by (rewrite Hb; split;
    [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia]).
  rewrite !Hb. cbn [Z.of_nat Z.mul].
  change (2 ^ 0) with 1. change (2 ^ 8) with 256.
  change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  rewrite Z.div_1_r.
  (* v = (v mod 256) + 256*((v/256) mod 256) + 65536*((v/65536) mod 256)
         + 16777216*((v/16777216) mod 256), for v < 2^32 *)
  assert (E1 : v = 256 * (v / 256) + v mod 256) by (apply Z.div_mod; lia).
  assert (E2 : v / 256 = 256 * (v / 65536) + (v / 256) mod 256).
  { replace (v / 65536) with (v / 256 / 256)
      by (rewrite Z.div_div by lia; f_equal; lia).
    apply Z.div_mod. lia. }
  assert (E3 : v / 65536 = 256 * (v / 16777216) + (v / 65536) mod 256).
  { replace (v / 16777216) with (v / 65536 / 256)
      by (rewrite Z.div_div by lia; f_equal; lia).
    apply Z.div_mod. lia. }
  assert (E4 : (v / 16777216) mod 256 = v / 16777216).
  { apply Z.mod_small. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

(* =========================================================================
   4.  Adler-32
   ========================================================================= *)

Definition ABASE : Z := 65521.
Definition NMAX : Z := 5552.

(** The mathematical model: reduce after every byte. *)
Fixpoint adl (bs : list Z) (s1 s2 : Z) : Z * Z :=
  match bs with
  | [] => (s1, s2)
  | b :: r => let s1' := (s1 + b) mod ABASE in
              adl r s1' ((s2 + s1') mod ABASE)
  end.

(** What the machine runs: no reduction inside a block. *)
Fixpoint adl_raw (bs : list Z) (s1 s2 : Z) : Z * Z :=
  match bs with
  | [] => (s1, s2)
  | b :: r => let s1' := s1 + b in adl_raw r s1' (s2 + s1')
  end.

Definition adler32_model (init : Z) (bs : list Z) : Z :=
  let s1 := Z.land init 65535 in
  let s2 := Z.land (Z.shiftr init 16) 65535 in
  let (a, b) := adl bs (s1 mod ABASE) (s2 mod ABASE) in
  Z.lxor (Z.shiftl b 16) a.

(** THE DEFERRAL CONGRUENCE: reducing once at the end of a block gives the
    same answer as reducing after every byte.  This is what allows the
    NMAX blocking, and it is the only real content on the Adler side apart
    from the compiled modulo.  Proved by carrying both reductions through
    the fold. *)
Lemma adl_raw_mod : forall bs s1 s2,
  adl bs (s1 mod ABASE) (s2 mod ABASE)
  = (fst (adl_raw bs s1 s2) mod ABASE, snd (adl_raw bs s1 s2) mod ABASE).
Proof.
  induction bs as [|b bs IH]; intros s1 s2; cbn [adl adl_raw fst snd].
  - reflexivity.
  - replace ((s1 mod ABASE + b) mod ABASE) with ((s1 + b) mod ABASE)
      by (rewrite Zplus_mod_idemp_l; reflexivity).
    replace ((s2 mod ABASE + (s1 + b) mod ABASE) mod ABASE)
      with ((s2 + (s1 + b)) mod ABASE)
      by (rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; reflexivity).
    apply IH.
Qed.

(** CANONICALITY.  Both accumulators come out reduced, which is what lets a
    CHAIN of [adler32] calls satisfy the next call's precondition: zlib's
    [len == 1] shortcut does a single conditional subtract and is therefore
    only correct on a canonical incoming adler, so canonicality is a real
    precondition of the compiled code and not a modelling convenience.
    (That was found the hard way: the first version of the walk's
    postcondition was FALSE at [len = 1] for a non-canonical input.) *)
Lemma adl_canon : forall bs s1 s2,
  0 <= s1 < ABASE -> 0 <= s2 < ABASE ->
  0 <= fst (adl bs s1 s2) < ABASE /\ 0 <= snd (adl bs s1 s2) < ABASE.
Proof.
  induction bs as [|b bs IH]; intros s1 s2 H1 H2; cbn [adl fst snd].
  - split; assumption.
  - apply IH; apply Z.mod_pos_bound; unfold ABASE; lia.
Qed.

(* =========================================================================
   5.  The compiled modulo
   ========================================================================= *)

(** GCC turns [% 65521] into a 64-bit multiply-high, an add-shift
    correction, and a multiply-back by [65521 = (4095 << 4) + 1].  The
    constant is the one in the image at [adler32_z+0x20..0x48]:
    [0xf00e1 << 32 | 0xd2fc5cd]. *)
Definition AMAGIC : Z := 983265 * 4294967296 + 221234637.

Definition mulhu (x y : Z) : Z := (x * y) / 18446744073709551616.

(** The exact instruction sequence: [q = mulhu x M], then
    [t = q + (x - q) / 2], then [t >> 15], then [x - 65521 * that]. *)
Definition mdiv (x : Z) : Z :=
  let q := mulhu x AMAGIC in
  Z.shiftr (q + Z.shiftr (x - q) 1) 15.

Definition mrem (x : Z) : Z := x - ABASE * mdiv x.

(** The obligation the Adler walk consumes, stated here so the walk and the
    arithmetic are separable work.  Range: the deferred sums reach
    [65520 + 5552 * (65520 + 5552 * 255) < 2^34], so [2^40] is generous;
    the sequence is in fact valid for all 64-bit inputs. *)
Definition mdiv_correct_S : Prop :=
  forall x, 0 <= x < 1099511627776 -> mdiv x = x / ABASE.

Definition mrem_correct_S : Prop :=
  forall x, 0 <= x < 1099511627776 -> mrem x = x mod ABASE.

Lemma mrem_of_mdiv : mdiv_correct_S -> mrem_correct_S.
Proof.
  intros H x Hx. unfold mrem. rewrite (H x Hx).
  symmetry. apply Z.mod_eq. unfold ABASE. lia.
Qed.

(* =========================================================================
   6.  Non-vacuity probes
   ========================================================================= *)

(** The operator is not the identity and not constant, the CRC table's first
    two entries are zlib's, and the braid exponents are the measured ones.
    A definition that had drifted from the image would fail here rather than
    inside a walk. *)
Lemma probe_crc_tab_0 : crc_tab 0 = 0. Proof. reflexivity. Qed.
Lemma probe_crc_tab_1 : crc_tab 1 = 1996959894. Proof. vm_compute. reflexivity. Qed.
Lemma probe_crc_tab_255 : crc_tab 255 = 755167117. Proof. vm_compute. reflexivity. Qed.
Lemma probe_braid_0_1 : braid_tab 0 1 = 1701264198. Proof. vm_compute. reflexivity. Qed.
Lemma probe_braid_3_1 : braid_tab 3 1 = 2275855171. Proof. vm_compute. reflexivity. Qed.

(** An end-to-end value: zlib's [crc32(0, "123456789", 9) = 0xcbf43926]. *)
Definition CHECK_BYTES : list Z := [49;50;51;52;53;54;55;56;57].
Lemma probe_crc32_check : crc32_model 0 CHECK_BYTES = 3421780262.
Proof. vm_compute. reflexivity. Qed.

(** and Adler's: [adler32(1, "123456789", 9) = 0x091e01de]. *)
Lemma probe_adler32_check : adler32_model 1 CHECK_BYTES = 152961502.
Proof. vm_compute. reflexivity. Qed.
