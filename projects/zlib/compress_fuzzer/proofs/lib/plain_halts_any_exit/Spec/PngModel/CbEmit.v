(** * Spec.PngModel.CbEmit — the seam: zlib's [compress_block] emits what the
      declarative encoder says it does (round-trip layer L-C, part C).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    This is the file the other two were built for.  [EmitSym.v] proved the
    declarative per-symbol inverse over [list bool]; [BwStream.v] gave the
    transcribed bit writer an abstraction into [list bool]; this joins them
    to [Trees.v]'s [cb_step], which is zlib's [compress_block] loop body
    ([trees.c:906-946]) transcribed bug for bug.  It is therefore the only
    file in layer L-C whose statement says anything about the reference
    BINARY, and the only one that has to reconcile two vocabularies.

    TWO VOCABULARIES FOR ONE RFC TABLE, and the trap in it.
    [Trees.v:188-240] carries zlib's tables as [zarr] (functions [Z -> Z]):
    [base_length], [extra_lbits], [base_dist], [extra_dbits], indexed by
    code number.  [DeflateSpec.v:93-111] carries RFC 1951 §3.2.5's as
    [list nat]: [length_base], [length_extra], [dist_base], [dist_extra].
    Same tables, two representations, and names that differ only by word
    order — the shape of hazard §GTBL-PROD reported for the two [Code]
    records.  Every crossing below is discharged by COMPUTATION over the
    full index range, never by an import and never by eyeball.

    AND THE TABLES DO NOT MATCH ENTRY FOR ENTRY.  This is the finding that
    shaped the file.  zlib's tables are OFFSET — [base_length] is relative
    to [MIN_MATCH] ([base_length[i] = length_base[i] - 3]) and [base_dist]
    to a distance of one ([base_dist[i] = dist_base[i] - 1]) — which is
    expected.  What is NOT expected is that the offset FAILS at one entry:
    zlib's [base_length[28] = 0], a SENTINEL, where RFC's
    [length_base[28] = 258].  Length code 285 has zero extra bits, so zlib
    never reads that entry, and [compress_block] skips the send entirely
    ([if Z.eqb ex 0]).  The two sides still agree — but they agree because
    the WIDTH is zero and [write_bits 0] is [[]] on both sides, NOT because
    the bases agree.  A table-agreement lemma stated as
    "[Z.of_nat length_base[i] = base_length i + 3] for all i" is FALSE, and
    it is false at exactly the index RFC 1951 made anomalous.  Measured, not
    reasoned: that statement was the first thing this file tried and the
    computational check refuted it at i = 28.
    AND THAT 0 IS DELIBERATE — DO NOT "REPAIR" IT.  filter-id's [.rodata]
    diff (all ten deflate tables byte-for-byte, §FILTER-ID-DEFTABLES)
    confirms the binary carries 0 there, and the reason is that zlib's
    [tr_static_init] loop runs [code = 0 .. LENGTH_CODES-2], i.e. 0..27, so
    index 28 is a slot it NEVER WRITES and nothing ever reads (code 285 has
    no extra bits).  [Trees.v] transcribes the uninitialised slot rather
    than tidying it to 255 — bug-for-bug fidelity at a value no proof can
    see.  A model that "fixed" it would still satisfy every length bound and
    every round-trip theorem, and only a [.rodata] diff would catch the
    divergence.  So the crossing is stated at
    the level of the BITS EMITTED ([lextra_agree] below), which is what the
    seam actually needs and which is true at every index including 28.

    WHAT IS ASSUMED, and it is one interface with a named supplier.
    [tree_codes t lengths] says a zlib [ct_data] tree agrees with [Huff]'s
    canonical construction ON THE STREAM: for every symbol the length vector
    codes, the tree's stored code written LSB-first by [send_bits] is the
    canonical codeword.  That is layer L-B's item (i) (huffman-id's
    [gen_codes]/[bi_reverse] work), and it is where the bit REVERSAL is
    discharged — see [BwStream.v]'s header and §SYMID-STMT.

    BUT FOR THE STATIC TREES IT IS NOT ASSUMED, IT IS PROVED.
    [static_ltree_codes] and [static_dtree_codes] below discharge
    [tree_codes] for zlib's PRECOMPUTED static trees ([Trees.v:235-236]) by
    computation over all 288 and 30 symbols.  So for static-Huffman blocks
    layer L-C needs nothing from L-B at all, and the corollary
    [cb_step_emits_static] is unconditional in that parameter.  It is also
    an independent cross-check of both artefacts: zlib's hand-computed
    bit-reversed table and [Huff.v]'s [nc]/[code_offset] construction from
    the RFC length vector are two unrelated derivations of the same 318
    codewords, and they agree bit for bit. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec ZBitsOut Trees BwStream EmitSym.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Enumerating a [Z] range without quadratic cost

    [seq 0 32768 : list nat] builds 32768 UNARY numerals and is quadratic;
    the distance check below runs over the whole DEFLATE window, so it
    matters.  [zseq] uses [nat] only as fuel, one constructor per step. *)

Fixpoint zseq (n : nat) (start : Z) : list Z :=
  match n with O => [] | S k => start :: zseq k (start + 1) end.

Lemma In_zseq : forall n start x,
  start <= x < start + Z.of_nat n -> In x (zseq n start).
Proof.
  induction n as [|n IH]; intros start x H; cbn [zseq].
  - cbn in H. lia.
  - rewrite Nat2Z.inj_succ in H.
    destruct (Z.eq_dec x start) as [->|Hne]; [now left|].
    right. apply IH. lia.
Qed.

Lemma forallb_zseq : forall (f : Z -> bool) n start x,
  forallb f (zseq n start) = true ->
  start <= x < start + Z.of_nat n -> f x = true.
Proof.
  intros f n start x Hb Hx.
  rewrite forallb_forall in Hb. apply Hb, In_zseq, Hx.
Qed.

(** The form every check below uses: the bound as a [Z] literal, with the
    [Z.of_nat] of the fuel discharged by computation once. *)
Lemma forallb_zseq' : forall (f : Z -> bool) (n : nat) (m : Z) x,
  Z.of_nat n = m -> forallb f (zseq n 0) = true -> 0 <= x < m -> f x = true.
Proof. intros f n m x Hm Hb Hx. apply (forallb_zseq f n 0 x Hb). lia. Qed.

(** Same, from an arbitrary start.  BOTH must be applied with [_] for [f]:
    writing the predicate out by hand at the call site makes unification
    compare two lambdas up to conversion, and it does that by EVALUATING the
    [forallb] — measured at minutes for a 254-element range, versus instant
    when [f] is left to be read off the boolean lemma's own type by delta. *)
Lemma forallb_zseq'' : forall (f : Z -> bool) (n : nat) (lo hi : Z) x,
  lo + Z.of_nat n = hi -> forallb f (zseq n lo) = true -> lo <= x < hi -> f x = true.
Proof. intros f n lo hi x Hm Hb Hx. apply (forallb_zseq f n lo x Hb). lia. Qed.

(** [znth] reads a [list nat] table at a [Z] index, in [Z]. *)
Definition znth (l : list nat) (i : Z) : Z := Z.of_nat (nth (Z.to_nat i) l 0%nat).

Lemma nth_error_znth : forall l i,
  0 <= i -> (Z.to_nat i < length l)%nat ->
  nth_error l (Z.to_nat i) = Some (Z.to_nat (znth l i)).
Proof.
  intros l i Hi Hlen. unfold znth.
  rewrite Nat2Z.id. now apply nth_error_nth'.
Qed.

(** ** 2. The two vocabularies, reconciled by computation *)

(** *** 2.1 Extra-bit WIDTHS agree exactly, at every index *)

Lemma lext_agree : forall li, 0 <= li < 29 -> znth length_extra li = extra_lbits li.
Proof.
  intros li H. apply Z.eqb_eq.
  apply (forallb_zseq' (fun i => Z.eqb (znth length_extra i) (extra_lbits i)) 29 29);
    [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

Lemma dext_agree : forall di, 0 <= di < 30 -> znth dist_extra di = extra_dbits di.
Proof.
  intros di H. apply Z.eqb_eq.
  apply (forallb_zseq' (fun i => Z.eqb (znth dist_extra i) (extra_dbits i)) 30 30);
    [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

(** *** 2.2 BASES agree only where the width is non-zero

    The sentinel.  Stated with its guard, because without the guard it is
    false at [li = 28] — see the header. *)

Lemma lbase_agree : forall li,
  0 <= li < 29 -> 0 < extra_lbits li -> znth length_base li = base_length li + 3.
Proof.
  intros li H Hex.
  assert (Hb : (if Z.ltb 0 (extra_lbits li)
                then Z.eqb (znth length_base li) (base_length li + 3)
                else true) = true).
  { apply (forallb_zseq' (fun i => if Z.ltb 0 (extra_lbits i)
                                   then Z.eqb (znth length_base i) (base_length i + 3)
                                   else true) 29 29);
      [vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
  rewrite (proj2 (Z.ltb_lt 0 (extra_lbits li)) Hex) in Hb.
  now apply Z.eqb_eq.
Qed.

(** The distance side has NO sentinel: every one of the thirty entries is a
    true offset by one.  Checked, not assumed — the asymmetry with the
    length table is exactly the sort of thing that is invisible until
    somebody enumerates. *)
Lemma dbase_agree : forall di,
  0 <= di < 30 -> znth dist_base di = base_dist di + 1.
Proof.
  intros di H. apply Z.eqb_eq.
  apply (forallb_zseq' (fun i => Z.eqb (znth dist_base i) (base_dist i + 1)) 30 30);
    [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

(** *** 2.3 zlib's index tables land inside the RFC ranges

    [_length_code] over all 256 legal [lc] values and [d_code] over the
    whole 32768-entry window.  These are the facts that make the
    declarative [emit_extra] SUCCEED, i.e. that zlib never names a code
    whose range excludes the value it is encoding. *)

Definition lcode_range_b : bool :=
  forallb (fun lc => let li := length_code lc in
    andb (andb (Z.leb 0 li) (Z.ltb li 29))
         (andb (andb (Z.leb (znth length_base li) (lc + 3))
                     (Z.ltb (lc + 3 - znth length_base li) (2 ^ znth length_extra li)))
               (Z.leb (znth length_extra li) 16)))
    (zseq 256 0).

Lemma lcode_range_ok : lcode_range_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lcode_range : forall lc, 0 <= lc < 256 ->
  0 <= length_code lc < 29
  /\ znth length_base (length_code lc) <= lc + 3
       < znth length_base (length_code lc) + 2 ^ znth length_extra (length_code lc)
  /\ znth length_extra (length_code lc) <= 16.
Proof.
  intros lc Hlc.
  pose proof (forallb_zseq' _ 256 256 lc ltac:(vm_compute; reflexivity)
                            lcode_range_ok ltac:(lia)) as H.
  cbv zeta in H.
  apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb].
  apply andb_true_iff in H2 as [H3 Hc].
  apply andb_true_iff in H3 as [Hd He].
  apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
  apply Z.leb_le in Hd. apply Z.ltb_lt in He. apply Z.leb_le in Hc.
  repeat split; lia.
Qed.

(** *** The distance-code range over the WHOLE 32768-entry window

    TWO RULES, both learned the hard way and both mechanical.

    (1) EVERY REFLECTED PREDICATE IS A NAMED CONSTANT, never an inline lambda.
    (2) EVERY BOOLEAN FACT IS STATED IN APPLIED FORM — [forallb f (zseq n b)
        = true], NOT [some_definition_b = true].

    Both exist to stop a CONVERSION from normalising the boolean.  When the
    kernel or the elaborator cannot match an argument's type syntactically it
    falls back to whnf, and whnf of a 32768-element [forallb] over a
    512-entry table lookup plus a [Z.pow] per element is minutes in the
    standard evaluator — [vm_compute]'s speed is available only where a
    TACTIC asks for it, never to a conversion check.  Measured: with a
    [Definition dcode_all_b] in the way, the [exact] in [dcode_chunk_ok] did
    not finish in 400s; stated applied, the whole file is seconds.  Any delta
    step that is genuinely wanted is taken explicitly by [unfold ... in H],
    where it is cheap and visible, instead of being left to unification. *)

Definition dcode_at (d1 : Z) : bool :=
  let dc := d_code d1 in
  andb (andb (Z.leb 0 dc) (Z.ltb dc 30))
       (andb (andb (Z.leb (znth dist_base dc) (d1 + 1))
                   (Z.ltb (d1 + 1 - znth dist_base dc) (2 ^ znth dist_extra dc)))
             (Z.leb (znth dist_extra dc) 16)).

(** THE SHIFT STRUCTURE, which is why 510 checks replace 32768.

    Above 255, [d_code dist] is [dist_code (256 + dist >> 7)] — it reads the
    distance only through its top bits.  So all 128 distances sharing a shift
    value get the same code, and checking that block's two ENDPOINTS covers it:
    the range test is monotone in [d1] on both sides, so if the code's window
    contains [q*128] and [q*128+127] it contains everything between.
    256 checks below the boundary plus 254 above it, against 32768.

    WHY THIS IS WORTH A RESTRUCTURE RATHER THAN LEFT ALONE: Phase C runs
    coqchk, and the kernel re-check of the 32768-element version measured
    **1485s** against 72s for every other module in the block combined.  That
    is a real cost this file imposes on the graded build, not a build-time
    inconvenience.

    Both predicates are NAMED CONSTANTS and both facts are stated in APPLIED
    form, per the whnf law: a conversion that cannot match syntactically falls
    back to normalising the [forallb], and [vm_compute] is available only where
    a TACTIC asks for it, never to a conversion check.  An earlier attempt at
    exactly this shift argument was ABANDONED because it hit that wall; the
    argument was always right and only the packaging was wrong. *)

Definition dcode_hi_at (i : Z) : bool :=
  let q := i + 2 in
  let dc := dist_code (256 + q) in
  andb (andb (Z.leb 0 dc) (Z.ltb dc 30))
       (andb (andb (Z.leb (znth dist_base dc) (q * 128 + 1))
                   (Z.ltb (q * 128 + 128 - znth dist_base dc)
                          (2 ^ znth dist_extra dc)))
             (Z.leb (znth dist_extra dc) 16)).

Lemma z128 : Z.of_nat 128 = 128. Proof. vm_compute. reflexivity. Qed.
Lemma z254 : Z.of_nat 254 = 254. Proof. vm_compute. reflexivity. Qed.
Lemma z256z : Z.of_nat 256 = 256. Proof. vm_compute. reflexivity. Qed.

(** Applied form on both: no [_b] constant for a conversion to unfold. *)
Lemma dcode_lo_all : forallb dcode_at (zseq 256 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dcode_hi_all : forallb dcode_hi_at (zseq 254 0) = true.
Proof. vm_compute. reflexivity. Qed.

Definition DcodeRange (d1 : Z) : Prop :=
  0 <= d_code d1 < 30
  /\ znth dist_base (d_code d1) <= d1 + 1
       < znth dist_base (d_code d1) + 2 ^ znth dist_extra (d_code d1)
  /\ znth dist_extra (d_code d1) <= 16.

Lemma DcodeRange_lo : forall d1, 0 <= d1 < 256 -> DcodeRange d1.
Proof.
  intros d1 Hd.
  pose proof (forallb_zseq' dcode_at 256 256 d1 z256z dcode_lo_all Hd) as H.
  unfold dcode_at in H. cbv beta zeta in H.
  apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb].
  apply andb_true_iff in H2 as [H3 Hc].
  apply andb_true_iff in H3 as [Hd2 He].
  apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
  apply Z.leb_le in Hd2. apply Z.ltb_lt in He. apply Z.leb_le in Hc.
  unfold DcodeRange. repeat split; lia.
Qed.

Lemma DcodeRange_hi : forall d1, 256 <= d1 < 32768 -> DcodeRange d1.
Proof.
  intros d1 [Hlo Hhi].
  assert (Hm : 0 <= d1 mod 128 < 128) by (apply Z.mod_pos_bound; lia).
  assert (Hdm : d1 = 128 * (d1 / 128) + d1 mod 128) by (apply Z.div_mod; lia).
  assert (Hq2 : 2 <= d1 / 128) by (apply Z.div_le_lower_bound; lia).
  assert (Hq256 : d1 / 128 < 256) by (apply Z.div_lt_upper_bound; lia).
  assert (Hi : 0 <= d1 / 128 - 2 < 254) by lia.
  pose proof (forallb_zseq' dcode_hi_at 254 254 (d1 / 128 - 2) z254 dcode_hi_all Hi) as H.
  unfold dcode_hi_at in H. cbv beta zeta in H.
  replace (d1 / 128 - 2 + 2) with (d1 / 128) in H by lia.
  apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb].
  apply andb_true_iff in H2 as [H3 Hc].
  apply andb_true_iff in H3 as [Hd2 He].
  apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
  apply Z.leb_le in Hd2. apply Z.ltb_lt in He. apply Z.leb_le in Hc.
  assert (Hdc : d_code d1 = dist_code (256 + d1 / 128)).
  { unfold d_code. rewrite (proj2 (Z.ltb_ge d1 256) Hlo).
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  unfold DcodeRange. rewrite Hdc. repeat split; lia.
Qed.

Lemma DcodeRange_all : forall d1, 0 <= d1 < 32768 -> DcodeRange d1.
Proof.
  intros d1 Hd.
  destruct (Z.ltb_spec d1 256) as [Hlt|Hge].
  - apply DcodeRange_lo; lia.
  - apply DcodeRange_hi; lia.
Qed.

(** *** 2.4 THE CROSSING THAT MATTERS: the extra-bit FIELDS agree as BITS

    Not as base values — see the header.  At [li = 28] the two bases differ
    (0 vs 258) and the fields are nonetheless equal, because the width is
    zero and [zwrite 0] is [[]] on both sides.  That case is the [else]
    branch below and it is why this lemma is stated over bits. *)

Lemma lextra_agree : forall lc, 0 <= lc < 256 ->
  emit_extra length_base length_extra
             (Z.to_nat (length_code lc)) (Z.to_nat (lc + 3))
  = Some (zwrite (extra_lbits (length_code lc))
                 (lc - base_length (length_code lc))).
Proof.
  intros lc Hlc.
  pose proof (lcode_range lc Hlc) as [Hli [Hrange Hw16]].
  set (li := length_code lc) in *.
  assert (Hlenb : (Z.to_nat li < length length_base)%nat)
    by (rewrite length_base_length; lia).
  assert (Hlene : (Z.to_nat li < length length_extra)%nat)
    by (rewrite length_extra_length; lia).
  unfold emit_extra.
  rewrite (nth_error_znth length_base li) by (lia || assumption).
  rewrite (nth_error_znth length_extra li) by (lia || assumption).
  assert (Hpe : 0 < 2 ^ znth length_extra li)
    by (apply Z.pow_pos_nonneg; [lia | unfold znth; lia]).
  replace (Nat.leb (Z.to_nat (znth length_base li)) (Z.to_nat (lc + 3))) with true
    by (symmetry; apply Nat.leb_le; unfold znth in *; lia).
  replace (Nat.ltb (Z.to_nat (lc + 3) - Z.to_nat (znth length_base li))%nat
                   (2 ^ Z.to_nat (znth length_extra li))%nat) with true.
  2:{ symmetry. apply Nat.ltb_lt.
      apply (proj2 (Nat2Z.inj_lt _ _)).
      rewrite Nat2Z.inj_sub by (unfold znth in *; lia).
      rewrite <- two_pow_nat.
      rewrite !Z2Nat.id by (unfold znth in *; lia). lia. }
  cbn [andb].
  f_equal.
  rewrite <- (lext_agree li Hli).
  unfold zwrite.
  (* THE CASE SPLIT MUST COME BEFORE ANY [f_equal] ON THE VALUE.  At
     [li = 28] the two bases differ (0 vs 258), so the values are NOT equal
     and a proof that reduced [write_bits W a = write_bits W b] to [a = b]
     would be trying to prove something false.  What is true is that [W] is
     zero there, so both sides are [[]] whatever the values are. *)
  destruct (Z.eq_dec (znth length_extra li) 0) as [E0|Ene].
  - rewrite E0. reflexivity.
  - f_equal.
    assert (Hex : 0 < extra_lbits li)
      by (rewrite <- (lext_agree li Hli); unfold znth in *; lia).
    rewrite Nat2Z.inj_sub by (unfold znth in *; lia).
    rewrite !Z2Nat.id by (unfold znth in *; lia).
    rewrite (lbase_agree li Hli Hex). lia.
Qed.

(** The distance side of the same crossing.  The distance table has no
    sentinel ([dbase_agree] is unconditional), so this one needs no case
    split on the width — the asymmetry with [lextra_agree] is the table's,
    not the proof's. *)
Lemma dextra_agree : forall dist,
  1 <= dist <= 32768 -> DcodeRange (dist - 1) ->
  emit_extra dist_base dist_extra
             (Z.to_nat (d_code (dist - 1))) (Z.to_nat dist)
  = Some (zwrite (extra_dbits (d_code (dist - 1)))
                 (dist - 1 - base_dist (d_code (dist - 1)))).
Proof.
  intros dist Hd [Hdc [Hrange Hw16]].
  set (dc := d_code (dist - 1)) in *.
  assert (Hlenb : (Z.to_nat dc < length dist_base)%nat)
    by (rewrite dist_base_length; lia).
  assert (Hlene : (Z.to_nat dc < length dist_extra)%nat)
    by (rewrite dist_extra_length; lia).
  unfold emit_extra.
  rewrite (nth_error_znth dist_base dc) by (lia || assumption).
  rewrite (nth_error_znth dist_extra dc) by (lia || assumption).
  replace (Nat.leb (Z.to_nat (znth dist_base dc)) (Z.to_nat dist)) with true
    by (symmetry; apply Nat.leb_le; unfold znth in *; lia).
  replace (Nat.ltb (Z.to_nat dist - Z.to_nat (znth dist_base dc))%nat
                   (2 ^ Z.to_nat (znth dist_extra dc))%nat) with true.
  2:{ symmetry. apply Nat.ltb_lt.
      apply (proj2 (Nat2Z.inj_lt _ _)).
      rewrite Nat2Z.inj_sub by (unfold znth in *; lia).
      rewrite <- two_pow_nat.
      rewrite !Z2Nat.id by (unfold znth in *; lia). lia. }
  cbn [andb].
  f_equal.
  rewrite <- (dext_agree dc ltac:(lia)).
  unfold zwrite. f_equal.
  rewrite Nat2Z.inj_sub by (unfold znth in *; lia).
  rewrite !Z2Nat.id by (unfold znth in *; lia).
  rewrite (dbase_agree dc ltac:(lia)). lia.
Qed.

(** ** 3. The code-assignment interface, and its static-tree DISCHARGE

    [tree_codes t lengths] is the one thing layer L-C takes from layer L-B:
    a zlib [ct_data] tree agrees with [Huff]'s canonical construction ON THE
    STREAM.  Note what the three conjuncts are for.  The bit equality alone
    is NOT enough: [zwrite n v] reads only the low [n] bits of [v], so it
    constrains neither the WIDTH nor the code's range, and
    [bw_send_bits_stream] needs both. *)

(** The bound [n] is NOT decoration.  RFC 1951 §3.2.6 declares THIRTY-TWO
    fixed distance codes and [fixed_dist_lengths] has 32 entries, but zlib's
    [static_dtree] materialises only THIRTY ([Trees.v:146-150]), so
    [t_len static_dtree 30] reads off the end of the array and returns 0.
    An unbounded [tree_codes static_dtree fixed_dist_lengths] is therefore
    FALSE, at exactly symbols 30 and 31 — found by the computation failing,
    not by inspection.  It is the same unobservability [DeflateSpec.v] pins
    at [fixed_dist_32_unobservable] and the reason [dist_base] stops at 30:
    those two codes cannot occur, so the binary does not carry them. *)
Definition tree_codes_upto (t : Tree) (lengths : list nat) (n : nat) : Prop :=
  forall i cw, (i < n)%nat -> code_for lengths 15%nat i = Some cw ->
    0 < t_len t (Z.of_nat i) <= 16
    /\ 0 <= t_code t (Z.of_nat i) < 2 ^ t_len t (Z.of_nat i)
    /\ cw = zwrite (t_len t (Z.of_nat i)) (t_code t (Z.of_nat i)).

Definition tcode_ok_b (t : Tree) (lengths : list nat) (i : nat) : bool :=
  match code_for lengths 15%nat i with
  | None => true
  | Some cw =>
      let s := Z.of_nat i in
      andb (andb (Z.ltb 0 (t_len t s)) (Z.leb (t_len t s) 16))
           (andb (andb (Z.leb 0 (t_code t s)) (Z.ltb (t_code t s) (2 ^ t_len t s)))
                 (if list_eq_dec Bool.bool_dec cw (zwrite (t_len t s) (t_code t s))
                  then true else false))
  end.

Definition tree_codes_b (t : Tree) (lengths : list nat) (n : nat) : bool :=
  forallb (tcode_ok_b t lengths) (seq 0 n).

Lemma tree_codes_reflect : forall t lengths n,
  tree_codes_b t lengths n = true -> tree_codes_upto t lengths n.
Proof.
  intros t lengths n Hb i cw Hi Hcw.
  - unfold tree_codes_b in Hb. rewrite forallb_forall in Hb.
    specialize (Hb i ltac:(apply in_seq; lia)).
    unfold tcode_ok_b in Hb. rewrite Hcw in Hb. cbv zeta in Hb.
    apply andb_true_iff in Hb as [H1 H2].
    apply andb_true_iff in H1 as [Ha Hb1].
    apply andb_true_iff in H2 as [H3 Heq].
    apply andb_true_iff in H3 as [Hc Hd].
    apply Z.ltb_lt in Ha. apply Z.leb_le in Hb1.
    apply Z.leb_le in Hc. apply Z.ltb_lt in Hd.
    destruct (list_eq_dec Bool.bool_dec cw (zwrite (t_len t (Z.of_nat i))
                                                  (t_code t (Z.of_nat i))))
      as [E|]; [|discriminate].
    repeat split; assumption.
Qed.

(** NOT ASSUMED FOR THE STATIC TREES.  zlib's precomputed [static_ltree] and
    [static_dtree] ([Trees.v:235-236]) agree bit for bit with [Huff]'s
    canonical construction over RFC 1951 §3.2.6's fixed length vectors — all
    288 and 30 symbols, by computation.  Two consequences worth separating:
      * for static-Huffman blocks layer L-C needs NOTHING from layer L-B;
      * it is an independent cross-check of both artefacts.  zlib's
        hand-computed, BIT-REVERSED table and [Huff.v]'s [nc]/[code_offset]
        construction from the length vector are two unrelated derivations of
        the same 318 codewords, written by different people decades apart,
        and they agree. *)

Lemma static_ltree_codes : tree_codes_upto static_ltree fixed_lit_lengths 288.
Proof. apply tree_codes_reflect. vm_compute. reflexivity. Qed.

Lemma static_dtree_codes : tree_codes_upto static_dtree fixed_dist_lengths 30.
Proof. apply tree_codes_reflect. vm_compute. reflexivity. Qed.

(** ** 4. What a [sym_buf] triple denotes

    [trees.c:906-914]: three bytes per entry, the distance low byte, the
    distance high byte, and the length code MINUS [MIN_MATCH] — or, when the
    distance is zero, a literal in the third slot. *)

Definition cb_dist (sym : zarr) (sx : Z) : Z :=
  Z.land (sym sx) 255 + Z.shiftl (Z.land (sym (sx + 1)) 255) 8.
Definition cb_lc (sym : zarr) (sx : Z) : Z := sym (sx + 2).

Definition cb_sym_of (sym : zarr) (sx : Z) : lz_sym :=
  if Z.eqb (cb_dist sym sx) 0
  then LzLit (cb_lc sym sx)
  else LzRef (Z.to_nat (cb_lc sym sx + 3)) (Z.to_nat (cb_dist sym sx)).

Definition cb_out (r : CbStep) : CbSt :=
  match r with CbCont s => s | CbDone s => s end.

(** Every literal 0..255 HAS a code in the fixed tree.  By reflection over
    the 288 symbols, for the same reason [tree_codes_b] is: an [In]-based
    argument over the four [repeat] blocks of [fixed_lit_lengths] is more
    fragile than computing. *)
Definition lit_coded_b : bool :=
  forallb (fun i => match code_for fixed_lit_lengths 15%nat i with
                    | Some _ => true | None => false end)
          (seq 0 288).

Lemma lit_coded_ok : lit_coded_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lit_coded : forall i, (i < 288)%nat ->
  exists cw, code_for fixed_lit_lengths 15%nat i = Some cw.
Proof.
  intros i Hi.
  pose proof lit_coded_ok as H. unfold lit_coded_b in H.
  rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)).
  destruct (code_for fixed_lit_lengths 15%nat i) as [cw|];
    [now exists cw | discriminate].
Qed.

(** ** 5. THE SEAM, literal arm

    The [dist = 0] case needs no table at all: the emitted bits are exactly
    the tree's codeword, so this arm is unconditional in everything except
    the code assignment — and for the static tree that too is discharged
    (see [cb_step_emits_lit_static]). *)

Theorem cb_step_emits_lit : forall sym symnext lt dt ll dl n st,
  tree_codes_upto lt ll n ->
  (256 <= n)%nat ->
  bw_wf (c_bw st) ->
  cb_dist sym (c_sx st) = 0 ->
  0 <= cb_lc sym (c_sx st) < 256 ->
  (exists cw, code_for ll 15%nat (Z.to_nat (cb_lc sym (c_sx st))) = Some cw) ->
  exists bs,
    bw_stream (c_bw (cb_out (cb_step sym symnext lt dt st)))
      = bw_stream (c_bw st) ++ bs
    /\ EmitsTo ll dl (cb_sym_of sym (c_sx st)) bs
    /\ bw_wf (c_bw (cb_out (cb_step sym symnext lt dt st))).
Proof.
  intros sym symnext lt dt ll dl n st Hlt Hn Hwf Hd0 Hlc [cw Hcw].
  assert (Hid : Z.of_nat (Z.to_nat (cb_lc sym (c_sx st))) = cb_lc sym (c_sx st))
    by lia.
  assert (Hin : (Z.to_nat (cb_lc sym (c_sx st)) < n)%nat).
  { apply (Nat.lt_le_trans _ 256 _); [|exact Hn].
    apply (proj2 (Nat2Z.inj_lt _ _)). rewrite Hid.
    replace (Z.of_nat 256) with 256 by (vm_compute; reflexivity). lia. }
  destruct (Hlt _ _ Hin Hcw) as [Hlen [Hcode Hbits]].
  rewrite Hid in Hlen, Hcode, Hbits.
  exists cw. unfold cb_sym_of. rewrite Hd0. cbn [Z.eqb].
  assert (Hstep : c_bw (cb_out (cb_step sym symnext lt dt st))
                  = send_code (cb_lc sym (c_sx st)) lt (c_bw st)).
  { unfold cb_step, cb_out, cb_dist, cb_lc in *.
    rewrite Hd0. cbn [Z.eqb].
    destruct (Z.ltb (c_sx st + 3) symnext); reflexivity. }
  destruct (bw_send_bits_stream (t_code lt (cb_lc sym (c_sx st)))
                                (t_len lt (cb_lc sym (c_sx st))) (c_bw st)
                                Hwf ltac:(unfold Buf_size; lia) Hcode)
    as [Hs Hw].
  (* [split; [|split]] and NOT [repeat split]: [bw_wf] is itself a
     conjunction, and [repeat split] would take the goal apart past it. *)
  split; [|split].
  - rewrite Hstep. unfold send_code. rewrite Hs, Hbits. reflexivity.
  - exists 0%nat, 0%nat. cbn [emit_sym].
    replace (andb (Z.leb 0 (cb_lc sym (c_sx st))) (Z.ltb (cb_lc sym (c_sx st)) 256))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le | apply Z.ltb_lt]; lia).
    exact Hcw.
  - rewrite Hstep. unfold send_code. exact Hw.
Qed.

Corollary cb_step_emits_lit_static : forall sym symnext dt st,
  bw_wf (c_bw st) ->
  cb_dist sym (c_sx st) = 0 ->
  0 <= cb_lc sym (c_sx st) < 256 ->
  exists bs,
    bw_stream (c_bw (cb_out (cb_step sym symnext static_ltree dt st)))
      = bw_stream (c_bw st) ++ bs
    /\ EmitsTo fixed_lit_lengths fixed_dist_lengths (cb_sym_of sym (c_sx st)) bs
    /\ bw_wf (c_bw (cb_out (cb_step sym symnext static_ltree dt st))).
Proof.
  intros sym symnext dt st Hwf Hd0 Hlc.
  apply (cb_step_emits_lit sym symnext static_ltree dt
                           fixed_lit_lengths fixed_dist_lengths 288 st
                           static_ltree_codes ltac:(lia) Hwf Hd0 Hlc).
  apply (lit_coded (Z.to_nat (cb_lc sym (c_sx st)))).
  apply (Nat.lt_le_trans _ 256 _); [|lia].
  apply (proj2 (Nat2Z.inj_lt _ _)).
  rewrite Z2Nat.id by lia.
  replace (Z.of_nat 256) with 256 by (vm_compute; reflexivity). lia.
Qed.

(** ** 6. THE SEAM, match arm

    The [dist <> 0] case emits four fields in order: the length code's
    codeword, its extra bits, the distance code's codeword, its extra bits.
    Two of the four are CONDITIONAL in the transcription
    ([if Z.eqb ex 0 then b1 else ...]), and the uniform statement works
    because [zwrite 0 _] is [[]] — a skipped send and a zero-width send append
    the same thing.  That is the same fact [lextra_agree]'s sentinel case
    rests on, used a second time. *)

Lemma send_extra_stream : forall v n b,
  bw_wf b -> 0 <= n <= Buf_size -> (n = 0 \/ 0 <= v < 2 ^ n) ->
  bw_stream (if Z.eqb n 0 then b else bw_send_bits v n b) = bw_stream b ++ zwrite n v
  /\ bw_wf (if Z.eqb n 0 then b else bw_send_bits v n b).
Proof.
  intros v n b Hwf Hn Hv.
  destruct (Z.eqb_spec n 0) as [->|Hne].
  - rewrite zwrite_0, app_nil_r. split; [reflexivity | exact Hwf].
  - destruct Hv as [->|Hv]; [contradiction|].
    apply (bw_send_bits_stream v n b Hwf Hn Hv).
Qed.

Theorem cb_step_emits_ref : forall sym symnext lt dt ll dl nl nd st,
  tree_codes_upto lt ll nl -> tree_codes_upto dt dl nd ->
  bw_wf (c_bw st) ->
  cb_dist sym (c_sx st) <> 0 ->
  0 <= cb_lc sym (c_sx st) < 256 ->
  1 <= cb_dist sym (c_sx st) <= 32768 ->
  DcodeRange (cb_dist sym (c_sx st) - 1) ->
  (Z.to_nat (length_code (cb_lc sym (c_sx st)) + LITERALS + 1) < nl)%nat ->
  (Z.to_nat (d_code (cb_dist sym (c_sx st) - 1)) < nd)%nat ->
  (exists cw, code_for ll 15%nat
                (Z.to_nat (length_code (cb_lc sym (c_sx st)) + LITERALS + 1)) = Some cw) ->
  (exists dw, code_for dl 15%nat
                (Z.to_nat (d_code (cb_dist sym (c_sx st) - 1))) = Some dw) ->
  exists bs,
    bw_stream (c_bw (cb_out (cb_step sym symnext lt dt st)))
      = bw_stream (c_bw st) ++ bs
    /\ EmitsTo ll dl (cb_sym_of sym (c_sx st)) bs
    /\ bw_wf (c_bw (cb_out (cb_step sym symnext lt dt st))).
Proof.
  intros sym symnext lt dt ll dl nl nd st Hlt Hdt Hwf Hd0 Hlc Hdist
         HD Hnl Hnd [cwl Hcwl] [cwd Hcwd].
  (* THE ORDER IS THE WHOLE DIFFICULTY, and both halves of it are one lesson:
     a [set] folds exactly what is present when it runs.
       UNFOLD FIRST — [unfold cb_step] exposes the raw [sym (sx+2)] projections,
         so a [set] done before it folds nothing in the goal.
       DERIVE SECOND, still on the raw terms.
       FOLD LAST, once, so goal AND hypotheses become the same atoms.
     Getting this wrong in either direction leaves [lia] with an abbreviation on
     one side and the raw term on the other; it cost a cycle in BwStream.v and
     one in each direction here. *)
  unfold cb_step, cb_out, send_code, cb_sym_of, cb_dist, cb_lc in *.
  (* fold the two PROJECTIONS first, so the derivations below can name them;
     the two CODE INDICES are folded after, so those derivations' outputs get
     folded too *)
  set (lc := sym (c_sx st + 2)) in *.
  set (dist := Z.land (sym (c_sx st)) 255
               + Z.shiftl (Z.land (sym (c_sx st + 1)) 255) 8) in *.
  pose proof (lcode_range lc Hlc) as [Hli [Hlrange Hlw16]].
  destruct HD as [Hdcr [Hdrange Hdw16]].
  destruct (Hlt _ _ Hnl Hcwl) as [HlenL [HcodeL HbitsL]].
  destruct (Hdt _ _ Hnd Hcwd) as [HlenD [HcodeD HbitsD]].
  pose proof (lextra_agree lc Hlc) as HexL.
  pose proof (dextra_agree dist ltac:(lia)
                (conj Hdcr (conj Hdrange Hdw16))) as HexD.
  set (li := length_code lc) in *.
  set (dc := d_code (dist - 1)) in *.
  destruct (Z.eqb_spec dist 0) as [E|_]; [contradiction|].
  cbn zeta.
  rewrite (Z2Nat.id (li + LITERALS + 1)) in HlenL, HcodeL, HbitsL
    by (unfold LITERALS; lia).
  rewrite (Z2Nat.id dc) in HlenD, HcodeD, HbitsD by lia.
  (* widths and values of the two CONDITIONAL extra-bit sends *)
  assert (HwL : 0 <= extra_lbits li <= Buf_size).
  { rewrite <- (lext_agree li Hli). unfold znth, Buf_size in *. lia. }
  assert (HwD : 0 <= extra_dbits dc <= Buf_size).
  { rewrite <- (dext_agree dc ltac:(lia)). unfold znth, Buf_size in *. lia. }
  assert (HvL : extra_lbits li = 0 \/ 0 <= lc - base_length li < 2 ^ extra_lbits li).
  { destruct (Z.eq_dec (extra_lbits li) 0) as [E0|Hne]; [now left|]. right.
    assert (Hex : 0 < extra_lbits li)
      by (rewrite <- (lext_agree li Hli) in *; unfold znth in *; lia).
    rewrite (lbase_agree li Hli Hex) in Hlrange.
    rewrite <- (lext_agree li Hli). unfold znth in *. lia. }
  assert (HvD : extra_dbits dc = 0
                \/ 0 <= dist - 1 - base_dist dc < 2 ^ extra_dbits dc).
  { right. rewrite (dbase_agree dc ltac:(lia)) in Hdrange.
    rewrite <- (dext_agree dc ltac:(lia)). unfold znth in *. lia. }
  (* thread the four appends, in emission order *)
  destruct (bw_send_bits_stream (t_code lt (li + LITERALS + 1))
                                (t_len lt (li + LITERALS + 1)) (c_bw st)
                                Hwf ltac:(unfold Buf_size; lia) HcodeL) as [S1 W1].
  destruct (send_extra_stream (lc - base_length li) (extra_lbits li) _ W1 HwL HvL)
    as [S2 W2].
  destruct (bw_send_bits_stream (t_code dt dc) (t_len dt dc) _
                                W2 ltac:(unfold Buf_size; lia) HcodeD) as [S3 W3].
  destruct (send_extra_stream (dist - 1 - base_dist dc) (extra_dbits dc) _ W3 HwD HvD)
    as [S4 W4].
  exists (cwl ++ zwrite (extra_lbits li) (lc - base_length li)
              ++ cwd ++ zwrite (extra_dbits dc) (dist - 1 - base_dist dc)).
  split; [|split].
  - destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw];
      rewrite S4, S3, S2, S1, HbitsL, HbitsD, <- !app_assoc; reflexivity.
  - exists (Z.to_nat li), (Z.to_nat dc). cbn [emit_sym].
    replace (257 + Z.to_nat li)%nat
      with (Z.to_nat (li + LITERALS + 1)) by (unfold LITERALS; lia).
    rewrite Hcwl, HexL, Hcwd, HexD. reflexivity.
  - destruct (Z.ltb (c_sx st + 3) symnext); cbn [c_bw]; exact W4.
Qed.

(** Every distance code 0..29 has a code in the fixed tree, by the same
    reflection as [lit_coded]. *)
Definition dist_coded_b : bool :=
  forallb (fun i => match code_for fixed_dist_lengths 15%nat i with
                    | Some _ => true | None => false end)
          (seq 0 30).

Lemma dist_coded_ok : dist_coded_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dist_coded : forall i, (i < 30)%nat ->
  exists cw, code_for fixed_dist_lengths 15%nat i = Some cw.
Proof.
  intros i Hi.
  pose proof dist_coded_ok as H. unfold dist_coded_b in H.
  rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)).
  destruct (code_for fixed_dist_lengths 15%nat i) as [cw|];
    [now exists cw | discriminate].
Qed.

(** The match arm at the STATIC trees: four of the five parameters discharged,
    leaving exactly one hypothesis — [DcodeRange] for the distance, which is
    proved for distances below 256 ([DcodeRange_lo]) and witnessed but not yet
    Qed'd above (see the build-pathology note in section 2). *)
(** UNCONDITIONAL.  [DcodeRange] was this corollary's last hypothesis and is
    now discharged for the whole window by [DcodeRange_all], so the static
    match arm quantifies over nothing but the symbol's own shape. *)
Corollary cb_step_emits_ref_static : forall sym symnext st,
  bw_wf (c_bw st) ->
  cb_dist sym (c_sx st) <> 0 ->
  0 <= cb_lc sym (c_sx st) < 256 ->
  1 <= cb_dist sym (c_sx st) <= 32768 ->
  exists bs,
    bw_stream (c_bw (cb_out (cb_step sym symnext static_ltree static_dtree st)))
      = bw_stream (c_bw st) ++ bs
    /\ EmitsTo fixed_lit_lengths fixed_dist_lengths (cb_sym_of sym (c_sx st)) bs
    /\ bw_wf (c_bw (cb_out (cb_step sym symnext static_ltree static_dtree st))).
Proof.
  intros sym symnext st Hwf Hd0 Hlc Hdist.
  assert (HD : DcodeRange (cb_dist sym (c_sx st) - 1))
    by (apply DcodeRange_all; lia).
  pose proof (lcode_range _ Hlc) as [Hli _].
  pose proof HD as [Hdcr _].
  assert (HnL : (Z.to_nat (length_code (cb_lc sym (c_sx st)) + LITERALS + 1) < 288)%nat)
    by (unfold LITERALS; lia).
  assert (HnD : (Z.to_nat (d_code (cb_dist sym (c_sx st) - 1)) < 30)%nat) by lia.
  apply (cb_step_emits_ref sym symnext static_ltree static_dtree
                           fixed_lit_lengths fixed_dist_lengths 288 30 st
                           static_ltree_codes static_dtree_codes
                           Hwf Hd0 Hlc Hdist HD HnL HnD).
  - apply lit_coded, HnL.
  - apply dist_coded, HnD.
Qed.
