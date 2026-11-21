(** * HuffMaxBits — the [maxBits] argument is irrelevant where it is not binding,
      so L-B's theorems apply to the CODE-LENGTH tree at [maxBits = 7].

    OWNER: huffman-id (claim §HUFFID).

    RENAMED from MaxBits.v per TL's §TL-ACK-TRACE19 directive: wp4w8's maxbits
    lane has a DIFFERENT MaxBits.v (md5 , 34 Qed) and a splice cannot
    take both names.  The two files COMPLEMENT rather than overlap — see the
    note below — so both survive, under distinct names.

    OVERLAP STATEMENT (owed to TL).  wp4w8/maxbits/MaxBits.v bounds the INFLATE
    decode table's [c_bits] FIELD (Inftrees.TblBitsPos, [bits_ok], the fixed
    tables checked by forallb over seq 0 512 / seq 0 32, and the
    InflateFast.if_drop underflow that makes 15 rather than 16 the largest sound
    bound).  THIS file bounds nothing: it proves the [maxBits] ARGUMENT of
    Huff.code_for / Huff.code_table is IRRELEVANT where it is not binding, so the
    L-B encode-side theorems apply at the code-length tree's own bound of 7.
    Zero shared statements; different sides of the codec (their decode table vs
    my declarative encode layer); they meet only at the shared constant 15, which
    is exactly why the names collided.  NEITHER SUBSUMES THE OTHER.

    WHY THIS IS NEEDED, and it is not cosmetic.  L-B's theorems conclude about
    [code_table L 15].  But DEFLATE's third tree — the CODE-LENGTH tree that
    carries the RLE'd length stream — has [MAX_BL_BITS = 7]
    ([Trees.v:85], [sd_max_length TK_BL]), and the decoder reads it with
    [hdecode (code_table cl 7)] ([DeflateSpec.v:773]).  15 and 7 are different
    tables in general, and Huff.v is emphatic that the argument is load bearing
    ([maxbits_matters_9] / [maxbits_matters_7] pin exactly that): a silent
    15-for-7 would let an oversubscribed code-length tree validate.

    So composing L-B with the code-length stream needs a THEOREM that the two
    tables coincide on the range where neither bound binds — not an assumption
    that [maxBits] does not matter.  That theorem is
    [code_table_maxbits_irrel], and it carries the hypothesis that makes it
    true (every length at most BOTH bounds) rather than dropping it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Bits Huff Trees ZBitsBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** ** [code_for] does not read [maxBits] where it is not binding *)

Lemma code_for_maxbits_irrel : forall L m1 m2 sym,
  (forall len, In len L -> (len <= m1)%nat) ->
  (forall len, In len L -> (len <= m2)%nat) ->
  code_for L m1 sym = code_for L m2 sym.
Proof.
  intros L m1 m2 sym H1 H2. unfold code_for.
  destruct (nth_error L sym) as [len|] eqn:E; [|reflexivity].
  assert (Hin : In len L) by (eapply nth_error_In; exact E).
  destruct (Nat.eqb len 0) eqn:E0; [reflexivity|].
  assert (Hm1 : (m1 <? len)%nat = false) by (apply Nat.ltb_ge, H1, Hin).
  assert (Hm2 : (m2 <? len)%nat = false) by (apply Nat.ltb_ge, H2, Hin).
  rewrite Hm1, Hm2. reflexivity.
Qed.

Lemma fold_code_entry_irrel : forall L m1 m2 l,
  (forall sym, code_for L m1 sym = code_for L m2 sym) ->
  fold_right (code_entry L m1) [] l = fold_right (code_entry L m2) [] l.
Proof.
  intros L m1 m2 l H. induction l as [|a l IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH. unfold code_entry. rewrite H. reflexivity.
Qed.

Lemma all_codes_maxbits_irrel : forall L m1 m2,
  (forall len, In len L -> (len <= m1)%nat) ->
  (forall len, In len L -> (len <= m2)%nat) ->
  all_codes L m1 = all_codes L m2.
Proof.
  intros L m1 m2 H1 H2. unfold all_codes.
  apply fold_code_entry_irrel. intro sym.
  apply code_for_maxbits_irrel; assumption.
Qed.

Theorem code_table_maxbits_irrel : forall L m1 m2,
  (forall len, In len L -> (len <= m1)%nat) ->
  (forall len, In len L -> (len <= m2)%nat) ->
  code_table L m1 = code_table L m2.
Proof.
  intros L m1 m2 H1 H2. unfold code_table.
  f_equal. apply all_codes_maxbits_irrel; assumption.
Qed.

(** ** Kraft transfers upward

    [ValidLengths L 7] implies [ValidLengths L 15]: every leaf weight scales by
    the same [2^(m2-m1)], so the sum scales and the bound scales with it.  This
    is what lets a caller who checked Kraft at 7 (the code-length tree's real
    bound) discharge L-B's [ValidLengths L 15] hypothesis. *)

Lemma hid_kraft_at_scale : forall L m1 m2 b len,
  In len L -> (forall x, In x L -> (x <= m1)%nat) -> (m1 <= m2)%nat ->
  kraft_at m2 b len = (2 ^ (m2 - m1) * kraft_at m1 b len)%nat.
Proof.
  intros L m1 m2 b len Hin Hb Hm.
  specialize (Hb len Hin).
  unfold kraft_at. destruct (Nat.leb b len) eqn:E; [|lia].
  unfold kraft_term. destruct len as [|len']; [lia|].
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

Lemma kraft_sum_from_scale : forall L m1 m2 b,
  (forall x, In x L -> (x <= m1)%nat) -> (m1 <= m2)%nat ->
  kraft_sum_from L m2 b = (2 ^ (m2 - m1) * kraft_sum_from L m1 b)%nat.
Proof.
  intros L m1 m2 b Hb Hm.
  (* Peel with Huff's own [kraft_sum_from_cons] rather than unfolding to
     [list_sum (map ...)]: [cbn [list_sum]] rewrites [list_sum] into
     [fold_right] and then the induction hypothesis no longer matches the
     goal, which is the same cbn-reshapes-the-goal trap as [firstn]. *)
  induction L as [|a L IH]; [rewrite !kraft_sum_from_nil; lia|].
  rewrite !kraft_sum_from_cons.
  rewrite (hid_kraft_at_scale (a :: L) m1 m2 b a)
    by (try (left; reflexivity); assumption).
  rewrite IH by (intros x Hx; apply Hb; right; exact Hx).
  lia.
Qed.

Theorem ValidLengths_mono : forall L m1 m2,
  (m1 <= m2)%nat -> ValidLengths L m1 -> ValidLengths L m2.
Proof.
  intros L m1 m2 Hm [Hb Hk]. split.
  - intros len Hin. specialize (Hb len Hin). lia.
  - unfold kraft_sum in *.
    rewrite (kraft_sum_from_scale L m1 m2 0 Hb Hm).
    assert (Hp : (2 ^ (m2 - m1) * 2 ^ m1 = 2 ^ m2)%nat)
      by (rewrite <- Nat.pow_add_r; f_equal; lia).
    pose proof (two_pow_pos (m2 - m1)) as Hpos.   (* Huff.v's own *)
    nia.
Qed.

(** ** L-B at the code-length tree's own bound

    The same theorem as [gen_codes_decode_of_encode], but with the DECODE table
    read at [maxBits = mb] — so a caller decoding with [code_table cl 7], as
    [DeflateSpec.read_lengths] does, can use it directly. *)
Theorem gen_codes_decode_of_encode_at : forall L t maxc blc sym cw rest mb,
  LensOf t L -> BlcOf blc L -> ValidLengths L mb ->
  (mb <= 15)%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  code_for L mb sym = Some cw ->
  hdecode (code_table L mb)
          (write_bits (Z.to_nat (t_len (gen_codes t maxc blc) (Z.of_nat sym)))
                      (t_code (gen_codes t maxc blc) (Z.of_nat sym)) ++ rest)
  = Some (sym, rest).
Proof.
  intros L t maxc blc sym cw rest mb Hlens Hblc HV Hmb Hab Hmc Hcf.
  assert (HV15 : ValidLengths L 15%nat) by (apply (ValidLengths_mono L mb 15%nat Hmb HV)).
  assert (Hb : forall len, In len L -> (len <= mb)%nat) by apply (proj1 HV).
  assert (Hb15 : forall len, In len L -> (len <= 15)%nat) by apply (proj1 HV15).
  assert (Hcf15 : code_for L 15%nat sym = Some cw).
  { rewrite (code_for_maxbits_irrel L 15%nat mb sym Hb15 Hb). exact Hcf. }
  rewrite (code_table_maxbits_irrel L mb 15%nat Hb Hb15).
  apply (gen_codes_decode_of_encode L t maxc blc sym cw rest
           Hlens Hblc HV15 Hab Hmc Hcf15).
Qed.

(** ** Non-vacuity at 7, and the guard is real

    A code-length tree really does have lengths at most 7, and Huff.v's warning
    that the argument is load bearing is confirmed here rather than taken on
    trust: an oversubscribed-at-7 code is REJECTED at 7 and ACCEPTED at 15, so
    [code_table_maxbits_irrel]'s hypothesis cannot be dropped. *)

Definition Lbl : list nat := [3;3;3;3;2;0;0;3]%nat.   (* a plausible bl_tree *)
Definition tbl : Tree := mkTree zzero (zlist [3;3;3;3;2;0;0;3]).
Definition blcbl : zarr := zlist [0;0;1;5].

Lemma bl_LensOf : LensOf tbl Lbl.
Proof.
  intros k Hk. cbn [length Lbl] in Hk.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity. lia.
Qed.

Lemma bl_BlcOf : BlcOf blcbl Lbl.
Proof.
  apply BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try reflexivity. lia.
Qed.

Lemma bl_ValidLengths7 : ValidLengths Lbl 7%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

Lemma bl_AbsentBeyond : AbsentBeyond Lbl 7.
Proof. intros k Hk. apply nth_overflow. cbn [length Lbl]. lia. Qed.

Example bl_code_for_4 : code_for Lbl 7%nat 4%nat = Some [false;false].
Proof. vm_compute. reflexivity. Qed.

(** The code-length tree round-trips through the table the DECODER actually
    builds, [code_table cl 7]. *)
Theorem bl_roundtrip_4 : forall rest,
  hdecode (code_table Lbl 7%nat)
          (write_bits (Z.to_nat (t_len (gen_codes tbl 7 blcbl) (Z.of_nat 4%nat)))
                      (t_code (gen_codes tbl 7 blcbl) (Z.of_nat 4%nat)) ++ rest)
  = Some (4%nat, rest).
Proof.
  intro rest.
  apply (gen_codes_decode_of_encode_at Lbl tbl 7 blcbl 4%nat [false;false] rest 7%nat
           bl_LensOf bl_BlcOf bl_ValidLengths7).
  - lia.
  - exact bl_AbsentBeyond.
  - lia.
  - exact bl_code_for_4.
Qed.

(** THE HYPOTHESIS IS NOT DECORATION.  [Lwide] is two 9-bit codes: valid at
    [maxBits = 15] and INVALID at 7, because 9 exceeds the length bound.  It is
    exactly a code for which the two tables differ, so it witnesses that
    [code_table_maxbits_irrel]'s "every length at most both bounds" cannot be
    dropped — which is the concrete form of Huff.v's warning that a silent
    15-for-7 would let an oversubscribed code-length tree validate. *)
Definition Lwide : list nat := [9;9]%nat.

Example Lwide_rejected_at_7 : valid_lengths_b Lwide 7%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example Lwide_accepted_at_15 : valid_lengths_b Lwide 15%nat = true.
Proof. vm_compute. reflexivity. Qed.

(** ...and the two tables genuinely DIFFER there, so
    [code_table_maxbits_irrel]'s hypothesis is load bearing and not a
    formality: at 7 every symbol is out of range and the table is EMPTY. *)
Example Lwide_tables_differ : code_table Lwide 7%nat <> code_table Lwide 15%nat.
Proof. vm_compute. discriminate. Qed.

Print Assumptions code_table_maxbits_irrel.
Print Assumptions ValidLengths_mono.
Print Assumptions gen_codes_decode_of_encode_at.
Print Assumptions bl_roundtrip_4.
