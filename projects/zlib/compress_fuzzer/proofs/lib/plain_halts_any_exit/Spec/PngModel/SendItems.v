(** * SendItems — the four layers chained: what zlib's writer EMITS for a
      code-length item stream decodes back to the code lengths.

    OWNER: huffman-id, claim §HUFFID-EMIT.  The release condition of
    §HUFFID-BRIDGE extends here verbatim if symbol-id reads [send_code_bits] as
    L-C's.

    WHAT THIS ADDS.  The four earlier files each end at a different vocabulary:

      HuffGenCodes.v  gen_codes' stored code, as a [write_bits] bit list
      HuffMaxBits.v   ...at the code-length tree's own bound, 7 rather than 15
      ClStream.v      the RLE'd item stream, as a bit list, decoded by
                      DeflateSpec.read_lengths
      BwStream.v      the writer's stream, as a bit list

    Separately they are four results; chained they are one.  This file does the
    chaining, and the top theorem is the one a reader should look at:

      read_lengths cl (length (cl_lens items))
        (bw_stream (emit_items (gen_codes t maxc blc) items bw_init) ++ rest)
      = Some (cl_lens items, rest)

    i.e. run zlib's own bit writer over the item stream through a tree built by
    zlib's own gen_codes, and the inflate side's own length reader gives back
    exactly the lengths the items denote, remainder untouched.

    THE HONEST BOUNDARY, and it is the whole remaining gap.  [emit_item] below
    is [send_go]'s EMISSION, lifted verbatim out of [Trees.v:770-780] — the four
    expressions are copied, not paraphrased.  What is NOT here is [send_go]'s
    CONTROL FLOW: which items its prevlen/nextlen/count/maxcnt/mincnt state
    machine chooses for a given tree.  So this file closes the "what do the
    emitted bits mean" half of (iii-b) and leaves the "which items get emitted"
    half open.  Anyone reading this as [send_tree] being verified would be
    wrong, and the gap is named rather than blurred. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes HuffMaxBits ClStream.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** BwBits -> BwStream migration shims

    [BwBits.v] is RETIRED (§TL-RULINGS-SYMBACK, on my own recommendation) and
    [BwStream.v] is the campaign's seam artifact — now LIVE in the spec tree, so
    this lane depends on the shared one rather than on a private duplicate.

    The two are CONVERTIBLE, not merely equivalent, which is why the migration is
    a rename and not a re-proof:
      [bw_bits  b = bytes_bits (bw_out b) ++ write_bits (Z.to_nat (bw_valid b)) (bw_buf b)]
      [bw_stream b = bytes_bits (bw_out b) ++ zwrite            (bw_valid b)  (bw_buf b)]
    with [zwrite n v := write_bits (Z.to_nat n) v]; and [BWInv]/[bw_wf] differ
    only by [Buf_size] versus its value 16.

    These two shims exist for ONE reason: BwStream packages the stream law and
    the invariant as a single conjunction where I had two separate lemmas.  Every
    proof script below is therefore untouched by the migration. *)
Lemma bw_send_bits_bits : forall v n b,
  bw_wf b -> 0 <= n <= 16 -> 0 <= v < 2 ^ n ->
  bw_stream (bw_send_bits v n b) = bw_stream b ++ write_bits (Z.to_nat n) v.
Proof. intros v n b H Hn Hv. exact (proj1 (bw_send_bits_stream v n b H Hn Hv)). Qed.

Lemma bw_send_bits_inv : forall v n b,
  bw_wf b -> 0 <= n <= 16 -> 0 <= v < 2 ^ n ->
  bw_wf (bw_send_bits v n b).
Proof. intros v n b H Hn Hv. exact (proj2 (bw_send_bits_stream v n b H Hn Hv)). Qed.

(** ** The stored code fits in its own width

    [BwStream]'s law needs [0 <= v < 2^n] for the value being sent.  For a code
    out of [gen_codes] that is not an extra hypothesis: the stored value is a
    REVERSAL of a value below [2^len], so it is itself below [2^len]. *)
Lemma gen_codes_code_lt : forall L t maxc blc sym len,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  nth_error L sym = Some len -> (1 <= len <= 15)%nat ->
  0 <= t_code (gen_codes t maxc blc) (Z.of_nat sym) < 2 ^ Z.of_nat len.
Proof.
  intros L t maxc blc sym len Hlens Hblc HV Hab Hmc He Hl.
  rewrite (gen_codes_stored_value L t maxc blc sym len Hlens Hblc HV Hab Hmc He
             (proj1 Hl)).
  rewrite bi_reverse_zrev by lia.
  rewrite Nat2Z.id.
  pose proof (zrev_bound len (Z.of_nat (nc L len + code_offset L sym len))) as H.
  exact H.
Qed.

(** ** Sending one symbol appends its canonical codeword

    This is the join of [HuffGenCodes] (what the stored pair IS) with [BwStream]
    (what the writer DOES with a pair).  [mb] is the tree's own bound, so a
    caller with the code-length tree passes 7. *)
Theorem send_code_bits : forall cl t maxc blc sym cw b mb,
  LensOf t cl -> BlcOf blc cl -> ValidLengths cl mb -> (mb <= 15)%nat ->
  AbsentBeyond cl maxc -> -1 <= maxc <= 288 ->
  code_for cl mb sym = Some cw ->
  bw_wf b ->
  bw_stream (send_code (Z.of_nat sym) (gen_codes t maxc blc) b)
    = bw_stream b ++ cw
  /\ bw_wf (send_code (Z.of_nat sym) (gen_codes t maxc blc) b).
Proof.
  intros cl t maxc blc sym cw b mb Hlens Hblc HV Hmb Hab Hmc Hcf Hinv.
  assert (HV15 : ValidLengths cl 15%nat) by (apply (ValidLengths_mono cl mb 15%nat Hmb HV)).
  assert (Hb : forall len, In len cl -> (len <= mb)%nat) by apply (proj1 HV).
  assert (Hb15 : forall len, In len cl -> (len <= 15)%nat) by apply (proj1 HV15).
  assert (Hcf15 : code_for cl 15%nat sym = Some cw)
    by (rewrite (code_for_maxbits_irrel cl 15%nat mb sym Hb15 Hb); exact Hcf).
  (* the width and value of the pair the writer is handed *)
  apply code_for_inv in Hcf15 as [len [He [Hl1 [Hl15 Hcw]]]].
  assert (Hlr : (1 <= len <= 15)%nat) by lia.
  assert (Hwidth : t_len (gen_codes t maxc blc) (Z.of_nat sym) = Z.of_nat len).
  { rewrite gen_codes_len. apply (LensOf_at t cl sym len Hlens He). }
  assert (Hval : 0 <= t_code (gen_codes t maxc blc) (Z.of_nat sym) < 2 ^ Z.of_nat len)
    by (apply (gen_codes_code_lt cl t maxc blc sym len); assumption).
  unfold send_code. rewrite Hwidth.
  split.
  - rewrite (bw_send_bits_bits _ (Z.of_nat len) b Hinv) by lia.
    rewrite Nat2Z.id.
    (* and the bits of that pair ARE the canonical codeword *)
    assert (Hbits : write_bits len (t_code (gen_codes t maxc blc) (Z.of_nat sym)) = cw).
    { rewrite Hcw.
      rewrite (gen_codes_stored_value cl t maxc blc sym len Hlens Hblc HV15 Hab Hmc He Hl1).
      apply bi_rev_write_bits; lia. }
    rewrite Hbits. reflexivity.
  - apply bw_send_bits_inv; [exact Hinv | lia | lia].
Qed.

(** ** Emitting one item

    THESE FOUR EXPRESSIONS ARE [send_go]'s, copied from [Trees.v:770-780] rather
    than paraphrased: the codeword goes to the INNER writer and the extra field
    to the outer one, so the codeword reaches the stream first. *)
Definition emit_item (bl : Tree) (it : CLItem) (b : BW) : BW :=
  match it with
  | CLit l   => send_code (Z.of_nat l) bl b
  | CRep _ k => bw_send_bits (Z.of_nat k - 3) 2 (send_code 16 bl b)
  | CZ3 k    => bw_send_bits (Z.of_nat k - 3) 3 (send_code 17 bl b)
  | CZ11 k   => bw_send_bits (Z.of_nat k - 11) 7 (send_code 18 bl b)
  end.

Fixpoint emit_items (bl : Tree) (items : list CLItem) (b : BW) : BW :=
  match items with
  | [] => b
  | it :: tl => emit_items bl tl (emit_item bl it b)
  end.

(** ** Emitting the stream appends exactly [cl_bits]

    Proved together with invariant preservation, because the fold needs both at
    every step. *)
Lemma emit_items_bits : forall cl t maxc blc items acc bits b,
  LensOf t cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxc -> -1 <= maxc <= 288 ->
  CLWf acc items ->
  cl_bits cl items = Some bits ->
  bw_wf b ->
  bw_stream (emit_items (gen_codes t maxc blc) items b) = bw_stream b ++ bits
  /\ bw_wf (emit_items (gen_codes t maxc blc) items b).
Proof.
  intros cl t maxc blc items.
  induction items as [|it tl IH]; intros acc bits b Hlens Hblc HV Hab Hmc Hwf Hb Hinv.
  - cbn [cl_bits] in Hb. inversion Hb; subst bits.
    cbn [emit_items]. rewrite app_nil_r. split; [reflexivity|exact Hinv].
  - cbn [cl_bits] in Hb.
    destruct (cl_item_bits cl it) as [b1|] eqn:E1; [|discriminate].
    destruct (cl_bits cl tl) as [b2|] eqn:E2; [|discriminate].
    inversion Hb; subst bits. clear Hb.
    cbn [emit_items].
    (* one item: its bits go on, and the invariant survives *)
    assert (Hstep : bw_stream (emit_item (gen_codes t maxc blc) it b) = bw_stream b ++ b1
                    /\ bw_wf (emit_item (gen_codes t maxc blc) it b)).
    { destruct it as [l|p k|k|k]; cbn [emit_item cl_item_bits] in E1 |- *.
      - destruct (code_for cl 7%nat l) as [cw|] eqn:Ecf; [|discriminate].
        inversion E1; subst b1.
        apply (send_code_bits cl t maxc blc l cw b 7%nat); try assumption; lia.
      - destruct (code_for cl 7%nat 16%nat) as [cw|] eqn:Ecf; [|discriminate].
        inversion E1; subst b1.
        destruct Hwf as [Hk [_ _]].
        destruct (send_code_bits cl t maxc blc 16%nat cw b 7%nat
                    Hlens Hblc HV ltac:(lia) Hab Hmc Ecf Hinv) as [Hs Hi].
        change (send_code 16 (gen_codes t maxc blc) b)
          with (send_code (Z.of_nat 16%nat) (gen_codes t maxc blc) b).
        split.
        + rewrite (bw_send_bits_bits (Z.of_nat k - 3) 2 _ Hi) by (cbn; lia).
          rewrite Hs, <- app_assoc. reflexivity.
        + apply bw_send_bits_inv; [exact Hi | cbn; lia | cbn; lia].
      - destruct (code_for cl 7%nat 17%nat) as [cw|] eqn:Ecf; [|discriminate].
        inversion E1; subst b1.
        destruct Hwf as [Hk _].
        destruct (send_code_bits cl t maxc blc 17%nat cw b 7%nat
                    Hlens Hblc HV ltac:(lia) Hab Hmc Ecf Hinv) as [Hs Hi].
        change (send_code 17 (gen_codes t maxc blc) b)
          with (send_code (Z.of_nat 17%nat) (gen_codes t maxc blc) b).
        split.
        + rewrite (bw_send_bits_bits (Z.of_nat k - 3) 3 _ Hi) by (cbn; lia).
          rewrite Hs, <- app_assoc. reflexivity.
        + apply bw_send_bits_inv; [exact Hi | cbn; lia | cbn; lia].
      - destruct (code_for cl 7%nat 18%nat) as [cw|] eqn:Ecf; [|discriminate].
        inversion E1; subst b1.
        destruct Hwf as [Hk _].
        destruct (send_code_bits cl t maxc blc 18%nat cw b 7%nat
                    Hlens Hblc HV ltac:(lia) Hab Hmc Ecf Hinv) as [Hs Hi].
        change (send_code 18 (gen_codes t maxc blc) b)
          with (send_code (Z.of_nat 18%nat) (gen_codes t maxc blc) b).
        split.
        + rewrite (bw_send_bits_bits (Z.of_nat k - 11) 7 _ Hi) by (cbn; lia).
          rewrite Hs, <- app_assoc. reflexivity.
        + apply bw_send_bits_inv; [exact Hi | cbn; lia | cbn; lia]. }
    destruct Hstep as [Hs1 Hi1].
    (* the well-formedness of the tail, at the stepped accumulator *)
    assert (Hwf' : CLWf (acc ++ cl_item_lens it) tl).
    { destruct it as [l|p k|k|k]; cbn [CLWf cl_item_lens] in Hwf |- *; tauto. }
    (* [destruct (cl_bits cl tl) eqn:E2] rewrote that term inside IH too, so IH's
       remaining hypothesis is [Some b2 = Some bits] and [eq_refl] discharges it;
       passing E2 fails on a type mismatch that looks like a different bug. *)
    destruct (IH (acc ++ cl_item_lens it) b2 (emit_item (gen_codes t maxc blc) it b)
                Hlens Hblc HV Hab Hmc Hwf' (eq_refl (Some b2)) Hi1) as [Hs2 Hi2].
    split; [|exact Hi2].
    rewrite Hs2, Hs1, <- app_assoc. reflexivity.
Qed.

(** ** THE CHAIN: emitted bits decode back to the code lengths *)

Theorem emit_items_roundtrip : forall cl t maxc blc items bits rest,
  LensOf t cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxc -> -1 <= maxc <= 288 ->
  CLWf [] items ->
  cl_bits cl items = Some bits ->
  read_lengths cl (length (cl_lens items))
    (bw_stream (emit_items (gen_codes t maxc blc) items bw_init) ++ rest)
  = Some (cl_lens items, rest).
Proof.
  intros cl t maxc blc items bits rest Hlens Hblc HV Hab Hmc Hwf Hb.
  destruct (emit_items_bits cl t maxc blc items [] bits bw_init
              Hlens Hblc HV Hab Hmc Hwf Hb bw_wf_init) as [Hs _].
  rewrite Hs, bw_stream_init. cbn [app].
  apply (read_lengths_inverts_cl_bits cl items bits rest HV Hwf Hb).
Qed.

(** ** WITNESS: the whole chain, on a real code-length tree

    [clw] and [itemsw] are ClStream.v's witness.  Here they are run through a
    tree that zlib's own [gen_codes] built from [clw]'s lengths, into zlib's own
    bit writer, and back out through [read_lengths]. *)

Definition tw : Tree :=
  mkTree zzero (zlist [0;0;2;2;0;0;0;0;0;0;0;0;0;0;0;0;2;2;0]).
Definition blcw : zarr := zlist [0;0;4].     (* four 2-bit codes *)

Lemma tw_LensOf : LensOf tw clw.
Proof.
  intros k Hk. cbn [length clw] in Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]]]]];
    try reflexivity. lia.
Qed.

Lemma blcw_BlcOf : BlcOf blcw clw.
Proof.
  apply BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try reflexivity. lia.
Qed.

Lemma clw_absent : AbsentBeyond clw 17.
Proof.
  intros k Hk.
  destruct (Nat.eq_dec k 18%nat) as [->|Hne]; [reflexivity|].
  apply nth_overflow. cbn [length clw]. lia.
Qed.

(** gen_codes really does reproduce the codes the declarative side specifies —
    checked, not assumed, at the four symbols the stream uses. *)
Example tw_codes_agree :
  map (fun sy => write_bits (Z.to_nat (t_len (gen_codes tw 17 blcw) (Z.of_nat sy)))
                            (t_code (gen_codes tw 17 blcw) (Z.of_nat sy)))
      [2;3;16;17]%nat
  = [[false;false]; [false;true]; [true;false]; [true;true]].
Proof. vm_compute. reflexivity. Qed.

(** The writer's stream after emitting the item list IS the 13 bits
    ClStream.v computed independently. *)
Example tw_emits_bitsw :
  bw_stream (emit_items (gen_codes tw 17 blcw) itemsw bw_init) = bitsw.
Proof. vm_compute. reflexivity. Qed.

(** THE CHAIN, applied.  Eleven code lengths recovered from the bits zlib's own
    writer produced, for an arbitrary remainder of the stream. *)
Theorem witness_chain : forall rest,
  read_lengths clw (length (cl_lens itemsw))
    (bw_stream (emit_items (gen_codes tw 17 blcw) itemsw bw_init) ++ rest)
  = Some (cl_lens itemsw, rest).
Proof.
  intro rest.
  apply (emit_items_roundtrip clw tw 17 blcw itemsw bitsw rest
           tw_LensOf blcw_BlcOf clw_valid clw_absent).
  - lia.
  - exact itemsw_wf.
  - exact itemsw_bits.
Qed.

Print Assumptions send_code_bits.
Print Assumptions emit_items_bits.
Print Assumptions emit_items_roundtrip.
Print Assumptions witness_chain.
