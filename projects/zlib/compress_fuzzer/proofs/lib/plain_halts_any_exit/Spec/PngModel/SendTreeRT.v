(** * SendTreeRT — THE CAPSTONE.  [send_tree]'s bytes decode back to the tree's
      own code lengths.

    OWNER: huffman-id, claim §HUFFID-SENDGO.

    This is what L-B was for.  Every link is now Qed and this file joins them:

      SendGo.v       send_tree IS emit_items over send_tree_items
      SendGoLens.v   those items denote the tree's own length vector      (B2)
      SendGoWf.v     ...and are well formed                              (B3)
      SendItems.v    emitting them appends exactly ClStream's cl_bits
      BwStream.v     ...and that is what the bit writer really writes
      HuffGenCodes.v the code-length tree's codes ARE Huff's canonical ones
      HuffMaxBits.v  ...at the code-length tree's own bound, 7
      ClStream.v     and read_lengths inverts the RLE'd stream

    So: run zlib's [send_tree] over a code-length tree that zlib's [gen_codes]
    built, and DeflateSpec's [read_lengths] — the model of inflate's CODELENS
    phase — reads back exactly the code lengths [send_tree] was describing, with
    the remainder of the bit stream untouched.

    THE HYPOTHESES, and which of them are facts about zlib rather than
    conveniences:
      the 0xffff guard at [tree[max_code+1]]   a real store, by [scan_tree]
      every real length in 0..15               [gen_bitlen]'s bound, MAX_BITS
      the code-length tree is Kraft-valid      [build_bl_tree]'s job
      it covers the symbols the stream uses    also [build_bl_tree]'s job, and
                                               the one hypothesis here that is
                                               a genuine coverage obligation
                                               rather than a range fact
    None of them is discharged here; all four are [build_tree]/[build_bl_tree]
    territory, which §RT-IDENTITY-PLAN puts outside this layer.  The last one is
    called out because it is the only one that could fail silently in a real
    encoder rather than being a syntactic bound. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens SendGoWf.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** THE CAPSTONE *)

Theorem send_tree_roundtrip :
  forall t maxc cl blt maxcbl blc bits rest,
  (* the tree whose lengths are being sent *)
  0 <= maxc <= 285 ->
  (forall i, 0 <= t_len t i) ->
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (* the code-length tree that carries the stream, built by gen_codes *)
  LensOf blt cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  (* ...and it has a code for every symbol the stream uses *)
  cl_bits cl (send_tree_items t maxc) = Some bits ->
  read_lengths cl (length (tree_lens t maxc))
    (bw_stream (send_tree t maxc (gen_codes blt maxcbl blc) bw_init) ++ rest)
  = Some (tree_lens t maxc, rest).
Proof.
  intros t maxc cl blt maxcbl blc bits rest
         Hmc Hnn Hguard Hlen15 Hlens Hblc HV Hab Hmcbl Hcb.
  rewrite (send_tree_emit t maxc (gen_codes blt maxcbl blc) bw_init Hnn).
  rewrite <- (send_tree_items_lens t maxc Hmc Hguard Hlen15).
  apply (emit_items_roundtrip cl blt maxcbl blc (send_tree_items t maxc) bits rest
           Hlens Hblc HV Hab Hmcbl
           (send_tree_items_wf t maxc Hmc Hguard Hlen15) Hcb).
Qed.

(** ** WITNESS

    A tree with eleven code lengths — five 3s, five 0s and a 2 — plus the 0xffff
    guard at index 11.  It exercises all three item shapes: the run of 3s leaves
    through symbol 16, the run of 0s through symbol 17, and the trailing 2 is
    below [mincnt] so it leaves as a bare literal.

    THE PREDICTION WORTH CHECKING.  [itemsw] in ClStream.v was written BY HAND as
    a plausible code-length stream, long before [send_items] existed.  The
    Example below says [send_tree_items] on this tree produces exactly that list.
    Two independent routes — a human guess at what a DEFLATE encoder emits, and
    zlib's actual control flow transcribed from trees.c — landing on the same
    four items. *)

Definition twt : Tree :=
  mkTree zzero (zlist [3;3;3;3;3;0;0;0;0;0;2;65535]).

Lemma zlist_nonneg : forall l i, forallb (Z.leb 0) l = true -> 0 <= zlist l i.
Proof.
  intros l i H. unfold zlist.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hlt|Hge].
  - apply Z.leb_le.
    apply (proj1 (forallb_forall (Z.leb 0) l) H). apply nth_In. exact Hlt.
  - rewrite nth_overflow by lia. lia.
Qed.

(** A range hypothesis over [Z] is far easier to discharge one [nat] at a time. *)
Lemma range_nat : forall (P : Z -> Prop) (hi : nat),
  (forall k, (k <= hi)%nat -> P (Z.of_nat k)) ->
  forall i, 0 <= i <= Z.of_nat hi -> P i.
Proof.
  intros P hi H i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply H. lia.
Qed.

Lemma twt_nonneg : forall i, 0 <= t_len twt i.
Proof. intro i. apply zlist_nonneg. vm_compute. reflexivity. Qed.

Lemma twt_guard : t_len twt (10 + 1) = 65535.
Proof. vm_compute. reflexivity. Qed.

Lemma twt_len15 : forall i, 0 <= i <= 10 -> 0 <= t_len twt i <= 15.
Proof.
  apply (range_nat (fun i => 0 <= t_len twt i <= 15) 10%nat).
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]];
    try (vm_compute; split; discriminate). lia.
Qed.

(** zlib's control flow produces the very list ClStream.v guessed. *)
Example twt_items : send_tree_items twt 10 = itemsw.
Proof. vm_compute. reflexivity. Qed.

Example twt_lens : tree_lens twt 10 = [3;3;3;3;3;0;0;0;0;0;2]%nat.
Proof. vm_compute. reflexivity. Qed.

Example twt_cl_bits : cl_bits clw (send_tree_items twt 10) = Some bitsw.
Proof. vm_compute. reflexivity. Qed.

(** THE APPLIED CAPSTONE: eleven code lengths recovered from the bytes zlib's own
    [send_tree] wrote, for an arbitrary remainder of the stream. *)
Theorem twt_roundtrip : forall rest,
  read_lengths clw (length (tree_lens twt 10))
    (bw_stream (send_tree twt 10 (gen_codes tw 17 blcw) bw_init) ++ rest)
  = Some (tree_lens twt 10, rest).
Proof.
  intro rest.
  apply (send_tree_roundtrip twt 10 clw tw 17 blcw bitsw rest);
    [ lia | exact twt_nonneg | exact twt_guard | exact twt_len15
    | exact tw_LensOf | exact blcw_BlcOf | exact clw_valid | exact clw_absent
    | lia | exact twt_cl_bits ].
Qed.

(** ...and the fully concrete reading of it, so a reader can see the numbers. *)
Corollary twt_roundtrip_concrete : forall rest,
  read_lengths clw 11%nat
    (bw_stream (send_tree twt 10 (gen_codes tw 17 blcw) bw_init) ++ rest)
  = Some ([3;3;3;3;3;0;0;0;0;0;2]%nat, rest).
Proof.
  intro rest.
  pose proof (twt_roundtrip rest) as H.
  rewrite twt_lens in H. exact H.
Qed.

Print Assumptions send_tree_roundtrip.
Print Assumptions twt_roundtrip.
Print Assumptions twt_roundtrip_concrete.
