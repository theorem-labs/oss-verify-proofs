(** * BsSupport — ladder (b) support pieces (an earlier development run bodyasm fork).

    P1: strict-decoder accumulation monotonicity (the room-threading
    obligation flagged in the commission);
    P2: the TYPEDO good-only entry (NEEDBITS(3) starve killed by K1
    against the block's own read successes);
    the strict per-block extractor; the EOB connective (decode_symbols
    success forces 256 coded — hdecode_sound + code_table_In_iff);
    read_bytes bit accounting (stored input availability).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff InflateFast Inflate DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6B ZReproQ6I ZReproL0E W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill LkNb.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [resolve_lz] only ever appends to its accumulator. *)
Lemma bs_resolve_extends : forall syms acc out,
  resolve_lz syms acc = Some out -> exists suf, out = acc ++ suf.
Proof.
  induction syms as [|s tl IH]; intros acc out H; cbn [resolve_lz] in H.
  - injection H as <-. exists []. now rewrite app_nil_r.
  - destruct s as [b|len dist|].
    + destruct (IH _ _ H) as (suf & ->).
      exists ([b] ++ suf). now rewrite app_assoc.
    + destruct ((dist =? 0) || (length acc <? dist))%nat; [discriminate|].
      destruct (IH _ _ H) as (suf & ->).
      eexists. now rewrite app_assoc.
    + injection H as <-. exists []. now rewrite app_nil_r.
Qed.

(** The strict block decoder, destructed into its three arms. *)
Lemma bs_blk_extract : forall bits acc fin out rem,
  dec_blk_strict bits acc = Some (fin, out, rem) ->
  exists bfinal btype r1 r2,
    read_bits 1%nat bits = Some (bfinal, r1)
    /\ read_bits 2%nat r1 = Some (btype, r2)
    /\ fin = Z.eqb bfinal 1
    /\ ( (btype = 0 /\ exists payload,
            decode_stored r2 = Some (payload, rem)
            /\ out = acc ++ payload)
      \/ (btype = 1 /\ exists syms,
            decode_symbols fixed_lit_lengths fixed_dist_lengths r2
              = Some (syms, rem)
            /\ resolve_lz syms acc = Some out)
      \/ (btype = 2 /\ exists lit dst r3 syms,
            decode_dynamic_tables_strict r2 = Some (lit, dst, r3)
            /\ decode_symbols lit dst r3 = Some (syms, rem)
            /\ resolve_lz syms acc = Some out)).
Proof.
  intros bits acc fin out rem H. unfold dec_blk_strict in H.
  destruct (read_bits 1%nat bits) as [[bfinal r1]|] eqn:E1; [|discriminate].
  destruct (read_bits 2%nat r1) as [[btype r2]|] eqn:E2; [|discriminate].
  cbv zeta in H.
  exists bfinal, btype, r1, r2.
  split; [reflexivity|]. split; [exact E2|].
  destruct (Z.eqb_spec btype 0) as [->|N0].
  { destruct (decode_stored r2) as [[payload r3]|] eqn:ED; [|discriminate].
    injection H as F O R. subst fin out rem.
    split; [reflexivity|]. left. split; [reflexivity|].
    exists payload. split; [reflexivity | reflexivity]. }
  destruct (Z.eqb_spec btype 1) as [->|N1].
  { destruct (decode_symbols fixed_lit_lengths fixed_dist_lengths r2)
      as [[syms r3]|] eqn:ED; [|discriminate].
    destruct (resolve_lz syms acc) as [o|] eqn:ER; [|discriminate].
    injection H as F O R. subst fin out rem.
    split; [reflexivity|]. right; left. split; [reflexivity|].
    exists syms. split; [reflexivity | exact ER]. }
  destruct (Z.eqb_spec btype 2) as [->|N2]; [|discriminate].
  destruct (decode_dynamic_tables_strict r2) as [[[lit dst] r3]|] eqn:EH;
    [|discriminate].
  destruct (decode_symbols lit dst r3) as [[syms r4]|] eqn:ED;
    [|discriminate].
  destruct (resolve_lz syms acc) as [o|] eqn:ER; [|discriminate].
  injection H as F O R. subst fin out rem.
  split; [reflexivity|]. right; right. split; [reflexivity|].
  exists lit, dst, r3, syms.
  split; [reflexivity|]. split; [exact ED | exact ER].
Qed.

Lemma bs_blk_extends : forall bits acc fin out rem,
  dec_blk_strict bits acc = Some (fin, out, rem) ->
  exists suf, out = acc ++ suf.
Proof.
  intros bits acc fin out rem H.
  destruct (bs_blk_extract _ _ _ _ _ H)
    as (bf & bt & r1 & r2 & _ & _ & _ &
        [ (_ & p & _ & ->)
        | [ (_ & syms & _ & HR)
          | (_ & lit & dst & r3 & syms & _ & _ & HR) ] ]).
  - now exists p.
  - exact (bs_resolve_extends _ _ _ HR).
  - exact (bs_resolve_extends _ _ _ HR).
Qed.

(** P1: the strict stream decoder's output extends its accumulator. *)
Lemma bs_fuel_mono : forall fs bits acc X rem,
  dec_stream_strict_fuel fs bits acc = Some (X, rem) ->
  exists suf, X = acc ++ suf.
Proof.
  induction fs as [|f IH]; intros bits acc X rem H;
    cbn [dec_stream_strict_fuel] in H; [discriminate|].
  destruct (dec_blk_strict bits acc) as [[[fin out1] rem1]|] eqn:SD;
    [|discriminate].
  destruct (bs_blk_extends _ _ _ _ _ SD) as (s1 & ->).
  destruct fin.
  - injection H as <- <-. now exists s1.
  - destruct (IH _ _ _ _ H) as (s2 & ->).
    exists (s1 ++ s2). now rewrite app_assoc.
Qed.

Lemma bs_zlen_mono : forall fs bits acc X rem,
  dec_stream_strict_fuel fs bits acc = Some (X, rem) ->
  zlen acc <= zlen X.
Proof.
  intros fs bits acc X rem H.
  destruct (bs_fuel_mono _ _ _ _ _ H) as (suf & ->).
  unfold zlen. rewrite length_app. lia.
Qed.

(** P2: TYPEDO cannot starve when the block's own three header bits are
    present — K1 kills the NBLeave branch. *)
Lemma bs_typedo_cont : forall c q,
  n_flush c <> Z_TREES ->
  h_last (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  (3 <= length (br_stream (q_br q)))%nat ->
  exists q', inf_TYPEDO c q = InfCont q'.
Proof.
  intros c q HF Hlast Hwf HL.
  unfold inf_TYPEDO. cbv zeta.
  rewrite Hlast. change (negb (0 =? 0)) with false.
  destruct (inf_nb 3 (q_br q)) as [b|b] eqn:EN; cbv beta iota.
  - destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 0) as [E0|N0].
    { eexists. reflexivity. }
    destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 1) as [E1|N1].
    { rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF).
      cbv beta iota. eexists. reflexivity. }
    destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 2) as [E2|N2].
    { eexists. reflexivity. }
    eexists. reflexivity.
  - exfalso.
    destruct (k1_nb_starve_short 3 (q_br q) b Hwf ltac:(lia) EN)
      as (HS & _ & _).
    change (Z.to_nat 3) with 3%nat in HS. lia.
Qed.

(** The EOB connective: a successful symbol decode forces symbol 256
    coded (its LzEnd terminator has no other producer). *)
Lemma bs_dec_256 : forall ll dl bits syms rem,
  decode_symbols ll dl bits = Some (syms, rem) ->
  exists cw, code_for ll 15%nat 256%nat = Some cw.
Proof.
  intros ll dl bits syms rem H. unfold decode_symbols in H.
  set (f := S (length bits)) in H. clearbody f.
  revert bits syms rem H.
  induction f as [|f IH]; intros bits syms rem H;
    cbn [decode_symbols_fuel] in H; [discriminate|].
  destruct (decode_lit_len ll dl bits) as [[s r]|] eqn:DL; [|discriminate].
  destruct (lz_is_end s) eqn:LE.
  - apply lz_is_end_true in LE. subst s.
    unfold decode_lit_len in DL.
    destruct (hdecode (code_table ll 15%nat) bits) as [[sym r1]|] eqn:HD;
      [|discriminate].
    destruct (Nat.ltb sym 256) eqn:LT. { discriminate DL. }
    destruct (Nat.eqb sym 256) eqn:EQ.
    + apply Nat.eqb_eq in EQ. subst sym.
      destruct (hdecode_sound _ _ _ _ _ HD) as (cw & HIn & _ & _).
      exists cw. now apply code_table_In_iff.
    + destruct (read_extra length_base length_extra (sym - 257)%nat r1)
        as [[len r2]|]; [|discriminate].
      destruct (hdecode (code_table dl 15%nat) r2) as [[dsym r3]|];
        [|discriminate].
      destruct (read_extra dist_base dist_extra dsym r3) as [[dist r4]|];
        [|discriminate].
      discriminate DL.
  - destruct (decode_symbols_fuel f ll dl r) as [[syms2 rem2]|] eqn:DS;
      [|discriminate].
    exact (IH _ _ _ DS).
Qed.

(** [read_bytes] consumes exactly eight bits per byte. *)
Lemma bs_read_bytes_bits : forall n bits bs rem,
  read_bytes n bits = Some (bs, rem) ->
  (length bits = 8 * n + length rem)%nat.
Proof.
  induction n as [|n IH]; intros bits bs rem H; cbn [read_bytes] in H.
  - injection H as B R. subst bs rem. lia.
  - destruct (read_bits 8%nat bits) as [[b r]|] eqn:E; [|discriminate].
    destruct (read_bytes n r) as [[bs2 r2]|] eqn:E2; [|discriminate].
    injection H as B R. subst bs rem.
    pose proof (read_bits_length _ _ _ _ E).
    pose proof (IH _ _ _ E2). lia.
Qed.
