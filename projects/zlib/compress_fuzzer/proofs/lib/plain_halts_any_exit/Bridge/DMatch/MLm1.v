(** * Bridge.DMatch.MLm1 — group M: pair D20, [longest_match]'s byte compare.

    S5 compares a candidate eight bytes per step from offset 3 on and stops
    when a step leaves [scan] at [strend = scan + 258] ([lm_cmp_loop], fuel
    33); RT compares one byte per step from offset 3 and stops at 258
    without reading it ([lm_cpl], fuel 258).  Both give the offset of the
    first mismatch in [[3, 258)], or 258 ([m_cmp_len]).  When the only
    mismatch is at offset 258 S5 reads it and RT does not, and both still
    answer 258.

    The proof reads S5's array as a closure ([arr_get w]), states each
    model's answer by its specification (the bytes before it match, the
    byte at it differs unless it is 258), and concludes by uniqueness. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk Deflate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module RD := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Deflate.
Module DS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateState.
Module RC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Chunk.

(** S5's compare step and loop, on offsets from [a] / [b] and a closure. *)
Fixpoint s5cmp (k : nat) (w : Base.zarr) (a b j : Z) : Z * bool :=
  match k with
  | O => (j, true)
  | S k' => if Z.eqb (w (a + (j + 1))) (w (b + (j + 1))) then s5cmp k' w a b (j + 1) else (j + 1, false)
  end.

Fixpoint s5loop (f : nat) (w : Base.zarr) (a b j : Z) : Z :=
  match f with
  | O => j
  | S f' => let r := s5cmp 8 w a b j in
            if snd r && Z.ltb (fst r) 258 then s5loop f' w a b (fst r) else fst r
  end.

Lemma m_lm_cmpk_off : forall k w a b j,
  SLz.lm_cmpk k w (a + j) (b + j)
  = (a + fst (s5cmp k (arr_get w) a b j), b + fst (s5cmp k (arr_get w) a b j),
     snd (s5cmp k (arr_get w) a b j)).
Proof.
  induction k as [|k IH]; intros w a b j; [reflexivity|].
  cbn [SLz.lm_cmpk s5cmp]. cbv zeta.
  replace (a + j + 1) with (a + (j + 1)) by lia. replace (b + j + 1) with (b + (j + 1)) by lia.
  destruct (Z.eqb (arr_get w (a + (j + 1))) (arr_get w (b + (j + 1)))); [apply IH | reflexivity].
Qed.

Lemma m_lm_cmp_loop_off : forall f w a b j,
  SLz.lm_cmp_loop f w (a + j) (b + j) (a + 258) = a + s5loop f (arr_get w) a b j.
Proof.
  induction f as [|f IH]; intros w a b j; [reflexivity|].
  cbn [SLz.lm_cmp_loop s5loop]. rewrite m_lm_cmpk_off.
  replace (Z.ltb (a + fst (s5cmp 8 (arr_get w) a b j)) (a + 258))
    with (Z.ltb (fst (s5cmp 8 (arr_get w) a b j)) 258)
    by (destruct (Z.ltb_spec (a + fst (s5cmp 8 (arr_get w) a b j)) (a + 258));
        destruct (Z.ltb_spec (fst (s5cmp 8 (arr_get w) a b j)) 258); lia).
  destruct (snd (s5cmp 8 (arr_get w) a b j) && Z.ltb (fst (s5cmp 8 (arr_get w) a b j)) 258); [|reflexivity].
  apply IH.
Qed.

(** ** Specifications *)

Definition mt (w : Base.zarr) (a b i : Z) : Prop := w (a + i) = w (b + i).

Lemma m_s5cmp_spec : forall k w a b j, (1 <= k)%nat ->
  let r := s5cmp k w a b j in
  j < fst r <= j + Z.of_nat k
  /\ (forall i, j < i < fst r -> mt w a b i)
  /\ (snd r = true -> fst r = j + Z.of_nat k /\ mt w a b (fst r))
  /\ (snd r = false -> ~ mt w a b (fst r)).
Proof.
  induction k as [|k IH]; intros w a b j Hk; [lia|].
  cbn [s5cmp]. unfold mt.
  destruct (Z.eqb_spec (w (a + (j + 1))) (w (b + (j + 1)))) as [E|E].
  - destruct k as [|k].
    + cbn [s5cmp fst snd]. split; [lia|]. split; [intros i Hi; lia|].
      split; [intros _; split; [lia | exact E] | discriminate].
    + destruct (IH w a b (j + 1) ltac:(lia)) as (H1 & H2 & H3 & H4). unfold mt in *.
      split; [lia|]. split.
      * intros i Hi. destruct (Z.eq_dec i (j + 1)) as [->|Hne]; [exact E | apply H2; lia].
      * split; [intros Ht; destruct (H3 Ht) as [Hf Hm]; split; [lia | exact Hm] | exact H4].
  - cbn [fst snd]. split; [lia|]. split; [intros i Hi; lia|]. split; [discriminate | intros _; exact E].
Qed.

Lemma m_s5loop_spec : forall m f w a b j,
  j = 258 - 8 * Z.of_nat m -> (1 <= m)%nat -> (m <= f)%nat ->
  (forall i, 3 <= i <= j -> mt w a b i) ->
  let y := s5loop f w a b j in
  j < y <= 258 /\ (forall i, 3 <= i < y -> mt w a b i) /\ (y < 258 -> ~ mt w a b y).
Proof.
  induction m as [|m IH]; intros f w a b j Hj Hm Hf Hpre; [lia|].
  destruct f as [|f]; [lia|]. cbn [s5loop].
  destruct (m_s5cmp_spec 8 w a b j ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (s5cmp 8 w a b j) as [j' ok] eqn:EC. cbn [fst snd] in C1, C2, C3, C4 |- *.
  destruct ok.
  - destruct (C3 eq_refl) as [Ej' Mj']. cbn [andb].
    destruct (Z.ltb_spec j' 258) as [Lt|Ge].
    + destruct m as [|m]; [lia|].
      destruct (IH f w a b j' ltac:(lia) ltac:(lia) ltac:(lia)) as (D1 & D2 & D3).
      { intros i Hi. destruct (Z_le_gt_dec i j); [apply Hpre; lia|].
        destruct (Z.eq_dec i j') as [->|Hne]; [exact Mj' | apply C2; lia]. }
      split; [lia|]. split; [exact D2 | exact D3].
    + split; [lia|]. split; [|intros; lia].
      intros i Hi. destruct (Z_le_gt_dec i j); [apply Hpre; lia | apply C2; lia].
  - cbn [andb]. split; [lia|]. split; [|intros _; apply C4; reflexivity].
    intros i Hi. destruct (Z_le_gt_dec i j); [apply Hpre; lia | apply C2; lia].
Qed.

Lemma m_lm_cpl_spec : forall F w a b x, x <= 258 -> 258 - x <= Z.of_nat F ->
  let y := RD.lm_cpl F w a b x in
  x <= y <= 258 /\ (forall i, x <= i < y -> mt w a b i) /\ (y < 258 -> ~ mt w a b y).
Proof.
  induction F as [|F IH]; intros w a b x Hx HF; cbn [RD.lm_cpl].
  - assert (x = 258) by lia. subst x. split; [lia|]. split; [intros; lia | intros; lia].
  - change RC.MAX_MATCH with 258.
    destruct (Z.leb_spec 258 x).
    + split; [lia|]. split; [intros; lia | intros; lia].
    + destruct (Z.eqb_spec (w (a + x)) (w (b + x))) as [E|E].
      * destruct (IH w a b (x + 1) ltac:(lia) ltac:(lia)) as (D1 & D2 & D3).
        split; [lia|]. split; [|exact D3].
        intros i Hi. destruct (Z.eq_dec i x) as [->|Hne]; [exact E | apply D2; lia].
      * split; [lia|]. split; [intros; lia | intros _; exact E].
Qed.

(** ** The two compares agree *)

Theorem m_s5loop_cpl : forall w a b,
  s5loop 33 w a b 2 = RD.lm_cpl 258 w a b 3.
Proof.
  intros w a b.
  destruct (m_s5loop_spec 32 33 w a b 2 ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(intros; lia))
    as (S1 & S2 & S3).
  destruct (m_lm_cpl_spec 258 w a b 3 ltac:(lia) ltac:(lia)) as (R1 & R2 & R3).
  set (y1 := s5loop 33 w a b 2) in *. set (y2 := RD.lm_cpl 258 w a b 3) in *.
  destruct (Z.lt_trichotomy y1 y2) as [Lt|[Eq|Gt]]; [|exact Eq|].
  - exfalso. apply S3; [lia|]. apply R2. lia.
  - exfalso. apply R3; [lia|]. apply S2. lia.
Qed.

(** RT's compare reads only offsets [[x, 258)]. *)
Lemma m_lm_cpl_ext : forall F w w' a b x,
  (forall i, x <= i < 258 -> w (a + i) = w' (a + i) /\ w (b + i) = w' (b + i)) ->
  RD.lm_cpl F w a b x = RD.lm_cpl F w' a b x.
Proof.
  induction F as [|F IH]; intros w w' a b x H; cbn [RD.lm_cpl]; [reflexivity|].
  change RC.MAX_MATCH with 258.
  destruct (Z.leb_spec 258 x); [reflexivity|].
  destruct (H x ltac:(lia)) as [Ha Hb]. rewrite Ha, Hb.
  destruct (Z.eqb (w' (a + x)) (w' (b + x))); [|reflexivity].
  apply IH. intros i Hi. apply H. lia.
Qed.

(** S5's match length at [scan] against candidate [mtch], as the body of
    [longest_match_body] computes it, is RT's [lm_cpl]. *)
Theorem m_cmp_len : forall w (z : Base.zarr) scan mtch,
  (forall i, 3 <= i < 258 -> arr_get w (scan + i) = z (scan + i) /\ arr_get w (mtch + i) = z (mtch + i)) ->
  DS.MAX_MATCH - (scan + DS.MAX_MATCH - SLz.lm_cmp_loop 33 w (scan + 2) (mtch + 2) (scan + DS.MAX_MATCH))
  = RD.lm_cpl 258 z scan mtch 3.
Proof.
  intros w z scan mtch H. change DS.MAX_MATCH with 258.
  rewrite m_lm_cmp_loop_off, m_s5loop_cpl.
  rewrite (m_lm_cpl_ext 258 (arr_get w) z scan mtch 3 H). lia.
Qed.
