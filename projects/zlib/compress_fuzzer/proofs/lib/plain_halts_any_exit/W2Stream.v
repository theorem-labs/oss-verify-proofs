(** * W2Stream — the IfSt stream view and the entry/writeback
      correspondence for [inflate_fast] (q7-decode lane, W2 of the
      ZrLenFastLeg discharge plan, 2026-08-20, OFF-TREE).

    [ZrLenFastLeg] is spelled in [ZBitsBridge.br_stream]; the fast walk
    lives in [IfSt].  This file gives the fast side its own abstraction
    function [if_stream] (same shape as [br_stream]: pending hold bits,
    then unread bytes), the entry equality against [br_stream], the three
    step laws (loads preserve, drops are [skipn], [if_low] spells a
    [firstn]), and the epilogue law: [if_finish]'s byte-return trick
    ([in -= bits >> 3]) preserves the stream — PROVIDED hold's whole
    bytes really are the input bytes just below the cursor, which is the
    [if_haligned] invariant.  That invariant is established at entry only
    from the BR-side twin [br_haligned], which [br_wf] does NOT imply:
    ZrLenFastLeg needs it as a NEW premise (negotiation feed; see the
    lane report). *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits ZBitsIn ZBitsBridge DecodeBridge InflateFast Inflate.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Small helpers.
   ========================================================================== *)

Lemma w2_bytes_bits_app : forall xs ys,
  bytes_bits (xs ++ ys) = bytes_bits xs ++ bytes_bits ys.
Proof.
  induction xs as [|x xs IH]; intro ys; cbn [app]; [reflexivity|].
  rewrite !bytes_bits_cons, IH. apply app_assoc.
Qed.

Lemma w2_map_seq_shift : forall (A : Type) (f : nat -> A) (a n : nat),
  map f (seq a n) = map (fun k => f (a + k)%nat) (seq 0 n).
Proof.
  intros A f a n. revert a.
  induction n as [|n IH]; intro a; cbn [seq map]; [reflexivity|].
  f_equal; [f_equal; lia|].
  rewrite (IH (S a)), <- seq_shift, map_map.
  apply map_ext; intro k. f_equal. lia.
Qed.

(** Low 8 bits of a shift do not see a mod at 8-or-more above the shift. *)
Lemma w2_low8_mod_shift : forall a B s,
  0 <= s -> s + 8 <= B ->
  Z.land (Z.shiftr (a mod 2 ^ B) s) 255 = Z.land (Z.shiftr a s) 255.
Proof.
  intros a B s Hs HB.
  change 255 with (Z.ones 8).
  apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.ltb_spec n 8) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia.
    now rewrite !andb_false_r.
Qed.

(* ==========================================================================
   1.  The abstraction function and its invariants.
   ========================================================================== *)

(** The bytes the walk has not read: from the cursor to the true input
    end.  [f_last] is [in + (avail_in - 5)], so the end is [f_last + 5]. *)
Definition if_bytes (c : IfCtx) (s : IfSt) : list Z :=
  map (fun k => f_inbuf c (f_in s + Z.of_nat k))
      (seq 0 (Z.to_nat (f_last c + 5 - f_in s))).

Definition if_stream (c : IfCtx) (s : IfSt) : list bool :=
  write_bits (Z.to_nat (f_bits s)) (f_hold s) ++ bytes_bits (if_bytes c s).

(** Reader sanity, [br_wf]'s hold/bits half. *)
Definition if_swf (s : IfSt) : Prop :=
  0 <= f_bits s /\ 0 <= f_hold s < Z.shiftl 1 (f_bits s).

Definition if_inb (c : IfCtx) : Prop :=
  forall i, 0 <= f_inbuf c i < 256.

(** Hold's whole bytes are the input bytes just below the cursor —
    byte [j] from the TOP of the live window (1-indexed) is the array
    byte at [f_in - j].  This is what makes [if_finish]'s byte-return
    sound; loads and drops preserve it, [br_wf] does NOT imply it at
    entry. *)
Definition if_haligned (c : IfCtx) (s : IfSt) : Prop :=
  forall j, 1 <= j <= f_bits s / 8 ->
    Z.land (Z.shiftr (f_hold s) (f_bits s - 8 * j)) 255
    = f_inbuf c (f_in s - j).

(** The BR-side twin, at the slow reader: THE NEW ZrLenFastLeg PREMISE. *)
Definition br_haligned (b : BR) : Prop :=
  forall j, 1 <= j <= br_bits b / 8 ->
    Z.land (Z.shiftr (br_hold b) (br_bits b - 8 * j)) 255
    = br_in b (br_next b - j).

(** Bit-order smoke: 4 pending bits of 11 = 0b1011 (LSB first), then one
    byte 165 = . *)
Example w2_order_smoke :
  if_stream
    {| f_inbuf := fun i => if Z.eqb i 7 then 165 else 0;
       f_last := 3; f_beg := 0; f_end := 0; f_wsize := 0; f_whave := 0;
       f_wnext := 0; f_window := zzero;
       f_lcode := fun _ => mkCode 0 0 0; f_dcode := fun _ => mkCode 0 0 0;
       f_lmask := 0; f_dmask := 0; f_sane := 1 |}
    {| f_in := 7; f_out := 0; f_hold := 11; f_bits := 4; f_buf := zzero |}
  = [true; true; false; true;
     true; false; true; false; false; true; false; true].
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2.  Entry: [if_stream] at [inf_LEN]'s argument record IS [br_stream].
   ========================================================================== *)

Lemma w2_entry_stream : forall (a : IfArgs) (b : BR),
  a_inbuf a = br_in b -> a_next_in a = br_next b ->
  a_avail_in a = br_have b -> a_hold a = br_hold b -> a_bits a = br_bits b ->
  if_stream (if_ctx a) (if_st0 a) = br_stream b.
Proof.
  intros a b H1 H2 H3 H4 H5.
  unfold if_stream, if_bytes, br_stream, br_bytes.
  cbn [if_ctx if_st0 f_inbuf f_last f_in f_hold f_bits].
  rewrite H1, H2, H3, H4, H5.
  replace (br_next b + (br_have b - 5) + 5 - br_next b)
    with (br_have b) by ring.
  reflexivity.
Qed.

Lemma w2_entry_swf : forall (a : IfArgs) (b : BR),
  br_wf b -> a_hold a = br_hold b -> a_bits a = br_bits b ->
  if_swf (if_st0 a).
Proof.
  intros a b (Hb & Hh & _) H4 H5.
  unfold if_swf. cbn [if_st0 f_hold f_bits].
  rewrite H4, H5. split; [lia | exact Hh].
Qed.

Lemma w2_entry_haligned : forall (a : IfArgs) (b : BR),
  br_haligned b ->
  a_inbuf a = br_in b -> a_next_in a = br_next b ->
  a_hold a = br_hold b -> a_bits a = br_bits b ->
  if_haligned (if_ctx a) (if_st0 a).
Proof.
  intros a b Hal H1 H2 H4 H5 j Hj.
  cbn [if_ctx if_st0 f_inbuf f_in f_hold f_bits] in *.
  rewrite H1, H2, H4, H5 in *.
  apply Hal. exact Hj.
Qed.

(* ==========================================================================
   3.  Step laws.
   ========================================================================== *)

Lemma w2_bytes_peel : forall c s,
  f_in s < f_last c + 5 ->
  if_bytes c s = f_inbuf c (f_in s) :: if_bytes c (if_load1 c s).
Proof.
  intros c s H. unfold if_bytes. cbn [if_load1 f_in].
  replace (Z.to_nat (f_last c + 5 - f_in s))
    with (S (Z.to_nat (f_last c + 5 - (f_in s + 1)))) by lia.
  cbn [seq map].
  f_equal; [f_equal; lia|].
  rewrite <- seq_shift, map_map.
  apply map_ext; intro k. f_equal. lia.
Qed.

Lemma w2_load1_stream : forall c s,
  if_inb c -> if_swf s -> f_in s < f_last c + 5 ->
  if_stream c (if_load1 c s) = if_stream c s.
Proof.
  intros c s Hin (Hb & Hh0 & Hh1) Hlt.
  rewrite Z.shiftl_1_l in Hh1.
  unfold if_stream.
  rewrite (w2_bytes_peel c s Hlt), bytes_bits_cons.
  cbn [if_load1 f_hold f_bits f_in f_buf f_out].
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (Z.to_nat (f_bits s + 8)) with (Z.to_nat (f_bits s) + 8)%nat by lia.
  replace (2 ^ f_bits s) with (2 ^ Z.of_nat (Z.to_nat (f_bits s)))
    by (rewrite Z2Nat.id by lia; reflexivity).
  rewrite write_bits_split
    by (rewrite Z2Nat.id by lia; lia).
  rewrite <- byte_bits_write_bits, <- app_assoc. reflexivity.
Qed.

Lemma w2_load1_swf : forall c s,
  if_inb c -> if_swf s -> if_swf (if_load1 c s).
Proof.
  intros c s Hin (Hb & Hh0 & Hh1).
  rewrite Z.shiftl_1_l in Hh1.
  unfold if_swf. cbn [if_load1 f_hold f_bits].
  rewrite Z.shiftl_1_l, Z.shiftl_mul_pow2 by lia.
  assert (He : 2 ^ (f_bits s + 8) = 256 * 2 ^ f_bits s)
    by (rewrite Z.pow_add_r by lia; ring).
  pose proof (Hin (f_in s)) as Hby.
  pose proof (Z.pow_pos_nonneg 2 (f_bits s) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; nia.
Qed.

Lemma w2_load1_haligned : forall c s,
  if_inb c -> if_swf s -> if_haligned c s ->
  if_haligned c (if_load1 c s).
Proof.
  intros c s Hin (Hb & Hh0 & Hh1) Hal j Hj.
  rewrite Z.shiftl_1_l in Hh1.
  cbn [if_load1 f_hold f_bits f_in] in *.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hdiv : (f_bits s + 8) / 8 = f_bits s / 8 + 1)
    by (replace (f_bits s + 8) with (f_bits s + 1 * 8) by ring;
        rewrite Z.div_add by lia; ring).
  rewrite Hdiv in Hj.
  assert (Hmd : 8 * (f_bits s / 8) <= f_bits s) by (apply Z.mul_div_le; lia).
  pose proof (Z.pow_pos_nonneg 2 (f_bits s) ltac:(lia) ltac:(lia)) as Hp.
  destruct (Z.eqb_spec j 1) as [->|Hne].
  - replace (f_bits s + 8 - 8 * 1) with (f_bits s) by ring.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    rewrite Z.add_0_l.
    rewrite Z.mod_small by (pose proof (Hin (f_in s)); lia).
    f_equal. lia.
  - assert (Hj2 : 2 <= j) by lia.
    set (e := f_bits s + 8 - 8 * j).
    assert (He0 : 0 <= e) by (unfold e; lia).
    assert (Hsp : 2 ^ f_bits s = 2 ^ e * 2 ^ (8 * (j - 1)))
      by (rewrite <- Z.pow_add_r by (unfold e; lia);
          f_equal; unfold e; ring).
    rewrite Z.shiftr_div_pow2 by exact He0.
    rewrite Hsp.
    replace (f_hold s + f_inbuf c (f_in s) * (2 ^ e * 2 ^ (8 * (j - 1))))
      with (f_hold s + (f_inbuf c (f_in s) * 2 ^ (8 * (j - 1))) * 2 ^ e)
      by ring.
    pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He0) as Hpe.
    rewrite Z.div_add by lia.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    assert (E8 : 8 * (j - 1) = (8 * (j - 1) - 8) + 8) by ring.
    rewrite E8 at 1.
    rewrite Z.pow_add_r by lia.
    assert (Eassoc : f_inbuf c (f_in s) * (2 ^ (8 * (j - 1) - 8) * 2 ^ 8)
                     = f_inbuf c (f_in s) * 2 ^ (8 * (j - 1) - 8) * 2 ^ 8)
      by ring.
    rewrite Eassoc.
    rewrite Z.mod_add by (change (2 ^ 8) with 256; lia).
    specialize (Hal (j - 1) ltac:(lia)).
    rewrite Z.shiftr_div_pow2 in Hal by lia.
    replace (f_bits s - 8 * (j - 1)) with e in Hal by (unfold e; ring).
    change 255 with (Z.ones 8) in Hal. rewrite Z.land_ones in Hal by lia.
    rewrite Hal. f_equal. lia.
Qed.

(** [if_refill15]: two conditional loads.  [f_in] advances by 0 or 2. *)
Lemma w2_refill15_stream : forall c s,
  if_inb c -> if_swf s -> f_in s + 2 <= f_last c + 5 ->
  if_stream c (if_refill15 c s) = if_stream c s.
Proof.
  intros c s Hin Hwf Hlt. unfold if_refill15.
  destruct (Z.ltb_spec (f_bits s) 15) as [H|H]; [|reflexivity].
  rewrite (w2_load1_stream c (if_load1 c s) Hin (w2_load1_swf c s Hin Hwf)
             ltac:(cbn [if_load1 f_in]; lia)).
  apply (w2_load1_stream c s Hin Hwf). lia.
Qed.

Lemma w2_refill15_swf : forall c s,
  if_inb c -> if_swf s -> if_swf (if_refill15 c s).
Proof.
  intros c s Hin Hwf. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); [|exact Hwf].
  apply w2_load1_swf; [exact Hin|]. apply w2_load1_swf; assumption.
Qed.

Lemma w2_refill15_haligned : forall c s,
  if_inb c -> if_swf s -> if_haligned c s ->
  if_haligned c (if_refill15 c s).
Proof.
  intros c s Hin Hwf Hal. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); [|exact Hal].
  apply w2_load1_haligned;
    [exact Hin | apply w2_load1_swf; assumption
    | apply w2_load1_haligned; assumption].
Qed.

Lemma w2_refill15_in : forall c s,
  f_in s <= f_in (if_refill15 c s) <= f_in s + 2.
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); cbn [if_load1 f_in]; lia.
Qed.

Lemma w2_refill15_out : forall c s, f_out (if_refill15 c s) = f_out s.
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); reflexivity.
Qed.

Lemma w2_refill15_buf : forall c s, f_buf (if_refill15 c s) = f_buf s.
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); reflexivity.
Qed.

Lemma w2_refill15_bits : forall c s,
  if_swf s -> 15 <= f_bits (if_refill15 c s).
Proof.
  intros c s (Hb & _). unfold if_refill15.
  destruct (Z.ltb_spec (f_bits s) 15); cbn [if_load1 f_bits]; lia.
Qed.

(** [if_drop] consumes: the stream loses its first [n] bits. *)
Lemma w2_drop_stream : forall n c s,
  0 <= n <= f_bits s -> f_bits s <= 4294967295 -> 0 <= f_hold s ->
  if_stream c (if_drop n s) = skipn (Z.to_nat n) (if_stream c s).
Proof.
  intros n c s [H0 H1] Hc Hh.
  unfold if_stream, if_bytes. cbn [if_drop f_hold f_bits f_in].
  rewrite u32_id by lia.
  rewrite skipn_app, write_bits_length.
  replace (Z.to_nat n - Z.to_nat (f_bits s))%nat with 0%nat by lia.
  cbn [skipn].
  rewrite write_bits_skipn by exact Hh.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.to_nat (f_bits s - n))
    with (Z.to_nat (f_bits s) - Z.to_nat n)%nat by lia.
  replace (2 ^ n) with (2 ^ Z.of_nat (Z.to_nat n))
    by (rewrite Z2Nat.id by lia; reflexivity).
  reflexivity.
Qed.

Lemma w2_drop_swf : forall n s,
  0 <= n <= f_bits s -> f_bits s <= 4294967295 -> if_swf s ->
  if_swf (if_drop n s).
Proof.
  intros n s [H0 H1] Hc (Hb & Hh0 & Hh1).
  rewrite Z.shiftl_1_l in Hh1.
  unfold if_swf. cbn [if_drop f_hold f_bits].
  rewrite u32_id by lia.
  rewrite Z.shiftl_1_l, Z.shiftr_div_pow2 by lia.
  assert (Hsp : 2 ^ f_bits s = 2 ^ n * 2 ^ (f_bits s - n))
    by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 (f_bits s - n) ltac:(lia) ltac:(lia)).
  split; [lia|].
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma w2_drop_haligned : forall n c s,
  0 <= n <= f_bits s -> f_bits s <= 4294967295 ->
  if_haligned c s -> if_haligned c (if_drop n s).
Proof.
  intros n c s [H0 H1] Hc Hal j Hj.
  cbn [if_drop f_hold f_bits f_in] in *.
  rewrite u32_id in Hj by lia.
  assert (Hmd : 8 * ((f_bits s - n) / 8) <= f_bits s - n)
    by (apply Z.mul_div_le; lia).
  rewrite u32_id by lia.
  rewrite Z.shiftr_shiftr by lia.
  replace (n + (f_bits s - n - 8 * j)) with (f_bits s - 8 * j) by ring.
  apply Hal.
  split; [lia|].
  apply Z.le_trans with ((f_bits s - n) / 8); [lia|].
  apply Z.div_le_mono; lia.
Qed.

(** [if_low] reads: the machine's masked value spells the stream head. *)
Lemma w2_low_spells_stream : forall k c s,
  0 <= k <= f_bits s -> 0 <= f_hold s ->
  write_bits (Z.to_nat k) (if_low k s) = firstn (Z.to_nat k) (if_stream c s).
Proof.
  intros k c s [H0 H1] Hh.
  unfold if_low, if_stream.
  rewrite firstn_app, write_bits_length.
  replace (Z.to_nat k - Z.to_nat (f_bits s))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_write_bits by lia.
  rewrite Z.shiftl_1_l.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (E := write_bits_mod_pow2 (Z.to_nat k) k (f_hold s) ltac:(lia)).
  exact E.
Qed.

(* ==========================================================================
   4.  The epilogue: the byte-return trick preserves the stream.
   ========================================================================== *)

(** The arithmetic core: an aligned hold decomposes as its byte-fraction
    followed by the whole bytes it mirrors. *)
Lemma w2_hold_decomp_core :
  forall (l : nat) (r hold pos : Z) (byteat : Z -> Z),
    0 <= r < 8 ->
    0 <= hold < 2 ^ (r + 8 * Z.of_nat l) ->
    (forall i, 0 <= byteat i < 256) ->
    (forall j, 1 <= j <= Z.of_nat l ->
       Z.land (Z.shiftr hold (r + 8 * Z.of_nat l - 8 * j)) 255
       = byteat (pos - j)) ->
    write_bits (Z.to_nat (r + 8 * Z.of_nat l)) hold
    = write_bits (Z.to_nat r) (hold mod 2 ^ r)
      ++ bytes_bits (map (fun k => byteat (pos - Z.of_nat l + Z.of_nat k))
                         (seq 0 l)).
Proof.
  induction l as [|l' IH]; intros r hold pos byteat Hr Hh Hba Hal.
  - cbn [seq map]. rewrite bytes_bits_nil, app_nil_r.
    replace (r + 8 * Z.of_nat 0) with r in * by (cbn; ring).
    symmetry.
    replace (hold mod 2 ^ r) with (hold mod 2 ^ Z.of_nat (Z.to_nat r))
      by (rewrite Z2Nat.id by lia; reflexivity).
    apply write_bits_mod_pow2. lia.
  - set (B' := r + 8 * Z.of_nat l').
    assert (HB'0 : 0 <= B') by (unfold B'; lia).
    assert (HBS : r + 8 * Z.of_nat (S l') = B' + 8)
      by (unfold B'; rewrite Nat2Z.inj_succ; ring).
    rewrite HBS in *.
    pose proof (Z.pow_pos_nonneg 2 B' ltac:(lia) ltac:(lia)) as HpB.
    assert (Hsp8 : 2 ^ (B' + 8) = 2 ^ B' * 256)
      by (rewrite Z.pow_add_r by lia; ring).
    set (v := hold mod 2 ^ B').
    set (w := hold / 2 ^ B').
    assert (Hvw : hold = v + w * 2 ^ B')
      by (unfold v, w; rewrite (Z.div_mod hold (2 ^ B')) at 1 by lia; ring).
    assert (Hv : 0 <= v < 2 ^ B')
      by (unfold v; apply Z.mod_pos_bound; lia).
    assert (Hw : 0 <= w < 256)
      by (unfold w; split;
          [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    (* the top byte is the array byte at pos - 1 *)
    assert (Hw1 : w = byteat (pos - 1)).
    { specialize (Hal 1 ltac:(lia)).
      replace (B' + 8 - 8 * 1) with B' in Hal by ring.
      rewrite Z.shiftr_div_pow2 in Hal by lia.
      change 255 with (Z.ones 8) in Hal.
      rewrite Z.land_ones in Hal by lia.
      rewrite Z.mod_small in Hal by exact Hw.
      exact Hal. }
    (* split the write at B' *)
    replace (Z.to_nat (B' + 8)) with (Z.to_nat B' + 8)%nat by lia.
    rewrite Hvw at 1.
    replace (2 ^ B') with (2 ^ Z.of_nat (Z.to_nat B'))
      by (rewrite Z2Nat.id by lia; reflexivity).
    rewrite write_bits_split by (rewrite Z2Nat.id by lia; exact Hv).
    (* recurse on the low part *)
    assert (Hal' : forall j, 1 <= j <= Z.of_nat l' ->
        Z.land (Z.shiftr v (r + 8 * Z.of_nat l' - 8 * j)) 255
        = byteat (pos - 1 - j)).
    { intros j Hj.
      fold B'. unfold v.
      assert (Hjs : 0 <= B' - 8 * j) by (unfold B'; lia).
      assert (E := w2_low8_mod_shift hold B' (B' - 8 * j)
                     Hjs ltac:(lia)).
      rewrite E.
      specialize (Hal (j + 1) ltac:(lia)).
      replace (B' + 8 - 8 * (j + 1)) with (B' - 8 * j) in Hal by ring.
      rewrite Hal.
      f_equal. lia. }
    assert (Hv' : 0 <= v < 2 ^ (r + 8 * Z.of_nat l'))
      by (unfold B' in Hv; exact Hv).
    assert (IHi := IH r v (pos - 1) byteat Hr Hv' Hba Hal').
    fold B' in IHi.
    rewrite IHi.
    (* reassemble *)
    replace (v mod 2 ^ r) with (hold mod 2 ^ r).
    2:{ transitivity (v mod 2 ^ Z.of_nat (Z.to_nat r));
          [|rewrite Z2Nat.id by lia; reflexivity].
        transitivity (hold mod 2 ^ Z.of_nat (Z.to_nat r));
          [rewrite Z2Nat.id by lia; reflexivity|].
        apply write_bits_inj_mod.
        unfold v. symmetry.
        apply write_bits_mod_pow2. unfold B'; lia. }
    rewrite Hw1, <- byte_bits_write_bits.
    rewrite seq_S, map_app, w2_bytes_bits_app.
    cbn [map]. rewrite bytes_bits_cons, bytes_bits_nil, app_nil_r.
    rewrite <- !app_assoc.
    do 2 f_equal.
    + f_equal. apply map_ext; intro k. f_equal. lia.
    + f_equal. f_equal. lia.
Qed.

(** The writeback record's stream equals the walk's: [if_finish] returns
    the whole bytes of [hold] to the input and keeps the fraction. *)
Lemma w2_finish_stream : forall c s e,
  if_inb c -> if_swf s -> if_haligned c s ->
  f_bits s <= 4294967295 ->
  f_in s <= f_last c + 5 ->
  0 <= f_last c + 5 - (f_in s - f_bits s / 8) <= 4294967295 ->
  br_stream {| br_in := f_inbuf c;
               br_have := y_avail_in (if_finish c s e);
               br_next := y_in (if_finish c s e);
               br_hold := y_hold (if_finish c s e);
               br_bits := y_bits (if_finish c s e) |}
  = if_stream c s.
Proof.
  intros c s e Hin (Hb & Hh0 & Hh1) Hal Hcap Hle Hav.
  rewrite Z.shiftl_1_l in Hh1.
  unfold if_finish. cbn [y_in y_hold y_bits y_avail_in].
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8.
  rewrite (Z.shiftl_mul_pow2 (f_bits s / 8) 3) by lia.
  change (2 ^ 3) with 8.
  assert (Hmd : 8 * (f_bits s / 8) <= f_bits s) by (apply Z.mul_div_le; lia).
  assert (Hd0 : 0 <= f_bits s / 8) by (apply Z.div_pos; lia).
  assert (Hmod : f_bits s - f_bits s / 8 * 8 = f_bits s mod 8)
    by (rewrite Z.mod_eq by lia; ring).
  rewrite Hmod.
  pose proof (Z.mod_pos_bound (f_bits s) 8 ltac:(lia)) as Hm8.
  rewrite (u32_id (f_bits s mod 8)) by lia.
  set (i := f_in s - f_bits s / 8).
  (* both avail branches are last + 5 - i *)
  assert (Hava : (if Z.ltb i (f_last c)
                  then 5 + (f_last c - i) else 5 - (i - f_last c))
                 = f_last c + 5 - i)
    by (destruct (Z.ltb i (f_last c)); ring).
  rewrite Hava, u32_id by lia.
  unfold br_stream, br_bytes. cbn [br_hold br_bits br_in br_next br_have].
  (* split the byte window at the cursor *)
  replace (Z.to_nat (f_last c + 5 - i))
    with (Z.to_nat (f_bits s / 8) + Z.to_nat (f_last c + 5 - f_in s))%nat
    by (unfold i; lia).
  rewrite seq_app, map_app, w2_bytes_bits_app.
  rewrite (w2_map_seq_shift _ _ (Z.to_nat (f_bits s / 8))).
  unfold if_stream.
  (* the decomposition of the hold *)
  assert (HD := w2_hold_decomp_core (Z.to_nat (f_bits s / 8))
                  (f_bits s mod 8) (f_hold s) (f_in s) (f_inbuf c)
                  ltac:(lia)).
  replace (f_bits s mod 8 + 8 * Z.of_nat (Z.to_nat (f_bits s / 8)))
    with (f_bits s) in HD
    by (rewrite Z2Nat.id by lia; rewrite Z.mod_eq by lia; ring).
  rewrite (HD ltac:(lia) Hin).
  2:{ intros j Hj. apply Hal. lia. }
  rewrite <- !app_assoc.
  f_equal.
  { change (2 ^ (f_bits s mod 8)) with (2 ^ (f_bits s mod 8)).
    rewrite Z.shiftl_1_l.
    replace (2 ^ (f_bits s mod 8) - 1) with (Z.ones (f_bits s mod 8))
      by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. reflexivity. }
  f_equal.
  { f_equal. apply map_ext; intro k. f_equal.
    unfold i. lia. }
  unfold if_bytes. f_equal.
  apply map_ext; intro k. f_equal.
  unfold i. lia.
Qed.

(** The written-back reader is well-formed. *)
Lemma w2_finish_br_wf : forall c s e,
  if_inb c -> if_swf s ->
  f_bits s <= 4294967295 ->
  0 <= f_last c + 5 - (f_in s - f_bits s / 8) <= 4294967295 ->
  br_wf {| br_in := f_inbuf c;
           br_have := y_avail_in (if_finish c s e);
           br_next := y_in (if_finish c s e);
           br_hold := y_hold (if_finish c s e);
           br_bits := y_bits (if_finish c s e) |}.
Proof.
  intros c s e Hin (Hb & Hh0 & Hh1) Hcap Hav.
  unfold if_finish. cbn [y_in y_hold y_bits y_avail_in].
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8.
  rewrite (Z.shiftl_mul_pow2 (f_bits s / 8) 3) by lia.
  change (2 ^ 3) with 8.
  assert (Hmd : 8 * (f_bits s / 8) <= f_bits s) by (apply Z.mul_div_le; lia).
  assert (Hd0 : 0 <= f_bits s / 8) by (apply Z.div_pos; lia).
  assert (Hmod : f_bits s - f_bits s / 8 * 8 = f_bits s mod 8)
    by (rewrite Z.mod_eq by lia; ring).
  rewrite Hmod.
  pose proof (Z.mod_pos_bound (f_bits s) 8 ltac:(lia)) as Hm8.
  rewrite (u32_id (f_bits s mod 8)) by lia.
  set (i := f_in s - f_bits s / 8).
  assert (Hava : (if Z.ltb i (f_last c)
                  then 5 + (f_last c - i) else 5 - (i - f_last c))
                 = f_last c + 5 - i)
    by (destruct (Z.ltb i (f_last c)); ring).
  rewrite Hava, u32_id by lia.
  unfold br_wf. cbn [br_hold br_bits br_in br_next br_have].
  split; [lia|].
  split.
  { rewrite !Z.shiftl_1_l.
    replace (2 ^ (f_bits s mod 8) - 1) with (Z.ones (f_bits s mod 8))
      by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia. }
  split; [lia | exact Hin].
Qed.

(** [if_finish]'s remaining projections, for the writeback bookkeeping. *)
Lemma w2_finish_out : forall c s e, y_out (if_finish c s e) = f_out s.
Proof. reflexivity. Qed.
Lemma w2_finish_buf : forall c s e, y_buf (if_finish c s e) = f_buf s.
Proof. reflexivity. Qed.
Lemma w2_finish_exit : forall c s e, y_exit (if_finish c s e) = e.
Proof. reflexivity. Qed.

(* ==========================================================================
   5.  RESTORE/LOAD projection block (all reflexivity; the setters are
       flat record rebuilds).
   ========================================================================== *)

Lemma w2_restore_br : forall q, q_br (q_restore q) = q_br q.
Proof. reflexivity. Qed.
Lemma w2_restore_ob : forall q, q_ob (q_restore q) = q_ob q.
Proof. reflexivity. Qed.
Lemma w2_restore_z : forall q, q_z (q_restore q) = q_z q.
Proof. reflexivity. Qed.
Lemma w2_restore_in : forall q, q_in (q_restore q) = q_in q.
Proof. reflexivity. Qed.
Lemma w2_restore_out : forall q, q_out (q_restore q) = q_out q.
Proof. reflexivity. Qed.
Lemma w2_restore_ret : forall q, q_ret (q_restore q) = q_ret q.
Proof. reflexivity. Qed.
Lemma w2_restore_hold : forall q,
  s_hold (q_st (q_restore q)) = br_hold (q_br q).
Proof. reflexivity. Qed.
Lemma w2_restore_bits : forall q,
  s_bits (q_st (q_restore q)) = br_bits (q_br q).
Proof. reflexivity. Qed.
Lemma w2_restore_tab : forall q, s_tab (q_st (q_restore q)) = s_tab (q_st q).
Proof. reflexivity. Qed.
Lemma w2_restore_win : forall q, s_win (q_st (q_restore q)) = s_win (q_st q).
Proof. reflexivity. Qed.
Lemma w2_restore_hdr : forall q, s_hdr (q_st (q_restore q)) = s_hdr (q_st q).
Proof. reflexivity. Qed.
Lemma w2_restore_cur : forall q, s_cur (q_st (q_restore q)) = s_cur (q_st q).
Proof. reflexivity. Qed.
Lemma w2_restore_bld : forall q, s_bld (q_st (q_restore q)) = s_bld (q_st q).
Proof. reflexivity. Qed.

Lemma w2_load_st : forall q, q_st (q_load q) = q_st q.
Proof. reflexivity. Qed.
Lemma w2_load_ob : forall q, q_ob (q_load q) = q_ob q.
Proof. reflexivity. Qed.
Lemma w2_load_z : forall q, q_z (q_load q) = q_z q.
Proof. reflexivity. Qed.
Lemma w2_load_in : forall q, q_in (q_load q) = q_in q.
Proof. reflexivity. Qed.
Lemma w2_load_out : forall q, q_out (q_load q) = q_out q.
Proof. reflexivity. Qed.
Lemma w2_load_ret : forall q, q_ret (q_load q) = q_ret q.
Proof. reflexivity. Qed.
Lemma w2_load_hold : forall q, br_hold (q_br (q_load q)) = s_hold (q_st q).
Proof. reflexivity. Qed.
Lemma w2_load_bits : forall q, br_bits (q_br (q_load q)) = s_bits (q_st q).
Proof. reflexivity. Qed.
Lemma w2_load_next : forall q, br_next (q_br (q_load q)) = br_next (q_br q).
Proof. reflexivity. Qed.
Lemma w2_load_have : forall q, br_have (q_br (q_load q)) = br_have (q_br q).
Proof. reflexivity. Qed.
Lemma w2_load_arr : forall q, br_in (q_br (q_load q)) = br_in (q_br q).
Proof. reflexivity. Qed.

Print Assumptions w2_entry_stream.
Print Assumptions w2_load1_stream.
Print Assumptions w2_drop_stream.
Print Assumptions w2_low_spells_stream.
Print Assumptions w2_hold_decomp_core.
Print Assumptions w2_finish_stream.
Print Assumptions w2_finish_br_wf.
