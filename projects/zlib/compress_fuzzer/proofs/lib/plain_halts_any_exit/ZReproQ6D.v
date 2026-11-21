(** * ZReproQ6D — Q6 leg (d): the stored path vs [decode_stored].

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  Four pieces:

    - [zr_bytebits_align]: the model's BYTEBITS is the declarative
      [align_byte] on the stream view — the byte-boundary the stored
      header (and later the trailer) reads from.
    - [zr_bytes_split] / [zr_ob_append]: byte-window plumbing — dropping
      [k] bytes from the reader splits the byte view, and a [zcopy] into
      the output buffer extends the output slice by exactly the copied
      window.
    - [zr_stored_sound]: a continuing [inf_STORED] either goes BAD
      (LEN/NLEN mismatch — absorbed) or reads the two 16-bit fields the
      declarative [decode_stored] reads, with the same values, the same
      complement identity, and lands (through the [inf_COPY_]
      fallthrough) in the copy loop with [length] pinned and the
      accumulator cleared.
    - [zr_copy_step]: one copy trip — exit to [M_TYPE] at length 0,
      starvation leave (absorbed), or a [c2]-byte transfer whose output
      slice grows by exactly the next [c2] input bytes while the stream
      drops the same bytes.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A ZReproQ6B.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  BYTEBITS is align_byte.
   ========================================================================== *)

Lemma zr_bytebits_align : forall b,
  br_wf b ->
  br_stream (br_bytebits b) = align_byte (br_stream b).
Proof.
  intros b Hwf.
  pose proof Hwf as (Hb & Hh & Hv & Hr).
  unfold align_byte.
  assert (HL : (length (br_stream b) mod 8)%nat = Z.to_nat (br_bits b mod 8)).
  { pose proof (br_stream_length b Hwf) as HLen.
    assert (length (br_stream b) = Z.to_nat (br_bits b + 8 * br_have b))%nat
      by lia.
    rewrite H.
    rewrite Z2Nat.inj_add by lia.
    rewrite Nat.Div0.add_mod by lia.
    replace (Z.to_nat (8 * br_have b) mod 8)%nat with 0%nat
      by (replace (Z.to_nat (8 * br_have b)) with (Z.to_nat (br_have b) * 8)%nat
            by lia;
          now rewrite Nat.Div0.mod_mul).
    rewrite Nat.add_0_r, Nat.Div0.mod_mod.
    change 8%nat with (Z.to_nat 8).
    rewrite <- Z2Nat.inj_mod by lia. reflexivity. }
  rewrite HL.
  unfold br_bytebits.
  assert (Hk7 : Z.land (br_bits b) 7 = br_bits b mod 8).
  { replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. reflexivity. }
  rewrite Hk7.
  set (k := br_bits b mod 8).
  assert (Hk : 0 <= k <= br_bits b)
    by (pose proof (Z.mod_pos_bound (br_bits b) 8 ltac:(lia));
        pose proof (Z.mod_le (br_bits b) 8 ltac:(lia) ltac:(lia)); lia).
  pose proof (br_read_agree k b Hwf Hk) as R.
  apply read_bits_rem in R.
  rewrite <- R. reflexivity.
Qed.

(* ==========================================================================
   2.  Byte-window plumbing.
   ========================================================================== *)

Lemma zr_map_seq_shift : forall (A : Type) (f : nat -> A) s n,
  map f (seq s n) = map (fun m => f (s + m)%nat) (seq 0 n).
Proof.
  intros A f s n. revert s. induction n as [|n IH]; intro s; [reflexivity|].
  cbn [seq map]. rewrite Nat.add_0_r. f_equal.
  rewrite IH. rewrite <- seq_shift, map_map.
  apply map_ext. intro m. f_equal. lia.
Qed.

(** Dropping [k] bytes: the byte view splits at [k]. *)
Lemma zr_bytes_split : forall (arr : zarr) (have next k : Z),
  0 <= k <= have ->
  map (fun m => arr (next + Z.of_nat m)) (seq 0 (Z.to_nat have))
  = map (fun m => arr (next + Z.of_nat m)) (seq 0 (Z.to_nat k))
    ++ map (fun m => arr (next + k + Z.of_nat m)) (seq 0 (Z.to_nat (have - k))).
Proof.
  intros arr have next k Hk.
  replace (Z.to_nat have)
    with (Z.to_nat k + Z.to_nat (have - k))%nat by lia.
  rewrite seq_app, map_app. f_equal.
  rewrite zr_map_seq_shift. apply map_ext. intro m.
  f_equal. lia.
Qed.

(** The output slice after a [zcopy] at the write head: the old slice,
    then exactly the copied window. *)
Lemma zr_ob_append : forall (o : OB) (src : zarr) (si c2 : Z),
  0 <= o_put o -> 0 <= c2 ->
  ob_slice {| o_buf := zcopy (Z.to_nat c2) (o_buf o) (o_put o) src si;
              o_put := o_put o + c2;
              o_left := o_left o - c2 |} 0 (o_put o + c2)
  = ob_slice o 0 (o_put o)
    ++ map (fun m => src (si + Z.of_nat m)) (seq 0 (Z.to_nat c2)).
Proof.
  intros o src si c2 Hp Hc.
  unfold ob_slice. cbn [o_buf o_put].
  replace (Z.to_nat (o_put o + c2))
    with (Z.to_nat (o_put o) + Z.to_nat c2)%nat by lia.
  rewrite seq_app, map_app. f_equal.
  - apply map_ext_in. intros m Hm. apply in_seq in Hm.
    apply zcopy_miss. intros j Hj. lia.
  - rewrite zr_map_seq_shift. apply map_ext_in. intros m Hm.
    apply in_seq in Hm.
    match goal with |- zcopy _ _ _ _ _ ?i = _ =>
      replace i with (o_put o + Z.of_nat m) by lia end.
    apply zcopy_hit. lia.
Qed.

(* ==========================================================================
   3.  The stored header.
   ========================================================================== *)

Lemma zr_stored_sound : forall c q,
  n_flush c <> Z_TREES ->
  br_wf (q_br q) ->
  (exists b, inf_STORED c q = InfLeave (qset_br q b))          (* starved *)
  \/ (exists b, inf_STORED c q
                = InfCont (qbad (qset_br q b) MSG_STORED_LEN)) (* absorbed *)
  \/ (exists b len r1,
        read_bits 16%nat (align_byte (br_stream (q_br q))) = Some (len, r1)
        /\ read_bits 16%nat r1
           = Some (Z.lxor len 65535, br_stream (br_initbits b))
        /\ 0 <= len < 65536
        /\ br_wf (br_initbits b)
        /\ br_bits (br_initbits b) = 0
        /\ inf_STORED c q
           = inf_COPY_ (qmode (qset_br
                (qset_st q (set_length (q_st q) len))
                (br_initbits b)) M_COPY_)).
Proof.
  intros c q HF Hwf.
  unfold inf_STORED. cbv zeta.
  assert (Hwfa : br_wf (br_bytebits (q_br q))).
  { unfold br_bytebits. apply br_wf_dropbits; [exact Hwf|].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    destruct (Z.leb_spec 8 (br_bits (q_br q)));
      [ lia | rewrite Z.mod_small by lia; lia ]. }
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:EN;
    [| left; eexists; reflexivity].
  destruct (inf_nb_ok 32 (br_bytebits (q_br q)) b Hwfa ltac:(lia) EN)
    as (ES & Hwfb & Hb32).
  destruct (negb (Z.land (br_hold b) 65535
                  =? Z.lxor (Z.shiftr (br_hold b) 16) 65535)) eqn:ECHK.
  { right; left. eexists. reflexivity. }
  right; right.
  apply negb_false_iff, Z.eqb_eq in ECHK.
  (* the aligned entry has bits in 8Z, so NEEDBITS(32) stops at exactly 32 *)
  assert (Hb0 : (br_bits (br_bytebits (q_br q))) mod 8 = 0).
  { unfold br_bytebits, br_dropbits. cbn [br_bits].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Zminus_mod, Z.mod_mod by lia.
    rewrite Z.sub_diag. reflexivity. }
  assert (Hbeq : br_bits b = 32).
  { pose proof (Z.div_mod (br_bits (br_bytebits (q_br q))) 8
                  ltac:(lia)) as HD.
    rewrite Hb0, Z.add_0_r in HD.
    destruct (zr_nb_bits 32 (br_bytebits (q_br q)) b EN)
      as [HE | (Hlt & k & Hk)];
      destruct Hwfa as (HbA & _); destruct Hwfb as (HbB & _); lia. }
  (* the two declarative reads *)
  pose proof (br_read_agree 16 b Hwfb ltac:(lia)) as R1.
  change (Z.to_nat 16) with 16%nat in R1.
  assert (Hwfd : br_wf (br_dropbits 16 b))
    by (apply br_wf_dropbits; [exact Hwfb | lia]).
  pose proof (br_read_agree 16 (br_dropbits 16 b) Hwfd
                ltac:(rewrite br_dropbits_bits; lia)) as R2.
  change (Z.to_nat 16) with 16%nat in R2.
  set (len := br_bits_of 16 b).
  assert (Hlen : 0 <= len < 65536).
  { unfold len, br_bits_of.
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    apply Z.mod_pos_bound. lia. }
  exists b, len, (br_stream (br_dropbits 16 b)).
  assert (Hland : Z.land (br_hold b) 65535 = len).
  { unfold len, br_bits_of. f_equal. }
  assert (Hnlen : br_bits_of 16 (br_dropbits 16 b) = Z.lxor len 65535).
  { unfold br_bits_of, br_dropbits. cbn [br_hold].
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    rewrite Z.mod_small
      by (rewrite Z.shiftr_div_pow2 by lia;
          split; [apply Z.div_pos; lia
                 | apply Z.div_lt_upper_bound; lia]).
    rewrite Hland in ECHK. rewrite ECHK.
    now rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. }
  split; [| split; [| split; [exact Hlen | split; [| split]]]].
  - (* first read, on the aligned stream *)
    rewrite <- (zr_bytebits_align (q_br q) Hwf), <- ES.
    rewrite R1. now fold len.
  - (* second read; the exit stream is INITBITS' byte tail *)
    rewrite R2. rewrite Hnlen. do 2 f_equal.
    (* stream (dropbits 32 b) = stream (initbits b): both are the byte
       tail — dropbits 32 leaves bits = 0 (Hbeq) with hold = hold/2^32 = 0
       (wf), initbits zeroes both; byte lists agree definitionally *)
    unfold br_stream, br_dropbits, br_initbits;
      cbn [br_bits br_hold].
    rewrite Hbeq.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    replace (32 - 32) with 0 by lia.
    replace (Z.shiftr (br_hold b) 32) with 0
      by (rewrite Z.shiftr_div_pow2 by lia; symmetry;
          apply Z.div_small; lia).
    reflexivity.
  - (* wf of the cleared reader *)
    destruct Hwfb as (_ & _ & Hv & Hr).
    unfold br_initbits, br_wf; cbn [br_bits br_hold br_have br_in].
    rewrite Z.shiftl_1_l.
    repeat split; try lia;
      try (match goal with |- context [br_in b ?k] =>
             specialize (Hr k); lia end).
  - reflexivity.
  - (* the arm equation: Z_TREES leave dead, set_length value bridged *)
    rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF).
    cbv beta iota.
    (* Z.land (u32 hold) 65535 = len: u32 is the identity under wf *)
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    unfold u32. rewrite Z.mod_small by lia.
    rewrite Hland. reflexivity.
Qed.

(* ==========================================================================
   4.  One copy trip.  The [< 65536] length premise is the stored-header
      bound [zr_stored_sound] establishes; reader/output well-formedness
      come from the walk.
   ========================================================================== *)

Lemma zr_copy_step : forall q,
  br_wf (q_br q) ->
  0 <= o_left (q_ob q) ->
  0 <= o_put (q_ob q) ->
  0 <= u_length (s_cur (q_st q)) < 65536 ->
  (u_length (s_cur (q_st q)) = 0
     /\ inf_COPY q = InfCont (qmode q M_TYPE))
  \/ inf_COPY q = InfLeave q                                    (* absorbed *)
  \/ (exists c2 q',
        0 < c2 <= u_length (s_cur (q_st q))
        /\ c2 <= br_have (q_br q)
        /\ c2 <= o_left (q_ob q)
        /\ inf_COPY q = InfCont q'
        /\ u_length (s_cur (q_st q')) = u_length (s_cur (q_st q)) - c2
        /\ h_mode (s_hdr (q_st q')) = h_mode (s_hdr (q_st q))
        /\ br_hold (q_br q') = br_hold (q_br q)
        /\ br_bits (q_br q') = br_bits (q_br q)
        /\ br_bytes (q_br q) = (map (fun m => br_in (q_br q)
                                (br_next (q_br q) + Z.of_nat m))
                                (seq 0 (Z.to_nat c2)))
                               ++ br_bytes (q_br q')
        /\ br_wf (q_br q')
        /\ o_put (q_ob q') = o_put (q_ob q) + c2
        /\ o_left (q_ob q') = o_left (q_ob q) - c2
        /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
           = ob_slice (q_ob q) 0 (o_put (q_ob q))
             ++ map (fun m => br_in (q_br q)
                      (br_next (q_br q) + Z.of_nat m))
                    (seq 0 (Z.to_nat c2))).
Proof.
  intros q Hwf Hleft Hput Hcp.
  pose proof Hwf as (Hb & Hh & Hv & Hr).
  unfold inf_COPY. cbv zeta.
  destruct (Z.eqb_spec (u_length (s_cur (q_st q))) 0) as [E0|N0].
  { left. split; [exact E0 | reflexivity]. }
  set (cp := u_length (s_cur (q_st q))) in *.
  set (c1 := if br_have (q_br q) <? cp then br_have (q_br q) else cp).
  set (c2 := if o_left (q_ob q) <? c1 then o_left (q_ob q) else c1).
  destruct (Z.eqb_spec c2 0) as [Ez|Nz].
  { right; left. reflexivity. }
  right; right.
  assert (Hc1 : 0 <= c1 <= cp /\ c1 <= br_have (q_br q)).
  { unfold c1. destruct (Z.ltb_spec (br_have (q_br q)) cp); lia. }
  assert (Hc2 : 0 < c2 <= c1 /\ c2 <= o_left (q_ob q)).
  { unfold c2. destruct (Z.ltb_spec (o_left (q_ob q)) c1); lia. }
  exists c2. eexists.
  unfold qset_ob, qset_br, qset_st;
    cbn [q_st q_br q_ob].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [reflexivity|].
  cbn [q_st q_br q_ob s_cur br_hold br_bits br_have br_next br_in
       o_put o_buf o_left].
  split.
  { (* length: u32 collapses under the stored bound *)
    replace (u_length (s_cur (set_length (q_st q) (u32 (cp - c2)))))
      with (u32 (cp - c2)) by reflexivity.
    unfold u32. apply Z.mod_small. lia. }
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  { (* byte split *)
    replace (br_bytes {| br_in := br_in (q_br q);
                         br_have := br_have (q_br q) - c2;
                         br_next := br_next (q_br q) + c2;
                         br_hold := br_hold (q_br q);
                         br_bits := br_bits (q_br q) |})
      with (map (fun m => br_in (q_br q)
                   (br_next (q_br q) + c2 + Z.of_nat m))
                (seq 0 (Z.to_nat (br_have (q_br q) - c2))))
      by reflexivity.
    apply (zr_bytes_split (br_in (q_br q)) (br_have (q_br q))
             (br_next (q_br q)) c2); lia. }
  split.
  { (* reader wf: only have/next moved *)
    unfold br_wf; cbn [br_bits br_hold br_have br_in].
    rewrite Z.shiftl_1_l in *.
    repeat split; try lia;
      try (match goal with |- context [br_in (q_br q) ?k] =>
             specialize (Hr k); lia end). }
  split; [reflexivity|].
  split; [reflexivity|].
  (* the slice extension *)
  apply (zr_ob_append (q_ob q) (br_in (q_br q)) (br_next (q_br q)) c2);
    lia.
Qed.

Print Assumptions zr_stored_sound.
Print Assumptions zr_copy_step.
