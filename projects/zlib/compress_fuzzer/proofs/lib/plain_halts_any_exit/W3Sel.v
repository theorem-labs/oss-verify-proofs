(** * W3Sel — the per-trip classification at the ROOT-ONLY tables with
      SELECTION-usable BAD arms (FIXED leg, q7-decode fixsel fork,
      2026-08-21, OFF-TREE SCRATCH — PROVISIONAL: statements owner
      an earlier development run, Gap7FixSel.v md5 ).

    Mirror of the landed [W3Trip] (proof bodies verbatim) with:
    - TWO new premises [zr_inv_len]/[zr_inv_dist] (FixSelCore): at the
      fixed tables an invalid-op ent at a coded symbol forces the
      declarative base-table lookup to be None (discharged at the leg
      instantiation from ownership alone via [zr_invl_own]/[zr_invd_own]);
    - ONE new premise [f_beg c = 0] (true at the leg instantiation:
      W4's Ebeg + Hstart), which makes the machine's too-far test the
      model's [dist > out] test (the W3DSel move);
    - every [BodyBad] arm carries the declarative-failure payload
      (arm shapes mirror the dyn W3DSel/Gap7TripSel).

    The root read needs NO enrichment on the fixed leg: [w3_root_read]
    is total (every code fits the root — no marker/pointer arms), so the
    only BAD sources are LEN-invalid (286/287), DIST-invalid (30/31) and
    DISTANCE-TOO-FAR.

    Reused verbatim FROM the landed [W3Trip] (not duplicated): the
    root/extra reads, the put/drop/copy frame lemmas, [w3_dist_tail]'s
    good arms.

    PA-EXPORTS: w3sel_trip (w3sel_dist_tail is its internal stage).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import FixSelCore.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma w3sel_dist_tail :
  forall c (s2 : IfSt) (rootD : Z) (dl : list nat) (entd : nat -> Code)
         (len : Z) (len_spec : nat) (k : nat),
    ValidLengths dl 15%nat ->
    w3_root_own (f_dcode c) rootD dl 15%nat entd ->
    w3_dist_ents dl entd ->
    zr_inv_dist dl entd ->
    0 < rootD <= 15 ->
    f_dmask c = Z.shiftl 1 rootD - 1 ->
    f_whave c = 0 -> f_sane c <> 0 -> if_inb c ->
    if_swf s2 -> if_haligned c s2 -> f_bits s2 <= 60 ->
    f_in s2 + 3 <= f_last c + 5 ->
    (f_bits s2 < 4 -> f_in s2 + 4 <= f_last c + 5) ->
    0 <= f_beg c <= f_out s2 -> f_beg c = 0 ->
    f_out s2 <= 4294967295 ->
    len = Z.of_nat len_spec ->
    (3 <= len_spec)%nat -> (len_spec <= 258)%nat ->
    match if_dodist (S k) c len (if_refill15 c s2)
            (f_dcode c (Z.land (f_hold (if_refill15 c s2)) (f_dmask c)))
    with
    | BodyOk s' =>
        exists (dsym : nat) (dist_spec : nat) (r3 r4 : list bool),
          hdecode (code_table dl 15%nat) (if_stream c s2) = Some (dsym, r3)
          /\ read_extra dist_base dist_extra dsym r3 = Some (dist_spec, r4)
          /\ if_stream c s' = r4
          /\ (1 <= dist_spec)%nat
          /\ Z.of_nat dist_spec <= f_out s2
          /\ zslice (f_buf s') 0 (f_out s')
             = zslice (f_buf s2) 0 (f_out s2)
               ++ lz_copy (zslice (f_buf s2) 0 (f_out s2)) len_spec dist_spec
          /\ f_out s' = f_out s2 + len
          /\ if_swf s' /\ if_haligned c s' /\ f_bits s' <= 60
          /\ f_in s2 <= f_in s'
          /\ f_in s' <= f_last c + 5
          /\ f_in s2 - f_bits s2 / 8 <= f_in s' - f_bits s' / 8
    | BodyEob _ => False
    | BodyBad _ _ =>
        (exists (dsym' : nat) (r3 : list bool),
            hdecode (code_table dl 15%nat) (if_stream c s2)
            = Some (dsym', r3)
            /\ read_extra dist_base dist_extra dsym' r3 = None)
        \/ (exists (dsym' : nat) (r3 : list bool) (dist_spec' : nat)
                   (r4 : list bool),
            hdecode (code_table dl 15%nat) (if_stream c s2)
            = Some (dsym', r3)
            /\ read_extra dist_base dist_extra dsym' r3
               = Some (dist_spec', r4)
            /\ Z.of_nat dist_spec' > f_out s2)
    | BodyFuel => True
    end.
Proof.
  intros c s2 rootD dl entd len len_spec k HVd HownD Hde Hinvd HrD EmD
         Hwh Hsn Hinb Hsw2 Hal2 Hcap2 Hrm3 Hrm4 Hbeg Hbeg0 Hocap Elen
         Hl3 Hl258.
  pose proof Hsw2 as (Hb2 & Hh2 & _).
  set (s3 := if_refill15 c s2).
  assert (Hst3 : if_stream c s3 = if_stream c s2)
    by (apply w2_refill15_stream; auto; lia).
  assert (Hsw3 : if_swf s3) by (apply w2_refill15_swf; auto).
  pose proof Hsw3 as (Hb3 & Hh3 & _).
  assert (Hal3 : if_haligned c s3) by (apply w2_refill15_haligned; auto).
  assert (Hb15 : 15 <= f_bits s3) by (apply w2_refill15_bits; auto).
  assert (Hbuf3 : f_buf s3 = f_buf s2) by apply w2_refill15_buf.
  assert (Hout3 : f_out s3 = f_out s2) by apply w2_refill15_out.
  pose proof (w3_refill15_facts c s2) as Hrf2. fold s3 in Hrf2.
  assert (Hcap3 : f_bits s3 <= 60)
    by (destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  destruct (w3_root_read (f_dcode c) rootD dl entd (f_dmask c) c s3
              HVd HownD HrD EmD Hsw3 ltac:(lia))
    as (dsym & cwD & HcfD & HTD & HcbD & HlenD & HhdD).
  rewrite Hst3 in HhdD.
  rewrite if_dodist_S. cbv zeta.
  rewrite HTD, HcbD.
  set (s1' := if_drop (Z.of_nat (length cwD)) s3).
  assert (Hds1 : if_stream c s1' = skipn (length cwD) (if_stream c s2)).
  { unfold s1'.
    rewrite (w2_drop_stream (Z.of_nat (length cwD)) c s3)
      by (auto; lia).
    rewrite Hst3, Nat2Z.id. reflexivity. }
  assert (Hsw1' : if_swf s1')
    by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1' as (Hb1' & Hh1' & _).
  assert (Hal1' : if_haligned c s1')
    by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1' : f_buf s1' = f_buf s2)
    by (unfold s1'; rewrite w3_drop_buf; exact Hbuf3).
  assert (Hout1' : f_out s1' = f_out s2)
    by (unfold s1'; rewrite w3_drop_out; exact Hout3).
  assert (Hin1' : f_in s1' = f_in s3) by apply w3_drop_in.
  assert (Hbits1' : f_bits s1' = f_bits s3 - Z.of_nat (length cwD))
    by (apply w3_drop_bits; lia).
  destruct (Hde _ _ HcfD) as
    [ (b0' & e0' & Hnb' & Hne' & Hop' & H64' & H15' & Hval' & Hb1d & He13')
    | (H64d & H16d) ].
  2:{ assert (E16 : (Z.land (c_op (entd dsym)) 16 =? 0) = true)
        by (apply Z.eqb_eq; exact H16d).
      rewrite E16. cbn [negb].
      assert (E64 : (Z.land (c_op (entd dsym)) 64 =? 0) = false)
        by (apply Z.eqb_neq; exact H64d).
      rewrite E64.
      cbv iota.
      left.
      exists dsym, (skipn (length cwD) (if_stream c s2)).
      split; [exact HhdD|].
      pose proof (Hinvd dsym cwD HcfD H64d) as HND.
      unfold read_extra. rewrite HND.
      destruct (nth_error dist_extra dsym); reflexivity. }
  pose proof (w3_land16 (Z.of_nat e0') ltac:(lia)) as (L16' & _ & _ & _).
  assert (E16 : (Z.land (c_op (entd dsym)) 16 =? 0) = false)
    by (rewrite Hop', L16'; reflexivity).
  rewrite E16. cbn [negb].
  rewrite H15'.
  set (sa2 := if Z.ltb (f_bits s1') (Z.of_nat e0')
              then (if Z.ltb (f_bits (if_load1 c s1')) (Z.of_nat e0')
                    then if_load1 c (if_load1 c s1') else if_load1 c s1')
              else s1').
  assert (Hroom1 : f_bits s1' < Z.of_nat e0' -> f_in s1' < f_last c + 5).
  { intros _. rewrite Hin1'.
    destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]. }
  assert (Hroom2 : f_bits s1' + 8 < Z.of_nat e0' ->
                   f_in s1' + 1 < f_last c + 5).
  { intros Hb. rewrite Hin1'.
    destruct Hrf2 as [(A&B&C)|(A&E)].
    - assert (f_bits s2 < 4) by lia.
      pose proof (Hrm4 ltac:(assumption)). lia.
    - rewrite E. lia. }
  destruct (w3_extra2 c s1' (Z.of_nat e0') sa2 Hinb Hsw1' Hal1'
              ltac:(lia) ltac:(lia) Hroom1 Hroom2 eq_refl)
    as (Hrb2 & Hds2 & Hsw3' & Hal3' & Hbufa2 & Houta2 & Hlow2 & Hacc2).
  set (s3' := if_drop (Z.of_nat e0') sa2).
  fold s3' in Hrb2, Hds2, Hsw3', Hal3', Hacc2.
  pose proof Hsw3' as (Hb3' & Hh3' & _).
  assert (Hbuf3' : f_buf s3' = f_buf s2)
    by (unfold s3'; rewrite w3_drop_buf; rewrite Hbufa2; exact Hbuf1').
  assert (Hout3' : f_out s3' = f_out s2)
    by (unfold s3'; rewrite w3_drop_out; rewrite Houta2; exact Hout1').
  assert (Hbits3' : f_bits s3' <= 60)
    by (destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]]; lia).
  assert (Hin3' : f_in s2 <= f_in s3').
  { assert (f_in s2 <= f_in s1')
      by (rewrite Hin1';
          destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
    destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]]; lia. }
  set (v' := if_low (Z.of_nat e0') sa2) in *.
  assert (Hpow13 : 2 ^ Z.of_nat e0' <= 8192).
  { replace 8192 with (2 ^ 13) by reflexivity.
    apply Z.pow_le_mono_r; lia. }
  set (dist_spec := (b0' + Z.to_nat v')%nat).
  assert (Edist : c_val (entd dsym) + v' = Z.of_nat dist_spec).
  { unfold dist_spec. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    rewrite Hval'. reflexivity. }
  assert (Eod : u32 (f_out s3' - f_beg c) = f_out s2 - f_beg c)
    by (rewrite Hout3'; apply u32_id; lia).
  rewrite Eod.
  destruct (Z.ltb_spec (f_out s2 - f_beg c) (c_val (entd dsym) + v'))
    as [Hlt | Hge].
  - (* window arm: whave = 0 forces BAD before any window read *)
    rewrite Hwh.
    assert (Eow : (0 <? u32 (c_val (entd dsym) + v'
                             - (f_out s2 - f_beg c))) = true).
    { apply Z.ltb_lt. apply u32_pos. rewrite Hval'. lia. }
    rewrite Eow.
    assert (Esn : (f_sane c =? 0) = false) by (apply Z.eqb_neq; exact Hsn).
    rewrite Esn. cbn [negb andb].
    cbv iota.
    right.
    exists dsym, (skipn (length cwD) (if_stream c s2)), dist_spec,
           (if_stream c s3').
    split; [exact HhdD|].
    split.
    { unfold read_extra. rewrite Hnb', Hne'.
      rewrite Nat2Z.id in Hrb2.
      rewrite Hds1 in Hrb2.
      rewrite Hrb2. reflexivity. }
    rewrite <- Edist. lia.
  - (* direct copy *)
    rewrite if_copydirect_flat by lia.
    cbv iota.
    exists dsym, dist_spec, (skipn (length cwD) (if_stream c s2)),
           (if_stream c s3').
    split; [exact HhdD|].
    split.
    { unfold read_extra. rewrite Hnb', Hne'.
      rewrite Nat2Z.id in Hrb2.
      rewrite Hds1 in Hrb2.
      rewrite Hrb2. reflexivity. }
    split.
    { rewrite w3_stream_copyn. reflexivity. }
    split; [unfold dist_spec; lia|].
    split; [rewrite <- Edist, Hval'; lia|].
    split.
    { rewrite Edist.
      replace (Z.to_nat len) with len_spec by lia.
      rewrite <- Hbuf3', <- Hout3'.
      rewrite if_copyn_out.
      rewrite (if_copyn_lz len_spec dist_spec c s3')
        by (rewrite Hout3'; rewrite <- Edist, Hval'; lia).
      reflexivity. }
    split.
    { rewrite if_copyn_out, Hout3'. lia. }
    split; [apply w3_swf_copyn; exact Hsw3'|].
    split; [apply w3_haligned_copyn; exact Hal3'|].
    assert (HinA : f_in s3 = f_in s2 + 2 /\ f_bits s3 = f_bits s2 + 16
                   \/ f_in s3 = f_in s2 /\ f_bits s3 = f_bits s2).
    { destruct Hrf2 as [(B1&B2&B3)|(B1&B2)];
        [ left; auto
        | right; rewrite B2; auto ]. }
    split.
    { unfold if_swf in Hsw3'.
      rewrite (if_copyn_bits (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      exact Hbits3'. }
    split.
    { rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      exact Hin3'. }
    split.
    { (* the cursor stays inside the input window *)
      rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]];
        destruct HinA as [(C1&C2)|(C1&C2)];
        try lia;
        (* two loads fired AND the refill fired: bits s2 < 4 fires Hrm4 *)
        assert (Hb4 : f_bits s2 < 4) by lia;
        pose proof (Hrm4 Hb4); lia. }
    { (* the virtual byte cursor [f_in - bits/8] is monotone *)
      rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))),
              (if_copyn_bits (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      assert (HV23 : f_in s2 - f_bits s2 / 8 <= f_in s3 - f_bits s3 / 8).
      { destruct HinA as [(C1&C2)|(C1&C2)]; rewrite C1, C2;
          [ replace (f_bits s2 + 16) with (f_bits s2 + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | lia ]. }
      assert (HV31 : f_in s3 - f_bits s3 / 8 <= f_in s1' - f_bits s1' / 8).
      { rewrite Hin1', Hbits1'.
        pose proof (w3_div8_mono (f_bits s3 - Z.of_nat (length cwD))
                      (f_bits s3) ltac:(lia)).
        lia. }
      assert (HV13 : f_in s1' - f_bits s1' / 8 <= f_in s3' - f_bits s3' / 8).
      { destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]].
        - rewrite A3, A4.
          pose proof (w3_div8_mono (f_bits s1' + 16 - Z.of_nat e0')
                        (f_bits s1' + 16) ltac:(lia)) as M1.
          assert (E1 : (f_bits s1' + 16) / 8 = f_bits s1' / 8 + 2)
            by (replace (f_bits s1' + 16) with (f_bits s1' + 8 * 2) by ring;
                apply w3_div8_add).
          lia.
        - rewrite A3, A4.
          pose proof (w3_div8_mono (f_bits s1' + 8 - Z.of_nat e0')
                        (f_bits s1' + 8) ltac:(lia)) as M1.
          assert (E1 : (f_bits s1' + 8) / 8 = f_bits s1' / 8 + 1)
            by (replace (f_bits s1' + 8) with (f_bits s1' + 8 * 1) by ring;
                apply w3_div8_add).
          lia.
        - rewrite A2, A3.
          pose proof (w3_div8_mono (f_bits s1' - Z.of_nat e0')
                        (f_bits s1') ltac:(lia)) as M1.
          lia. }
      lia. }
Qed.

Lemma w3sel_trip :
  forall c s (rootL rootD : Z) (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
    w3_root_own (f_lcode c) rootL ll 15%nat entl ->
    w3_root_own (f_dcode c) rootD dl 15%nat entd ->
    w3_len_ents ll entl -> w3_dist_ents dl entd ->
    zr_inv_len ll entl -> zr_inv_dist dl entd ->
    0 < rootL <= 15 -> 0 < rootD <= 15 ->
    f_lmask c = Z.shiftl 1 rootL - 1 ->
    f_dmask c = Z.shiftl 1 rootD - 1 ->
    f_whave c = 0 -> f_sane c <> 0 ->
    if_inb c -> if_swf s -> if_haligned c s ->
    f_bits s <= 60 ->
    f_in s + 6 <= f_last c + 5 ->
    0 <= f_beg c <= f_out s ->
    f_beg c = 0 ->
    f_out s <= 4294967295 ->
    match if_body c s with
    | BodyOk s' =>
        exists sy rest,
          decode_lit_len ll dl (if_stream c s) = Some (sy, rest)
          /\ sy <> LzEnd
          /\ if_stream c s' = rest
          /\ resolve_lz [sy] (zslice (f_buf s) 0 (f_out s))
             = Some (zslice (f_buf s') 0 (f_out s'))
          /\ w3_post c s s'
    | BodyEob s' =>
        decode_lit_len ll dl (if_stream c s) = Some (LzEnd, if_stream c s')
        /\ f_out s' = f_out s /\ f_buf s' = f_buf s
        /\ w3_post c s s'
    | BodyBad s' m =>
        decode_lit_len ll dl (if_stream c s) = None
        \/ (exists sy rest,
              decode_lit_len ll dl (if_stream c s) = Some (sy, rest)
              /\ exists len' dist', sy = LzRef len' dist'
                 /\ Z.of_nat dist' > f_out s)
    | BodyFuel => True
    end.
Proof.
  intros c s rootL rootD ll dl entl entd HVl HVd HownL HownD Hle Hde
         Hinvl Hinvd HrL HrD EmL EmD Hwh Hsn Hinb Hswf Hal Hcap Hroom
         Hbeg Hbeg0 Hocap.
  pose proof Hswf as (Hb0s & Hh0s & _).
  unfold if_body. cbv zeta.
  set (s0 := if_refill15 c s).
  assert (Hst0 : if_stream c s0 = if_stream c s)
    by (apply w2_refill15_stream; auto; lia).
  assert (Hsw0 : if_swf s0) by (apply w2_refill15_swf; auto).
  pose proof Hsw0 as (Hb0 & Hh0 & _).
  assert (Hal0 : if_haligned c s0) by (apply w2_refill15_haligned; auto).
  assert (Hb15 : 15 <= f_bits s0) by (apply w2_refill15_bits; auto).
  assert (Hbuf0 : f_buf s0 = f_buf s) by apply w2_refill15_buf.
  assert (Hout0 : f_out s0 = f_out s) by apply w2_refill15_out.
  pose proof (w3_refill15_facts c s) as Hrf. fold s0 in Hrf.
  assert (Hcap0 : f_bits s0 <= 60)
    by (destruct Hrf as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  assert (Hin0 : f_in s <= f_in s0 <= f_in s + 2)
    by (destruct Hrf as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  destruct (w3_root_read (f_lcode c) rootL ll entl (f_lmask c) c s0
              HVl HownL HrL EmL Hsw0 ltac:(lia))
    as (symL & cwL & HcfL & HTL & HcbL & HlenL & HhdL).
  rewrite Hst0 in HhdL.
  change tbl_fuel with (S 15).
  rewrite if_dolen_S. cbv zeta.
  rewrite HTL, HcbL.
  set (s1 := if_drop (Z.of_nat (length cwL)) s0).
  assert (Er1 : if_stream c s1 = skipn (length cwL) (if_stream c s)).
  { unfold s1.
    rewrite (w2_drop_stream (Z.of_nat (length cwL)) c s0) by (auto; lia).
    rewrite Hst0, Nat2Z.id. reflexivity. }
  assert (Hsw1 : if_swf s1) by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1 as (Hb1 & Hh1 & _).
  assert (Hal1 : if_haligned c s1) by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1 : f_buf s1 = f_buf s)
    by (unfold s1; rewrite w3_drop_buf; exact Hbuf0).
  assert (Hout1 : f_out s1 = f_out s)
    by (unfold s1; rewrite w3_drop_out; exact Hout0).
  assert (Hin1 : f_in s1 = f_in s0) by apply w3_drop_in.
  assert (Hbits1 : f_bits s1 = f_bits s0 - Z.of_nat (length cwL))
    by (apply w3_drop_bits; lia).
  destruct (Hle _ _ HcfL) as
    [ (Hsym & Hop0 & Hval)
    | [ (Esym & Hopn & H32e & H16e & H64e)
    | [ (Hsym257 & b0 & e0 & Hnb & Hne & Hop3 & H32l & H64l & H15l & Hval
         & Hb3 & Hb258 & He5 & Hjoint)
    | (Hopn & H32i & H16i & H64i) ] ] ].
  - (* class 1: literal *)
    rewrite Hop0.
    change (0 =? 0) with true. cbv iota.
    exists (LzLit (Z.of_nat symL)), (skipn (length cwL) (if_stream c s)).
    split.
    { unfold decode_lit_len. rewrite HhdL.
      rewrite (proj2 (Nat.ltb_lt symL 256) Hsym).
      reflexivity. }
    split; [discriminate|].
    split.
    { rewrite w3_stream_put. exact Er1. }
    split.
    { assert (Ev : u8 (c_val (entl symL)) = Z.of_nat symL)
        by (rewrite Hval; apply w3_u8_small; exact Hsym).
      rewrite Ev.
      cbn [resolve_lz].
      rewrite if_put_out.
      rewrite if_put_slice by lia.
      rewrite Hbuf1, Hout1.
      reflexivity. }
    split; [apply w3_swf_put; exact Hsw1|].
    split; [apply w3_haligned_put; exact Hal1|].
    split.
    { cbn [if_put f_bits]. lia. }
    split.
    { cbn [if_put f_in]. lia. }
    split.
    { rewrite if_put_out, Hout1. lia. }
    split.
    { cbn [if_put f_in]. lia. }
    split.
    { cbn [if_put f_in f_bits].
      assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
      { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          [ rewrite B2, B3;
            replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | rewrite B2; lia ]. }
      assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
      { rewrite Hin1, Hbits1.
        pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                      (f_bits s0) ltac:(lia)).
        lia. }
      lia. }
    { rewrite if_put_out, Hout1. lia. }
  - (* class 2: end of block *)
    assert (E0 : (c_op (entl symL) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl symL)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16e).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl symL)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64e).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl symL)) 32 =? 0) = false)
      by (apply Z.eqb_neq; exact H32e).
    rewrite E32. cbn [negb]. cbv iota.
    split.
    { unfold decode_lit_len. rewrite HhdL.
      subst symL.
      change (256 <? 256)%nat with false.
      change (256 =? 256)%nat with true.
      rewrite Er1. reflexivity. }
    split; [exact Hout1|].
    split; [exact Hbuf1|].
    split; [exact Hsw1|].
    split; [exact Hal1|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split.
    { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
      { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          [ rewrite B2, B3;
            replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | rewrite B2; lia ]. }
      assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
      { rewrite Hin1, Hbits1.
        pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                      (f_bits s0) ltac:(lia)).
        lia. }
      lia. }
    lia.
  - (* class 3: length/distance pair *)
    rewrite Hop3.
    pose proof (w3_land16 (Z.of_nat e0) ltac:(lia)) as (L16 & L15 & L64 & L32).
    assert (E0 : (16 + Z.of_nat e0 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite E0.
    assert (E16 : (Z.land (16 + Z.of_nat e0) 16 =? 0) = false)
      by (rewrite L16; reflexivity).
    rewrite E16. cbn [negb].
    rewrite L15.
    destruct (Z.eqb_spec (Z.of_nat e0) 0) as [Ee|Ee].
    + (* no extra bits *)
      cbv iota.
      assert (Ee0 : e0 = 0%nat) by lia.
      subst e0.
      set (len_spec := b0).
      assert (Hre : read_extra length_base length_extra (symL - 257)%nat
                      (skipn (length cwL) (if_stream c s))
                    = Some (len_spec, if_stream c s1)).
      { unfold read_extra. rewrite Hnb, Hne.
        cbn [read_bits].
        rewrite Er1.
        unfold len_spec. rewrite Nat.add_0_r. reflexivity. }
      assert (Elen : c_val (entl symL) = Z.of_nat len_spec)
        by (unfold len_spec; exact Hval).
      change tbl_fuel with (S 15).
      pose proof (w3sel_dist_tail c s1 rootD dl entd (c_val (entl symL))
                    len_spec 15 HVd HownD Hde Hinvd HrD EmD Hwh Hsn Hinb
                    Hsw1 Hal1 ltac:(lia)
                    ltac:(lia) ltac:(intros _; lia)
                    ltac:(lia) Hbeg0 ltac:(lia)
                    Elen ltac:(unfold len_spec; lia)
                    ltac:(unfold len_spec; lia)) as Htail.
      match goal with
      | |- match ?X with _ => _ end => destruct X as [s5|s5|s5 m|]
      end; [| destruct Htail | | exact I].
      2:{ destruct Htail as [ (dsym' & r3' & Hhd2N & HreN)
                            | (dsym' & r3' & dist' & r4' & Hhd2N & Hre2N
                               & HfarN) ].
          - left.
            unfold decode_lit_len. rewrite HhdL. cbv beta iota.
            rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
            rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
            cbv beta iota.
            rewrite Hre. cbv beta iota.
            rewrite Hhd2N. cbv beta iota.
            rewrite HreN. reflexivity.
          - right.
            exists (LzRef len_spec dist'), r4'.
            split.
            { unfold decode_lit_len. rewrite HhdL. cbv beta iota.
              rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
              rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
              cbv beta iota.
              rewrite Hre. cbv beta iota.
              rewrite Hhd2N. cbv beta iota.
              rewrite Hre2N. reflexivity. }
            exists len_spec, dist'.
            split; [reflexivity|].
            rewrite Hout1 in HfarN. exact HfarN. }
      destruct Htail as (dsym & dist_spec & r3 & r4 & Hhd2 & Hre2 & Hstr5
                         & Hd1 & Hdle & Hslice & Hout5 & Hsw5 & Hal5
                         & Hbits5 & Hin5 & Hin5cap & Hv5).
      exists (LzRef len_spec dist_spec), r4.
      split.
      { unfold decode_lit_len. rewrite HhdL.
        rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
        rewrite Hre, Hhd2, Hre2. reflexivity. }
      split; [discriminate|].
      split; [exact Hstr5|].
      split.
      { cbn [resolve_lz].
        assert (Ez : (dist_spec =? 0)%nat = false)
          by (apply Nat.eqb_neq; lia).
        assert (El : (length (zslice (f_buf s) 0 (f_out s)) <? dist_spec)%nat
                     = false).
        { apply Nat.ltb_ge. rewrite zslice_length. lia. }
        rewrite Ez, El. cbn [orb].
        rewrite Hbuf1, Hout1 in Hslice.
        rewrite Hslice. reflexivity. }
      split; [exact Hsw5|].
      split; [exact Hal5|].
      split; [exact Hbits5|].
      split; [lia|].
      split.
      { rewrite Hout5, Hout1. unfold len_spec. lia. }
      split; [exact Hin5cap|].
      split.
      { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
        { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
            [ rewrite B2, B3;
              replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
              rewrite w3_div8_add; lia
            | rewrite B2; lia ]. }
        assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
        { rewrite Hin1, Hbits1.
          pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                        (f_bits s0) ltac:(lia)).
          lia. }
        lia. }
      rewrite Hout5, Hout1. unfold len_spec. lia.
    + (* extra bits *)
      cbv iota.
      set (sa := if Z.ltb (f_bits s1) (Z.of_nat e0)
                 then if_load1 c s1 else s1).
      destruct (w3_extra1 c s1 (Z.of_nat e0) sa Hinb Hsw1 Hal1
                  ltac:(lia) ltac:(lia) ltac:(intros _; lia) eq_refl)
        as (Hrb1 & Hds1 & Hsw2 & Hal2 & Hbufa & Houta & Hlow1 & Hacc1).
      set (s2 := if_drop (Z.of_nat e0) sa).
      fold s2 in Hrb1, Hds1, Hsw2, Hal2, Hacc1.
      assert (Hbuf2 : f_buf s2 = f_buf s)
        by (unfold s2; rewrite w3_drop_buf; rewrite Hbufa; exact Hbuf1).
      assert (Hout2 : f_out s2 = f_out s)
        by (unfold s2; rewrite w3_drop_out; rewrite Houta; exact Hout1).
      set (v := if_low (Z.of_nat e0) sa) in *.
      set (len_spec := (b0 + Z.to_nat v)%nat).
      assert (Hpow5 : 2 ^ Z.of_nat e0 <= 32).
      { replace 32 with (2 ^ 5) by reflexivity.
        apply Z.pow_le_mono_r; lia. }
      assert (Elen : c_val (entl symL) + v = Z.of_nat len_spec).
      { unfold len_spec. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
        rewrite Hval. reflexivity. }
      assert (Hjz : Z.of_nat b0 + 2 ^ Z.of_nat e0 - 1 <= 258).
      { replace (2 ^ Z.of_nat e0) with (Z.of_nat (2 ^ e0))
          by (rewrite Nat2Z.inj_pow; reflexivity).
        lia. }
      assert (Hre : read_extra length_base length_extra (symL - 257)%nat
                      (skipn (length cwL) (if_stream c s))
                    = Some (len_spec, if_stream c s2)).
      { unfold read_extra. rewrite Hnb, Hne.
        rewrite Nat2Z.id in Hrb1.
        rewrite Er1 in Hrb1.
        rewrite Hrb1. reflexivity. }
      assert (Hcap2 : f_bits s2 <= 60)
        by (destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia).
      assert (Hrm3 : f_in s2 + 3 <= f_last c + 5)
        by (destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia).
      assert (Hrm4 : f_bits s2 < 4 -> f_in s2 + 4 <= f_last c + 5).
      { intros Hb4.
        destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)];
          destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          try lia.
        rewrite B2 in *. lia. }
      change tbl_fuel with (S 15).
      pose proof (w3sel_dist_tail c s2 rootD dl entd
                    (c_val (entl symL) + v) len_spec 15
                    HVd HownD Hde Hinvd HrD EmD Hwh Hsn Hinb
                    Hsw2 Hal2 Hcap2 Hrm3 Hrm4
                    ltac:(lia) Hbeg0 ltac:(lia)
                    Elen ltac:(unfold len_spec; lia)
                    ltac:(unfold len_spec; lia)) as Htail.
      match goal with
      | |- match ?X with _ => _ end => destruct X as [s5|s5|s5 m|]
      end; [| destruct Htail | | exact I].
      2:{ destruct Htail as [ (dsym' & r3' & Hhd2N & HreN)
                            | (dsym' & r3' & dist' & r4' & Hhd2N & Hre2N
                               & HfarN) ].
          - left.
            unfold decode_lit_len. rewrite HhdL. cbv beta iota.
            rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
            rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
            cbv beta iota.
            rewrite Hre. cbv beta iota.
            rewrite Hhd2N. cbv beta iota.
            rewrite HreN. reflexivity.
          - right.
            exists (LzRef len_spec dist'), r4'.
            split.
            { unfold decode_lit_len. rewrite HhdL. cbv beta iota.
              rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
              rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
              cbv beta iota.
              rewrite Hre. cbv beta iota.
              rewrite Hhd2N. cbv beta iota.
              rewrite Hre2N. reflexivity. }
            exists len_spec, dist'.
            split; [reflexivity|].
            rewrite Hout2 in HfarN. exact HfarN. }
      destruct Htail as (dsym & dist_spec & r3 & r4 & Hhd2 & Hre2 & Hstr5
                         & Hd1 & Hdle & Hslice & Hout5 & Hsw5 & Hal5
                         & Hbits5 & Hin5 & Hin5cap & Hv5).
      exists (LzRef len_spec dist_spec), r4.
      split.
      { unfold decode_lit_len. rewrite HhdL.
        rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
        rewrite Hre, Hhd2, Hre2. reflexivity. }
      split; [discriminate|].
      split; [exact Hstr5|].
      split.
      { cbn [resolve_lz].
        assert (Ez : (dist_spec =? 0)%nat = false)
          by (apply Nat.eqb_neq; lia).
        assert (El : (length (zslice (f_buf s) 0 (f_out s)) <? dist_spec)%nat
                     = false).
        { apply Nat.ltb_ge. rewrite zslice_length. lia. }
        rewrite Ez, El. cbn [orb].
        rewrite Hbuf2, Hout2 in Hslice.
        rewrite Hslice. reflexivity. }
      split; [exact Hsw5|].
      split; [exact Hal5|].
      split; [exact Hbits5|].
      split.
      { destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia. }
      split.
      { rewrite Hout5, Hout2. unfold len_spec. lia. }
      split; [exact Hin5cap|].
      split.
      { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
        { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
            [ rewrite B2, B3;
              replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
              rewrite w3_div8_add; lia
            | rewrite B2; lia ]. }
        assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
        { rewrite Hin1, Hbits1.
          pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                        (f_bits s0) ltac:(lia)).
          lia. }
        assert (HV2 : f_in s1 - f_bits s1 / 8 <= f_in s2 - f_bits s2 / 8).
        { destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; rewrite A2, A3.
          - pose proof (w3_div8_mono (f_bits s1 + 8 - Z.of_nat e0)
                          (f_bits s1 + 8) ltac:(lia)) as M1.
            assert (E1 : (f_bits s1 + 8) / 8 = f_bits s1 / 8 + 1)
              by (replace (f_bits s1 + 8) with (f_bits s1 + 8 * 1) by ring;
                  apply w3_div8_add).
            lia.
          - pose proof (w3_div8_mono (f_bits s1 - Z.of_nat e0)
                          (f_bits s1) ltac:(lia)) as M1.
            lia. }
        lia. }
      rewrite Hout5, Hout2. lia.
  - (* class 4: invalid *)
    assert (E0 : (c_op (entl symL) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl symL)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16i).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl symL)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64i).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl symL)) 32 =? 0) = true)
      by (apply Z.eqb_eq; exact H32i).
    rewrite E32. cbn [negb]. cbv iota.
    pose proof (Hinvl symL cwL HcfL H64i H32i) as (Hs257i & HNi).
    left.
    unfold decode_lit_len. rewrite HhdL. cbv beta iota.
    rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
    rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
    cbv beta iota.
    unfold read_extra. rewrite HNi.
    destruct (nth_error length_extra (symL - 257)%nat); reflexivity.
Qed.

Set Printing Width 2000.
Print Assumptions w3sel_dist_tail.
Print Assumptions w3sel_trip.
