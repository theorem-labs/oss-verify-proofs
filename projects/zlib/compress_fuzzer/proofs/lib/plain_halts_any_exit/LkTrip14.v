(* the zlib 1.4 twin of LkTrip, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkTrip), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkTrip — THE SLOW TRIP, GOOD-ONLY (q7-decode leavekill fork,
    2026-08-22, OFF-TREE SCRATCH).

    [TripSel.zr_sym_trip_sel]'s good arm as the WHOLE conclusion: the
    per-symbol declarative success is premise-pinned ([decode_lit_len
    ... = Some (sy, rem)], with per-symbol room), and every absorbed
    arm of the 3-arm trip is refuted at its site:

      - LEN/DIST decode starve/fuel  -> LkStage's split_good lemmas
        (LkFetch kills, driven by the hdecode success the premise's
        own computation supplies);
      - LEN/DIST invalid codes       -> the inv packs force the
        premise's computation to None (contradiction);
      - LENEXT/DISTEXT starve        -> K1 against the premise's own
        read_bits successes;
      - MATCH starve/partial/too-far -> the room premises pin the
        full-copy arm ([lk_match_full]);
      - LIT output-full              -> the LzLit room premise.

    Conclusion conjunct list byte-verbatim from the 3-arm trip's good
    arm, so the loop mirror consumes it with unchanged text.

    PA-EXPORT: lk_sym_trip_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6M ZReproQ6N ZReproQ6P GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import FixSelCore.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkNb LkFetch LkStage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkTrip.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1trip14 LkStage14 Spec.PngModel.Inflate14 Spec.PngModel.Inflate14Iter.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma lk_sym_trip_good14 :
  forall c q (ll dl : list nat) (entl entd : nat -> Code)
         (sy : lz_sym) (rem : list bool),
  ValidLengths ll 15%nat ->
  ValidLengths dl 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (forall sym cw, code_for dl 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  zr_len_ents ll entl ->
  zr_dist_ents dl entd ->
  zr_inv_len ll entl ->
  zr_inv_dist dl entd ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  h_mode (s_hdr (q_st q)) = M_LEN ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8) = false ->
  decode_lit_len ll dl (br_stream (q_br q)) = Some (sy, rem) ->
  match sy with
  | LzLit _ => 0 < o_left (q_ob q)
  | LzEnd => True
  | LzRef len dist =>
      Z.of_nat dist <= o_put (q_ob q)
      /\ Z.of_nat len <= o_left (q_ob q)
  end ->
  exists k q',
     inf_iter14 k c q = Some q'
     /\ decode_lit_len ll dl (br_stream (q_br q))
        = Some (sy, br_stream (q_br q'))
     /\ match sy with
        | LzLit v =>
            ob_slice (q_ob q') 0 (o_put (q_ob q'))
            = ob_slice (q_ob q) 0 (o_put (q_ob q)) ++ [v]
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        | LzEnd =>
            q_ob q' = q_ob q
            /\ h_mode (s_hdr (q_st q')) = M_TYPE
        | LzRef len dist =>
            (dist =? 0)%nat = false
            /\ Z.of_nat dist <= o_put (q_ob q)
            /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
               = ob_slice (q_ob q) 0 (o_put (q_ob q))
                 ++ lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                            len dist
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        end
     /\ br_wf (q_br q')
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ s_tab (q_st q') = s_tab (q_st q)
     /\ s_win (q_st q') = s_win (q_st q)
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br q'))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).
Proof.
  intros c q ll dl entl entd sy rem HVl HVd Hownl Hownd Hrbl Hrbd Hsubl
         Hsubd Hentsl Hentsd Hinvl Hinvd Hwf Hput Hleft Htie Hcap Hwh
         Hsn Hm Hg Hdec Hroom.
  assert (HSTEP : inf_step14 c q = inf_LEN14 q)
    by (apply zr_step14_at_len; exact Hm).
  (* the premise's own computation, opened to its hdecode *)
  pose proof Hdec as Hdec0.
  unfold decode_lit_len in Hdec0.
  destruct (hdecode (code_table ll 15%nat) (br_stream (q_br q)))
    as [[s1 r1]|] eqn:EHD; [|discriminate Hdec0].
  destruct (lk_len_split_good14 q ll entl s1 r1 Hwf HVl Hownl Hrbl Hsubl
              Hg EHD)
    as [ (qb & symB & cwB & remB & EB & HMb & HcfB & HhdB & HopB
          & H32B & H64B)
       | [ (qL & sym & cw & EC & Hcf & Hhd & Hop0 & HlenL & HmL
            & HwfL & HhaL & HfrL)
         | [ (qT & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & HmT
              & HwfT & HhaT & HfrT)
           | (qE & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & Hl64
              & HlenE & HextE & HwfE & HhaE & HfrE) ] ] ].
  - (* invalid lit/len code: the premise's computation dies *)
    exfalso.
    rewrite EHD in HhdB. injection HhdB as Es _. subst symB.
    destruct (Hinvl s1 cwB HcfB H64B H32B) as (Hs257B & HNB).
    rewrite (proj2 (Nat.ltb_ge s1 256) ltac:(lia)) in Hdec0.
    rewrite (proj2 (Nat.eqb_neq s1 256) ltac:(lia)) in Hdec0.
    cbv beta iota in Hdec0.
    unfold read_extra in Hdec0.
    rewrite HNB in Hdec0.
    discriminate Hdec0.
  - (* ---- literal ---- *)
    rewrite EHD in Hhd. injection Hhd as Es Er. subst s1.
    destruct (Hentsl sym cw Hcf)
      as [ (Hs256 & _ & Hval)
         | [ (_ & HopC & _) | [ (_ & (b0 & e0 & _ & _ & HopC & _))
           | (HopC & _ & _) ] ] ];
      try (exfalso; congruence);
      try (exfalso; rewrite Hop0 in HopC; lia).
    rewrite (proj2 (Nat.ltb_lt sym 256) Hs256) in Hdec0.
    cbv beta iota in Hdec0.
    injection Hdec0 as Esy Erem. subst sy.
    destruct HfrL as (HObL & HRetL & HInL & HOutL & HTabL & HWinL
                      & HLastL & HWrapL & HFlagL & HCheckL & HTotalL).
    assert (HI1 : inf_iter14 1 c q = Some qL)
      by (apply inf_iter14_one; rewrite HSTEP; exact EC).
    assert (HlenLv : 0 <= u_length (s_cur (q_st qL)) < 256)
      by (rewrite HlenL, Hval; lia).
    assert (HSTEP2 : inf_step14 c qL = inf_LIT qL)
      by (apply zr_step14_at_lit; exact HmL).
    destruct (zr_lit_split qL ltac:(rewrite HObL; exact Hput) HlenLv)
      as [ (Elz & ELV) | (qL' & ECw & HSl & HPutw & HLeftw & HMw & HBrw
                          & HRetw & HInw & HOutw & HTabw & HWinw & HLastw
                          & HWrapw & HFlagw & HCheckw & HTotalw) ].
    { (* output full: killed by the LzLit room premise *)
      exfalso. rewrite HObL in Elz. lia. }
    exists 2%nat, qL'.
    split.
    { change 2%nat with (1 + 1)%nat.
      rewrite (inf_iter14_add 1 1 c q qL HI1).
      apply inf_iter14_one. rewrite HSTEP2. exact ECw. }
    split.
    { unfold decode_lit_len. rewrite EHD. cbv beta iota.
      rewrite (proj2 (Nat.ltb_lt sym 256) Hs256). cbv beta iota.
      rewrite HBrw. rewrite <- Er. reflexivity. }
    split.
    { split.
      - rewrite HSl, HObL, HlenL, Hval. reflexivity.
      - exact HMw. }
    split. { rewrite HBrw. exact HwfL. }
    split. { rewrite HPutw, HObL. lia. }
    split.
    { rewrite HLeftw, HObL.
      destruct (Z.eqb_spec (o_left (q_ob qL)) 0) as [E|N].
      - exfalso. unfold inf_LIT in ECw.
        rewrite (proj2 (Z.eqb_eq _ 0) E) in ECw. discriminate.
      - rewrite HObL in N. lia. }
    split. { rewrite HPutw, HLeftw, HObL. lia. }
    split. { rewrite HTabw. exact HTabL. }
    split. { rewrite HWinw. exact HWinL. }
    split. { rewrite HLastw. exact HLastL. }
    split. { rewrite HWrapw. exact HWrapL. }
    split. { rewrite HRetw. exact HRetL. }
    split. { rewrite HInw. exact HInL. }
    split. { rewrite HOutw. exact HOutL. }
    split. { intro Hal. rewrite HBrw. exact (HhaL Hal). }
    split. { rewrite HFlagw. exact HFlagL. }
    split. { rewrite HCheckw. exact HCheckL. }
    rewrite HTotalw. exact HTotalL.
  - (* ---- end of block ---- *)
    rewrite EHD in Hhd. injection Hhd as Es Er. subst s1.
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (Hs256 & _ & _) | [ (_ & (b0 & e0 & _ & _ & _ & Hl32C & _))
           | (_ & Hl32C & _) ] ] ];
      try (exfalso; congruence).
    rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)) in Hdec0.
    rewrite (proj2 (Nat.eqb_eq sym 256) Hs256) in Hdec0.
    cbv beta iota in Hdec0.
    injection Hdec0 as Esy Erem. subst sy.
    destruct HfrT as (HObT & HRetT & HInT & HOutT & HTabT & HWinT
                      & HLastT & HWrapT & HFlagT & HCheckT & HTotalT).
    exists 1%nat, qT.
    split.
    { apply inf_iter14_one. rewrite HSTEP. exact EC. }
    split.
    { unfold decode_lit_len. rewrite EHD. cbv beta iota.
      rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
      rewrite (proj2 (Nat.eqb_eq sym 256) Hs256). cbv beta iota.
      rewrite <- Er. reflexivity. }
    split. { split; [exact HObT | exact HmT]. }
    split. { exact HwfT. }
    split. { rewrite HObT. exact Hput. }
    split. { rewrite HObT. exact Hleft. }
    split. { rewrite HObT. reflexivity. }
    split. { exact HTabT. }
    split. { exact HWinT. }
    split. { exact HLastT. }
    split. { exact HWrapT. }
    split. { exact HRetT. }
    split. { exact HInT. }
    split. { exact HOutT. }
    split. { intro Hal. exact (HhaT Hal). }
    split. { exact HFlagT. }
    split. { exact HCheckT. }
    exact HTotalT.
  - (* ---- length/distance reference ---- *)
    rewrite EHD in Hhd. injection Hhd as Es Er. subst s1.
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (_ & _ & Hl32C & _) | [ (Hs257 & (b0 & e0 & Hb0 & He0 & HopC
              & _ & _ & Hl15 & Hval & Hb3 & Hb258 & He5 & Hjoint))
           | (_ & _ & _ & Hl64C) ] ] ];
      try (exfalso; congruence).
    (* open the premise's computation to the dist read *)
    rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)) in Hdec0.
    rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)) in Hdec0.
    cbv beta iota in Hdec0.
    unfold read_extra in Hdec0.
    rewrite Hb0, He0 in Hdec0. cbv beta iota in Hdec0.
    rewrite Er in Hdec0.
    destruct (read_bits e0 (br_stream (q_br qE)))
      as [[v1x r2x]|] eqn:ERB1; [|discriminate Hdec0].
    cbv beta iota in Hdec0.
    destruct (hdecode (code_table dl 15%nat) r2x)
      as [[ds1 r3x]|] eqn:EHD2; [|discriminate Hdec0].
    cbv beta iota in Hdec0.
    destruct HfrE as (HObE & HRetE & HInE & HOutE & HTabE & HWinE
                      & HLastE & HWrapE & HFlagE & HCheckE & HTotalE).
    (* stage: LENEXT, starve killed by the read's own floor *)
    assert (HextEv : 0 <= u_extra (s_cur (q_st qE)) <= 13)
      by (rewrite HextE, Hl15; lia).
    assert (Hfloor1 : (Z.to_nat (u_extra (s_cur (q_st qE)))
                       <= length (br_stream (q_br qE)))%nat).
    { rewrite HextE, Hl15, Nat2Z.id.
      pose proof (read_bits_length e0 (br_stream (q_br qE)) v1x r2x
                    ERB1) as HL1. lia. }
    destruct (lk_lenext_good qE HwfE HextEv Hfloor1)
      as (qD & v1 & ECD & HRd1 & Hv1 & HlenD & HwfD & HhaD & HfrD).
    rewrite HextE, Hl15, Nat2Z.id in HRd1.
    rewrite ERB1 in HRd1. injection HRd1 as Ev1 Er2. subst v1.
    destruct HfrD as (HObD & HRetD & HInD & HOutD & HTabD & HWinD
                      & HLastD & HWrapD & HFlagD & HCheckD & HTotalD).
    (* stage: DIST — transport the table hypotheses to qD *)
    assert (HstD : s_tab (q_st qD) = s_tab (q_st q))
      by (rewrite HTabD; exact HTabE).
    assert (HownDq : ZReproQ6M.zr_root_own
              (tbl_of (q_st qD) (t_distcode (s_tab (q_st qD))))
              (t_distbits (s_tab (q_st qD))) dl 15%nat entd).
    { rewrite HstD, (tbl_of_stable (q_st q) (q_st qD) _ HstD).
      exact Hownd. }
    assert (HrbDq : 0 < t_distbits (s_tab (q_st qD)) <= 15)
      by (rewrite HstD; exact Hrbd).
    assert (EHD2' : hdecode (code_table dl 15%nat) (br_stream (q_br qD))
                    = Some (ds1, r3x))
      by (rewrite <- Er2; exact EHD2).
    destruct (lk_dist_split_good qD dl entd ds1 r3x HwfD HVd HownDq
                HrbDq Hsubd EHD2')
      as [ (qbd & dsymB & cwdB & remdB & EBd & HMbd & HcfdB & HhddB
            & H64dB)
         | (qX & dsym & cwd & ECX & Hcfd & Hhdd & HoffX & HextX
            & HlenX & Hl64d & HwfX & HhaX & HfrX) ].
    { (* invalid distance code: the premise's computation dies *)
      exfalso.
      rewrite EHD2' in HhddB. injection HhddB as Eds _. subst dsymB.
      pose proof (Hinvd ds1 cwdB HcfdB H64dB) as HNdB.
      unfold read_extra in Hdec0.
      rewrite HNdB in Hdec0.
      discriminate Hdec0. }
    rewrite EHD2' in Hhdd. injection Hhdd as Eds Er3. subst ds1.
    destruct (Hentsd dsym cwd Hcfd)
      as [ (b0d & e0d & Hb0d & He0d & HopCd & _ & Hl15d & Hvald
            & Hb0db & He0db)
         | (Hl64Cd & _) ];
      [ | exfalso; congruence ].
    (* open the premise's computation to the dist extra read *)
    unfold read_extra in Hdec0.
    rewrite Hb0d, He0d in Hdec0. cbv beta iota in Hdec0.
    rewrite Er3 in Hdec0.
    destruct (read_bits e0d (br_stream (q_br qX)))
      as [[v2x r4x]|] eqn:ERB2; [|discriminate Hdec0].
    cbv beta iota in Hdec0.
    injection Hdec0 as Esy Erem. subst sy.
    destruct HfrX as (HObX & HRetX & HInX & HOutX & HTabX & HWinX
                      & HLastX & HWrapX & HFlagX & HCheckX & HTotalX).
    (* stage: DISTEXT, starve killed by the read's own floor *)
    assert (HextXv : 0 <= u_extra (s_cur (q_st qX)) <= 13)
      by (rewrite HextX, Hl15d; lia).
    assert (Hfloor2 : (Z.to_nat (u_extra (s_cur (q_st qX)))
                       <= length (br_stream (q_br qX)))%nat).
    { rewrite HextX, Hl15d, Nat2Z.id.
      pose proof (read_bits_length e0d (br_stream (q_br qX)) v2x r4x
                    ERB2) as HL2. lia. }
    destruct (lk_distext_good qX HwfX HextXv Hfloor2)
      as (qM & v2 & ECM & HRd2 & Hv2 & HoffM & HlenM & HmM & HwfM
          & HhaM & HfrM).
    rewrite HextX, Hl15d, Nat2Z.id in HRd2.
    rewrite ERB2 in HRd2. injection HRd2 as Ev2 Er4. subst v2.
    destruct HfrM as (HObM & HRetM & HInM & HOutM & HTabM & HWinM
                      & HLastM & HWrapM & HFlagM & HCheckM & HTotalM).
    (* the composite frame q -> qM *)
    assert (HObQ : q_ob qM = q_ob q) by congruence.
    assert (HRetQ : q_ret qM = q_ret q) by congruence.
    assert (HInQ : q_in qM = q_in q) by congruence.
    assert (HOutQ : q_out qM = q_out q) by congruence.
    assert (HTabQ : s_tab (q_st qM) = s_tab (q_st q)) by congruence.
    assert (HWinQ : s_win (q_st qM) = s_win (q_st q)) by congruence.
    assert (HLastQ : h_last (s_hdr (q_st qM)) = h_last (s_hdr (q_st q)))
      by congruence.
    assert (HWrapQ : h_wrap (s_hdr (q_st qM)) = h_wrap (s_hdr (q_st q)))
      by congruence.
    assert (HFlagQ : h_flags (s_hdr (q_st qM)) = h_flags (s_hdr (q_st q)))
      by congruence.
    assert (HCheckQ : h_check (s_hdr (q_st qM)) = h_check (s_hdr (q_st q)))
      by congruence.
    assert (HTotalQ : h_total (s_hdr (q_st qM)) = h_total (s_hdr (q_st q)))
      by congruence.
    (* values at qM *)
    assert (HoffMv : u_offset (s_cur (q_st qM)) = Z.of_nat b0d + v2x)
      by (rewrite HoffM, HoffX, Hvald; reflexivity).
    assert (HlenMv : u_length (s_cur (q_st qM)) = Z.of_nat b0 + v1x)
      by (rewrite HlenM, HlenX, HlenD, HlenE, Hval; reflexivity).
    (* concrete extra-value bounds *)
    assert (Hv1b : 0 <= v1x < 32).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qE)))); [lia|].
      replace 32 with (2 ^ 5) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextE, Hl15. lia. }
    assert (Hv2b : 0 <= v2x < 8192).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qX)))); [lia|].
      replace 8192 with (2 ^ 13) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextX, Hl15d. lia. }
    (* the room premises, converted to the machine's Z values *)
    destruct Hroom as (Hrdist & Hrlen).
    assert (Hrd : Z.of_nat (b0d + Z.to_nat v2x) = Z.of_nat b0d + v2x)
      by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; reflexivity).
    assert (Hrl : Z.of_nat (b0 + Z.to_nat v1x) = Z.of_nat b0 + v1x)
      by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; reflexivity).
    (* MATCH: pinned to the full copy *)
    destruct (lk_match_full qM
                ltac:(rewrite HObQ; exact Hput)
                ltac:(rewrite HObQ; exact Hleft)
                ltac:(rewrite HObQ, HOutQ; exact Htie)
                ltac:(rewrite HOutQ; exact Hcap)
                ltac:(rewrite HWinQ; exact Hwh)
                ltac:(rewrite HTabQ; exact Hsn)
                ltac:(first [ clear - HoffMv Hb0db Hv2b Hrd Hrdist; rewrite HoffMv; lia | rewrite HoffMv; lia ])
                ltac:(first [ clear - HlenMv Hv1b Hb258 Hrl Hrlen; rewrite HlenMv; lia | rewrite HlenMv; lia ])
                ltac:(first [ clear - HoffMv HObQ Hrdist Hrd Hb0db Hv2b; rewrite HoffMv, HObQ; lia | rewrite HoffMv, HObQ; lia ])
                ltac:(first [ clear - HlenMv HObQ Hrlen Hrl Hv1b; rewrite HlenMv, HObQ; lia | rewrite HlenMv, HObQ; lia ])
                ltac:(first [ clear - HObQ Hrlen Hrl Hb3 Hb258 Hv1b Hput Hleft; rewrite HObQ; lia | rewrite HObQ; lia ]))
      as (q' & ECf & HSlf & HPutf & HSumf & HMf & HBrf & HLastf
          & HWrapf & HFlagf & HCheckf & HTotalf & HWinf & HTabf
          & HRetf & HInf & HOutf).
    exists 1%nat, q'.
    assert (HI1 : inf_iter14 1 c q = Some q')
      by (apply inf_iter14_one; rewrite HSTEP, EC, ECD, ECX, ECM;
          exact ECf).
    assert (HlenN : Z.to_nat (u_length (s_cur (q_st qM)))
                    = (b0 + Z.to_nat v1x)%nat)
      by (rewrite HlenMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
          reflexivity).
    assert (HoffN : Z.to_nat (u_offset (s_cur (q_st qM)))
                    = (b0d + Z.to_nat v2x)%nat)
      by (rewrite HoffMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
          reflexivity).
    split. { exact HI1. }
    split.
    { unfold decode_lit_len. rewrite EHD. cbv beta iota.
      rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
      rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)).
      cbv beta iota.
      unfold read_extra. rewrite Hb0, He0. cbv beta iota.
      rewrite Er, ERB1. cbv beta iota.
      rewrite EHD2. cbv beta iota.
      rewrite Hb0d, He0d. cbv beta iota.
      rewrite Er3, ERB2. cbv beta iota.
      rewrite HBrf. rewrite <- Er4. reflexivity. }
    split.
    { split.
      { apply (proj2 (Nat.eqb_neq _ 0)). first [ clear - Hb0db Hv2b; lia | lia ]. }
      split.
      { exact Hrdist. }
      split.
      { rewrite HSlf, HObQ, HlenN, HoffN. reflexivity. }
      exact HMf. }
    split. { rewrite HBrf. exact HwfM. }
    split. { rewrite HPutf, HObQ, HlenMv. first [ clear - Hput Hleft Htie Hv1b Hrl Hrlen; lia | lia ]. }
    split.
    { rewrite HObQ in HSumf, HPutf.
      rewrite HlenMv in HPutf. first [ clear - HSumf HPutf Hput Hleft Hrlen Hrl Hv1b Htie; lia | lia ]. }
    split. { rewrite HSumf, HObQ. reflexivity. }
    split. { rewrite HTabf. exact HTabQ. }
    split. { rewrite HWinf. exact HWinQ. }
    split. { rewrite HLastf. exact HLastQ. }
    split. { rewrite HWrapf. exact HWrapQ. }
    split. { rewrite HRetf. exact HRetQ. }
    split. { rewrite HInf. exact HInQ. }
    split. { rewrite HOutf. exact HOutQ. }
    split. { intro Hal. rewrite HBrf.
             exact (HhaM (HhaX (HhaD (HhaE Hal)))). }
    split. { rewrite HFlagf. exact HFlagQ. }
    split. { rewrite HCheckf. exact HCheckQ. }
    rewrite HTotalf. exact HTotalQ.
Qed.

Set Printing Width 2000.
