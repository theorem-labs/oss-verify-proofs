(** * LkFetch2 — the TWO-LEVEL fetch kills for the K3 good-only walks
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    LkFetch's no-starve/no-fuel package at the BUILT tables: ownership
    is [zr_two_own_v3] (root leaves + sub-table pointers + the max==1
    marker), so a starve point has three shapes and each dies against
    the premise's [hdecode] success on the same stream:

      - LEAF: the fixed-table argument verbatim (the decodable word is
        a proper prefix of the owner's, refuting prefix-freeness);
      - POINTER: any child's full code extends the root index the
        whole stream spells, so the decodable word is its proper
        prefix — same refutation, child 0 as witness;
      - MARKER: root = 1 and the stream is empty at the starve, so
        the decodable word is [] — dead against [zr_no_short_code].

    The sub-table starve ([inf_fetch2]) uses the selected child at the
    machine's window index: [zr_spell_two] + [zrA_shiftr_bits_mod]
    spell the stream's first [|cw0|] bits as exactly the child code's
    truncation, so the decodable word is again a proper prefix.

    PA-EXPORTS: lk_decode_two_no_leave, lk_decode_two_no_fuel. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate
  DecodeBridge ItGWidth ItGClassHead.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6M ZReproQ6P ZReproQ6T A1StmtsV3 A1core.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkFetch.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Fuel: the sub-table fetch never answers FetchFuel either.
   ========================================================================== *)

Lemma lk_fetch2_go_no_fuel : forall f (t : ztbl) (lst : Code) (b : BR),
  0 <= br_have b -> (Z.to_nat (br_have b) < f)%nat ->
  inf_fetch2_go f t lst b <> FetchFuel.
Proof.
  induction f as [|f IH]; intros t lst b Hv Hf; [lia|].
  cbn [inf_fetch2_go]. cbv zeta.
  destruct (Z.leb (c_bits lst
                   + c_bits (t (c_val lst
                                + Z.shiftr (br_bits_of
                                              (c_bits lst + c_op lst) b)
                                           (c_bits lst))))
                  (br_bits b)); [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:EP; [|discriminate].
  assert (Hne : br_have b <> 0).
  { intro E0. rewrite (proj2 (br_pullbyte_none b) E0) in EP.
    discriminate. }
  destruct (br_pullbyte_step b b1 EP) as (Hh1 & _ & _ & _).
  apply IH; lia.
Qed.

(* ==========================================================================
   2.  Root fetch: no starve under two-own + declarative success.
   ========================================================================== *)

Lemma lk_fetch_go_two_no_starve :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    forall f b (sym0 : nat) (rem0 : list bool) b',
      br_wf b ->
      hdecode (code_table lens 15%nat) (br_stream b)
      = Some (sym0, rem0) ->
      inf_fetch_go f T root b <> FetchLeave b'.
Proof.
  intros T root lens ent Hroot HV Hown.
  induction f as [|f IH]; intros b sym0 rem0 b' Hwf Hdec;
    cbn [inf_fetch_go]; cbv zeta; [discriminate|].
  pose proof (DecodeBridge.br_bits_of_in_range root b ltac:(lia)) as Hir.
  destruct (Z.leb_spec (c_bits (T (br_bits_of root b))) (br_bits b))
    as [Hle|Hgt]; [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:EP.
  - (* a successful pull transports everything *)
    assert (H31 : br_bits b <= 31).
    { pose proof (zrA_two_own_cbits T root lens ent ltac:(lia) Hown
                    (br_bits_of root b) Hir). lia. }
    assert (Hwf1 : br_wf b1) by (apply (br_wf_pullbyte b b1 Hwf H31 EP)).
    pose proof (br_stream_pullbyte b b1 Hwf EP) as HS1.
    apply (IH b1 sym0 rem0 b' Hwf1).
    rewrite HS1. exact Hdec.
  - (* THE STARVE POINT *)
    intros _.
    assert (Hh0 : br_have b = 0)
      by (apply (proj1 (br_pullbyte_none b)); exact EP).
    pose proof (br_stream_length b Hwf) as HL.
    rewrite Hh0 in HL.
    destruct (hdecode_sound nat (code_table lens 15%nat)
                (br_stream b) sym0 rem0 Hdec)
      as (cw0 & Hin0 & Hpf0 & Hsplit).
    assert (Hcf0 : code_for lens 15%nat sym0 = Some cw0)
      by (apply (proj1 (code_table_In_iff lens 15%nat sym0 cw0));
          exact Hin0).
    assert (Hlen0 : (length cw0 <= length (br_stream b))%nat)
      by (rewrite Hsplit, length_app; lia).
    destruct (Hown (br_bits_of root b) Hir)
      as [ (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref)
         | [ (Hcb & Hop & Hval & Hwc & Hch)
           | (Hrec & Hro1 & Hns & Hnl) ] ].
    + (* LEAF: the fixed-table refutation *)
      rewrite HTi, Hcb in Hgt.
      assert (Hcwlt : (length cw0 < length cw)%nat) by lia.
      assert (Hspell : write_bits (length cw0) (br_bits_of root b) = cw0).
      { pose proof (br_index_spells_stream (Z.of_nat (length cw0)) root b
                      ltac:(lia) ltac:(lia)) as HS.
        change ZBitsBridge.br_stream with br_stream in HS.
        rewrite Nat2Z.id in HS.
        rewrite (is_prefix_firstn cw0 (br_stream b) Hpf0) in HS.
        exact HS. }
      assert (Hsub : firstn (length cw0) cw = cw0).
      { rewrite <- Hpref.
        rewrite firstn_firstn.
        rewrite Nat.min_l by lia.
        rewrite (DecodeBridge.firstn_write_bits (Z.to_nat root)
                   (length cw0) (br_bits_of root b)) by lia.
        exact Hspell. }
      assert (Hpfx : is_prefix cw0 cw = true)
        by (apply is_prefix_of_firstn; exact Hsub).
      assert (Hin : In (cw, sym) (code_table lens 15%nat))
        by (apply (proj2 (code_table_In_iff lens 15%nat sym cw));
            exact Hcf).
      assert (Hne : (cw0, sym0) <> (cw, sym)).
      { intro E. injection E as Ecw _.
        apply (f_equal (@length bool)) in Ecw. lia. }
      pose proof (code_table_prefix_free lens 15%nat HV
                    cw0 sym0 cw sym Hin0 Hin Hne) as Hff.
      rewrite Hpfx in Hff. discriminate.
    + (* POINTER: child 0 as the long witness *)
      rewrite Hcb in Hgt.
      assert (Hspell : write_bits (length cw0) (br_bits_of root b) = cw0).
      { pose proof (br_index_spells_stream (Z.of_nat (length cw0)) root b
                      ltac:(lia) ltac:(lia)) as HS.
        change ZBitsBridge.br_stream with br_stream in HS.
        rewrite Nat2Z.id in HS.
        rewrite (is_prefix_firstn cw0 (br_stream b) Hpf0) in HS.
        exact HS. }
      destruct (Hch 0 ltac:(split; [lia|];
                            apply Z.pow_pos_nonneg; lia))
        as (sym & cw & Hcf & Hrng & HTj & Hcbj & Hsp).
      assert (Hcwlt : (length cw0 < length cw)%nat) by lia.
      assert (Hsub : firstn (length cw0) cw = cw0).
      { rewrite <- Hsp.
        rewrite firstn_firstn.
        rewrite Nat.min_l by lia.
        rewrite firstn_app.
        rewrite write_bits_length.
        replace (length cw0 - Z.to_nat root)%nat with 0%nat by lia.
        cbn [firstn]. rewrite app_nil_r.
        rewrite (DecodeBridge.firstn_write_bits (Z.to_nat root)
                   (length cw0) (br_bits_of root b)) by lia.
        exact Hspell. }
      assert (Hpfx : is_prefix cw0 cw = true)
        by (apply is_prefix_of_firstn; exact Hsub).
      assert (Hin : In (cw, sym) (code_table lens 15%nat))
        by (apply (proj2 (code_table_In_iff lens 15%nat sym cw));
            exact Hcf).
      assert (Hne : (cw0, sym0) <> (cw, sym)).
      { intro E. injection E as Ecw _.
        apply (f_equal (@length bool)) in Ecw. lia. }
      pose proof (code_table_prefix_free lens 15%nat HV
                    cw0 sym0 cw sym Hin0 Hin Hne) as Hff.
      rewrite Hpfx in Hff. discriminate.
    + (* MARKER: the stream is empty, dead against no-short *)
      assert (Hc1 : c_bits (mkCodeT 64 1 0) = 1) by reflexivity.
      rewrite Hrec, Hc1 in Hgt.
      assert (Hnil : cw0 = []).
      { apply length_zero_iff_nil. lia. }
      subst cw0.
      exact (Hns sym0 [] Hcf0 ltac:(cbn [length]; lia) eq_refl).
Qed.

(* ==========================================================================
   3.  Sub-table fetch: no starve under the children pack.
   ========================================================================== *)

Lemma lk_fetch2_go_no_starve :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (i0 : Z) (h0 : Code),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    c_bits h0 = root ->
    1 <= c_op h0 <= 15 - root ->
    zr_ptr_children T root lens ent i0 (c_op h0) (c_val h0) ->
    forall f b (sym0 : nat) (rem0 : list bool) b',
      br_wf b ->
      root <= br_bits b ->
      firstn (Z.to_nat root) (br_stream b)
      = write_bits (Z.to_nat root) i0 ->
      hdecode (code_table lens 15%nat) (br_stream b)
      = Some (sym0, rem0) ->
      inf_fetch2_go f T h0 b <> FetchLeave b'.
Proof.
  intros T root lens ent i0 h0 Hroot HV Hcb0 Hop0 Hch.
  induction f as [|f IH]; intros b sym0 rem0 b' Hwf Hrb Hpre Hdec;
    cbn [inf_fetch2_go]; cbv zeta; [discriminate|].
  destruct (Z.leb_spec
              (c_bits h0
               + c_bits (T (c_val h0
                            + Z.shiftr (br_bits_of (c_bits h0 + c_op h0) b)
                                       (c_bits h0))))
              (br_bits b)) as [Hle|Hgt]; [discriminate|].
  (* the selected child *)
  assert (Hjw : 0 <= Z.shiftr (br_bits_of (c_bits h0 + c_op h0) b)
                              (c_bits h0)
                < 2 ^ c_op h0).
  { rewrite Hcb0.
    pose proof (zrA_bits_window (root + c_op h0) root b
                  ltac:(lia)
                  ltac:(destruct Hwf as (_ & Hh & _); lia)) as HW.
    replace (root + c_op h0 - root) with (c_op h0) in HW by lia.
    exact HW. }
  set (jw := Z.shiftr (br_bits_of (c_bits h0 + c_op h0) b) (c_bits h0))
    in *.
  destruct (Hch jw Hjw) as (sym & cw & Hcf & Hrng & HTj & Hcbj & Hsp).
  rewrite Hcb0 in Hgt.
  rewrite HTj, Hcbj in Hgt.
  destruct (br_pullbyte b) as [b1|] eqn:EP.
  - (* pull: transport *)
    assert (H31 : br_bits b <= 31) by lia.
    assert (Hwf1 : br_wf b1) by (apply (br_wf_pullbyte b b1 Hwf H31 EP)).
    destruct (br_pullbyte_step b b1 EP) as (_ & _ & Hb8 & _).
    pose proof (br_stream_pullbyte b b1 Hwf EP) as HS1.
    apply (IH b1 sym0 rem0 b' Hwf1 ltac:(lia)
             ltac:(rewrite HS1; exact Hpre)
             ltac:(rewrite HS1; exact Hdec)).
  - (* THE STARVE POINT *)
    intros _.
    assert (Hh0v : br_have b = 0)
      by (apply (proj1 (br_pullbyte_none b)); exact EP).
    pose proof (br_stream_length b Hwf) as HL.
    rewrite Hh0v in HL.
    destruct (hdecode_sound nat (code_table lens 15%nat)
                (br_stream b) sym0 rem0 Hdec)
      as (cw0 & Hin0 & Hpf0 & Hsplit).
    assert (Hcf0 : code_for lens 15%nat sym0 = Some cw0)
      by (apply (proj1 (code_table_In_iff lens 15%nat sym0 cw0));
          exact Hin0).
    assert (Hlen0 : (length cw0 <= length (br_stream b))%nat)
      by (rewrite Hsplit, length_app; lia).
    assert (Hfp0 : firstn (length cw0) (br_stream b) = cw0)
      by (apply is_prefix_firstn; exact Hpf0).
    assert (Hcwlt : (length cw0 < length cw)%nat) by lia.
    assert (Hin : In (cw, sym) (code_table lens 15%nat))
      by (apply (proj2 (code_table_In_iff lens 15%nat sym cw));
          exact Hcf).
    assert (Hne : (cw0, sym0) <> (cw, sym)).
    { intro E. injection E as Ecw _.
      apply (f_equal (@length bool)) in Ecw. lia. }
    (* cw0 is a prefix of the child's full code *)
    assert (Hsub : firstn (length cw0) cw = cw0).
    { destruct (Z.le_gt_cases (Z.of_nat (length cw0)) root) as [Hshort|Hlong].
      - (* short: inside the root slab *)
        rewrite <- Hsp.
        rewrite firstn_firstn.
        rewrite Nat.min_l by lia.
        rewrite firstn_app.
        rewrite write_bits_length.
        replace (length cw0 - Z.to_nat root)%nat with 0%nat by lia.
        cbn [firstn]. rewrite app_nil_r.
        rewrite <- Hpre.
        rewrite firstn_firstn.
        rewrite Nat.min_l by lia.
        exact Hfp0.
      - (* long: root slab + the m-bit window slab *)
        set (m := Z.of_nat (length cw0) - root).
        assert (Hm : 0 < m) by (unfold m; lia).
        assert (Hmop : m <= c_op h0) by (unfold m; lia).
        assert (Hlcw0 : (length cw0 = Z.to_nat root + Z.to_nat m)%nat)
          by (unfold m; lia).
        (* the stream's first |cw0| bits, two slabs *)
        pose proof (ZReproQ6T.zr_spell_two root m b
                      ltac:(lia) ltac:(lia) ltac:(unfold m; lia) Hwf)
          as HSP.
        change ZBitsBridge.br_stream with br_stream in HSP.
        pose proof (br_index_spells_stream root root b
                      ltac:(lia) ltac:(lia)) as HS1.
        change ZBitsBridge.br_stream with br_stream in HS1.
        rewrite HS1, Hpre in HSP.
        assert (HM : jw mod 2 ^ m
                     = Z.shiftr (br_bits_of (root + m) b) root).
        { unfold jw. rewrite Hcb0.
          exact (zrA_shiftr_bits_mod b root m (c_op h0)
                   ltac:(lia) ltac:(lia)
                   ltac:(destruct Hwf as (_ & Hh & _); lia)). }
        rewrite <- HM in HSP.
        rewrite (DecodeBridge.write_bits_mod_pow2 (Z.to_nat m) m jw
                   ltac:(rewrite Z2Nat.id by lia; lia)) in HSP.
        (* cw0 IS that two-slab spelling *)
        assert (Hcw0sp : cw0 = write_bits (Z.to_nat root) i0
                               ++ write_bits (Z.to_nat m) jw).
        { rewrite <- Hfp0.
          replace (length cw0) with (Z.to_nat (root + m))
            by (rewrite Z2Nat.inj_add by lia; lia).
          exact HSP. }
        (* the child's |cw0|-truncation is the same spelling *)
        rewrite <- Hsp.
        rewrite firstn_firstn.
        rewrite Nat.min_l by lia.
        rewrite Hlcw0.
        rewrite firstn_app.
        rewrite write_bits_length.
        replace (Z.to_nat root + Z.to_nat m - Z.to_nat root)%nat
          with (Z.to_nat m) by lia.
        rewrite firstn_all2
          by (rewrite write_bits_length; lia).
        rewrite (DecodeBridge.firstn_write_bits (Z.to_nat (c_op h0))
                   (Z.to_nat m) jw)
          by (apply Nat2Z.inj_le; rewrite !Z2Nat.id by lia; lia).
        symmetry. exact Hcw0sp. }
    assert (Hpfx : is_prefix cw0 cw = true)
      by (apply is_prefix_of_firstn; exact Hsub).
    pose proof (code_table_prefix_free lens 15%nat HV
                  cw0 sym0 cw sym Hin0 Hin Hne) as Hff.
    rewrite Hpfx in Hff. discriminate.
Qed.

(* ==========================================================================
   4.  The [inf_decode] corollaries at two-level tables.
   ========================================================================== *)

Lemma lk_decode_two_no_leave :
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (ent : nat -> Code) b (sym0 : nat) (rem0 : list bool) b2,
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    (forall sym cw, code_for lens 15%nat sym = Some cw ->
         sub (ent sym) = false) ->
    (forall e, c_op e <> 0 -> Z.land (c_op e) 240 = 0 -> sub e = true) ->
    sub (mkCodeT 64 1 0) = false ->
    br_wf b ->
    hdecode (code_table lens 15%nat) (br_stream b) = Some (sym0, rem0) ->
    inf_decode sub T root b <> DecLeave b2.
Proof.
  intros sub T root lens ent b sym0 rem0 b2 Hroot HV Hown HsubL HsubP
         HsubM Hwf Hdec.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode_two T root lens ent b Hroot HV Hown Hwf)
    as HF.
  unfold zr_fetch_hdecode_two_STMT in HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF.
  - destruct HF as (Hs0 & Hwf0 & _ & Hbb0 & HC).
    destruct HC as [ (sym & cw & Hcf & Hent & Hcbw & Hhd)
                   | [ (i & Hir & Hh0 & Hcb & Hop & Hval & Hrb0
                        & Hpre0 & Hwc & Hch)
                     | (Hrec & Hnone) ] ].
    + (* leaf: sub false, DecOk *)
      rewrite Hent, (HsubL sym cw Hcf). discriminate.
    + (* pointer: sub true, chase fetch2 *)
      assert (Hsub0 : sub h0 = true).
      { apply HsubP; [lia|].
        apply zrA_land240_small. lia. }
      rewrite Hsub0.
      unfold inf_fetch2.
      destruct (inf_fetch2_go (S (Z.to_nat (br_have b0))) T h0 b0)
        as [h1 b1|b1|] eqn:EF2; [discriminate| |].
      * exfalso.
        refine (lk_fetch2_go_no_starve T root lens ent i h0 Hroot HV
                  Hcb Hop Hch _ b0 sym0 rem0 b1 Hwf0 _ Hpre0 _ EF2).
        -- exact Hrb0.
        -- rewrite Hs0. exact Hdec.
      * exfalso.
        destruct Hwf0 as (_ & _ & Hv0 & _).
        exact (lk_fetch2_go_no_fuel (S (Z.to_nat (br_have b0))) T h0 b0
                 Hv0 ltac:(lia) EF2).
    + (* marker: sub false, DecOk *)
      rewrite Hrec, HsubM. discriminate.
  - exfalso.
    unfold inf_fetch in EF.
    exact (lk_fetch_go_two_no_starve T root lens ent Hroot HV Hown
             _ b sym0 rem0 b0 Hwf Hdec EF).
  - discriminate.
Qed.

Lemma lk_decode_two_no_fuel :
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (ent : nat -> Code) b (sym0 : nat) (rem0 : list bool),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    (forall sym cw, code_for lens 15%nat sym = Some cw ->
         sub (ent sym) = false) ->
    (forall e, c_op e <> 0 -> Z.land (c_op e) 240 = 0 -> sub e = true) ->
    sub (mkCodeT 64 1 0) = false ->
    br_wf b ->
    hdecode (code_table lens 15%nat) (br_stream b) = Some (sym0, rem0) ->
    inf_decode sub T root b <> DecFuel.
Proof.
  intros sub T root lens ent b sym0 rem0 Hroot HV Hown HsubL HsubP
         HsubM Hwf Hdec.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode_two T root lens ent b Hroot HV Hown Hwf)
    as HF.
  unfold zr_fetch_hdecode_two_STMT in HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF.
  - destruct HF as (Hs0 & Hwf0 & _ & Hbb0 & HC).
    destruct HC as [ (sym & cw & Hcf & Hent & Hcbw & Hhd)
                   | [ (i & Hir & Hh0 & Hcb & Hop & Hval & Hrb0
                        & Hpre0 & Hwc & Hch)
                     | (Hrec & Hnone) ] ].
    + rewrite Hent, (HsubL sym cw Hcf). discriminate.
    + assert (Hsub0 : sub h0 = true).
      { apply HsubP; [lia|].
        apply zrA_land240_small. lia. }
      rewrite Hsub0.
      unfold inf_fetch2.
      destruct (inf_fetch2_go (S (Z.to_nat (br_have b0))) T h0 b0)
        as [h1 b1|b1|] eqn:EF2; [discriminate|discriminate|].
      exfalso.
      destruct Hwf0 as (_ & _ & Hv0 & _).
      exact (lk_fetch2_go_no_fuel (S (Z.to_nat (br_have b0))) T h0 b0
               Hv0 ltac:(lia) EF2).
    + rewrite Hrec, HsubM. discriminate.
  - discriminate.
  - exfalso.
    destruct Hwf as (_ & _ & Hv & _).
    unfold inf_fetch in EF.
    exact (lk_fetch_go_no_fuel (S (Z.to_nat (br_have b))) T root b
             Hv ltac:(lia) EF).
Qed.

Set Printing Width 2000.
Print Assumptions lk_decode_two_no_leave.
Print Assumptions lk_decode_two_no_fuel.
