(** * KeyCodes — zr_codes_own: the CT_CODES keystone assembly.

    Proves q7's ONE MISSING INPUT
    (GtCodesBridge.v ): ownership of every root slot of an
    accepted CODES build by a coded symbol at true length with the
    canonical spelling fact, plus the val-is-the-symbol tie.  The
    [zr_codes_own] Definition below is a VERBATIM duplicate of q7's
    (until-landing-home rule); their
    [zr_codes_fetch_res_from_own] closes ZrCodesFetchRes by one
    application of [zr_codes_own_holds].

    HOME RULING (q7 chair, 2026-08-21): GtCodesBridge is
    [zr_codes_own]'s home — when the bridge lands, this duplicate
    RE-POINTS to it (one mechanical pass, the A1StmtsV3-home
    precedent; q7's bridge fork flags the exact Require/name lines).

    Route: my own_loop pipeline directly (NOT via zr_fill_class — the
    weakened Prop's marker arm cannot be refuted from the Prop alone,
    but OwnFin has no marker arm): CODES at PreGo is COMPLETE
    ([it_pre_go_codes_complete]: the it_incomplete guard at CT_CODES
    forces kraft-left <= 0, kraft-nonneg forces >= 0, it_kraft_mass
    turns lft = 0 into mass = 2^15), so the break state has huff = 0,
    it_finish is the identity, every root cell's position window is
    consumed, and OwnFin classifies each as OwnLeaf or OwnPtr; OwnPtr
    is refuted (its first child's codeword is longer than root, but
    every CODES length is <= max <= root — single-level, the q6
    ALL-CLEAR's shape); OwnLeaf is zr_root_own's payload verbatim,
    with code_for moved from maxBits 15 to 7 by
    [code_for_maxbits_le] (all lengths <= 7).  The ent witness is
    ent_of; the val tie is the x_match = 20 literal arm of it_entry
    (every CODES symbol is < 19 < 20). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees ItGTblRev ItGTblGeom ItGTblSortWin
  InftreesBridge ItGTblCover ItGSubCover Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6K ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtCodesBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import KeyTie KeyRank KeyBits KeyClass KeyStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** CODES at PreGo is complete. *)
Lemma it_pre_go_codes_complete : forall lens codes root0 t0 c st,
  it_pre CT_CODES lens codes root0 t0 = PreGo c st ->
  it_mass 15%nat 1 (sw_cnt lens codes) = 2 ^ 15.
Proof.
  intros lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  fold (sw_cnt lens codes) in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (sw_cnt lens codes)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (sw_cnt lens codes)) as [lft|] eqn:HK;
    [|discriminate H].
  destruct (it_incomplete CT_CODES lft
              (it_findmax 15%nat MAXBITS (sw_cnt lens codes))) eqn:HI;
    [discriminate H|].
  unfold it_incomplete in HI.
  rewrite Z.eqb_refl in HI.
  rewrite orb_true_l, andb_true_r in HI.
  apply Z.ltb_ge in HI.
  pose proof (it_kraft_nonneg 15%nat 1 1 (sw_cnt lens codes) lft
                ltac:(lia) HK) as Hnn.
  pose proof (it_kraft_mass 15%nat 1 1 (sw_cnt lens codes) lft HK) as HM.
  change (Z.of_nat 15) with 15 in HM.
  lia.
Qed.

(** code_for is maxBits-insensitive below the cap. *)
Lemma code_for_maxbits_le : forall (L : list nat) (m1 m2 sym : nat),
  (forall x, In x L -> (x <= m1)%nat) ->
  (m1 <= m2)%nat ->
  code_for L m1 sym = code_for L m2 sym.
Proof.
  intros L m1 m2 sym Hb Hle. unfold code_for.
  destruct (nth_error L sym) as [len|] eqn:Hn; [|reflexivity].
  pose proof (Hb len (nth_error_In L sym Hn)) as Hl.
  destruct (Nat.ltb_spec m1 len); destruct (Nat.ltb_spec m2 len);
    try lia; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [zr_codes_own]: re-point per homes ruling, q4 standing assent -
    the verbatim duplicate formerly here is DELETED; the Definition
    lives at its home, GtCodesBridge (Required above), per this file
    header note (until-landing-home rule, now executed in the bridge
    window). *)

(* ------------------------------------------------------------------ *)
(** ** The keystone *)

Theorem zr_codes_own_holds : zr_codes_own.
Proof.
  unfold zr_codes_own.
  intros cl lens cs out Hlen19 Hag Hb7 Hmod Hret Hpre'.
  destruct Hpre' as (c0 & st0 & Hpre).
  set (t0 := fun i : Z => cs (0 + i)) in *.
  assert (H19 : Z.of_nat (length cl) = 19)
    by (rewrite Hlen19; reflexivity).
  rewrite <- H19 in Hpre, Hmod, Hag.
  set (codes := Z.of_nat (length cl)) in *.
  assert (Hcodes0 : 0 <= codes) by (unfold codes; lia).
  assert (Hlensb : forall i, 0 <= i < codes -> 0 <= lens i <= 15).
  { intros i Hi.
    unfold arr_eq_on in Hag.
    rewrite (Hag i) by lia.
    unfold zlens.
    assert (Hlt : (Z.to_nat i < length cl)%nat)
      by (unfold codes in Hi; lia).
    pose proof (Hb7 (nth (Z.to_nat i) cl 0%nat) (nth_In cl 0%nat Hlt)).
    lia. }
  assert (Hroot0 : 1 <= 7 <= 15) by lia.
  destruct (cov_pre CT_CODES lens codes 7 t0 c0 st0 Hcodes0 Hlensb Hroot0
              Hpre) as [Hctx Hinv0].
  pose proof (ledger_pre CT_CODES lens codes 7 t0 c0 st0 Hcodes0 Hlensb
                Hroot0 Hpre) as Hled0.
  set (cnt0 := sw_cnt lens codes) in *.
  pose proof (it_pre_go_type CT_CODES lens codes 7 t0 c0 st0 Hpre) as Hcty.
  rewrite <- Hcty in Hled0.
  destruct (it_pre_go_argsc CT_CODES lens codes 7 t0 c0 st0 Hpre)
    as [Hxl Hxc].
  pose proof (it_pre_go_codes_pos CT_CODES lens codes 7 t0 c0 st0 Hcodes0
                Hpre) as Hcpos.
  pose proof (it_pre_go_work CT_CODES lens codes 7 t0 c0 st0 Hpre) as Hwk.
  assert (Hwr : forall s, 0 <= x_work c0 s < codes)
    by (intro s; rewrite Hwk; apply sort_work_range; exact Hcpos).
  assert (Hbr : forall b : nat,
             cnt0 (Z.of_nat b) = Z.of_nat (count_len cl b)).
  { intro b. unfold cnt0, codes.
    apply sw_cnt_agree_count_len. exact Hag. }
  pose proof Hctx as HctxC.
  destruct HctxC as (HrootB & _ & HmxB & Hmxnz & Hmxz & _ & _ & _ & _ & _
                     & _ & Hcase & Hrootmx).
  assert (Hmxr0 : x_max c0 <= 7).
  { destruct (Z_le_gt_dec (x_max c0) 7) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    assert (Hni : ~ In (Z.to_nat (x_max c0)) cl).
    { intro Hin. pose proof (Hb7 _ Hin) as Hb. lia. }
    pose proof (Hbr (Z.to_nat (x_max c0))) as Hb2.
    rewrite Z2Nat.id in Hb2 by lia.
    apply Hmxnz. rewrite Hb2.
    unfold count_len.
    rewrite (count_occ_not_In Nat.eq_dec) in Hni.
    lia. }
  assert (Hmxroot : x_max c0 <= x_root c0)
    by (exact (it_pre_go_max_le_root CT_CODES lens codes 7 t0 c0 st0 Hpre
                 Hmxr0)).
  assert (Htyd : x_type c0 = CT_LENS \/ x_type c0 = CT_DISTS
                 \/ x_max c0 <= x_root c0)
    by (right; right; exact Hmxroot).
  assert (Hlfs : forall stx, LeafShape (x_type c0) (it_here c0 stx)).
  { intro stx. rewrite Hcty.
    apply here_leafshape_codes.
    - exact (it_pre_go_codes_match lens codes 7 t0 c0 st0 Hpre).
    - intro s. specialize (Hwr s).
      unfold codes in Hwr. rewrite Hlen19 in Hwr. lia. }
  pose proof (it_pre_go_count CT_CODES lens codes 7 t0 c0 st0 Hpre)
    as Hcnt_st.
  destruct (it_pre_go_shape CT_CODES lens codes 7 t0 c0 st0 Hpre)
    as [Hdrop0 _].
  assert (Hown0 : Own c0 cnt0 cl (ent_of c0 cl) st0)
    by (apply (own_seed c0 cnt0 cl (ent_of c0 cl) st0 Hcnt_st Hdrop0);
        exact HrootB).
  assert (HagX : arr_eq_on (x_lens c0) (zlens cl) 0 (Z.of_nat (length cl)))
    by (rewrite Hxl; exact Hag).
  pose proof (it_pre_go_codes_complete lens codes 7 t0 c0 st0 Hpre) as HM15.
  fold cnt0 in HM15.
  (* dissect it_model *)
  unfold it_model in Hmod. rewrite Hpre in Hmod. cbv beta match in Hmod.
  revert Hmod.
  destruct (it_loop (S (Z.to_nat codes)) c0 st0) as [[st1|st1|tt]|]
    eqn:Hloop; intro Hmod; try discriminate Hmod.
  - (* ItBreak *)
    injection Hmod as <-.
    destruct (own_loop (S (Z.to_nat codes)) c0 cnt0 cl st0 st1 Hctx Hinv0
                Hled0 HagX Hxc Htyd Hlfs Hown0 Hloop) as [HFin HBrk].
    destruct HBrk as (Hm0 & Hcompl & _).
    specialize (Hcompl HM15).
    assert (HposM : Pos (it_mass 15%nat 1 cnt0) st1 = 2 ^ 15)
      by (unfold Pos; rewrite Hm0, HM15; lia).
    assert (Hfin_id : it_finish st1 = s_tbl st1)
      by (unfold it_finish; rewrite Hcompl; reflexivity).
    exists (ent_of c0 cl).
    split.
    + (* zr_root_own *)
      unfold zr_root_own. cbn [o_tbl o_bits].
      intros i Hi.
      rewrite Hfin_id.
      assert (Hread : codes_wb cs 0 (s_tbl st1) (0 + i) = s_tbl st1 i).
      { unfold codes_wb.
        destruct (Z.leb_spec 0 (0 + i)); [|lia].
        f_equal. lia. }
      rewrite Hread.
      assert (Hupos : 0 < 2 ^ (15 - x_root c0)) by (apply pow2_pos_z; lia).
      assert (Hgi : (zrev (Z.to_nat (x_root c0)) i + 1)
                      * 2 ^ (15 - x_root c0)
                    <= Pos (it_mass 15%nat 1 cnt0) st1).
      { rewrite HposM.
        pose proof (zrev_lt (Z.to_nat (x_root c0)) i) as Hzl.
        rewrite to_nat_pow in Hzl by lia.
        assert (Hpw : 2 ^ (x_root c0) * 2 ^ (15 - x_root c0) = 2 ^ 15)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        clear -Hzl Hpw Hupos. nia. }
      destruct (HFin i Hi Hgi) as [HL|HP].
      * destruct HL as (sym & cw & Hcf & Hlcw & Hread2 & Hbits & Hfirst).
        exists sym, cw.
        rewrite (code_for_maxbits_le cl 7%nat 15%nat sym Hb7 ltac:(lia)).
        exact (conj Hcf (conj Hlcw (conj Hread2 (conj Hbits Hfirst)))).
      * (* OwnPtr is impossible for CODES: single-level *)
        exfalso.
        destruct HP as (_ & Hop & _ & _ & Hkids).
        assert (Hop0 : 0 < 2 ^ (c_op (s_tbl st1 i)))
          by (apply pow2_pos_z; lia).
        destruct (Hkids 0 ltac:(lia)) as (sym & cw & Hcf & Hlb & _).
        revert Hcf. unfold code_for.
        destruct (nth_error cl sym) as [len|] eqn:Hne; intro Hcf;
          [|discriminate].
        revert Hcf.
        destruct (Nat.eqb_spec len 0) as [E|E]; cbn [orb]; intro Hcf;
          [discriminate|].
        revert Hcf.
        destruct (Nat.ltb_spec 15 len) as [E2|E2]; cbn [orb]; intro Hcf;
          [discriminate|].
        injection Hcf as <-.
        rewrite code_bits_length in Hlb.
        pose proof (nth_error_In cl sym Hne) as Hin.
        pose proof (Hbr len) as Hb2.
        assert (Hcl1 : (0 < count_len cl len)%nat)
          by (unfold count_len; apply count_occ_In; exact Hin).
        assert (Hlemx : Z.of_nat len <= x_max c0).
        { destruct (Z_le_gt_dec (Z.of_nat len) (x_max c0)) as [|Hgt];
            [assumption|]. exfalso.
          pose proof (Hmxz (Z.of_nat len) ltac:(lia)) as Hz.
          lia. }
        lia.
    + (* the val tie: x_match = 20 puts every CODES symbol in the
         literal arm *)
      intros sym cw Hcf.
      rewrite (code_for_maxbits_le cl 7%nat 15%nat sym Hb7 ltac:(lia))
        in Hcf.
      assert (Hs19 : (sym < length cl)%nat).
      { apply nth_error_Some.
        revert Hcf. unfold code_for.
        destruct (nth_error cl sym) eqn:Hne; intro Hcf; [|discriminate].
        discriminate. }
      unfold ent_of. rewrite Hcf.
      unfold ZReproQ6K.it_entry.
      rewrite (it_pre_go_codes_match lens codes 7 t0 c0 st0 Hpre).
      destruct (Z.ltb_spec (Z.of_nat sym + 1) 20) as [_|Habs].
      2:{ exfalso. rewrite Hlen19 in Hs19. lia. }
      apply val_mkCodeT_id. rewrite Hlen19 in Hs19. lia.
  - (* ItOverflow: o_ret = 1 *)
    injection Hmod as <-. cbn [o_ret] in Hret. lia.
Qed.
