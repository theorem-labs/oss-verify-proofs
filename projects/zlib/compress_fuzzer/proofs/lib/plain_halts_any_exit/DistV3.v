(** * DistV3 — the DIST ownership export at the TIGHT pack (additive
    sibling; an earlier development run fork, dynsel parcel, owner-authorized Route-B).

    PROVENANCE: telescope VERBATIM from the landed
    B3B5Stmts.dyn_two_own_dist_STMT (B3B5Stmts.v:84); ONE delta — the
    conclusion existential enriched loose->tight
    (zr_dist_ents -> Gap7Ents.zr_dist_ents1).  Proof body VERBATIM from
    the landed B3Asm.dyn_two_own_dist (B3Asm.v:224-443); declared
    deltas: (1) the PreGo arm's final conjunct swaps
    KeyPins.zr_dist_ents_of_tie for Gap7Ents.zr_dist_ents1_of_tie
    (identical telescopes; the tie is the same
    KeyClass.ent_of_tie-at-HxD); (2) the PreEmpty arm's vacuity closes
    zr_dist_ents1 with the same code_for_none_of_zero_counts move;
    (3) lens_bound_in qualified as B3Asm.lens_bound_in.  The landed
    pair B3B5Stmts/B3Asm is UNTOUCHED — this file is a pure bed ADD
    riding the Gap7 train.

    PA-EXPORTS: dyn_two_own_dist_v3.
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees InftreesBridge Inflate StepReach
  ItGSubCover ItGTblCover DynTblOkHolds ItGModelExt ItGTblSortWin
  ItGClassHead.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  Q6TblChain Q6TblChainCore ZReproQ6K ZReproQ6P A1StmtsV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require KeyStep KeyClass KeyPins.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGMarkersPop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGWidth ItGPfWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require B3B5Stmts B3Asm.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Gap7Ents.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Definition dyn_two_own_dist_v3_STMT : Prop :=
  forall d q' (lit dst : list nat),
    db_acc d -> db_installed d q' ->
    db_lens d = zlens (lit ++ dst) ->
    db_nlen d = Z.of_nat (length lit) ->
    db_ndist d = Z.of_nat (length dst) ->
    db_nlen d <= 286 ->
    db_ndist d <= 30 ->
    exists entd,
      zr_two_own_v3
        (tbl_of (q_st q') (t_distcode (s_tab (q_st q'))))
        (o_bits (db_o2 d)) dst entd
      /\ Gap7Ents.zr_dist_ents1 dst entd.

Theorem dyn_two_own_dist_v3 : dyn_two_own_dist_v3_STMT.
Proof.
  unfold dyn_two_own_dist_v3_STMT.
  intros d q' lit dst Hacc Hinst Hlens Hnlen Hndist Hb286 Hb30.
  pose proof Hacc as (HwfL & HmodL & HretL & HwfD & HmodD0 & HretD).
  pose proof HwfD as HwfDp. destruct HwfDp as (Hc0D & HlensBD & Hroot06 & HkindsD).
  set (t0D := (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d))
                          ((0 + o_used (db_o1 d)) + i))) in *.
  set (lensD := (fun i => db_lens d (i + db_nlen d))) in *.
  (* window agreement with the list form *)
  assert (Hag : arr_eq_on lensD (zlens dst) 0 (db_ndist d)).
  { intros i Hi. unfold lensD.
    rewrite Hlens, Hnlen.
    rewrite <- (zlens_skipn (length lit) (lit ++ dst) i ltac:(lia)).
    rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
    reflexivity. }
  (* the model at the list-form array *)
  assert (HmodD : it_model CT_DISTS (zlens dst) (db_ndist d) 6 t0D
                  = Some (db_o2 d)).
  { rewrite <- (it_model_lens_ext CT_DISTS lensD (zlens dst) (db_ndist d)
                  6 t0D ltac:(lia) Hag).
    exact HmodD0. }
  (* the DIST view is the second write-back layer, unbounded above *)
  assert (HviewD : forall i, 0 <= i ->
            tbl_of (q_st q') (t_distcode (s_tab (q_st q'))) i
            = o_tbl (db_o2 d) i).
  { intros i Hi.
    pose proof (db_view_dist d q' Hinst i Hi) as HV.
    destruct Hinst as (_ & _ & Hdc & _). rewrite Hdc. cbn [tbl_of]. exact HV. }
  set (T' := tbl_of (q_st q') (t_distcode (s_tab (q_st q')))) in *.
  (* case on the list-form pre-state *)
  destruct (it_pre CT_DISTS (zlens dst) (db_ndist d) 6 t0D)
    as [ | tE | | cD stD] eqn:HpreD.
  - (* PreErr: killed by the accepted return *)
    exfalso. unfold it_model in HmodD. rewrite HpreD in HmodD.
    injection HmodD as HmodD. rewrite <- HmodD in HretD.
    cbn in HretD. lia.
  - (* PreEmpty: the two-marker pair; vacuity closes everything *)
    unfold it_model in HmodD. rewrite HpreD in HmodD.
    injection HmodD as Ho2.
    (* counts are all zero *)
    assert (Hz : forall l : nat, (1 <= l <= 15)%nat ->
              count_len dst l = 0%nat).
    { unfold it_pre in HpreD. cbv zeta in HpreD.
      destruct (Z.eqb_spec
                  (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat (db_ndist d)) 0 (zlens dst) zzero))
                  0) as [Hmx0|Hmx0].
      - intros l Hl.
        pose proof (it_findmax_zero 15%nat MAXBITS
                      (it_count (Z.to_nat (db_ndist d)) 0 (zlens dst) zzero)
                      ltac:(unfold MAXBITS; lia)
                      ltac:(unfold MAXBITS; lia)
                      Hmx0 (Z.of_nat l)
                      ltac:(unfold MAXBITS; lia)) as Hc.
        assert (Htie : it_count (Z.to_nat (db_ndist d)) 0 (zlens dst) zzero
                       = it_cnt0 (zlens dst) (db_ndist d)) by reflexivity.
        rewrite Htie in Hc.
        rewrite Hndist, it_cnt0_zlens in Hc. lia.
      - exfalso.
        destruct (it_kraft 15%nat 1 1 _) in HpreD; [|discriminate HpreD].
        destruct (it_incomplete _ _ _) in HpreD; [discriminate HpreD|].
        destruct (it_enough _ _) in HpreD; discriminate HpreD. }
    (* the pair table under the view *)
    exists (fun _ => mkCodeT 0 0 0).
    split.
    + (* zr_two_own_v3: marker arm at both cells *)
      intros i Hi.
      rewrite <- Ho2 in Hi. cbn [o_bits] in Hi.
      right; right.
      assert (HTi : T' i = mkCodeT 64 1 0).
      { rewrite (HviewD i ltac:(lia)).
        rewrite <- Ho2. cbn [o_tbl].
        rewrite (it_pre_empty_shape CT_DISTS (zlens dst) (db_ndist d) 6
                   t0D tE HpreD).
        change (2 ^ 1) with 2 in Hi.
        destruct (Z.eq_dec i 1) as [->|Hne].
        - rewrite tset_same. reflexivity.
        - assert (i = 0) by lia. subst i.
          rewrite tset_other by lia. rewrite tset_same. reflexivity. }
      split; [exact HTi|].
      split; [rewrite <- Ho2; reflexivity|].
      split.
      * intros sym cw Hcf _.
        exfalso.
        exact (ItGWidth.code_for_none_of_zero_counts dst sym cw Hz Hcf).
      * intros sym cw Hcf _.
        exfalso.
        exact (ItGWidth.code_for_none_of_zero_counts dst sym cw Hz Hcf).
    + (* zr_dist_ents1: vacuous, same move *)
      intros sym cw Hcf.
      exfalso.
      exact (ItGWidth.code_for_none_of_zero_counts dst sym cw Hz Hcf).
  - (* PreOver: killed by the accepted return *)
    exfalso. unfold it_model in HmodD. rewrite HpreD in HmodD.
    injection HmodD as HmodD. rewrite <- HmodD in HretD.
    cbn in HretD. lia.
  - (* PreGo: the LEN mirror at the DIST window *)
    pose proof (B3B5Stmts.dyn_distbits_acc d Hacc) as Hbits2.
    (* nat length bound on the DIST window *)
    assert (Hl15D : forall len, In len dst -> (len <= 15)%nat).
    { apply (B3Asm.lens_bound_in dst [] (db_ndist d)).
      - exact Hndist.
      - intros i Hi. rewrite app_nil_r.
        rewrite <- (Hag i Hi). exact (HlensBD i Hi). }
    (* the Z.of_nat-spelled copies for the generic-lens keystone call *)
    assert (HpreDn : it_pre CT_DISTS (zlens dst) (Z.of_nat (length dst))
                       6 t0D = PreGo cD stD)
      by (rewrite <- Hndist; exact HpreD).
    assert (HmodDn : it_model CT_DISTS (zlens dst) (Z.of_nat (length dst))
                       6 t0D = Some (db_o2 d))
      by (rewrite <- Hndist; exact HmodD).
    (* zlens dst = zlens (dst ++ []) for the (l1 ++ l2)-shaped suppliers *)
    assert (Hdnil : dst ++ [] = dst) by apply app_nil_r.
    assert (HpreDz : it_pre CT_DISTS (zlens (dst ++ []))
                       (Z.of_nat (length dst)) 6 t0D = PreGo cD stD)
      by (rewrite Hdnil, <- Hndist; exact HpreD).
    assert (HmodDz : it_model CT_DISTS (zlens (dst ++ []))
                       (Z.of_nat (length dst)) 6 t0D = Some (db_o2 d))
      by (rewrite Hdnil, <- Hndist; exact HmodD).
    (* the converted it_wf, for the population corollary *)
    assert (HwfDz : it_wf CT_DISTS (zlens (dst ++ []))
                      (Z.of_nat (length dst)) 6).
    { split; [lia|]. split.
      - intros i Hi. rewrite Hdnil, <- (Hag i ltac:(lia)).
        apply HlensBD. lia.
      - split; [exact Hroot06|].
        right; right. split; [reflexivity|]. lia. }
    (* prefix-freeness at the DIST window *)
    assert (HpfD : forall s1 s2 cw1 cw2,
              code_for dst 15%nat s1 = Some cw1 ->
              code_for dst 15%nat s2 = Some cw2 ->
              s1 <> s2 -> is_prefix cw1 cw2 = false).
    { intros s1 s2 cw1 cw2 H1 H2 Hs.
      exact (ItGPfWin.window_codes_prefix_free CT_DISTS dst [] 6 t0D cD stD
               s1 s2 cw1 cw2 Hl15D HpreDz H1 H2 Hs). }
    (* the classification at the o_tbl side *)
    assert (HclsD : KeyClass.zr_fill_class (o_tbl (db_o2 d))
                      (o_bits (db_o2 d)) dst (KeyClass.ent_of cD dst)).
    { apply (KeyStep.fill_class_holds CT_DISTS dst (zlens dst) 6 t0D cD stD
               (db_o2 d)).
      - right; right; reflexivity.
      - intros _. lia.
      - intro HH; exfalso; unfold CT_CODES, CT_DISTS in HH; lia.
      - intro HH; exfalso; unfold CT_LENS, CT_DISTS in HH; lia.
      - intro HH; exfalso; unfold CT_CODES, CT_DISTS in HH; lia.
      - exact Hl15D.
      - lia.
      - intros i Hi; reflexivity.
      - exact HpreDn.
      - exact HmodDn.
      - exact HretD. }
    (* geometry at the o_tbl side, from the ORIGINAL array forms *)
    destruct (it_covers_all CT_DISTS lensD (db_ndist d) 6 t0D (db_o2 d)
                (or_intror eq_refl) HwfD HmodD0 HretD) as (HcuD & HrootD & _).
    set (rb := o_bits (db_o2 d)) in *.
    (* transported classification at the view *)
    assert (HclsD' : forall i, 0 <= i < 2 ^ rb ->
        (exists sym cw, code_for dst 15%nat sym = Some cw
           /\ Z.of_nat (length cw) <= rb
           /\ T' i = KeyClass.ent_of cD dst sym
           /\ c_bits (KeyClass.ent_of cD dst sym) = Z.of_nat (length cw)
           /\ firstn (length cw) (write_bits (Z.to_nat rb) i) = cw)
        \/ (c_bits (T' i) = rb
            /\ 1 <= c_op (T' i) <= 15 - rb
            /\ 2 ^ rb <= c_val (T' i)
            /\ ItGClassHead.zr_ptr_children T' rb dst (KeyClass.ent_of cD dst)
                 i (c_op (T' i)) (c_val (T' i)))
        \/ (T' i = mkCodeT 64 1 0 /\ rb = 1 /\ i = 1
            /\ count_len dst 1%nat = 1%nat
            /\ (forall l : nat, (2 <= l <= 15)%nat ->
                  count_len dst l = 0%nat))
        \/ (T' i = mkCodeT 64 1 0 /\ rb = 1
            /\ (forall l : nat, (1 <= l <= 15)%nat ->
                  count_len dst l = 0%nat))).
    { intros i Hi.
      destruct (HclsD i Hi) as [Hleaf | [Hptr | Hm]].
      - left.
        destruct Hleaf as (sym & cw & Hcf & Hlw & Hti & Hcb & Hfw).
        exists sym, cw.
        rewrite (HviewD i ltac:(lia)).
        repeat split; assumption.
      - right; left.
        destruct Hptr as (Hb & Hop & Hval & Hch).
        rewrite (HviewD i ltac:(lia)).
        refine (conj Hb (conj Hop (conj Hval _))).
        intros j Hj.
        destruct (Hch j Hj) as (sym & cw & Hcf & Hlw & Htj & Hcb & Hfw).
        exists sym, cw.
        assert (Hjn : 0 <= c_val (o_tbl (db_o2 d) i) + j)
          by (pose proof (pow2_pos_z rb ltac:(lia)); lia).
        rewrite (HviewD _ Hjn).
        exact (conj Hcf (conj Hlw (conj Htj (conj Hcb Hfw)))).
      - destruct Hm as (Hrec & Hr1 & Hi1).
        right; right; left.
        assert (Hmark : exists k, 0 <= k < 2 ^ (o_bits (db_o2 d))
                          /\ c_op (o_tbl (db_o2 d) k) = 64)
          by (exists i; split; [exact Hi | rewrite Hrec; reflexivity]).
        destruct (ItGMarkersPop.marker_population_counts_win CT_DISTS dst []
                    6 t0D cD stD (db_o2 d)
                    (or_intror eq_refl)
                    ltac:(intros _; lia)
                    HwfDz HpreDz HmodDz HretD Hmark) as (Hc1 & Hh2).
        rewrite (HviewD i ltac:(lia)).
        repeat split; assumption. }
    (* the ctx root is nonnegative — for the ent tie *)
    assert (HxD : 0 <= x_root cD).
    { destruct (cov_pre CT_DISTS (zlens dst) (db_ndist d) 6 t0D cD stD
                  ltac:(lia)
                  ltac:(intros i Hi; rewrite <- (Hag i Hi);
                        exact (HlensBD i Hi))
                  ltac:(lia) HpreD) as [Hctx _].
      destruct Hctx as (Hxr & _). lia. }
    exists (KeyClass.ent_of cD dst).
    split.
    + exact (ItGWidth.two_own_v3_of_parts T' rb dst
               (KeyClass.ent_of cD dst) ltac:(lia) HpfD HclsD').
    + apply (Gap7Ents.zr_dist_ents1_of_tie cD (zlens dst) (db_ndist d) 6 t0D
               stD dst (KeyClass.ent_of cD dst) HpreD).
      * lia.
      * intro sym. exact (KeyClass.ent_of_tie cD dst sym HxD).
Qed.

Set Printing Width 2000.
Print Assumptions dyn_two_own_dist_v3.
