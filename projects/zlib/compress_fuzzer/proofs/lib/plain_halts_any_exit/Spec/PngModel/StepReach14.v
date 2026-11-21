
From Stdlib Require Import ZArith List Lia Bool.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtLenProv.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import CfgBitsTblLeaf.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblLeafPos ItGTblLeafPosX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGTblSortWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy14.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

#[local] Ltac ubk :=
  cbn [q_st qset_st qset_br qset_ob qmode qbad];
  repeat first [ rewrite uback_set_back | rewrite uback_set_length
               | rewrite uback_set_offset | rewrite uback_set_extra
               | rewrite uback_set_was | rewrite uback_set_mode ].

Theorem step_ok14_reachable :
  forall c q,
    ReachSt q ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS ->
       forall q', q_mode q' = M_CODELENS -> q_pos q' ->
         arm_ok q' (inf_CODELENS14 c q')) ->
    (q_mode q = M_CODELENS ->
       forall q', q_mode q' = M_LEN_ -> q_pos q' ->
         arm_ok q' (inf_LEN_14 q')) ->
    step_ok14 c q.
Proof.
  intros c q (Hcore & Hmode) HCL HLEN.
  destruct Hcore as [Hpos Hbits Hbytes Hhold Hwin Hwnext Hwhave Hsane
                     Hlen0 Hinbud Hleft24 Hlens Hbhave Hbnlen Hbndist
                     Hamb].
  destruct Hmode as [Hmatch Hlen1 Hextra Hoffext Hlenub HtblL HtblCL
                     Hbldrng Hlens7].
  assert (Hhave24 : br_have (q_br q) <= 4294967290)
    by (destruct Hpos as (_ & Hb0 & _); lia).
  apply step_ok14_covered.
  - exact Hpos.
  - exact Hlen0.
  - exact Hmatch.
  - intros _. split; [intros j; exact (proj1 (Hbytes j)) | exact Hhold].
  - intros Hm. split; [exact (Hlen1 Hm) | exact (proj1 Hwnext)].
  - exact Hextra.
  - intros Hm.
    assert (HL : LenTblSide q).
    { apply HtblL.
      destruct Hm as [Hm|Hm]; [right; right; left; exact Hm
                              | right; right; right; left; exact Hm]. }
    exact (proj1 (proj2 (proj2 HL))).
  - exact Hoffext.
  - intros Hm.
    assert (HL : LenTblSide q).
    { apply HtblL.
      destruct Hm as [Hm|Hm]; [left; exact Hm | right; left; exact Hm]. }
    destruct HL as (Htbl & Hlcs & Htds & Hlt & Hdt & Hlbnd & Hlb & Hdb & Hroot0).
    split.
    { intros Hgate.
      unfold len_gate14 in Hgate. apply andb_prop in Hgate as [Hgate _]. apply andb_prop in Hgate as [G1 G2].
      apply Z.leb_le in G1. apply Z.leb_le in G2.
      pose proof Hpos as (Hh & Hb & Hl).
      assert (Hb40 : 0 <= a_bits (len_args q) <= 40)
        by (cbn [len_args a_bits]; lia).
      split.
      { split; [exact G1|]. split; [exact G2|].
        split; [exact Hb40|].
        split; [exact Hlb|]. split; [exact Hdb|].
        split; [exact Hsane|].
        split; [exact Hwhave|]. split; [exact Hwnext|].
        split; [exact Hbytes|]. split; [exact Hwin|].
        split; [exact Hlt|]. split; [exact Hdt|]. exact Hlbnd. }
      split; [exact Htbl|].
      split; [exact Hhave24 | exact Hleft24]. }
    split; [exact Hlcs|]. split; [exact Htds|]. exact (proj1 Hwnext).
  - intros _. exact Hlens.
  - exact HCL.
  - intros Hm.
    split; [exact (HtblCL Hm)|].
    split; [exact Hbhave|]. split; [exact Hbnlen|].
    split; [exact Hbndist|].
    exact (HLEN Hm).
Qed.

Lemma tail_LEN14_ok :
  forall q', q_mode q' = M_LEN_ -> CoreFacts q' -> LenTblSide q' ->
    arm_ok q' (inf_LEN_14 q').
Proof.
  intros q' Hm (Hpos & Hbits & Hbytes & Hwin & Hwnext & Hwhave & Hsane
                & Hh24 & Hl24 & Hhold & Hamb) HL.
  destruct HL as (Htbl & Hlcs & Htds & Hlt & Hdt & Hlbnd & Hlb & Hdb & Hroot0).
  apply arm_LEN_14; try assumption.
  2:{ exact (proj1 Hwnext). }
  - intros Hgate.
    unfold len_gate14 in Hgate. apply andb_prop in Hgate as [Hgate _]. apply andb_prop in Hgate as [G1 G2].
    apply Z.leb_le in G1. apply Z.leb_le in G2.
    pose proof Hpos as (Hh & Hb & Hl).
    assert (Hb40 : 0 <= a_bits (len_args q') <= 40)
      by (cbn [len_args a_bits]; lia).
    split.
    { split; [exact G1|]. split; [exact G2|].
      split; [exact Hb40|].
      split; [exact Hlb|]. split; [exact Hdb|].
      split; [exact Hsane|].
      split; [exact Hwhave|]. split; [exact Hwnext|].
      split; [exact Hbytes|]. split; [exact Hwin|].
      split; [exact Hlt|]. split; [exact Hdt|]. exact Hlbnd. }
    split; [exact Htbl|].
    split; [lia | exact Hl24].
Qed.

Section Knot14.

Variable Hdyn : DynTblOk.

(** [inf_CODELENS14] with the LEN_ tail DISCHARGED: where the landed
    [arm_CODELENS] carries the tail as a quantified premise (the coverage
    ledger, retention convention), this one hands the constructed state to
    [tail_LEN14_ok], with the table bundle produced by [Hdyn] at the
    [DynBuild] the arm itself just accepted. *)
(* RSS cure C1' (ca2-b1 / F47, 2026-09-08): measured by one-conjunct probes, the two CoreFacts conjuncts whose goal projects the
   constructed state's TABLE (t_sane / t_codes through eight nested set_* on s_tab) cost 30 s and ~1.4 GiB EACH under `ksimp` (cbn refolding the setter
   chain) and 1.5 s / 0.47 GiB under the bare `exact` (lazy conversion); the two `ksimp` calls are dropped, nothing else moves. *)
Lemma reach_CODELENS14 :
  forall c q,
    q_mode q = M_CODELENS ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    arm_ok q (inf_CODELENS14 c q).
Proof.
  intros c q Hm Hcore Hlens Hhave Hnlen Hndist Htl.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  assert (Hnlen0 : 0 <= b_nlen (s_bld (q_st q))) by lia.
  assert (Hndist0 : 0 <= b_ndist (s_bld (q_st q))) by lia.
  unfold inf_CODELENS14. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hlens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  pose proof (cl_loop_env
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hhold
                (fun j => proj1 (Hbytes j)) H39 Hlens Hr) as HE.
  cbn [cl_br cl_lens cl_have] in HE.
  pose proof (cl_loop_have_mono
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Hr) as HM.
  cbn [cl_br cl_lens cl_have] in HM.
  pose proof (cl_loop_inbud
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r
                (fun i => proj1 (proj1 (Htl i))) Hr) as HBgt.
  cbn [cl_br cl_lens cl_have] in HBgt.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction; [| |exact I].
  - (* ClDone: the two builds, then the DISCHARGED LEN_ tail *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HM.
    destruct (Z.eqb (cl_lens s1 256) 0).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    unfold inf_table.
    assert (HLB1 : GtItTotal.LensBounded (cl_lens s1) (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen0 HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
    assert (HLB2 : GtItTotal.LensBounded
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist0 HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)) eqn:Er2.
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    apply Bool.negb_false_iff in Er2. apply Z.eqb_eq in Er2.
    destruct (Z.eqb (n_flush c) Z_TREES); [exact I|].
    (* The accepted build, named *)
    assert (HWF1 : it_wf CT_LENS (cl_lens s1) (b_nlen (s_bld (q_st q))) 9).
    { split; [lia|]. split; [intros i _; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; left; split; [reflexivity | lia]. }
    assert (HWF2 : it_wf CT_DISTS
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))) 6).
    { split; [lia|]. split; [intros i _; cbv beta; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; right; split; [reflexivity | lia]. }
    set (d := {| db_cs := t_codes (s_tab (q_st q));
                 db_lens := cl_lens s1;
                 db_nlen := b_nlen (s_bld (q_st q));
                 db_ndist := b_ndist (s_bld (q_st q));
                 db_o1 := o1; db_o2 := o2 |}).
    assert (Hdok : db_ok d).
    { split; [exact Hamb|].
      split; [exact HWF1|].
      split; [exact (eq_sym EI1)|].
      split; [exact Er1|].
      split; [exact HWF2|].
      split; [exact (eq_sym EI2)|].
      exact Er2. }
    match goal with
    | |- arm_ok _ (inf_LEN_14 ?qq) =>
        assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
    end.
    eapply (arm_ok_mono _ q).
    2:{ apply tail_LEN14_ok.
        - bsimp; reflexivity.
        - (* CoreFacts at the constructed tail *)
          split. { unfold q_pos. ksimp. repeat split; lia. }
          split. { ksimp. lia. }
          split. { intros j. ksimp. rewrite Ein. exact (Hbytes j). }
          split. { intros j. ksimp. exact (Hwinb j). }
          split. { ksimp. lia. }
          split. { ksimp. lia. }
          split. { exact Hsane. }
          split. { ksimp. lia. }
          split. { ksimp. lia. }
          split. { ksimp. exact Ehold. }
          exact (dyn_amb_wb Hdyn CT_DISTS
                   (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                   (b_ndist (s_bld (q_st q))) 6
                   (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
                   (0 + o_used o1) o2
                   (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                      (b_nlen (s_bld (q_st q))) 9
                      (t_codes (s_tab (q_st q))) 0 o1
                      Hamb HWF1
                      (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                      (eq_sym EI1))
                   HWF2
                   (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
                   (eq_sym EI2)).
        - (* LenTblSide at the constructed tail, from [Hdyn] at [d] *)
          split. { exact (dyn_wf_tbl Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_lcside Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_tblside_d Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_l Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_d Hdyn d _ Hdok Hinst). }
          split. { exact (wf_tbl_len_bounded _
                            (dyn_wf_tbl Hdyn d _ Hdok Hinst)). }
          split. { exact (dyn_lenbits Hdyn d Hdok). }
          split. { exact (dyn_distbits Hdyn d Hdok). }
          exact (dyn_root_opshape Hdyn d _ Hdok Hinst). }
    apply rank2_le' with (m := M_CODELENS) (m' := M_LEN_);
      [exact Hm | bsimp; reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - (* ClBad -> BAD (ascends, budget non-increasing) *)
    destruct HW as (W1 & W2 & W3 & W4).
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** [inf_LENLENS14] with the CODELENS tail discharged: the freshly built
    CODES table's [TblSide] is [dyn_codes_tblside] at the accepted
    [it_model CT_CODES] output; everything else threads. *)
Lemma reach_LENLENS14 :
  forall c q,
    q_mode q = M_LENLENS ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall h, 0 <= h < b_have (s_bld (q_st q)) ->
       0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    arm_ok q (inf_LENLENS14 c q).
Proof.
  intros c q Hm Hcore Hlens Hpre7 Hbh0 Hnlen Hndist.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENLENS14. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hlens) as HW.
  pose proof (ll_go_env 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hhold (fun j => proj1 (Hbytes j)) H39) as HE.
  pose proof (ll_go_have_mono 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q)) as HM.
  pose proof (ll_go_inbud 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q)) as HBgt.
  pose proof (ll_go_le7 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hpre7) as HL7.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b]; [|exact I].
  destruct HW as (W1 & W2 & W3 & W4).
  destruct HE as (Ein & Ehold & E39 & E0b).
  cbv beta iota in HM.
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  cbv beta iota in HL7. destruct HL7 as (Hhvge & Hp7).
  assert (Hg7 : forall h, 0 <= h < 19 -> 0 <= ls1 (inf_order h) <= 7).
  { intros h Hh19.
    pose proof (ll_zero_le7 19 hv ls Hp7
                  ltac:(cbn [Z.of_nat]; lia) h Hh19) as HZ7.
    rewrite <- EZ in HZ7. cbn [snd] in HZ7. exact HZ7. }
  assert (Hguard : CT_CODES = CT_CODES ->
                   forall i, 0 <= i < 19 -> ls1 i <= 7).
  { intros _ i Hi.
    destruct (inf_order_covers i Hi) as (h & Hh19 & E).
    rewrite <- E. exact (proj2 (Hg7 h Hh19)). }
  unfold inf_table.
  assert (HLB : GtItTotal.LensBounded ls1 19) by (intros i _; apply Hls1).
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_LENLENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
  assert (HWFC : it_wf CT_CODES ls1 19 7).
  { split; [lia|]. split; [intros i _; apply Hls1|].
    split; [unfold MAXBITS; lia|].
    left; split; [reflexivity | lia]. }
  eapply (arm_ok_mono _ q).
  2:{ apply reach_CODELENS14.
      - bsimp; reflexivity.
      - (* CoreFacts at the constructed tail *)
        split. { unfold q_pos. ksimp. repeat split; lia. }
        split. { ksimp. lia. }
        split. { intros j. ksimp. rewrite Ein. exact (Hbytes j). }
        split. { intros j. ksimp. exact (Hwinb j). }
        split. { ksimp. lia. }
        split. { ksimp. lia. }
        split. { ksimp. exact Hsane. }
        split. { ksimp. lia. }
        split. { ksimp. lia. }
        split. { ksimp. exact Ehold. }
        ksimp.
        exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
                 (t_codes (s_tab (q_st q))) 0 o1
                 Hamb HWFC Hguard (eq_sym EI1)).
      - ksimp. exact Hls1.
      - ksimp. lia.
      - ksimp. lia.
      - ksimp. lia.
      - (* TblSide at the freshly built CODES table *)
        exact (dyn_codes_tblside Hdyn ls1 19 7
                 (t_codes (s_tab (q_st q))) o1 Hamb HWFC (eq_sym EI1)
                 Er1). }
  apply rank2_le' with (m := M_LENLENS) (m' := M_CODELENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** [inf_TABLE14] with the LENLENS tail discharged.  The b_nlen/b_ndist
    bounds at the tail are CONSTRUCTED here ([bits_of_range 5] on the two
    5-bit reads), not carried — TABLE is where they are born. *)
Lemma reach_TABLE14 :
  forall c q,
    q_mode q = M_TABLE ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    arm_ok q (inf_TABLE14 c q).
Proof.
  intros c q Hm Hcore Hlens.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_TABLE14.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  pose proof (inf_nb_env 14 (q_br q) b ltac:(lia) Hhold Hb
                (fun j => proj1 (Hbytes j)) H39 Enb) as (Nin & Nhold & N39).
  pose proof (inf_nb_have_mono _ _ _ Enb) as NM.
  apply inf_nb_bud in Enb as (E1 & E2 & E3). specialize (E3 Hh).
  pose proof (bits_of_range 5 b ltac:(lia)) as B1.
  change (2 ^ 5) with 32 in B1.
  pose proof (bits_of_range 5 (br_dropbits 5 b) ltac:(lia)) as B2.
  change (2 ^ 5) with 32 in B2.
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_TABLE) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply reach_LENLENS14.
      - bsimp; reflexivity.
      - (* CoreFacts at the constructed tail *)
        split. { unfold q_pos. bsimp. repeat split; lia. }
        split. { bsimp. lia. }
        split. { intros j. bsimp. rewrite Nin. exact (Hbytes j). }
        split. { intros j. bsimp. exact (Hwinb j). }
        split. { bsimp. lia. }
        split. { bsimp. lia. }
        split. { ksimp. exact Hsane. }
        split. { bsimp. lia. }
        split. { bsimp. lia. }
        split.
        { exact (dropbits_hold_nonneg 4 (br_dropbits 5 (br_dropbits 5 b))
                   (dropbits_hold_nonneg 5 (br_dropbits 5 b)
                      (dropbits_hold_nonneg 5 b Nhold))). }
        ksimp. exact Hamb.
      - ksimp. exact Hlens.
      - ksimp. intros h Hh0. lia.
      - ksimp. lia.
      - ksimp. lia.
      - ksimp. lia. }
  apply rank2_le' with (m := M_TABLE) (m' := M_LENLENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** ** The deliverable: [step_ok14] at every reachable state, ONE residual
    ([DynTblOk] — see its header).  The 29 non-TABLE-chain modes route
    through [step_ok14_reachable], whose two carried callee obligations are
    vacuous off the chain (congruence on the mode); TABLE / LENLENS /
    CODELENS take the discharged arms above. *)
Theorem step_ok14_reach :
  forall c q, ReachSt q -> step_ok14 c q.
Proof.
  intros c q HR.
  pose proof HR as (Hcore & Hmode).
  pose proof (core_of_reach q Hcore) as HCF.
  pose proof (rc_lens q Hcore) as Hlens.
  pose proof (rc_bhave q Hcore) as Hbh.
  pose proof (rm_bldrng q Hmode) as Hbld.
  pose proof (rm_tblCL q Hmode) as HtblCL.
  pose proof (rm_lens7 q Hmode) as Hl7.
  destruct (q_mode q) eqn:Hm;
    try (apply (step_ok14_reachable c q HR);
         [ intros [F|F]; exfalso; congruence
         | intros F; exfalso; congruence ]).
  - (* M_TABLE *)
    unfold step_ok14, inf_step14. rewrite Hm. cbv beta iota.
    exact (reach_TABLE14 c q Hm HCF Hlens).
  - (* M_LENLENS *)
    unfold step_ok14, inf_step14. rewrite Hm. cbv beta iota.
    destruct (Hbld (or_introl eq_refl)) as [Hnl Hnd].
    exact (reach_LENLENS14 c q Hm HCF Hlens (Hl7 eq_refl) Hbh Hnl Hnd).
  - (* M_CODELENS *)
    unfold step_ok14, inf_step14. rewrite Hm. cbv beta iota.
    destruct (Hbld (or_intror eq_refl)) as [Hnl Hnd].
    exact (reach_CODELENS14 c q Hm HCF Hlens Hbh Hnl Hnd (HtblCL eq_refl)).
Qed.

End Knot14.
