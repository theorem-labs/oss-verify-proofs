(* GtDecTbl.v: one-bullet cand13 re-key by q4 fork , 2026-09-05, of the W8 member GtDecTbl.v (base md5 ): sites :373 (the reach_mode_scc bracket gains one hole) and :392 (the closing `+` bullet: DistSubSide of the LEN_ successor by StepReach.dsub_installed) -- cand13's StepPres.reach_mode_scc gained the sixth premise DistSubSide q (rm_dsub); proof-only, statements byte-identical to the base; author (by header, owner consent of record) q7-decode. *)
(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtDecTbl — the TABLE-chain cost
      arms: discharging [GtDecCost]'s parked [Hcost_tbl] leaf
      (q7-decode lane, zlib-rt, 2026-08-20)

    Assembly over the pres lane's exported machinery: the loop walks
    ([cl_loop_walk]/[cl_loop_env]/[ll_go_*]), the state rebuilders
    ([reach_core_build], [reach_mode_scc]), and the DynTblOk fields
    ([dyn_*]) exactly as [pres_TABLE]/[pres_LENLENS]/[pres_CODELENS]
    consume them — plus the LEAVE-side loop facts those walks did not
    need (their [PresOk] maps [InfLeave] to [True]; the cost bundle
    does not), added here as [cl_step_leave]/[cl_loop_leave]/
    [ll_go_leave].

    The chain's in-call fallthrough tail consumes [GtDecCost.cost_LEN_]
    at a [reach_core_build]+[reach_mode_scc]-rebuilt state. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require CodesBuildRows.   (* T2 res-t2: rm_tblCL0..3 suppliers (R2083 section 2) *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtInfTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecPump.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecCost.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Leave-side loop facts (the walks' [ClLeave]/[LlLeave] gap).
   ========================================================================== *)

Lemma cl_step_leave :
  forall t nb tot s s1,
    cl_step t nb tot s = ClLeave s1 ->
    8 * br_have (cl_br s1) + br_bits (cl_br s1)
      = 8 * br_have (cl_br s) + br_bits (cl_br s)
    /\ (0 <= br_have (cl_br s) -> 0 <= br_have (cl_br s1))
    /\ (0 <= br_bits (cl_br s) -> 0 <= br_bits (cl_br s1))
    /\ cl_lens s1 = cl_lens s
    /\ cl_have s1 = cl_have s.
Proof.
  intros t nb tot s s1 H. unfold cl_step in H.
  destruct (Z.leb tot (cl_have s)); [discriminate|].
  pose proof (inf_fetch_brok t nb (cl_br s)) as HF.
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; try discriminate.
  - destruct HF as (F1&F2&F3&F4&F5).
    destruct (Z.ltb (c_val h) 16); [discriminate|].
    cbv zeta in H.
    pose proof (inf_nb_brok (if Z.eqb (c_val h) 16 then c_bits h + 2
                             else if Z.eqb (c_val h) 17 then c_bits h + 3
                             else c_bits h + 7) b) as HN.
    destruct (inf_nb _ b) as [b'|b'] eqn:En.
    + (* every continuation from NBOk is ClBad/ClCont, never ClLeave *)
      exfalso.
      repeat first
        [ discriminate
        | match type of H with
          | context [if ?b0 then _ else _] =>
              destruct b0; cbv beta iota zeta in H
          end ].
    + destruct HN as (N1&N2&N3&N4&N5).
      injection H as <-. cbn [cl_br cl_lens cl_have].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * lia.
      * intros Hx. apply N3, F3, Hx.
      * intros Hx. apply N4, F4, Hx.
      * reflexivity.
      * reflexivity.
  - destruct HF as (F1&F2&F3&F4&F5).
    injection H as <-. cbn [cl_br cl_lens cl_have].
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + lia.
    + intros Hx. apply F3, Hx.
    + intros Hx. apply F4, Hx.
    + reflexivity.
    + reflexivity.
Qed.

Lemma cl_loop_leave :
  forall m t nb tot s s1,
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    lens_ok (cl_lens s) ->
    cl_loop m t nb tot s = Some (ClLeave s1) ->
    8 * br_have (cl_br s1) + br_bits (cl_br s1)
      <= 8 * br_have (cl_br s) + br_bits (cl_br s)
    /\ 0 <= br_have (cl_br s1)
    /\ 0 <= br_bits (cl_br s1).
Proof.
  induction m as [|m IH]; intros t nb tot s s1 Htbl Hh Hb Hlens H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_walk t nb tot s Htbl Hh Hb Hlens) as HW.
  destruct (cl_step t nb tot s) as [s0|s0|s0 m1|s0|] eqn:ES; try discriminate.
  - destruct HW as (W1 & W2 & W3 & W4).
    pose proof (IH t nb tot s0 s1 Htbl W2 W3 W4 H) as (I1 & I2 & I3).
    repeat split; try lia.
  - injection H as <-.
    destruct (cl_step_leave _ _ _ _ _ ES) as (L1 & L2 & L3 & _ & _).
    refine (conj _ (conj _ _)); [lia | apply L2, Hh | apply L3, Hb].
Qed.

Lemma ll_go_leave :
  forall f ncode have lens b hv ls b1,
    ll_go f ncode have lens b = LlLeave hv ls b1 ->
    8 * br_have b1 + br_bits b1 <= 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b1)
    /\ (0 <= br_bits b -> 0 <= br_bits b1).
Proof.
  induction f as [|f IH]; intros ncode have lens b hv ls b1 H;
    cbn [ll_go] in H; [discriminate|].
  destruct (Z.ltb have ncode); [|discriminate].
  pose proof (inf_nb_brok 3 b) as HN.
  destruct (inf_nb 3 b) as [b'|b'] eqn:En.
  - destruct HN as (N1&N2&N3&N4&N5).
    pose proof (inf_nb_ok _ _ _ En) as Hok.
    apply IH in H.
    unfold br_dropbits in H. cbn [br_have br_bits] in H.
    destruct H as (H1 & H2 & H3).
    refine (conj _ (conj _ _)).
    + lia.
    + intros Hx. apply H2. apply N3, Hx.
    + intros Hx. apply H3. lia.
  - destruct HN as (N1&N2&N3&N4&N5).
    injection H as <- <- <-.
    refine (conj _ (conj _ _));
      [lia | intros Hx; apply N3, Hx | intros Hx; apply N4, Hx].
Qed.

Lemma ll_go_walk_bud :
  forall f ncode have lens b r,
    ll_go f ncode have lens b = r ->
    match r with
    | LlOk hv ls b1 =>
        8 * br_have b1 + br_bits b1 <= 8 * br_have b + br_bits b
        /\ (0 <= br_have b -> 0 <= br_have b1)
        /\ (0 <= br_bits b -> 0 <= br_bits b1)
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b r H;
    cbn [ll_go] in H.
  - subst r. refine (conj _ (conj _ _)); [lia | intros; lia | intros; lia].
  - destruct (Z.ltb have ncode);
      [| subst r;
         refine (conj _ (conj _ _)); [lia | intros; lia | intros; lia]].
    pose proof (inf_nb_brok 3 b) as HN.
    destruct (inf_nb 3 b) as [b'|b'] eqn:En.
    + destruct HN as (N1&N2&N3&N4&N5).
      pose proof (inf_nb_ok _ _ _ En) as Hok.
      pose proof (IH _ _ _ _ _ H) as HR.
      destruct r as [hv ls b1|hv ls b1]; [|exact I].
      unfold br_dropbits in HR. cbn [br_have br_bits] in HR.
      destruct HR as (H1 & H2 & H3).
      refine (conj _ (conj _ _)).
      * lia.
      * intros Hx. apply H2. apply N3, Hx.
      * intros Hx. apply H3. lia.
    + destruct HN as (N1&N2&N3&N4&N5).
      subst r. exact I.
Qed.

(* ==========================================================================
   2.  The three arms, mirroring pres_TABLE/pres_LENLENS/pres_CODELENS
       with the cost bundle.
   ========================================================================== *)

Section TblCost.

Variable Hdyn : DynTblOk.

Variable Hsel : forall q h b2 nb,
    ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
    inf_decode sub_len (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
    1 <= nb
    /\ 0 <= c_val h
    /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 -> Z.land (c_op h) 64 = 0 ->
        3 <= c_val h
        /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258).

(** cand8 (q7 STATEMENT RULING, row; q4 cand8 StepPres.reach_mode_scc now also takes
    [TblPDSide] / [br_bits <= 14] / [TblWidSide]): the in-call LEN_ successor's bit bound needs
    the pre-state's [rm_bits14] and the codes table's [rm_tblpdCL], so the lemma carries the
    whole [ReachMode q] beside [ReachCore q]; the [TblSide] premise STAYS. *)
Lemma cost_CODELENS :
  forall c q,
    ReachCore q -> ReachMode q -> h_mode (s_hdr (q_st q)) = M_CODELENS ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    CostStep q (inf_CODELENS c q).
Proof.
  intros c q HC HM Hm Hnl Hnd Htl.
  core_facts q HC.
  assert (Hnlen0 : 0 <= b_nlen (s_bld (q_st q))) by lia.
  assert (Hndist0 : 0 <= b_ndist (s_bld (q_st q))) by lia.
  unfold inf_CODELENS. cbv zeta beta.
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
                   cl_br := q_br q |} r Htl Hh Hb Flens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  pose proof (cl_loop_env
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39 Flens Hr) as HE.
  cbn [cl_br cl_lens cl_have] in HE.
  pose proof (cl_loop_chave
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r ltac:(cbn [cl_have]; lia) Hr)
    as HCh.
  (* cand8: the CODELENS loop keeps [bits <= 14] over [rm_tblpdCL]'s TblPD, from [rm_bits14] at CODELENS *)
  pose proof (cl_loop_bits14
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r
                (proj1 (rm_tblpdCL q HM Hm))
                (rm_bits14 q HM
                   (or_intror (or_intror (or_intror (or_intror (or_introl Hm))))))
                Hr) as HB14.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction; cbv beta iota in HCh.
  - (* ClDone: the two builds *)
    destruct HW as (W1 & W2 & W3 & W4).
    cbv beta iota in HB14.
    destruct HE as (Ein & Ehold & E39 & E0b).
    destruct (Z.eqb (cl_lens s1 256) 0).
    { (* no EOB: qbad, an InfCont *)
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia; try (rewrite Ein; intros j; exact (proj1 (rc_bytes q HC j))).
      unfold CostAux. bsimp. aux_vac. }
    unfold inf_table.
    assert (HLB1 : GtItTotal.LensBounded (cl_lens s1)
                     (b_nlen (s_bld (q_st q))))
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
    { (* rejected LENS build: qbad *)
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
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
    { (* rejected DISTS build: qbad *)
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    apply Bool.negb_false_iff in Er2. apply Z.eqb_eq in Er2.
    destruct (Z.eqb (n_flush c) Z_TREES).
    { (* Z_TREES leave *)
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    (* accepted: fall through IN-CALL to LEN_ at the installed state *)
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
    { split; [exact Famb|].
      split; [exact HWF1|].
      split; [exact (eq_sym EI1)|].
      split; [exact Er1|].
      split; [exact HWF2|].
      split; [exact (eq_sym EI2)|].
      exact Er2. }
    assert (Hamb2 : amb_ok (codes_wb
              (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
              (0 + o_used o1) (o_tbl o2))).
    { exact (dyn_amb_wb Hdyn CT_DISTS
               (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
               (b_ndist (s_bld (q_st q))) 6
               (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
               (0 + o_used o1) o2
               (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                  (b_nlen (s_bld (q_st q))) 9
                  (t_codes (s_tab (q_st q))) 0 o1
                  Famb HWF1
                  (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                  (eq_sym EI1))
               HWF2
               (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
               (eq_sym EI2)). }
    (* RSS/wall cure (dec-u GTDECTBL fork, 2026-09-08): the LEN_ successor is a 17-layer unreduced
       setter chain; [ksimp] over the 27 [reach_core_build] subgoals re-normalised it ~31 times
       (63 s) and the kernel re-checked every conversion at Qed (4.6 GiB). State its reduced form
       once -- one conversion -- so every later projection is a single iota. *)
    change (CostStep q (inf_LEN_
      {| q_st :=
           {| s_hdr := {| h_mode := M_LEN_;
                          h_last := h_last (s_hdr (q_st q));
                          h_wrap := h_wrap (s_hdr (q_st q));
                          h_havedict := h_havedict (s_hdr (q_st q));
                          h_flags := h_flags (s_hdr (q_st q));
                          h_dmax := h_dmax (s_hdr (q_st q));
                          h_check := h_check (s_hdr (q_st q));
                          h_total := h_total (s_hdr (q_st q));
                          h_head := h_head (s_hdr (q_st q)) |};
              s_win := s_win (q_st q);
              s_cur := s_cur (q_st q);
              s_tab := {| t_lencode := TRcodes 0;
                          t_distcode := TRcodes (0 + o_used o1);
                          t_lenbits := o_bits o1;
                          t_distbits := o_bits o2;
                          t_next := 0 + o_used o1 + o_used o2;
                          t_codes := codes_wb (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
                                              (0 + o_used o1) (o_tbl o2);
                          t_sane := t_sane (s_tab (q_st q)) |};
              s_bld := {| b_ncode := b_ncode (s_bld (q_st q));
                          b_nlen := b_nlen (s_bld (q_st q));
                          b_ndist := b_ndist (s_bld (q_st q));
                          b_have := cl_have s1;
                          b_lens := cl_lens s1;
                          b_work := b_work (s_bld (q_st q)) |};
              s_hold := s_hold (q_st q);
              s_bits := s_bits (q_st q) |};
         q_z := q_z q; q_br := cl_br s1; q_ob := q_ob q;
         q_in := q_in q; q_out := q_out q; q_ret := o_ret o2 |})).
    match goal with
    | |- CostStep _ (inf_LEN_ ?t) =>
        assert (HR3 : ReachSt t)
    end.
    { split.
      - apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try lia; try hc_close.
      - match goal with
        | |- ReachMode ?qq =>
            assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
        end.
        apply reach_mode_scc; [right; left; bsimp; reflexivity| | | | |].
        + split. { exact (dyn_wf_tbl Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_lcside Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_tblside_d Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_l Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_d Hdyn d _ Hdok Hinst). }
          split. { exact (wf_tbl_len_bounded _
                            (dyn_wf_tbl Hdyn d _ Hdok Hinst)). }
          split. { exact (dyn_lenbits Hdyn d Hdok). }
          split. { exact (dyn_distbits Hdyn d Hdok). }
          exact (dyn_root_opshape Hdyn d _ Hdok Hinst).
        + (* cand8 TblPDSide of the LEN_ successor: the two installed builds
             (q4 cand8 StepReach.tblpd_installed_len / _dist over Hdok/Hinst) *)
          split; [ exact (tblpd_installed_len d _ Hdok Hinst)
                 | exact (tblpd_installed_dist d _ Hdok Hinst) ].
        + (* cand8 bits <= 14 of the LEN_ successor: the loop's exit register (HB14) *)
          ksimp. exact HB14.
        + (* cand8 TblWidSide of the LEN_ successor: the installed builds' widths
             (q4 cand8 StepReach.tblwid_installed over Hdok/Hinst) *)
          exact (tblwid_installed d _ Hdok Hinst).
        + (* cand13 DistSubSide of the LEN_ successor: the installed DIST build's sub-window leaves (StepReach.dsub_installed) *)
          exact (dsub_installed d _ Hdok Hinst). }
    eapply CostStep_pre.
    2: { apply (cost_LEN_ Hsel); [exact HR3 | bsimp; reflexivity]. }
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia; try (rewrite Ein; intros j; exact (proj1 (rc_bytes q HC j))).
    unfold CostAux. bsimp. aux_vac.
  - (* ClBad: the loop's own rejection *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbn [CostStep].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
  - (* ClLeave *)
    pose proof (cl_loop_leave
                  (S (Z.to_nat (b_nlen (s_bld (q_st q))
                                + b_ndist (s_bld (q_st q)))))
                  (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                  (t_lenbits (s_tab (q_st q)))
                  (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                  {| cl_have := b_have (s_bld (q_st q));
                     cl_lens := b_lens (s_bld (q_st q));
                     cl_br := q_br q |} s1 Htl
                  ltac:(cbn [cl_br]; exact Hh)
                  ltac:(cbn [cl_br]; exact Hb)
                  ltac:(cbn [cl_lens]; exact Flens) Hr) as (L1 & L2 & L3).
    cbn [cl_br] in L1, L2, L3.
    cbn [CostStep].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. rewrite !Hm. aux_vac.
Qed.

(** cand8 CASCADE (beyond q7's one-premise ruling, reported): the in-call CODELENS successor
    now needs [ReachMode] (cost_CODELENS), whose [rm_nlen257] / [rm_bits14] rows are not
    derivable from [ReachCore] alone -- so this arm carries [ReachMode q] too. *)
Lemma cost_LENLENS :
  forall c q,
    ReachCore q -> ReachMode q -> h_mode (s_hdr (q_st q)) = M_LENLENS ->
    (forall h, 0 <= h < b_have (s_bld (q_st q)) ->
       0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    CostStep q (inf_LENLENS c q).
Proof.
  intros c q HC HM Hm Hpre7 Hnl Hnd.
  pose proof (rm_nlen257 q HM (or_introl Hm)) as Hnt.
  core_facts q HC.
  unfold inf_LENLENS. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Flens) as HW.
  pose proof (ll_go_env 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39) as HE.
  pose proof (ll_go_chave 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Fbh) as HCh.
  pose proof (ll_go_le7 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hpre7) as HL7.
  (* cand8: the LENLENS loop keeps [bits <= 14] from [rm_bits14] at LENLENS *)
  pose proof (ll_go_bits14 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q)
                (rm_bits14 q HM (or_intror (or_intror (or_intror (or_introl Hm)))))) as HB14.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b].
  2:{ (* LlLeave *)
      symmetry in ELG.
      pose proof (ll_go_leave _ _ _ _ _ _ _ _ ELG) as (L1 & L2 & L3).
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply L2, Hh); try (apply L3, Hb).
      unfold CostAux. bsimp. rewrite !Hm. aux_vac. }
  pose proof (ll_go_walk_bud 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) _ (eq_sym ELG)) as HBud.
  cbv beta iota in HBud.
  destruct HBud as (B1 & B2 & B3).
  destruct HW as (W1 & W2 & W3 & W4).
  destruct HE as (Ein & Ehold & E39 & E0b).
  cbv beta iota in HCh.
  cbv beta iota in HB14.
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  assert (Hhv1 : 0 <= hv1).
  { pose proof (ll_zero_chave 19 hv ls HCh) as HZ2.
    rewrite <- EZ in HZ2. cbn [fst] in HZ2. exact HZ2. }
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
  { (* rejected CODES build: qbad *)
    cbn [CostStep].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia; try (rewrite Ein; intros j; exact (proj1 (rc_bytes q HC j))).
    unfold CostAux. bsimp. aux_vac. }
  apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
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
  assert (HWFC : it_wf CT_CODES ls1 19 7).
  { split; [lia|]. split; [intros i _; apply Hls1|].
    split; [unfold MAXBITS; lia|].
    left; split; [reflexivity | lia]. }
  assert (Hamb1 : amb_ok (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))).
  { exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
             (t_codes (s_tab (q_st q))) 0 o1
             Famb HWFC Hguard (eq_sym EI1)). }
  match goal with
  | |- CostStep _ (inf_CODELENS _ ?t) =>
      assert (HR3 : ReachCore t)
  end.
  { apply (reach_core_build q); ksimp;
      try reflexivity; try assumption; try lia; try hc_close. }
  eapply CostStep_pre.
  2: { apply cost_CODELENS;
       [ exact HR3
       | (* cand8: ReachMode of the CODELENS successor (mirror of
            StepPres.pres_LENLENS's reach_mode_codelens supply) *)
         apply reach_mode_codelens;
         [ bsimp; reflexivity
         | ksimp; lia
         | ksimp; lia
         | ksimp; lia
         | exact (dyn_codes_tblside Hdyn ls1 19 7
                    (t_codes (s_tab (q_st q))) o1 Famb HWFC (eq_sym EI1) Er1)
         | unfold tbl_of; ksimp; apply tblpd_codes_wb0;
           [ apply (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.CfgBitsTblLeaf.it_tblpd_wf CT_CODES ls1 19 7
                      (fun i => t_codes (s_tab (q_st q)) (0 + i)) o1);
             [ lia | intros i _; apply Hls1 | lia
             | left; split; [reflexivity | lia] | exact (eq_sym EI1) | exact Er1 ]
           | exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
                      (t_codes (s_tab (q_st q))) 0 o1 Famb HWFC Hguard (eq_sym EI1)) ]
         | ksimp; exact HB14
         | ksimp; exact (codes_build_root7 ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)
         (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 at the CODES build, from CodesBuildRows *)
         | ksimp; reflexivity
         | ksimp; exact (proj1 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1))
         | ksimp; pose proof (proj1 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1))) as HU; lia
         | ksimp; intros i Hi; unfold codes_wb; destruct (Z.leb 0 i) eqn:Ei;
           [ rewrite Z.sub_0_r; exact (proj2 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)) i Hi) | apply Z.leb_gt in Ei; lia ] ]
       | bsimp; reflexivity | ksimp; lia | ksimp; lia |].
       exact (dyn_codes_tblside Hdyn ls1 19 7
                (t_codes (s_tab (q_st q))) o1 Famb HWFC (eq_sym EI1)
                Er1). }
  unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
  cb8; try lia; try (rewrite Ein; intros j; exact (proj1 (rc_bytes q HC j))).
  unfold CostAux. bsimp. aux_vac.
Qed.

(** cand8 CASCADE (beyond the ruling, reported): the LENLENS successor's [ReachMode] needs
    [rm_bits14] at TABLE. *)
Lemma cost_TABLE :
  forall c q,
    ReachCore q -> ReachMode q -> h_mode (s_hdr (q_st q)) = M_TABLE ->
    CostStep q (inf_TABLE c q).
Proof.
  intros c q HC HM Hm.
  core_facts q HC.
  unfold inf_TABLE.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb;
    pose proof (inf_nb_brok 14 (q_br q)) as HN; rewrite Enb in HN;
    unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
  - pose proof (inf_nb_ok _ _ _ Enb) as E14.
    pose proof (inf_nb_ok_le _ _ _ Enb) as Ele.
    pose proof (rm_bits14 q HM (or_intror (or_intror (or_introl Hm)))) as HB14.
    pose proof (inf_nb_bits39 14 (q_br q) b ltac:(lia) F39 Enb) as B39.
    pose proof (bits_of_range 5 b ltac:(lia)) as B1.
    change (2 ^ 5) with 32 in B1.
    pose proof (bits_of_range 5 (br_dropbits 5 b) ltac:(lia)) as B2.
    change (2 ^ 5) with 32 in B2.
    pose proof (bits_of_range 4 (br_dropbits 5 (br_dropbits 5 b))
                  ltac:(lia)) as B3.
    change (2 ^ 4) with 16 in B3.
    cbv zeta.
    destruct (Z.ltb 286 (br_bits_of 5 b + 257)
              || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)) eqn:Eg.
    { (* too many: qbad *)
      cbn [CostStep].
      unfold CB, Kq, Wq, cpend, br_dropbits. bsimp.
      rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply E3, Hh).
      unfold CostAux. bsimp. aux_vac. }
    apply Bool.orb_false_iff in Eg. destruct Eg as (Eg1 & Eg2).
    apply Z.ltb_ge in Eg1. apply Z.ltb_ge in Eg2.
    match goal with
    | |- CostStep _ (inf_LENLENS _ ?t) =>
        assert (HR3 : ReachCore t)
    end.
    { apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try lia; try hc_close;
        try (apply E3, Hh); try exact E2;
        try (rewrite E2; intros j; exact (proj1 (rc_bytes q HC j)));
        try (repeat apply Z.shiftr_nonneg;
             apply E5;
             [ exact Fhold | exact Hb
             | intros j; exact (proj1 (rc_bytes q HC j)) ]). }
    eapply CostStep_pre.
    2: { apply cost_LENLENS;
         [ exact HR3
         | (* cand8: ReachMode of the LENLENS successor (mirror of
              StepPres.pres_TABLE's reach_mode_lenlens supply) *)
           apply reach_mode_lenlens;
           [ bsimp; reflexivity
           | ksimp; intros h Hh0; lia
           | ksimp; lia | ksimp; lia | ksimp; lia
           | ksimp; repeat rewrite br_dropbits_bits; unfold br_dropbits; cbn [br_bits]; lia ]
         | bsimp; reflexivity
         | ksimp; intros h Hh0; lia
         | ksimp; lia | ksimp; lia ]. }
    unfold CB, Kq, Wq, cpend, br_dropbits. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia; try (apply E3, Hh); try (rewrite E2; intros j;
      exact (proj1 (rc_bytes q HC j))).
    unfold CostAux. bsimp. aux_vac.
  - cbn [CostStep].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia; try (apply E3, Hh); try (apply E4, Hb).
    unfold CostAux. bsimp. rewrite !Hm. aux_vac.
Qed.

(** The parked leaf's exact shape, discharged. *)
Theorem cost_tbl_chain :
  forall c q,
    ReachSt q -> CostAux (q_st q) ->
    (h_mode (s_hdr (q_st q)) = M_TABLE -> CostStep q (inf_TABLE c q))
    /\ (h_mode (s_hdr (q_st q)) = M_LENLENS -> CostStep q (inf_LENLENS c q))
    /\ (h_mode (s_hdr (q_st q)) = M_CODELENS -> CostStep q (inf_CODELENS c q)).
Proof.
  intros c q HR Ha.
  pose proof HR as (HC & HM).
  split; [|split].
  - intros Hm. exact (cost_TABLE c q HC HM Hm).
  - intros Hm.
    destruct (rm_bldrng q HM (or_introl Hm)) as (Bn & Bd).
    exact (cost_LENLENS c q HC HM Hm (rm_lens7 q HM Hm) Bn Bd).
  - intros Hm.
    destruct (rm_bldrng q HM (or_intror Hm)) as (Bn & Bd).
    exact (cost_CODELENS c q HC HM Hm Bn Bd (rm_tblCL q HM Hm)).
Qed.

End TblCost.

(* ==========================================================================
   3.  The faces, leaf census updated: [Hcost_tbl] is now a THEOREM.
   ========================================================================== *)

Theorem decode_raw_modulo2 :
  forall (Hdyn : DynTblOk)
         (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_raw.
Proof.
  intros Hdyn Hsel Hret Hreenter Hshape.
  exact (decode_raw_modulo Hdyn Hsel (cost_tbl_chain Hdyn Hsel)
           Hret Hreenter Hshape).
Qed.

Theorem decode_auto_modulo2 :
  forall (Hdyn : DynTblOk)
         (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_auto.
Proof.
  intros Hdyn Hsel Hret Hreenter Hshape.
  exact (decode_auto_modulo Hdyn Hsel (cost_tbl_chain Hdyn Hsel)
           Hret Hreenter Hshape).
Qed.

(* ==========================================================================
   4.  [DynTblOk] is INHABITED ([DynTblOkHolds.DynTblOk_holds], an earlier development run)
       — instantiate it, shrinking the faces' leaf census by one.
   ========================================================================== *)

Theorem decode_raw_modulo3 :
  forall (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_raw.
Proof.
  intros Hsel Hret Hreenter Hshape.
  exact (decode_raw_modulo2 DynTblOk_holds Hsel Hret Hreenter Hshape).
Qed.

Theorem decode_auto_modulo3 :
  forall (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_auto.
Proof.
  intros Hsel Hret Hreenter Hshape.
  exact (decode_auto_modulo2 DynTblOk_holds Hsel Hret Hreenter Hshape).
Qed.
