(** * Bridge.Infl.IArmTableLLens — pair I9: the LENLENS arm, S5 vs RT.

    S5's [lenlens_while1] / [lenlens_while2] (fuel 19 each) against RT's [ll_go] / [ll_zero]
    (fuel 19 each), trip for trip; then the CODES table ([ITree.inflate_table_sim] at 0,
    root 7, 19 lengths) and the fall into CODELENS ([IArmTableCTail.cl_ok]).  After the two
    loops every [lens[order[j]]], [j < 19], has been written with a 3-bit value or 0, and
    [order] covers [0..18], so the CODES table sees 19 lengths of at most 7. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms Inftrees InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits ITree IArmTableKit
  IArmTableCLoop IArmTableCTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** LENLENS's partial state: [h] lengths read, every [lens[order[j]]] with [j < h] at most 7. *)
Definition llinv (q0 : RI.InfSt) (w : IS.iw) (h : Z) (l : RBa.zarr) (b : RB.BR) : Prop :=
  icore w (put_cl q0 (RI.mkClSt h l b))
  /\ 0 <= h <= 19
  /\ (forall i, 0 <= i < 19 -> (exists j, 0 <= j < h /\ RI.inf_order j = i) -> 0 <= l i <= 7).

Lemma llinv_write : forall l h v, 0 <= h < 19 -> 0 <= v <= 7 ->
  (forall i, 0 <= i < 19 -> (exists j, 0 <= j < h /\ RI.inf_order j = i) -> 0 <= l i <= 7) ->
  forall i, 0 <= i < 19 -> (exists j, 0 <= j < h + 1 /\ RI.inf_order j = i) ->
    0 <= RBa.zset l (RI.inf_order h) v i <= 7.
Proof.
  intros l h v Hh Hv Hl i Hi [j [Hj Ej]].
  destruct (Z.eq_dec i (RI.inf_order h)) as [->|Hne].
  - rewrite RBa.zset_same. exact Hv.
  - rewrite RBa.zset_other by exact Hne. apply Hl; [exact Hi|]. exists j. split; [|exact Ej].
    assert (j <> h) by (intros ->; congruence). lia.
Qed.

Lemma ll_go_sim : forall q0 f w h l b h' l' b',
  RI.b_ncode (RI.s_bld (RI.q_st q0)) <= 19 ->
  llinv q0 w h l b ->
  RI.ll_go f (RI.b_ncode (RI.s_bld (RI.q_st q0))) h l b = RI.LlOk h' l' b' ->
  exists w', IA.lenlens_while1 f w = IS.ARun tt w' /\ llinv q0 w' h' l' b'.
Proof.
  intros q0 f. induction f as [|f IH]; intros w h l b h' l' b' Hnc HI Hg.
  - cbn [RI.ll_go] in Hg. injection Hg as <- <- <-. exists w. split; [reflexivity | exact HI].
  - pose proof HI as (Hc & Hh & Hl).
    pose proof (icore_bld _ _ Hc) as (Hnc' & _ & _ & Hhv & Hll & Hlr & _).
    unfold put_cl in Hnc', Hhv, Hlr. rt_cbn_in Hnc'. rt_cbn_in Hhv. rt_cbn_in Hlr.
    pose proof (icore_brel _ _ Hc) as Hb. unfold put_cl in Hb. rt_cbn_in Hb.
    pose proof (icore_b8 _ _ Hc) as H8. unfold put_cl in H8. rt_cbn_in H8.
    cbn [RI.ll_go] in Hg. revert Hg.
    cbn [IA.lenlens_while1]. rewrite abind_gs. cbv beta.
    rewrite Hhv, Hnc'.
    destruct (Z.ltb_spec h (RI.b_ncode (RI.s_bld (RI.q_st q0)))) as [Lt|Ge].
    2: { intros Hg. injection Hg as <- <- <-. exists w. split; [reflexivity | exact HI]. }
    destruct (RI.inf_nb 3 b) as [b1|b1] eqn:Hn; [|intros Hg; discriminate Hg].
    intros Hg.
    pose proof (order_get h ltac:(lia)) as [Eo Ho].
    destruct (needbits_sim w b b1 3 Hb ltac:(lia) Hn) as (En & Hb1 & Hge & Hin1 & Hsum1).
    pose proof (nb_b8 _ _ _ Hn H8) as H81.
    pose proof (bits_of_nonneg 3 b1 ltac:(lia)) as Hv3.
    rewrite (abind_ARun _ _ _ _ _ En). cbv beta.
    rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 3 Hb1 ltac:(lia))). cbv beta.
    rewrite abind_gs. cbv beta.
    rewrite abind_setlens. cbv beta.
    rewrite abind_us. cbv beta.
    match goal with |- exists _, IS.abind (IA.DROPBITS 3) _ ?W3 = _ /\ _ =>
      assert (I3 : icore W3 (put_cl q0 (RI.mkClSt (h + 1) (RBa.zset l (RI.inf_order h) (RB.br_bits_of 3 b1)) b1)))
    end.
    { eapply icore_req.
      - eapply (icore_have _ _ _ _ (h + 1)).
        + eapply (icore_lens _ _ _ _ (RBa.zset l (RI.inf_order h) (RB.br_bits_of 3 b1))).
          * apply icore_br; [exact Hc|]. unfold put_cl. rt_cbn.
            exact (brf_intro w b b1 Hb1 Hin1 Hsum1 H81).
          * reflexivity.
          * rewrite arr_len_set. autorewrite with s5wbr. exact Hll.
          * autorewrite with s5wbr. rewrite Hhv, Eo, (wrap16_id (RB.br_bits_of 3 b1)) by lia.
            apply arr_rel_set; [exact Hlr | rewrite Hll; unfold NLENS; lia].
        + reflexivity.
        + autorewrite with s5w s5i_lens s5wbr. rewrite Hhv. apply wrap32_id. lia.
      - reflexivity. }
    pose proof (icore_brel _ _ I3) as Hb3. unfold put_cl in Hb3. rt_cbn_in Hb3.
    destruct (dropbits_sim _ b1 3 Hb3 ltac:(lia)) as (Ed3 & Hbd3).
    rewrite (abind_ARun _ _ _ _ _ Ed3). cbv beta.
    assert (I4 : icore (wbr _ (RB.br_dropbits 3 b1)) _)
      by (apply icore_br; [exact I3 | unfold put_cl; rt_cbn; exact (brf_drop _ b1 3 Hbd3 ltac:(lia) H81)]).
    match goal with |- exists _, IA.lenlens_while1 f ?W4 = _ /\ _ =>
      assert (HI4 : llinv q0 W4 (h + 1) (RBa.zset l (RI.inf_order h) (RB.br_bits_of 3 b1)) (RB.br_dropbits 3 b1))
    end.
    { split; [eapply icore_req; [exact I4 | reflexivity]|]. split; [lia|].
      apply llinv_write; [lia | lia | exact Hl]. }
    destruct (IH _ _ _ _ _ _ _ Hnc HI4 Hg) as (w' & E' & HI').
    exists w'. split; [exact E' | exact HI'].
Qed.

Lemma ll_zero_sim : forall q0 f w h l b h' l',
  llinv q0 w h l b -> RI.ll_zero f h l = (h', l') ->
  exists w', IA.lenlens_while2 f w = IS.ARun tt w' /\ llinv q0 w' h' l' b.
Proof.
  intros q0 f. induction f as [|f IH]; intros w h l b h' l' HI Hz.
  - cbn [RI.ll_zero] in Hz. injection Hz as <- <-. exists w. split; [reflexivity | exact HI].
  - pose proof HI as (Hc & Hh & Hl).
    pose proof (icore_bld _ _ Hc) as (_ & _ & _ & Hhv & Hll & Hlr & _).
    unfold put_cl in Hhv, Hlr. rt_cbn_in Hhv. rt_cbn_in Hlr.
    cbn [RI.ll_zero] in Hz. revert Hz.
    cbn [IA.lenlens_while2]. rewrite abind_gs. cbv beta.
    rewrite Hhv.
    destruct (Z.ltb_spec h 19) as [Lt|Ge].
    2: { intros Hz. injection Hz as <- <-. exists w. split; [reflexivity | exact HI]. }
    intros Hz.
    pose proof (order_get h ltac:(lia)) as [Eo Ho].
    rewrite abind_setlens. cbv beta.
    rewrite abind_us. cbv beta.
    match goal with |- exists _, IA.lenlens_while2 f ?W2 = _ /\ _ =>
      assert (HI2 : llinv q0 W2 (h + 1) (RBa.zset l (RI.inf_order h) 0) b) end.
    { split.
      - eapply icore_req.
        + eapply (icore_have _ _ _ _ (h + 1)).
          * eapply (icore_lens _ _ _ _ (RBa.zset l (RI.inf_order h) 0)).
            -- exact Hc.
            -- reflexivity.
            -- rewrite arr_len_set. exact Hll.
            -- rewrite Eo. change (wrap16 0) with 0.
               apply arr_rel_set; [exact Hlr | rewrite Hll; unfold NLENS; lia].
          * reflexivity.
          * autorewrite with s5w s5i_lens. rewrite Hhv. apply wrap32_id. lia.
        + reflexivity.
      - split; [lia|]. apply llinv_write; [lia | lia | exact Hl]. }
    destruct (IH _ _ _ _ _ _ HI2 Hz) as (w' & E' & HI').
    exists w'. split; [exact E' | exact HI'].
Qed.

Lemma ll_zero_19 : forall f h l h' l', 0 <= h <= 19 -> 19 - h <= Z.of_nat f ->
  RI.ll_zero f h l = (h', l') -> h' = 19.
Proof.
  induction f as [|f IH]; intros h l h' l' Hh Hf Hz; cbn [RI.ll_zero] in Hz.
  - injection Hz as <- _. lia.
  - revert Hz. destruct (Z.ltb_spec h 19) as [Lt|Ge]; intros Hz.
    + exact (IH (h + 1) _ h' l' ltac:(lia) ltac:(lia) Hz).
    + injection Hz as <- _. lia.
Qed.

Ltac s5_norm2 :=
  autorewrite with s5w s5wbr s5i_mode s5ir_ret s5i_work s5i_next s5i_codes s5i_lenbits s5i_lencode
                   s5i_distcode s5i_have s5i_lens.

(** zlib 1.4 LENLENS (inflate.c: [state->lencode = state->distcode = state->next]): the CODES table write sets
    distcode with lencode, on both sides ([RI14.inf_LENLENS14] sets [t_distcode] with [t_lencode]). *)
Lemma icore_ldtbl14 : forall w q s tbl tc k nx lb wk, icore w q -> s = IS.w_s w ->
  arr_len tbl = ENOUGH -> tbl_rel tbl tc 0 ENOUGH -> (forall i, code_rng (tc i)) ->
  arr_len wk = NWORK ->
  icore (IS.wset_s w (IS.iset_work (IS.iset_lenbits (IS.iset_next
           (IS.iset_lencode (IS.iset_distcode (IS.iset_codes s tbl) (IS.CDyn k)) (IS.CDyn k)) nx) lb) wk))
        (RI.qset_st q (RI.set_codes (RI.set_next (RI.set_lenbits
           (RI.set_distcode (RI.set_lencode (RI.q_st q) (RI.TRcodes k)) (RI.TRcodes k)) lb) nx) tc)).
Proof.
  intros w q s tbl tc k nx lb wk H -> Hl Hr Hg Hwl. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_work s5i_lenbits s5i_next s5i_lencode s5i_distcode s5i_codes. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity | exact eq_refl].
Qed.

Lemma ll_ok : forall c w q,
  ctx_rel FL c -> icore w q -> RI.q_mode q = RI.M_LENLENS ->
  RI.b_have (RI.s_bld (RI.q_st q)) = 0 ->
  257 <= RI.b_nlen (RI.s_bld (RI.q_st q)) <= 286 -> 1 <= RI.b_ndist (RI.s_bld (RI.q_st q)) <= 30 ->
  4 <= RI.b_ncode (RI.s_bld (RI.q_st q)) <= 19 ->
  step_ok (IA.arm_LENLENS IS.ivar_ref FL w) (RI14.inf_LENLENS14 c q).
Proof.
  intros c w q Hctx Hc Hm Hh0 Hnl Hnd Hnc.
  pose proof (icore_rng _ _ Hc) as Hrng.
  pose proof (icore_retok _ _ Hc) as Hret.
  assert (HI0 : llinv q w (RI.b_have (RI.s_bld (RI.q_st q))) (RI.b_lens (RI.s_bld (RI.q_st q))) (RI.q_br q)).
  { split; [rewrite put_cl_id; exact Hc|]. rewrite Hh0. split; [lia|]. intros i Hi [j [Hj _]]. lia. }
  unfold RI14.inf_LENLENS14. cbv zeta.
  destruct (RI.ll_go 19 (RI.b_ncode (RI.s_bld (RI.q_st q))) (RI.b_have (RI.s_bld (RI.q_st q)))
              (RI.b_lens (RI.s_bld (RI.q_st q))) (RI.q_br q)) as [hv ls b|hv ls b] eqn:Hg;
    [|apply step_ok_leave; exact Hret].
  destruct (ll_go_sim q 19 w _ _ _ hv ls b ltac:(lia) HI0 Hg) as (w1 & E1 & HI1).
  destruct (RI.ll_zero 19 hv ls) as [hv1 ls1] eqn:Hz.
  destruct (ll_zero_sim q 19 w1 hv ls b hv1 ls1 HI1 Hz) as (w2 & E2 & HI2).
  pose proof HI1 as (_ & Hh1 & _).
  pose proof (ll_zero_19 19 hv ls hv1 ls1 Hh1 ltac:(lia) Hz) as E19.
  pose proof HI2 as (Hc2 & _ & Hl2).
  pose proof (icore_tab _ _ Hc2) as (_ & _ & _ & _ & _ & Hcl2 & Hcr2 & _). unfold put_cl in Hcr2. rt_cbn_in Hcr2.
  pose proof (icore_bld _ _ Hc2) as (_ & _ & _ & _ & _ & Hlr2 & Hwl2).
  unfold put_cl in Hlr2. rt_cbn_in Hlr2.
  assert (Hm2 : IS.is_mode (IS.w_s w2) = RI.m_val RI.M_LENLENS).
  { rewrite (icore_mode _ _ Hc2). unfold put_cl, RI.q_mode. rt_cbn. unfold RI.q_mode in Hm. rewrite Hm.
    reflexivity. }
  assert (HL7 : forall i, 0 <= i < 19 -> 0 <= ls1 i <= 7).
  { intros i Hi. destruct (order_cover i Hi) as [j [Hj Ej]].
    apply (Hl2 i Hi). exists j. split; [lia | exact Ej]. }
  assert (HLC : forall i, 0 <= i < 19 -> arr_get (IS.is_lens (IS.w_s w2)) (0 + i) = ls1 i /\ 0 <= ls1 i <= 15).
  { intros i Hi. rewrite Z.add_0_l. split; [apply Hlr2; unfold NLENS; lia|]. pose proof (HL7 i Hi). lia. }
  unfold IA.arm_LENLENS.
  rewrite (abind_ARun _ _ _ _ _ E1). cbv beta.
  rewrite (abind_ARun _ _ _ _ _ E2). cbv beta.
  rewrite abind_gs. cbv beta.
  (* the CODES table *)
  unfold RI.inf_table.
  match goal with |- context [RIT.it_model ?ty ?l ?n ?r ?t0] =>
    destruct (RIT.it_model ty l n r t0) as [o|] eqn:Hit; [|exact I] end.
  pose proof (inflate_table_sim IS.CODES (IS.is_lens (IS.w_s w2)) ls1 0 19 (IS.is_codes (IS.w_s w2))
                (RI.t_codes (RI.s_tab (RI.q_st q))) 0 7 (IS.is_work (IS.w_s w2)) o
                ltac:(cbn [ty_max]; lia) ltac:(lia) ltac:(unfold NLENS; lia) HLC
                ltac:(intros _ i Hi; pose proof (HL7 i Hi); lia)
                Hcl2 Hcr2 Hrng ltac:(lia) ltac:(cbn [ICov.it_room]; unfold ENOUGH; lia)
                Hwl2 ltac:(lia) ltac:(intros; lia) Hit) as SL.
  revert SL.
  destruct (IT.inflate_table IS.CODES (IS.is_lens (IS.w_s w2)) 0 19 (IS.is_codes (IS.w_s w2)) 0 7
              (IS.is_work (IS.w_s w2))) as [[[[ret1 tbl1] nx1] lb1] wk1] eqn:Eit.
  intros SL. cbv beta iota in SL.
  destruct SL as [Er1 SL].
  cbv beta iota zeta.
  rewrite Er1.
  destruct (RIT.o_ret o =? 0) eqn:Hr0; [|cbn [negb]; apply step_ok_bad; reflexivity].
  apply Z.eqb_eq in Hr0.
  destruct (SL Hr0) as (Elb & Enx & _ & Htl1 & Hwl1 & Htr1 & Hrg1 & TV1).
  rewrite Hr0. cbn [negb].
  rewrite abind_us. cbv beta.
  rewrite abind_ur. cbv beta.
  rewrite abind_us. cbv beta.
  rewrite abind_setmode. cbv beta.
  rewrite Elb, Enx. rewrite Elb in TV1.
  (* into CODELENS *)
  apply cl_ok.
  - exact Hctx.
  - eapply icore_req.
    + eapply (icore_setmode _ _ _ _ RI.M_CODELENS).
      * eapply (icore_have _ _ _ _ 0).
        -- eapply icore_ret.
           ++ eapply (icore_ldtbl14 _ _ _ _ (RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o))).
              ** exact Hc2.
              ** reflexivity.
              ** exact Htl1.
              ** exact Htr1.
              ** exact Hrg1.
              ** exact Hwl1.
           ++ reflexivity.
           ++ reflexivity.
        -- reflexivity.
        -- reflexivity.
      * reflexivity.
      * reflexivity.
      * s5_norm2. rewrite Hm2. intros E. cbv in E. discriminate E.
    + reflexivity.
  - reflexivity.
  - s5_norm2. unfold RI.tbl_of. rt_cbn.
    eapply tview_ext; [exact TV1 | |].
    + intros x. unfold IS.code_at. cbv beta iota. s5_norm2. reflexivity.
    + intros x. reflexivity.
  - reflexivity.
  - exact Hnl.
  - exact Hnd.
Qed.
