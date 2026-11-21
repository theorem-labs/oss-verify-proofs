(** * Bridge.Infl.IArmTableCTail — pair I9: the CODELENS arm, S5 vs RT.

    The [while] ([IArmTableCLoop.cl_while_sim]), the [lens[256]] check, the LENS table at 0
    with root 9 and the DISTS table at [next] with root 6 over the lengths shifted by [nlen]
    ([ITree.inflate_table_sim] twice), then [mode = LEN_] and the fall into LEN_
    ([IArmLen.arm_LEN__ok]).  The LEN_ state's [tviews_blk]: the DISTS view is ITree's; the
    LENS view is ITree's carried over the DISTS write, which lands at and above [next]
    ([IArmTableKit.inflate_table_bnd] puts the whole LENS table below [next]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms Inftrees InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits ITree IArmLen IArmTableKit
  IArmTableCLoop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma imode_len_ : forall w q, tviews_blk w q -> RI.q_mode q = RI.M_LEN_ -> imode w q.
Proof. intros w q H E. unfold imode. rewrite E. exact H. Qed.

Lemma tview_ext : forall f g f' g' root k, tview f g root k ->
  (forall x, f' x = f x) -> (forall x, g' x = g x) -> tview f' g' root k.
Proof.
  intros f g f' g' root k [Hr Htv] Hf Hg. split; [exact Hr|].
  intros x Hx. rewrite !Hf, !Hg. destruct (Htv x Hx) as (A1 & A2 & A3 & A4 & A5).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  intros T. destruct (A5 T) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|].
  split; [exact B3|]. intros y Hy. cbv zeta. rewrite !Hf, !Hg. exact (B4 y Hy).
Qed.

Ltac s5_norm :=
  autorewrite with s5w s5wbr s5i_mode s5ir_ret s5i_work s5i_distbits s5i_next s5i_distcode s5i_codes
                   s5i_lenbits s5i_lencode.

Lemma cl_ok : forall c w q,
  ctx_rel FL c -> icore w q -> RI.q_mode q = RI.M_CODELENS ->
  tview (IS.code_at (IS.w_s w) (IS.is_lencode (IS.w_s w)))
        (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q)))) (IS.is_lenbits (IS.w_s w)) KCodes ->
  RI.b_have (RI.s_bld (RI.q_st q)) = 0 ->
  257 <= RI.b_nlen (RI.s_bld (RI.q_st q)) <= 286 -> 1 <= RI.b_ndist (RI.s_bld (RI.q_st q)) <= 30 ->
  step_ok (IA.arm_CODELENS IS.ivar_ref FL w) (RI14.inf_CODELENS14 c q).
Proof.
  intros c w q Hctx Hc Hm Htv Hh0 Hnl Hnd.
  pose proof (icore_tab _ _ Hc) as (_ & _ & Hlb & _).
  pose proof (icore_bld _ _ Hc) as (_ & Hnl' & Hnd' & _).
  pose proof (icore_rng _ _ Hc) as Hrng.
  pose proof (icore_retok _ _ Hc) as Hret.
  unfold RI14.inf_CODELENS14. cbv zeta.
  match goal with |- context [RI.cl_loop ?n ?t ?nb ?tot ?cs] =>
    destruct (RI.cl_loop n t nb tot cs) as [[s|s|s m|s|]|] eqn:Hl end;
    [exact I | | apply step_ok_bad; reflexivity | apply step_ok_leave; exact Hret | exact I | exact I].
  (* the [while] *)
  assert (HI0 : clinv q (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q))))
                  (RI.t_lenbits (RI.s_tab (RI.q_st q)))
                  (RI.b_nlen (RI.s_bld (RI.q_st q)) + RI.b_ndist (RI.s_bld (RI.q_st q))) w
                  (RI.mkClSt (RI.b_have (RI.s_bld (RI.q_st q))) (RI.b_lens (RI.s_bld (RI.q_st q))) (RI.q_br q))).
  { unfold clinv. rewrite put_cl_id. rewrite <- Hlb. cbn [RI.cl_have]. rewrite Hh0.
    split; [exact Hc|]. split; [exact Htv|]. split; [reflexivity|].
    split; [rewrite Hnl', Hnd'; reflexivity|]. split; [lia|]. split; [lia|]. intros i Hi; lia. }
  assert (Hk : (S (Z.to_nat (RI.b_nlen (RI.s_bld (RI.q_st q)) + RI.b_ndist (RI.s_bld (RI.q_st q)))) <= 321)%nat)
    by lia.
  destruct (cl_while_sim _ _ _ _ _ 321 _ _ _ HI0 Hk Hl) as (w1 & E1 & HI1 & Hge).
  pose proof HI1 as (Hc1 & _ & _ & _ & _ & _ & Hlr1).
  pose proof (icore_tab _ _ Hc1) as (_ & _ & _ & _ & _ & Hcl1 & Hcr1 & _).
  unfold put_cl in Hcr1. rt_cbn_in Hcr1.
  pose proof (icore_bld _ _ Hc1) as (_ & Hnl1 & Hnd1 & _ & _ & Hlr1' & Hwl1).
  unfold put_cl in Hnl1, Hnd1, Hlr1'.
  rt_cbn_in Hnl1. rt_cbn_in Hnd1. rt_cbn_in Hlr1'.
  assert (Hm1 : IS.is_mode (IS.w_s w1) = RI.m_val RI.M_CODELENS).
  { rewrite (icore_mode _ _ Hc1). unfold put_cl, RI.q_mode. rt_cbn. unfold RI.q_mode in Hm. rewrite Hm.
    reflexivity. }
  unfold IA.arm_CODELENS.
  rewrite (abind_ARun _ _ _ _ _ E1). cbv beta.
  rewrite abind_gs. cbv beta.
  rewrite Hm1. change (RI.m_val RI.M_CODELENS =? IS.BAD) with false. cbv iota.
  (* [lens[256]] *)
  rewrite (Hlr1' 256 ltac:(unfold NLENS; lia)).
  destruct (RI.cl_lens s 256 =? 0) eqn:E256; [apply step_ok_bad; reflexivity|].
  cbv iota.
  (* the LENS table *)
  rewrite Hnl1.
  unfold RI.inf_table.
  match goal with |- context [RIT.it_model ?ty ?l ?n ?r ?t0] =>
    destruct (RIT.it_model ty l n r t0) as [o|] eqn:Hit; [|exact I] end.
  assert (HLL : forall i, 0 <= i < RI.b_nlen (RI.s_bld (RI.q_st q)) ->
             arr_get (IS.is_lens (IS.w_s w1)) (0 + i) = RI.cl_lens s i /\ 0 <= RI.cl_lens s i <= 15).
  { intros i Hi. rewrite Z.add_0_l. split; [apply Hlr1'; unfold NLENS; lia | apply Hlr1; lia]. }
  pose proof (inflate_table_sim IS.LENS (IS.is_lens (IS.w_s w1)) (RI.cl_lens s) 0
                (RI.b_nlen (RI.s_bld (RI.q_st q))) (IS.is_codes (IS.w_s w1)) (RI.t_codes (RI.s_tab (RI.q_st q)))
                0 9 (IS.is_work (IS.w_s w1)) o
                ltac:(cbn [ty_max]; lia) ltac:(lia) ltac:(unfold NLENS; lia) HLL ltac:(discriminate)
                Hcl1 Hcr1 Hrng ltac:(lia) ltac:(cbn [ICov.it_room]; unfold IS.ENOUGH_LENS, ENOUGH; lia)
                Hwl1 ltac:(lia) ltac:(discriminate) Hit) as SL.
  pose proof (inflate_table_bnd IS.LENS (IS.is_lens (IS.w_s w1)) 0 (RI.b_nlen (RI.s_bld (RI.q_st q)))
                (IS.is_codes (IS.w_s w1)) 0 9 (IS.is_work (IS.w_s w1))
                ltac:(cbn [ty_max]; lia)
                ltac:(intros i Hi; rewrite (Hlr1' i ltac:(unfold NLENS; lia)); apply Hlr1; lia)
                ltac:(discriminate) Hcl1 ltac:(lia) ltac:(cbn [ICov.it_room]; unfold IS.ENOUGH_LENS, ENOUGH; lia)
                Hwl1 ltac:(lia) ltac:(discriminate)) as BL.
  revert SL BL.
  destruct (IT.inflate_table IS.LENS (IS.is_lens (IS.w_s w1)) 0 (RI.b_nlen (RI.s_bld (RI.q_st q)))
              (IS.is_codes (IS.w_s w1)) 0 9 (IS.is_work (IS.w_s w1))) as [[[[ret1 tbl1] nx1] lb1] wk1] eqn:Eit.
  intros SL BL. cbv beta iota in SL, BL.
  destruct SL as [Er1 SL].
  cbv beta iota zeta.
  rewrite Er1.
  destruct (RIT.o_ret o =? 0) eqn:Hr0; [|cbn [negb]; apply step_ok_bad; reflexivity].
  apply Z.eqb_eq in Hr0.
  destruct (SL Hr0) as (Elb & Enx & Hnx852 & Htl1 & Hwl1' & Htr1 & Hrg1 & TV1).
  destruct (BL ltac:(congruence)) as [BL1 BL2].
  rewrite Hr0. cbn [negb].
  rewrite abind_us. cbv beta.
  rewrite abind_ur. cbv beta.
  rewrite abind_gs. cbv beta.
  s5_norm.
  rewrite Hnl1, Hnd1, Enx, Elb.
  rewrite Elb in TV1, BL1, BL2. rewrite Enx in BL1, BL2, Hnx852.
  cbn [ICov.it_room] in Hnx852. unfold IS.ENOUGH_LENS in Hnx852.
  assert (Hp1 : 0 < 2 ^ RIT.o_bits o) by (destruct TV1 as [Hr1 _]; apply Z.pow_pos_nonneg; lia).
  (* the DISTS table *)
  match goal with |- context [RIT.it_model ?ty ?l ?n ?r ?t0] =>
    destruct (RIT.it_model ty l n r t0) as [o2|] eqn:Hit2; [|exact I] end.
  assert (HLD : forall i, 0 <= i < RI.b_ndist (RI.s_bld (RI.q_st q)) ->
             arr_get (IS.is_lens (IS.w_s w1)) (RI.b_nlen (RI.s_bld (RI.q_st q)) + i)
             = RI.cl_lens s (i + RI.b_nlen (RI.s_bld (RI.q_st q)))
             /\ 0 <= RI.cl_lens s (i + RI.b_nlen (RI.s_bld (RI.q_st q))) <= 15).
  { intros i Hi. rewrite (Z.add_comm (RI.b_nlen _) i).
    split; [apply Hlr1'; unfold NLENS; lia | apply Hlr1; lia]. }
  pose proof (inflate_table_sim IS.DISTS (IS.is_lens (IS.w_s w1))
                (fun i => RI.cl_lens s (i + RI.b_nlen (RI.s_bld (RI.q_st q))))
                (RI.b_nlen (RI.s_bld (RI.q_st q))) (RI.b_ndist (RI.s_bld (RI.q_st q))) tbl1
                (RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o))
                (0 + RIT.o_used o) 6 wk1 o2
                ltac:(cbn [ty_max]; lia) ltac:(lia) ltac:(unfold NLENS; lia) HLD ltac:(discriminate)
                Htl1 Htr1 Hrg1 ltac:(lia) ltac:(cbn [ICov.it_room]; unfold IS.ENOUGH_DISTS, ENOUGH; lia)
                Hwl1' ltac:(lia) ltac:(discriminate) Hit2) as SD.
  revert SD.
  destruct (IT.inflate_table IS.DISTS (IS.is_lens (IS.w_s w1)) (RI.b_nlen (RI.s_bld (RI.q_st q)))
              (RI.b_ndist (RI.s_bld (RI.q_st q))) tbl1 (0 + RIT.o_used o) 6 wk1)
    as [[[[ret2 tbl2] nx2] db2] wk2] eqn:Eit2.
  intros SD. cbv beta iota in SD.
  destruct SD as [Er2 SD].
  cbv beta iota zeta.
  rewrite Er2.
  destruct (RIT.o_ret o2 =? 0) eqn:Hr2; [|cbn [negb]; apply step_ok_bad; reflexivity].
  apply Z.eqb_eq in Hr2.
  destruct (SD Hr2) as (Edb & Enx2 & _ & Htl2 & Hwl2 & Htr2 & Hrg2 & TV2).
  rewrite Hr2. cbn [negb].
  rewrite abind_us. cbv beta.
  rewrite abind_ur. cbv beta.
  rewrite abind_setmode. cbv beta.
  rewrite Edb, Enx2. rewrite Edb in TV2.
  destruct Hctx as [Hfl _]. rewrite Hfl.
  cbn [IS.iv_flush_exits IS.ivar_ref andb FL ZIface.Z_NO_FLUSH ZIface.Z_TREES RI.Z_TREES Z.eqb].
  (* into LEN_ *)
  apply arm_LEN__ok; [|reflexivity].
  split.
  - eapply icore_req.
    + eapply (icore_setmode _ _ _ _ RI.M_LEN_).
      * eapply icore_ret.
        -- eapply (icore_dtbl _ _ _ _ (RI.codes_wb (RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o))
                                         (0 + RIT.o_used o) (RIT.o_tbl o2))).
           ++ eapply icore_ret.
              ** eapply (icore_ltbl _ _ _ _ (RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o))).
                 --- exact Hc1.
                 --- reflexivity.
                 --- exact Htl1.
                 --- exact Htr1.
                 --- exact Hrg1.
                 --- exact Hwl1'.
              ** reflexivity.
              ** reflexivity.
           ++ reflexivity.
           ++ exact Htl2.
           ++ exact Htr2.
           ++ exact Hrg2.
           ++ exact Hwl2.
        -- reflexivity.
        -- reflexivity.
      * reflexivity.
      * reflexivity.
      * s5_norm. rewrite Hm1. intros E. cbv in E. discriminate E.
    + reflexivity.
  - apply imode_len_; [|reflexivity].
    unfold tviews_blk. cbv zeta. s5_norm. unfold RI.tbl_of. rt_cbn.
    split.
    + eapply tview_transport; [exact TV1 | exact BL2 |].
      intros x Hx. unfold IS.code_at. cbv beta iota. s5_norm.
      assert (Hx0 : 0 <= 0 + x < ENOUGH) by (unfold ENOUGH; lia).
      assert (Ecd : RI.codes_wb (RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o))
                      (0 + RIT.o_used o) (RIT.o_tbl o2) (0 + x)
                    = RI.codes_wb (RI.t_codes (RI.s_tab (RI.q_st q))) 0 (RIT.o_tbl o) (0 + x)).
      { unfold RI.codes_wb at 1. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
      split.
      * rewrite (Htr2 (0 + x) Hx0), (Htr1 (0 + x) Hx0). f_equal. exact Ecd.
      * exact Ecd.
    + eapply tview_ext; [exact TV2 | |].
      * intros x. unfold IS.code_at. cbv beta iota. s5_norm. reflexivity.
      * intros x. reflexivity.
Qed.
