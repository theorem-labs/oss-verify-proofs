(** * Bridge.Infl.IArmTable — pair I9 of PAIRS.md: TABLE, LENLENS and CODELENS.

    TABLE reads HLIT/HDIST/HCLEN; LENLENS reads the code-length code lengths in [order] and
    builds the CODES table; CODELENS decodes the literal/length and distance code lengths
    (S5: [codelens_while] with fuel 321; RT: [cl_loop] with fuel [tot + 1]), builds the
    LENS and DISTS tables ([ITree.inflate_table_sim] twice) and falls through LEN_.

    Files: [IArmTableKit] (the [icore] update lemmas, monad stepping, [inflate_table_bnd]),
    [IArmTableCLoop] (CODELENS's [while]), [IArmTableCTail] (the CODELENS arm, [cl_ok]),
    [IArmTableLLens] (the LENLENS arm, [ll_ok]); this file: the TABLE header. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits ITree IArmLen
  IArmTableKit IArmTableCLoop IArmTableLLens.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma arm_TABLE_ok : forall c w q,
  ctx_rel FL c -> inv w q -> RI.q_mode q = RI.M_TABLE ->
  step_ok (IA.arm_TABLE IS.ivar_ref FL w) (RI14.inf_TABLE14 c q).
Proof.
  intros c w q Hctx [Hc _] Hm.
  pose proof (icore_brel _ _ Hc) as Hb.
  pose proof (icore_b8 _ _ Hc) as H8.
  pose proof (icore_retok _ _ Hc) as Hret.
  assert (Hm0 : IS.is_mode (IS.w_s w) = RI.m_val RI.M_TABLE) by (rewrite (icore_mode _ _ Hc), Hm; reflexivity).
  unfold RI14.inf_TABLE14.
  destruct (RI.inf_nb 14 (RI.q_br q)) as [b|b] eqn:Hn; [|apply step_ok_leave; exact Hret].
  cbv zeta.
  destruct (needbits_sim w (RI.q_br q) b 14 Hb ltac:(lia) Hn) as (En & Hb1 & Hge & Hin1 & Hsum1).
  pose proof (nb_b8 _ _ _ Hn H8) as H81.
  unfold IA.arm_TABLE.
  rewrite (abind_ARun _ _ _ _ _ En). cbv beta.
  assert (I0 : icore (wbr w b) (RI.qset_br q b))
    by (apply icore_br; [exact Hc | exact (brf_intro w _ b Hb1 Hin1 Hsum1 H81)]).
  (* HLIT *)
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 5 Hb1 ltac:(lia))). cbv beta.
  rewrite abind_us. cbv beta.
  match goal with |- step_ok (IS.abind (IA.DROPBITS 5) _ ?W) _ =>
    assert (I1 : icore W (RI.qset_st (RI.qset_br q b) (RI.set_nlen (RI.q_st (RI.qset_br q b))
                                                          (RB.br_bits_of 5 b + 257))))
      by (eapply icore_nlen; [exact I0 | reflexivity | reflexivity])
  end.
  pose proof (icore_brel _ _ I1) as Hb2. rt_cbn_in Hb2.
  destruct (dropbits_sim _ b 5 Hb2 ltac:(lia)) as (Ed1 & Hbd1).
  rewrite (abind_ARun _ _ _ _ _ Ed1). cbv beta.
  assert (I2 := icore_br _ _ (RB.br_dropbits 5 b) I1
                  ltac:(rt_cbn; exact (brf_drop _ b 5 Hbd1 ltac:(lia) H81))).
  (* HDIST *)
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 5 Hbd1 ltac:(lia))). cbv beta.
  rewrite abind_us. cbv beta.
  match goal with |- step_ok (IS.abind (IA.DROPBITS 5) _ ?W) _ =>
    assert (I3 : icore W (RI.qset_st (RI.qset_br (RI.qset_st (RI.qset_br q b) (RI.set_nlen (RI.q_st (RI.qset_br q b))
                                                          (RB.br_bits_of 5 b + 257))) (RB.br_dropbits 5 b))
                    (RI.set_ndist (RI.q_st (RI.qset_br (RI.qset_st (RI.qset_br q b) (RI.set_nlen (RI.q_st (RI.qset_br q b))
                                                          (RB.br_bits_of 5 b + 257))) (RB.br_dropbits 5 b)))
                       (RB.br_bits_of 5 (RB.br_dropbits 5 b) + 1))))
      by (eapply icore_ndist; [exact I2 | reflexivity | reflexivity])
  end.
  pose proof (icore_brel _ _ I3) as Hb3. rt_cbn_in Hb3.
  destruct (dropbits_sim _ (RB.br_dropbits 5 b) 5 Hb3 ltac:(cbn [RB.br_dropbits RB.br_bits]; lia))
    as (Ed2 & Hbd2).
  rewrite (abind_ARun _ _ _ _ _ Ed2). cbv beta.
  assert (I4 := icore_br _ _ (RB.br_dropbits 5 (RB.br_dropbits 5 b)) I3
                  ltac:(rt_cbn; apply (brf_drop _ _ 5 Hbd2 ltac:(lia));
                        cbn [RB.br_dropbits RB.br_bits RB.br_next]; lia)).
  (* HCLEN *)
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 4 Hbd2 ltac:(lia))). cbv beta.
  rewrite abind_us. cbv beta.
  match goal with |- step_ok (IS.abind (IA.DROPBITS 4) _ ?W) _ =>
    match type of I4 with icore _ ?Q4 =>
      assert (I5 : icore W (RI.qset_st Q4 (RI.set_ncode (RI.q_st Q4)
                                (RB.br_bits_of 4 (RB.br_dropbits 5 (RB.br_dropbits 5 b)) + 4))))
        by (eapply icore_ncode; [exact I4 | reflexivity | reflexivity])
    end
  end.
  pose proof (icore_brel _ _ I5) as Hb5. rt_cbn_in Hb5.
  destruct (dropbits_sim _ (RB.br_dropbits 5 (RB.br_dropbits 5 b)) 4 Hb5
              ltac:(cbn [RB.br_dropbits RB.br_bits]; lia)) as (Ed3 & Hbd3).
  rewrite (abind_ARun _ _ _ _ _ Ed3). cbv beta.
  assert (I6 := icore_br _ _ (RB.br_dropbits 4 (RB.br_dropbits 5 (RB.br_dropbits 5 b))) I5
                  ltac:(rt_cbn; apply (brf_drop _ _ 4 Hbd3 ltac:(lia));
                        cbn [RB.br_dropbits RB.br_bits RB.br_next]; lia)).
  (* the 286/30 check *)
  rewrite abind_gs. cbv beta.
  pose proof (icore_bld _ _ I6) as (Hnc6 & Hnl6 & Hnd6 & _). rt_cbn_in Hnl6. rt_cbn_in Hnd6. rt_cbn_in Hnc6.
  rewrite Hnl6, Hnd6.
  pose proof (bits_of_nonneg 5 b ltac:(lia)) as Hv1.
  pose proof (bits_of_nonneg 5 (RB.br_dropbits 5 b) ltac:(lia)) as Hv2.
  pose proof (bits_of_nonneg 4 (RB.br_dropbits 5 (RB.br_dropbits 5 b)) ltac:(lia)) as Hv3.
  destruct ((286 <? RB.br_bits_of 5 b + 257) || (30 <? RB.br_bits_of 5 (RB.br_dropbits 5 b) + 1)) eqn:Ebad;
    [apply step_ok_bad; reflexivity|].
  apply orb_false_iff in Ebad as [Eb1 Eb2]. apply Z.ltb_ge in Eb1, Eb2.
  cbv iota.
  rewrite abind_us. cbv beta.
  rewrite abind_setmode. cbv beta.
  (* into LENLENS *)
  apply ll_ok.
  - exact Hctx.
  - eapply icore_req.
    + eapply (icore_setmode _ _ _ _ RI.M_LENLENS).
      * eapply (icore_have _ _ _ _ 0); [exact I6 | reflexivity | reflexivity].
      * reflexivity.
      * reflexivity.
      * autorewrite with s5w s5wbr s5i_have s5i_ncode s5i_ndist s5i_nlen. rewrite Hm0.
        intros E. cbv in E. discriminate E.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - rt_cbn. lia.
  - rt_cbn. lia.
  - rt_cbn. lia.
Qed.
