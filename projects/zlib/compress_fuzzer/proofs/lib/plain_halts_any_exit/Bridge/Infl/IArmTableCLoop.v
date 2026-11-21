(** * Bridge.Infl.IArmTableCLoop — pair I9: CODELENS's inner [while], S5 vs RT.

    S5's [codelens_while] (fuel 321) against RT's [cl_loop] (fuel [tot + 1]), one
    [codelens_body] against one [cl_step].  The invariant [clinv] carries [icore] of the
    partial state (RT's [put_cl]), the code-length table's [tview], and the facts the
    LENS/DISTS builds need afterwards: [have <= tot <= 316] and every length written so far
    is at most 15.  S5's fuel is never the binding one: on RT's [ClDone] path RT's own
    fuel [tot + 1 <= 317] sufficed, and S5 takes one trip per RT trip. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits ITree IArmTableKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition clinv (q0 : RI.InfSt) (t : RBa.ztbl) (nb tot : Z) (w : IS.iw) (cs : RI.ClSt) : Prop :=
  icore w (put_cl q0 cs)
  /\ tview (IS.code_at (IS.w_s w) (IS.is_lencode (IS.w_s w))) t nb KCodes
  /\ IS.is_lenbits (IS.w_s w) = nb
  /\ IS.is_nlen (IS.w_s w) + IS.is_ndist (IS.w_s w) = tot
  /\ 0 <= RI.cl_have cs <= tot /\ tot <= 316
  /\ (forall i, 0 <= i < RI.cl_have cs -> 0 <= RI.cl_lens cs i <= 15).

Lemma codelens_while_S : forall k w, IA.codelens_while (S k) w =
  if IS.is_have (IS.w_s w) <? IS.is_nlen (IS.w_s w) + IS.is_ndist (IS.w_s w)
  then IS.abind IA.codelens_body (fun c => if c then IA.codelens_while k else IS.aret tt) w
  else IS.ARun tt w.
Proof.
  intros k w.
  change (IA.codelens_while (S k) w) with
    ((if IS.is_have (IS.w_s w) <? IS.is_nlen (IS.w_s w) + IS.is_ndist (IS.w_s w)
      then IS.abind IA.codelens_body (fun c => if c then IA.codelens_while k else IS.aret tt)
      else IS.aret tt) w).
  destruct (_ <? _); reflexivity.
Qed.

Lemma bits_of_nonneg : forall n b, 0 <= n -> 0 <= RB.br_bits_of n b < 2 ^ n.
Proof. intros n b Hn. unfold RB.br_bits_of. apply land_mask_range. exact Hn. Qed.

(** The common end of the three repeat symbols: [lens_repeat] and the new invariant. *)
Lemma cl_rep_fin : forall q0 t nb tot w cs W b2 cp lenS lenR,
  clinv q0 t nb tot w cs ->
  icore W (RI.qset_br (put_cl q0 cs) b2) -> IS.w_s W = IS.w_s w ->
  RI.cl_have cs + cp <= tot -> 3 <= cp -> lenS = lenR -> 0 <= lenR <= 15 ->
  exists W', IS.abind (IA.lens_repeat cp lenS) (fun _ => IS.aret true) W = IS.ARun true W'
    /\ clinv q0 t nb tot W'
         (RI.mkClSt (RI.cl_have cs + cp) (RI.zfill (Z.to_nat cp) (RI.cl_lens cs) (RI.cl_have cs) lenR) b2).
Proof.
  intros q0 t nb tot w cs W b2 cp lenS lenR HI HW HWs Hcp H3 -> Hlen.
  destruct HI as (Hc & Htv & Hnb & Htot & Hh & H316 & Hlr).
  pose proof (icore_bld _ _ HW) as (_ & _ & _ & Hhv & Hll & Hlrel & _).
  unfold put_cl in Hhv, Hlrel. rt_cbn_in Hhv. rt_cbn_in Hlrel.
  rewrite (abind_ARun _ _ _ _ _ (lens_repeat_eq cp lenR W)). cbv beta. rewrite aret_eq.
  rewrite Hhv.
  match goal with |- context [loopZ cp (rep_step lenR) ?st] =>
    destruct (rep_loop cp (IS.is_lens (IS.w_s W)) (RI.cl_lens cs) (RI.cl_have cs) lenR st eq_refl
                ltac:(lia) ltac:(lia) ltac:(unfold NLENS; lia) Hll Hlrel ltac:(lia)) as (L' & EL & HL'l & HL'r)
  end.
  rewrite EL. cbv iota.
  eexists; split; [reflexivity|].
  unfold clinv. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply icore_req.
    + exact (icore_lens_have _ _ _ _ (RI.zfill (Z.to_nat cp) (RI.cl_lens cs) (RI.cl_have cs) lenR) _
               (RI.cl_have cs + cp) HW eq_refl HL'l HL'r eq_refl).
    + reflexivity.
  - autorewrite with s5w s5i_have s5i_lens.
    rewrite (code_at_eq _ (IS.w_s W)) by (autorewrite with s5i_have s5i_lens; reflexivity).
    rewrite HWs. exact Htv.
  - autorewrite with s5w s5i_have s5i_lens. rewrite HWs. exact Hnb.
  - autorewrite with s5w s5i_have s5i_lens. rewrite HWs. exact Htot.
  - cbn [RI.cl_have]. lia.
  - exact H316.
  - intros i Hi. cbn [RI.cl_have RI.cl_lens] in Hi |- *.
    destruct (Z_lt_le_dec i (RI.cl_have cs)) as [Lt|Ge].
    + rewrite RI.zfill_miss by (intros m Hm; lia). apply Hlr; lia.
    + replace i with (RI.cl_have cs + Z.of_nat (Z.to_nat (i - RI.cl_have cs))) by lia.
      rewrite RI.zfill_hit by lia. exact Hlen.
Qed.

(** The 17/18 symbols (a run of zeros): NEEDBITS, DROPBITS, BITS, DROPBITS, then [lens_repeat]. *)
Lemma cl_rep_zero : forall q0 t nb tot w cs b1 b2 cb k base (bad : IS.AM bool),
  clinv q0 t nb tot w cs ->
  icore (wbr w b1) (RI.qset_br (put_cl q0 cs) b1) -> brel (wbr w b1) b1 ->
  0 <= cb <= 15 -> 1 <= k <= 7 -> 3 <= base ->
  RI.inf_nb (cb + k) b1 = RI.NBOk b2 ->
  (tot <? RI.cl_have cs + (base + RB.br_bits_of k (RB.br_dropbits cb b2))) = false ->
  exists w',
    IS.abind (IS.abind (IA.NEEDBITS (cb + k)) (fun _ => IS.abind (IA.DROPBITS cb)
        (fun _ => IS.abind (IA.BITS k) (fun b => IS.abind (IA.DROPBITS k)
        (fun _ => IS.aret (Some (0, base + b)))))))
      (fun lc => match lc with
                 | None => IS.aret false
                 | Some (len, copy) =>
                     IS.abind (IS.gs (fun s => s)) (fun s =>
                       if IS.is_nlen s + IS.is_ndist s <? IS.is_have s + copy then bad
                       else IS.abind (IA.lens_repeat copy len) (fun _ => IS.aret true))
                 end) (wbr w b1) = IS.ARun true w'
    /\ clinv q0 t nb tot w'
         (RI.mkClSt (RI.cl_have cs + (base + RB.br_bits_of k (RB.br_dropbits cb b2)))
                    (RI.zfill (Z.to_nat (base + RB.br_bits_of k (RB.br_dropbits cb b2)))
                              (RI.cl_lens cs) (RI.cl_have cs) 0)
                    (RB.br_dropbits k (RB.br_dropbits cb b2))).
Proof.
  intros q0 t nb tot w cs b1 b2 cb k base bad HI Hc1 Hb1 Hcb Hk Hbase Hn Ht.
  pose proof HI as (Hc & Htv & Hnb & Htot & Hh & H316 & Hlr).
  pose proof (icore_b8 _ _ Hc1) as H81. rt_cbn_in H81.
  pose proof (icore_bld _ _ Hc) as (_ & _ & _ & Hhv & _ & _ & _). unfold put_cl in Hhv. rt_cbn_in Hhv.
  rewrite abind_assoc.
  destruct (needbits_sim (wbr w b1) b1 b2 (cb + k) Hb1 ltac:(lia) Hn) as (En & Hbn & Hge & Hinn & Hsumn).
  rewrite (abind_ARun _ _ _ _ _ En). cbv beta.
  rewrite abind_assoc.
  destruct (dropbits_sim _ b2 cb Hbn ltac:(lia)) as (Ed2 & Hbd).
  rewrite (abind_ARun _ _ _ _ _ Ed2). cbv beta.
  rewrite abind_assoc.
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ k Hbd ltac:(lia))). cbv beta.
  rewrite abind_assoc.
  destruct (dropbits_sim _ (RB.br_dropbits cb b2) k Hbd ltac:(cbn [RB.br_dropbits RB.br_bits]; lia))
    as (Ed3 & Hbd3).
  rewrite (abind_ARun _ _ _ _ _ Ed3). cbv beta.
  rewrite abind_aret. cbv beta iota.
  rewrite abind_gs. cbv beta.
  rewrite !wbr_s, Hhv, Htot, Ht. cbv iota.
  pose proof (bits_of_nonneg k (RB.br_dropbits cb b2) ltac:(lia)) as Hbk.
  pose proof (nb_b8 _ _ _ Hn H81) as H82.
  apply (cl_rep_fin q0 t nb tot w cs _ _ _ 0 0 HI).
  - eapply icore_req;
      [apply icore_br; [apply icore_br; [apply icore_br; [exact Hc1|]|]|] | reflexivity]; rt_cbn.
    + exact (brf_intro (wbr w b1) b1 b2 Hbn Hinn Hsumn H82).
    + exact (brf_drop _ b2 cb Hbd ltac:(lia) H82).
    + apply (brf_drop _ _ k Hbd3 ltac:(lia)). cbn [RB.br_dropbits RB.br_bits RB.br_next]. lia.
  - reflexivity.
  - apply Z.ltb_ge in Ht. lia.
  - lia.
  - reflexivity.
  - lia.
Qed.

Lemma cl_body_sim : forall q0 t nb tot w cs cs',
  clinv q0 t nb tot w cs -> RI.cl_step t nb tot cs = RI.ClCont cs' ->
  exists w', IA.codelens_body w = IS.ARun true w' /\ clinv q0 t nb tot w' cs'.
Proof.
  intros q0 t nb tot w cs cs' HI Hs.
  pose proof HI as (Hc & Htv & Hnb & Htot & Hh & H316 & Hlr).
  pose proof (icore_brel _ _ Hc) as Hb. unfold put_cl in Hb. rt_cbn_in Hb.
  pose proof (icore_b8 _ _ Hc) as H8. unfold put_cl in H8. rt_cbn_in H8.
  pose proof (icore_bld _ _ Hc) as (_ & _ & _ & Hhv & Hll & Hlrel & _).
  unfold put_cl in Hhv, Hlrel. rt_cbn_in Hhv. rt_cbn_in Hlrel.
  unfold RI.cl_step in Hs. revert Hs.
  destruct (Z.leb_spec tot (RI.cl_have cs)) as [L|L]; [intros Hs; discriminate Hs|].
  destruct (RI.inf_fetch t nb (RI.cl_br cs)) as [h b1| |] eqn:Hf; [|intros Hs; discriminate Hs..].
  destruct (decode1_sim w (RI.cl_br cs) b1 (IS.is_lencode (IS.w_s w)) t nb KCodes h Hb Htv Hf)
    as (Ed & Hb1 & Hin1 & Hsum1 & (x & Hx & _ & Eh) & Hcb1).
  pose proof Htv as [Hroot Htv']. destruct (Htv' x Hx) as (Ef & Hrng & Hcbx & _).
  rewrite <- Eh in Ef, Hrng. rewrite Ef, (enc_bits _ Hrng) in Hcbx.
  pose proof Hrng as (Hop & Hbt & Hvr).
  pose proof (fetch_b8 _ _ _ _ _ Hf H8) as H81.
  assert (Fb1 : brf (RI.cl_br cs) b1) by exact (brf_intro w _ b1 Hb1 Hin1 Hsum1 H81).
  assert (Hc1 : icore (wbr w b1) (RI.qset_br (put_cl q0 cs) b1)) by (apply icore_br; [exact Hc | exact Fb1]).
  (* S5: the decode *)
  unfold IA.codelens_body. rewrite abind_gs. cbv beta. rewrite Hnb.
  rewrite (abind_ARun _ _ _ _ _ Ed). cbv beta.
  rewrite (enc_val _ Hrng), (enc_bits _ Hrng).
  destruct (RBa.c_val h <? 16) eqn:V.
  - (* a length 0..15 *)
    intros Hs. injection Hs as <-. cbv iota.
    destruct (dropbits_sim (wbr w b1) b1 (RBa.c_bits h) Hb1 ltac:(lia)) as (Edr & Hb2).
    rewrite (abind_ARun _ _ _ _ _ Edr). cbv beta.
    rewrite abind_gs. cbv beta.
    rewrite abind_setlens. cbv beta.
    rewrite abind_us. cbv beta.
    rewrite aret_eq.
    eexists; split; [reflexivity|].
    apply Z.ltb_lt in V.
    unfold clinv. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + eapply icore_req.
      * eapply (icore_have _ _ _ _ (RI.cl_have cs + 1)).
        -- eapply (icore_lens _ _ _ _ (RBa.zset (RI.cl_lens cs) (RI.cl_have cs) (RBa.c_val h))).
           ++ apply icore_br; [exact Hc1|]. rt_cbn.
              exact (brf_drop _ b1 (RBa.c_bits h) Hb2 ltac:(lia) H81).
           ++ reflexivity.
           ++ rewrite arr_len_set. autorewrite with s5wbr. exact Hll.
           ++ autorewrite with s5wbr. rewrite Hhv, wrap16_id by lia.
              apply arr_rel_set; [exact Hlrel | rewrite Hll; unfold NLENS; lia].
        -- reflexivity.
        -- autorewrite with s5w s5i_lens s5wbr. rewrite Hhv. apply wrap32_id. lia.
      * reflexivity.
    + autorewrite with s5w s5i_have s5i_lens s5wbr.
      rewrite (code_at_eq _ (IS.w_s w)) by (autorewrite with s5i_have s5i_lens; reflexivity).
      exact Htv.
    + autorewrite with s5w s5i_have s5i_lens s5wbr. exact Hnb.
    + autorewrite with s5w s5i_have s5i_lens s5wbr. exact Htot.
    + cbn [RI.cl_have]. lia.
    + exact H316.
    + intros i Hi. cbn [RI.cl_have RI.cl_lens] in Hi |- *.
      destruct (Z.eq_dec i (RI.cl_have cs)) as [->|Hne].
      * rewrite RBa.zset_same. lia.
      * rewrite RBa.zset_other by exact Hne. apply Hlr. lia.
  - (* a repeat symbol *)
    cbv iota zeta.
    destruct (RBa.c_val h =? 16) eqn:V16.
    + (* 16: repeat the previous length *)
      cbv iota.
      destruct (RI.inf_nb (RBa.c_bits h + 2) b1) as [b2|b2] eqn:Hn; [|intros Hs; discriminate Hs].
      cbv iota.
      destruct (RI.cl_have cs =? 0) eqn:H0; [intros Hs; discriminate Hs|].
      cbv iota.
      destruct (tot <? RI.cl_have cs + (3 + RB.br_bits_of 2 (RB.br_dropbits (RBa.c_bits h) b2))) eqn:Ht;
        [intros Hs; discriminate Hs|].
      intros Hs. injection Hs as <-.
      apply Z.eqb_neq in H0.
      pose proof (nb_b8 _ _ _ Hn H81) as H82.
      rewrite abind_assoc.
      destruct (needbits_sim (wbr w b1) b1 b2 (RBa.c_bits h + 2) Hb1 ltac:(lia) Hn)
        as (En & Hbn & Hge & Hinn & Hsumn).
      rewrite (abind_ARun _ _ _ _ _ En). cbv beta.
      rewrite abind_assoc.
      destruct (dropbits_sim _ b2 (RBa.c_bits h) Hbn ltac:(lia)) as (Ed2 & Hbd).
      rewrite (abind_ARun _ _ _ _ _ Ed2). cbv beta.
      rewrite abind_assoc, abind_gs. cbv beta zeta.
      rewrite !wbr_s, Hhv. rewrite (proj2 (Z.eqb_neq _ _) H0). cbv iota.
      rewrite abind_assoc.
      rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 2 Hbd ltac:(lia))). cbv beta.
      rewrite abind_assoc.
      destruct (dropbits_sim _ (RB.br_dropbits (RBa.c_bits h) b2) 2 Hbd
                  ltac:(cbn [RB.br_dropbits RB.br_bits]; lia)) as (Ed3 & Hbd3).
      rewrite (abind_ARun _ _ _ _ _ Ed3). cbv beta.
      rewrite abind_aret. cbv beta iota.
      rewrite abind_gs. cbv beta.
      rewrite !wbr_s, Hhv, Htot, Ht. cbv iota.
      pose proof (bits_of_nonneg 2 (RB.br_dropbits (RBa.c_bits h) b2) ltac:(lia)) as Hbk.
      apply (cl_rep_fin q0 t nb tot w cs _ _ _ _ _ HI).
      * eapply icore_req;
          [apply icore_br; [apply icore_br; [apply icore_br; [exact Hc1|]|]|] | reflexivity]; rt_cbn.
        -- exact (brf_intro (wbr w b1) b1 b2 Hbn Hinn Hsumn H82).
        -- exact (brf_drop _ b2 (RBa.c_bits h) Hbd ltac:(lia) H82).
        -- apply (brf_drop _ _ 2 Hbd3 ltac:(lia)). cbn [RB.br_dropbits RB.br_bits RB.br_next]. lia.
      * reflexivity.
      * apply Z.ltb_ge in Ht. lia.
      * lia.
      * apply Hlrel. unfold NLENS. lia.
      * apply Hlr. lia.
    + destruct (RBa.c_val h =? 17) eqn:V17.
      * (* 17: 3..10 zeros *)
        cbv iota.
        destruct (RI.inf_nb (RBa.c_bits h + 3) b1) as [b2|b2] eqn:Hn; [|intros Hs; discriminate Hs].
        cbv iota.
        destruct (tot <? RI.cl_have cs + (3 + RB.br_bits_of 3 (RB.br_dropbits (RBa.c_bits h) b2))) eqn:Ht;
          [intros Hs; discriminate Hs|].
        intros Hs. injection Hs as <-.
        exact (cl_rep_zero q0 t nb tot w cs b1 b2 (RBa.c_bits h) 3 3 _ HI Hc1 Hb1 ltac:(lia) ltac:(lia)
                 ltac:(lia) Hn Ht).
      * (* 18: 11..138 zeros *)
        cbv iota.
        destruct (RI.inf_nb (RBa.c_bits h + 7) b1) as [b2|b2] eqn:Hn; [|intros Hs; discriminate Hs].
        cbv iota.
        destruct (tot <? RI.cl_have cs + (11 + RB.br_bits_of 7 (RB.br_dropbits (RBa.c_bits h) b2))) eqn:Ht;
          [intros Hs; discriminate Hs|].
        intros Hs. injection Hs as <-.
        exact (cl_rep_zero q0 t nb tot w cs b1 b2 (RBa.c_bits h) 7 11 _ HI Hc1 Hb1 ltac:(lia) ltac:(lia)
                 ltac:(lia) Hn Ht).
Qed.

Lemma cl_step_done : forall t nb tot cs c, RI.cl_step t nb tot cs = RI.ClDone c ->
  c = cs /\ tot <= RI.cl_have cs.
Proof.
  intros t nb tot cs c. unfold RI.cl_step.
  destruct (Z.leb_spec tot (RI.cl_have cs)) as [L|L]; [intros H; injection H as <-; auto|].
  destruct (RI.inf_fetch t nb (RI.cl_br cs)) as [h b| |]; try discriminate.
  destruct (RBa.c_val h <? 16); [discriminate|]. cbv zeta.
  destruct (RI.inf_nb _ b); [|discriminate].
  destruct (RBa.c_val h =? 16); [destruct (RI.cl_have cs =? 0)|destruct (RBa.c_val h =? 17)]; cbv iota;
    try discriminate; destruct (Z.ltb _ _); discriminate.
Qed.

Lemma cl_step_cont_lt : forall t nb tot cs c, RI.cl_step t nb tot cs = RI.ClCont c -> RI.cl_have cs < tot.
Proof.
  intros t nb tot cs c. unfold RI.cl_step.
  destruct (Z.leb_spec tot (RI.cl_have cs)) as [L|L]; [discriminate | intros; lia].
Qed.

Lemma cl_while_sim : forall q0 t nb tot n k w cs cs',
  clinv q0 t nb tot w cs -> (n <= k)%nat ->
  RI.cl_loop n t nb tot cs = Some (RI.ClDone cs') ->
  exists w', IA.codelens_while k w = IS.ARun tt w' /\ clinv q0 t nb tot w' cs' /\ tot <= RI.cl_have cs'.
Proof.
  intros q0 t nb tot n. induction n as [|n IH]; intros k w cs cs' HI Hk Hl; [discriminate|].
  destruct k as [|k]; [lia|].
  pose proof HI as (Hc & _ & _ & Htot & _).
  pose proof (icore_bld _ _ Hc) as (_ & _ & _ & Hhv & _). unfold put_cl in Hhv. rt_cbn_in Hhv.
  rewrite RI.cl_loop_S in Hl. revert Hl.
  destruct (RI.cl_step t nb tot cs) as [c|c|c m|c|] eqn:Hs; intros Hl; try discriminate.
  - pose proof (cl_step_cont_lt _ _ _ _ _ Hs) as Lt.
    destruct (cl_body_sim q0 t nb tot w cs c HI Hs) as (w1 & E1 & HI1).
    destruct (IH k w1 c cs' HI1 ltac:(lia) Hl) as (w2 & E2 & HI2 & Hge).
    exists w2. split; [|split; assumption].
    rewrite codelens_while_S, Hhv, Htot, (proj2 (Z.ltb_lt _ _) Lt).
    rewrite (abind_ARun _ _ _ _ _ E1). cbv beta iota. exact E2.
  - injection Hl as <-. destruct (cl_step_done _ _ _ _ _ Hs) as [-> Ge].
    exists w. split; [|split; assumption].
    rewrite codelens_while_S, Hhv, Htot, (proj2 (Z.ltb_ge _ _) Ge). reflexivity.
Qed.
