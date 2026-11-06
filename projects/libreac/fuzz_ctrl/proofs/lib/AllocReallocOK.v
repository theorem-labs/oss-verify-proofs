From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0x YO03 YO0m YO0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0j YO0n YO0l YO0o YO0d YM02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import AllocSI AllocRealloc.
Import ListNotations.
Local Open Scope Z_scope.

Lemma In_lupd_inv {X} (l : list X) i v x : In x (lupd l i v) -> In x l \/ x = v.
Proof.
  revert i. induction l as [|a l IH]; intros i H; [destruct i; cbn in H; contradiction|].
  destruct i as [|i]; cbn in H.
  - destruct H as [<-|H]; [right; reflexivity | left; right; exact H].
  - destruct H as [<-|H]; [left; left; reflexivity|].
    destruct (IH i H) as [H1|H1]; [left; right; exact H1 | right; exact H1].
Qed.

Lemma II_upd_meta s g x : II s -> II (upd_meta g x s).
Proof. intros H. exact H. Qed.

Lemma II_rm s g am i off n rg : II s -> region_of s (prid (am_mem am)) = Some rg -> rg_kind rg = RkMap ->
  rm_need n off <= MG_REQ -> 0 <= rm_need n off -> II (rm_state s g am i off n).
Proof.
  intros HII Hr Hk Hq Hq0.
  destruct (YO0m.region_of_lt s _ rg Hr) as [Hlt Hnth].
  set (nw := mkRegion RkMap (rm_need n off) [] true).
  set (d := mkRegion RkMap 0 [] false).
  assert (Hn : nth (prid (am_mem am)) (st_regions s ++ [nw]) d = rg) by (rewrite app_nth1 by lia; exact Hnth).
  assert (ER : st_regions (rm_state s g am i off n) =
    lupd (st_regions s ++ [nw]) (prid (am_mem am)) (mkRegion RkMap (rg_len rg) [] false)).
  { unfold rm_state, rm_mid, upd_meta. cbn. fold d. fold nw. rewrite Hn. reflexivity. }
  assert (F : forall f, (forall x, rg_kind x = RkMap -> f x = 0) ->
    rsum f (st_regions (rm_state s g am i off n)) = rsum f (st_regions s)).
  { intros f Hf. rewrite ER, (rsum_lupd f _ _ _ d) by (rewrite length_app; cbn [length]; lia).
    rewrite rsum_app, Hn, (Hf rg Hk), (Hf (mkRegion RkMap (rg_len rg) [] false) eq_refl).
    unfold rsum. cbn [fold_right]. rewrite (Hf nw eq_refl). lia. }
  assert (Fr : forall x, rg_kind x = RkMap -> f_resvb x = 0) by (intros x Hx; unfold f_resvb, is_resv; rewrite Hx; reflexivity).
  assert (Fc : forall x, rg_kind x = RkMap -> f_resvc x = 0) by (intros x Hx; unfold f_resvc, is_resv; rewrite Hx; reflexivity).
  assert (Fb : forall x, rg_kind x = RkMap -> f_brkb x = 0)
    by (intros x Hx; unfold f_brkb, is_brk; rewrite Hx, Bool.andb_false_r; reflexivity).
  assert (ERT : resv_total (rm_state s g am i off n) = resv_total s) by (rewrite !resv_total_rsum; exact (F _ Fr)).
  assert (ERC : resv_count (rm_state s g am i off n) = resv_count s) by (unfold resv_count; exact (F _ Fc)).
  assert (EBB : brk_bytes (rm_state s g am i off n) = brk_bytes s) by (unfold brk_bytes; exact (F _ Fb)).
  assert (ESh : shift (rm_state s g am i off n) = shift s) by reflexivity.
  assert (EAc : acnt (rm_state s g am i off n) = acnt s) by reflexivity.
  assert (EAm : st_avail_meta_count (rm_state s g am i off n) = st_avail_meta_count s) by reflexivity.
  assert (ENa : nareas (rm_state s g am i off n) = nareas s) by reflexivity.
  assert (EH : hand (rm_state s g am i off n) = hand s) by reflexivity.
  pose proof HII as (NN & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & ML).
  unfold II. rewrite ERT, ERC, EBB, ESh, EAc, EAm, ENa, EH.
  split; [|split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|split; [exact H5|split; [exact H6|
    split; [exact H7|split; [exact H8|]]]]]]]]].
  - intros x Hx. rewrite ER in Hx. destruct (In_lupd_inv _ _ _ _ Hx) as [Hx' | ->].
    + apply in_app_iff in Hx' as [Hx'|[<-|[]]]; [exact (NN x Hx') | cbn; exact Hq0].
    + cbn. apply NN. rewrite <- Hnth. apply nth_In. exact Hlt.
  - intros x Hx. rewrite ER in Hx. destruct (In_lupd_inv _ _ _ _ Hx) as [Hx' | ->].
    + apply in_app_iff in Hx' as [Hx'|[<-|[]]]; [exact (ML x Hx') | unfold f_mapb; cbn; exact Hq].
    + unfold f_mapb. cbn. unfold MG_REQ. lia.
Qed.

Lemma move_OK4 s p k n : WF s -> In (p, k) (user_blocks s) -> II s -> 0 <= n -> ROOM4 s n ->
  OK4 (fun r => II (snd r)) (realloc_move p n s).
Proof.
  intros HW Hin HII Hn R4. unfold realloc_move.
  apply (OK4_bind_y (MPost s n)); [exact (OK4_malloc n s (malloc_reqs_ok s n HW Hn) HII Hn R4)|].
  intros [q|] s1 tr Hy HP; unfold MPost in HP; cbn [snd] in HP; destruct HP as (HII1 & _); cbv beta iota;
    [|apply OK4_ret; exact HII1].
  pose proof (malloc_wf s n tr (Some q) s1 HW Hn Hy) as HW1.
  destruct (malloc_blocks s n tr (Some q) s1 HW Hn Hy) as (l1 & l2 & E1 & E2 & _).
  pose proof (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) as Hin1.
  apply (OK4_bind (FPost s1)); [exact (OK4_free (Some p) s1 (free_reqs_ok s1 p k HW1 Hin1) HII1)|].
  intros [] s2 HF. apply OK4_ret. exact (proj1 HF).
Qed.

Lemma page_round_add x a : 0 <= a <= PGSZ -> page_round (x + a) <= page_round x + PGSZ.
Proof.
  intros Ha. unfold page_round, PGSZ in *.
  assert (D : (x + a + 4096 - 1) / 4096 <= (x + 4096 - 1) / 4096 + 1).
  { replace ((x + 4096 - 1) / 4096 + 1) with ((x + 4096 - 1 + 1 * 4096) / 4096) by (rewrite Z.div_add by lia; reflexivity).
    apply Z.div_le_mono; lia. }
  lia.
Qed.

Theorem realloc_OK4 : forall s p k n, WF s -> In (p, k) (user_blocks s) -> II s -> 0 <= n < 2 ^ 62 -> ROOM4 s n ->
  page_round (n + IB + UNIT) + PGSZ <= MG_REQ ->
  OK4 (fun r => II (snd r)) (realloc (Some p) n s).
Proof.
  intros s p k n HW Hin HII Hn R4 Hrq.
  assert (Ov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  destruct (user_blocks_frame s p k HW Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep).
  assert (Hff : find_frame_in (st_metas s) p = Some (g, i))
    by (rewrite Ep; exact (find_frame_in_spec [] None U0 s HW g am i fr Hu Hi Hfr)).
  pose proof (inv_groups HW g am Hu) as (_ & _ & Hsl & Hcl & Hmo & _).
  assert (Hoff : 0 <= fr_off fr <= 255).
  { pose proof (Hsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & Ho & _) & _). exact Ho. }
  pose proof (move_OK4 s p k n HW Hin HII (proj1 Hn) R4) as HM.
  unfold realloc. rewrite Ov. unfold bind.
  rewrite (ra_ffe p s (g, i) Hff). cbn [ibind fst snd].
  rewrite (ra_getm g s am (proj1 (usedX_MT _ _ _ _ Hu))). cbn [ibind]. rewrite Hfr.
  destruct ((n <=? stride_of am - IB - UNIT * fr_off fr) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1)).
  - cbn [ibind fst snd bind setm modify ret]. split; [exact I | exact HII].
  - destruct ((48 <=? am_sc am) && (MMAP_THRESHOLD <=? n)); [|exact HM].
    destruct (am_sc am =? 63) eqn:E63; cbn [ibind massert ret fail]; [|split; exact I].
    apply Z.eqb_eq in E63.
    destruct (am_maplen am * 4096 =? page_round (n + UNIT * fr_off fr + UNIT + IB)).
    + cbn [ibind fst snd bind setm modify ret]. split; [exact I | exact HII].
    + assert (Hml : 0 < am_maplen am).
      { destruct Hcl as [(_ & _ & Hm1 & _)|(Hc & _)]; [lia | lia]. }
      destruct (Hmo Hml) as (r & rg & Hmem & Hr & Hkd & _).
      assert (Hneed : 0 <= rm_need n (fr_off fr) <= MG_REQ).
      { unfold rm_need. pose proof (page_round_add (n + IB + UNIT) (UNIT * fr_off fr) ltac:(unfold UNIT, PGSZ; lia)) as PA.
        replace (n + UNIT * fr_off fr + UNIT + IB) with (n + IB + UNIT + UNIT * fr_off fr) by lia.
        pose proof (page_round_ge (n + IB + UNIT + UNIT * fr_off fr)) as PG.
        unfold UNIT, IB, PGSZ, MG_REQ in *. lia. }
      assert (Hr' : region_of s (prid (am_mem am)) = Some rg) by (rewrite Hmem; exact Hr).
      pose proof (II_rm s g am i (fr_off fr) n rg HII Hr' Hkd (proj2 Hneed) (proj1 Hneed)) as HIIr.
      split.
      * cbn [ibind ask ok04 mmapclass fallible]. split; [exact (proj1 HM)|].
        cbn [ibind fst snd bind setm modify ret new_region get put upd_region negb Z.eqb]. exact I.
      * cbn [ibind ask leaves]. intros z _. destruct (negb (z =? 0)); cbn [ibind fst snd]; [|exact (proj2 HM)].
        cbn [ibind fst snd bind setm modify ret new_region get put upd_region leaves]. exact HIIr.
Qed.

Theorem realloc_ok04 : forall s p k n, WF s -> In (p, k) (user_blocks s) -> II s -> 0 <= n < 2 ^ 62 -> ROOM4 s n ->
  page_round (n + IB + UNIT) + PGSZ <= MG_REQ -> ok04 mgrant (realloc (Some p) n s).
Proof. intros s p k n HW Hin HII Hn R4 Hrq. exact (proj1 (realloc_OK4 s p k n HW Hin HII Hn R4 Hrq)). Qed.

Theorem realloc_II : forall s p k n tr r s', WF s -> In (p, k) (user_blocks s) -> II s -> 0 <= n < 2 ^ 62 -> ROOM4 s n ->
  page_round (n + IB + UNIT) + PGSZ <= MG_REQ -> cpath04 (realloc (Some p) n s) tr (r, s') -> II s'.
Proof.
  intros s p k n tr r s' HW Hin HII Hn R4 Hrq Hp.
  exact (leaves_cpath04 _ _ _ _ (proj2 (realloc_OK4 s p k n HW Hin HII Hn R4 Hrq)) Hp).
Qed.

Theorem realloc_cpath04_some : forall s p k n tr r s', WF s -> In (p, k) (user_blocks s) -> size_overflows n = false ->
  cpath04 (realloc (Some p) n s) tr (r, s') -> exists q, r = Some q.
Proof.
  intros s p k n tr r s' HW Hin Ov Hp.
  destruct (user_blocks_frame s p k HW Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep).
  assert (Hff : find_frame_in (st_metas s) p = Some (g, i))
    by (rewrite Ep; exact (find_frame_in_spec [] None U0 s HW g am i fr Hu Hi Hfr)).
  destruct (ra_shape canswer04 s p n g i am fr tr r s' Ov Hff (proj1 (usedX_MT _ _ _ _ Hu)) Hfr (rpath_cpath04 _ _ _ Hp))
    as [(_ & -> & _) | [(_ & _ & _ & -> & _) | [(_ & _ & _ & -> & _) | (tr' & Hm)]]];
    try (eexists; reflexivity).
  destruct (ra_move canswer04 p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
  destruct (malloc_cpath04_some n s tr1 (q, s1) Ov (cpath04_rpath _ _ _ H1)) as [q' Eq]. cbn [fst] in Eq. subst q.
  destruct Hq as [-> _]. eexists; reflexivity.
Qed.
