(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngHeap MngSurgery.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma key_area : forall s q, WF s -> In q (keys s) ->
  exists a k, In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\ q = padd a (AREA_HDR + META_SIZE * k).
Proof.
  intros s q HW Hq. pose proof (inv_keys HW) as (_ & KP & _ & _ & Hcnt).
  destruct (KP q Hq) as (a & k & Ha & Hk & E). exists a, k. split; [exact Ha|]. split; [|exact E].
  unfold handed in Hk. destruct (sptr_eqb _ _); unfold METAS_PER_AREA in *; lia.
Qed.

Lemma area_page_In : forall s a, In a (st_areas s) -> In (LMem a, PGSZ) (footprint s).
Proof. intros s a Ha. unfold footprint. right. apply in_app_iff. left. apply (in_map (fun a1 => (LMem a1, PGSZ))). exact Ha. Qed.

Section G.
Variable L : layout.

#[using="Type"] Lemma meta_geom : forall s q spz, WF s -> layout_ok L s -> In q (keys s) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  exists a, In a (st_areas s) /\ loc_addr L (LMem a) + 24 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= loc_addr L (LMem a) + 4096 /\
    1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= spz - 1024 /\ loc_addr L (LMem q) + 40 < 2^63 /\
    (loc_addr L (LMem q) + 40 <= 0x10000 \/ 0x99000 <= loc_addr L (LMem q)) /\ loc_addr L (LMem q) mod 8 = 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s q spz HW HL Hq HFP HAP. destruct (key_area s q HW Hq) as (a & k & Ha & Hk & ->).
  pose proof (area_page_In s a Ha) as FA.
  pose proof (proj2 (proj2 (proj2 HL)) _ FA) as R. pose proof (HFP _ FA) as S.
  pose proof (HAP _ FA ltac:(discriminate)) as D. pose proof HL as (_ & Lal & _).
  pose proof (inv_areas HW) as (_ & AOK & _). destruct (AOK a Ha) as (ra & oa & rga & Ea & Oal & Opg & Hra & Hla & _).
  pose proof (Lal ra rga Hra Hla) as Aal.
  unfold crange, ranges_disjoint in R, D. cbn [fst snd] in R, S, D. rewrite loc_padd.
  unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
  exists a. split; [exact Ha|].
  assert (AM : loc_addr L (LMem a) mod 8 = 0).
  { rewrite Ea. cbn [loc_addr]. rewrite Zplus_mod.
    replace (ly_reg L ra mod 8) with 0. 2:{ pose proof (Z.div_mod (ly_reg L ra) 4096 ltac:(lia)) as E. rewrite Aal in E. rewrite E.
      replace (4096 * (ly_reg L ra / 4096) + 0) with ((512 * (ly_reg L ra / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    replace (oa mod 8) with 0. 2:{ pose proof (Z.div_mod oa 4096 ltac:(lia)) as E. rewrite Oal in E. rewrite E.
      replace (4096 * (oa / 4096) + 0) with ((512 * (oa / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    reflexivity. }
  repeat split; try lia.
Qed.

#[using="Type"] Lemma metas_disjoint : forall s q1 q2, WF s -> layout_ok L s -> In q1 (keys s) -> In q2 (keys s) -> q1 <> q2 ->
  loc_addr L (LMem q1) + 40 <= loc_addr L (LMem q2) \/ loc_addr L (LMem q2) + 40 <= loc_addr L (LMem q1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s q1 q2 HW HL H1 H2 Hne.
  destruct (key_area s q1 HW H1) as (a1 & k1 & Ha1 & Hk1 & ->). destruct (key_area s q2 HW H2) as (a2 & k2 & Ha2 & Hk2 & ->).
  rewrite !loc_padd. unfold AREA_HDR, META_SIZE, METAS_PER_AREA in *.
  destruct (sptr_eq_dec a1 a2) as [->|Ha].
  - assert (k1 <> k2) by (intro E; apply Hne; rewrite E; reflexivity). lia.
  - pose proof HL as (_ & _ & Ldisj & _).
    assert (Hne' : (LMem a1, PGSZ) <> (LMem a2, PGSZ)) by (intro E; injection E; intros; contradiction).
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj (area_page_In s a1 Ha1) (area_page_In s a2 Ha2) Hne') as [D|D];
      unfold ranges_disjoint, crange in D; cbn [fst snd] in D; unfold PGSZ in D; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_in_region : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) ->
  exists k rg, region_of s k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
    ly_reg L k <= loc_addr L (LMem (frame_ptr am i fr)) - 4 /\ loc_addr L (LMem (frame_ptr am i fr)) <= ly_reg L k + rg_len rg.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s g am i fr HW HF. destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  destruct (used_group_region [] None U0 s g am HW Hux) as (rg & Hr & Hk & Hl & Ho0 & Hext & _).
  pose proof (slot_in_span [] None U0 s HW g am i Hux Hi) as [SL1 SL2].
  pose proof (inv_groups HW g am Hux) as (_ & _ & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (_ & _ & (Fn & Foff & Ffit & _) & _).
  exists (prid (am_mem am)), rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|].
  assert (E : loc_addr L (LMem (frame_ptr am i fr)) = ly_reg L (prid (am_mem am)) + poff (slot_start am i) + UNIT * fr_off fr).
  { unfold frame_ptr. destruct (slot_start am i) as [r o] eqn:Es. cbn [padd loc_addr prid poff].
    assert (Er : r = prid (am_mem am)) by (rewrite <- (prid_slot_start am i), Es; reflexivity). subst r. ring. }
  rewrite E. unfold UNIT, IB in *. lia.
Qed.

#[using="Type"] Lemma area_vs_hdr : forall s g am i fr a, WF s -> layout_ok L s -> In (g, am, i, fr) (frames s) -> In a (st_areas s) ->
  loc_addr L (LMem a) + 4096 <= loc_addr L (LMem (frame_ptr am i fr)) - 4 \/ loc_addr L (LMem (frame_ptr am i fr)) <= loc_addr L (LMem a).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s g am i fr a HW HL HF Ha. destruct (hdr_in_region s g am i fr HW HF) as (k & rg & Hr & Hk & Hl & B1 & B2).
  pose proof (footprint_region_In s k rg Hr Hk Hl) as FG.
  pose proof (inv_areas HW) as (_ & AOK & _). destruct (AOK a Ha) as (ra & oa & rga & Ea & Oal & Opg & _).
  pose proof HL as (_ & _ & Ldisj & _).
  assert (Hne : (LMem a, PGSZ) <> (LMem (SP k 0), rg_len rg)) by (rewrite Ea; intro E; injection E; intros; unfold PGSZ in *; lia).
  destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj (area_page_In s a Ha) FG Hne) as [D|D];
    unfold ranges_disjoint, crange in D; cbn [fst snd] in D; change (loc_addr L (LMem (SP k 0))) with (ly_reg L k + 0) in D;
    unfold PGSZ in D; lia.
Qed.
End G.

(* [comment removed for export] *)
Lemma pair_eq_dec' : forall x y : option sptr * option sptr, {x = y} + {x <> y}.
Proof. decide equality; decide equality; apply sptr_eq_dec. Qed.

Lemma chain_members : forall lk prev l first x, chain lk prev l first -> In x l -> exists p n, lk x = Some (Some p, Some n).
Proof.
  intros lk prev l. revert prev. induction l as [|y t IH]; intros prev first x H Hx; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx]; [eexists; eexists; exact H1 | exact (IH y first x H2 Hx)].
Qed.

Lemma last_In' : forall (l : list sptr) d, l <> [] -> In (last l d) l.
Proof.
  induction l as [|x t IH]; intros d H; [contradiction|]. destruct t as [|y t'].
  - left. reflexivity.
  - right. change (last (x :: y :: t') d) with (last (y :: t') d). apply IH. discriminate.
Qed.

Lemma queue_ring_facts : forall s g am sc h, WF s -> usedX [] s g am -> am_sc am = sc -> 0 <= sc < 48 -> am_freed am = 0 ->
  active_hd s sc = Some h -> h <> g ->
  am_prev am = None /\ am_next am = None /\
  exists amh hp amhp, MT s h = Some (MUsed amh) /\ am_prev amh = Some hp /\ hp <> g /\ MT s hp = Some (MUsed amhp) /\
                      am_sc amh = sc /\ am_sc amhp = sc.
Proof.
  intros s g am sc h HW Hu Hsc Hr Hf0 Hhd Hhg.
  pose proof (inv_rings HW) as (_ & AR & _). destruct (AR sc Hr) as (ms & (CY & Ehd) & Hiff & _ & _ & R2).
  assert (Hg : ~ In g ms).
  { intro Hin. apply (R2 g am Hu Hsc Hin); [rewrite Hhd; intro E; injection E; intros; contradiction | intros i0 E; discriminate | exact Hf0]. }
  assert (Hl : (am_prev am, am_next am) = (None, None)).
  { destruct (pair_eq_dec' (am_prev am, am_next am) (None, None)) as [E|E]; [exact E|].
    exfalso. apply Hg. apply (proj2 (Hiff g am Hu Hsc)). exact E. }
  injection Hl as Hp Hn. split; [exact Hp|]. split; [exact Hn|].
  destruct ms as [|m0 rest]; [cbn in Ehd; rewrite Hhd in Ehd; discriminate|].
  cbn [hd_error] in Ehd. rewrite Hhd in Ehd. injection Ehd as <-.
  destruct CY as (_ & CH). cbn [chain] in CH. destruct CH as (Lh & CHr).
  unfold alinks, MTX in Lh. cbn [memb existsb] in Lh.
  destruct (MT s h) as [[pr nx| |amh]|] eqn:Mh; try discriminate.
  destruct (am_sc amh =? sc) eqn:Esc; [|discriminate]. injection Lh as Hpr Hnx.
  set (hp := last (h :: rest) h) in *.
  assert (Hhp : In hp (h :: rest)) by (apply last_In'; discriminate).
  assert (Chain : chain (alinks [] s sc) (last (h :: rest) h) (h :: rest) h) by (split; [unfold alinks, MTX; cbn [memb existsb]; rewrite Mh, Esc; rewrite Hpr, Hnx; reflexivity | exact CHr]).
  destruct (chain_members _ _ _ _ hp Chain Hhp) as (p0 & n0 & Lhp).
  unfold alinks, MTX in Lhp. cbn [memb existsb] in Lhp.
  destruct (MT s hp) as [[pr' nx'| |amhp]|] eqn:Mhp; try discriminate.
  destruct (am_sc amhp =? sc) eqn:Esc'; [|discriminate].
  exists amh, hp, amhp. split; [reflexivity|]. split; [exact Hpr|]. split.
  - intro E. apply Hg. rewrite <- E. exact Hhp.
  - split; [exact Mhp|]. split; apply Z.eqb_eq; assumption.
Qed.
