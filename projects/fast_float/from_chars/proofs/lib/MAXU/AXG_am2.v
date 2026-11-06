(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mt1z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mt1z.AXF_mt1fz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt1f1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma osptr_eqb_same : forall p, osptr_eqb (Some p) (Some p) = true.
Proof. intros p. cbn. apply sptr_eqb_refl. Qed.

Lemma osptr_eqb_diff : forall p q, p <> q -> osptr_eqb (Some p) (Some q) = false.
Proof. intros p q H. cbn. destruct (sptr_eqb p q) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma sptr_eqb_false : forall p q, p <> q -> sptr_eqb p q = false.
Proof. intros p q H. destruct (sptr_eqb p q) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma mupdate_twice2 : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn [mupdate].
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Definition s_pop1 (s : astate) (fm : sptr) : astate := upd_meta fm (MFree None None) (set_free_meta_head None s).

Lemma alloc_meta_pop1 : forall s fm pr, st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree pr (Some fm)) ->
  alloc_meta s = IRet (Some fm, s_pop1 s fm).
Proof.
  intros s fm pr Hi Hf Hm. unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn.
  unfold MT in Hm. rewrite Hm. cbn. rewrite sptr_eqb_refl. cbn. rewrite Hm. reflexivity.
Qed.

(* [comment removed for export] *)
Definition s_pop2 (s : astate) (fm x : sptr) : astate :=
  upd_meta fm (MFree None None) (set_free_meta_head (Some x) (upd_meta x (MFree (Some x) (Some x)) s)).

Lemma alloc_meta_pop2 : forall s fm x px nxx, st_init_done s = true -> st_free_meta_head s = Some fm ->
  MT s fm = Some (MFree (Some x) (Some x)) -> x <> fm -> MT s x = Some (MFree px nxx) ->
  alloc_meta s = IRet (Some fm, s_pop2 s fm x).
Proof.
  intros s fm x px nxx Hi Hf Hm Hne Hx. unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn.
  unfold MT in Hm, Hx. rewrite Hm. cbn. rewrite (sptr_eqb_false x fm Hne). cbn.
  rewrite Hx. cbn. rewrite Hx. cbn. rewrite mlookup_mupdate_same. cbn. rewrite mlookup_mupdate_same. cbn. rewrite Hf. cbn. rewrite sptr_eqb_refl. cbn.
  rewrite !mlookup_mupdate_other by exact (not_eq_sym Hne). rewrite Hm. cbn. unfold s_pop2, upd_meta. cbn. rewrite mupdate_twice2. reflexivity.
Qed.

(* [comment removed for export] *)
Definition s_popn (s : astate) (fm p n : sptr) (pp nn : option sptr) : astate :=
  upd_meta fm (MFree None None) (set_free_meta_head (Some n) (upd_meta n (MFree (Some p) nn) (upd_meta p (MFree pp (Some n)) s))).

Lemma alloc_meta_popn : forall s fm p n pp np pn nn, st_init_done s = true -> st_free_meta_head s = Some fm ->
  MT s fm = Some (MFree (Some p) (Some n)) -> n <> fm -> p <> fm -> p <> n ->
  MT s p = Some (MFree pp np) -> MT s n = Some (MFree pn nn) ->
  alloc_meta s = IRet (Some fm, s_popn s fm p n pp nn).
Proof.
  intros s fm p n pp np pn nn Hi Hf Hm Hnf Hpf Hpn Hp Hn. unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn.
  unfold MT in Hm, Hp, Hn. rewrite Hm. cbn. rewrite (sptr_eqb_false n fm Hnf). cbn.
  rewrite Hp. cbn. rewrite Hp. cbn. rewrite mlookup_mupdate_other by exact (not_eq_sym Hpn). rewrite Hn. cbn.
  rewrite mlookup_mupdate_other by exact (not_eq_sym Hpn). rewrite Hn. cbn. rewrite Hf. cbn. rewrite sptr_eqb_refl. cbn.
  rewrite !mlookup_mupdate_other by first [exact (not_eq_sym Hnf) | exact (not_eq_sym Hpf)]. rewrite Hm. cbn.
  unfold s_popn, upd_meta. cbn. reflexivity.
Qed.

Lemma deqh_pop1 : forall s fm pr, st_free_meta_head s = Some fm -> MT s fm = Some (MFree pr (Some fm)) ->
  dequeue_head HFreeMeta s = IRet (Some fm, s_pop1 s fm).
Proof.
  intros s fm pr Hf Hm. unfold dequeue_head. cbn. rewrite Hf. cbn.
  unfold MT in Hm. rewrite Hm. cbn. rewrite sptr_eqb_refl. cbn. rewrite Hm. reflexivity.
Qed.

Lemma deqh_pop2 : forall s fm x px nxx, st_free_meta_head s = Some fm ->
  MT s fm = Some (MFree (Some x) (Some x)) -> x <> fm -> MT s x = Some (MFree px nxx) ->
  dequeue_head HFreeMeta s = IRet (Some fm, s_pop2 s fm x).
Proof.
  intros s fm x px nxx Hf Hm Hne Hx. unfold dequeue_head. cbn. rewrite Hf. cbn.
  unfold MT in Hm, Hx. rewrite Hm. cbn. rewrite (sptr_eqb_false x fm Hne). cbn.
  rewrite Hx. cbn. rewrite Hx. cbn. rewrite mlookup_mupdate_same. cbn. rewrite mlookup_mupdate_same. cbn. rewrite Hf. cbn. rewrite sptr_eqb_refl. cbn.
  rewrite !mlookup_mupdate_other by exact (not_eq_sym Hne). rewrite Hm. cbn. unfold s_pop2, upd_meta. cbn. rewrite mupdate_twice2. reflexivity.
Qed.

Lemma deqh_popn : forall s fm p n pp np pn nn, st_free_meta_head s = Some fm ->
  MT s fm = Some (MFree (Some p) (Some n)) -> n <> fm -> p <> fm -> p <> n ->
  MT s p = Some (MFree pp np) -> MT s n = Some (MFree pn nn) ->
  dequeue_head HFreeMeta s = IRet (Some fm, s_popn s fm p n pp nn).
Proof.
  intros s fm p n pp np pn nn Hf Hm Hnf Hpf Hpn Hp Hn. unfold dequeue_head. cbn. rewrite Hf. cbn.
  unfold MT in Hm, Hp, Hn. rewrite Hm. cbn. rewrite (sptr_eqb_false n fm Hnf). cbn.
  rewrite Hp. cbn. rewrite Hp. cbn. rewrite mlookup_mupdate_other by exact (not_eq_sym Hpn). rewrite Hn. cbn.
  rewrite mlookup_mupdate_other by exact (not_eq_sym Hpn). rewrite Hn. cbn. rewrite Hf. cbn. rewrite sptr_eqb_refl. cbn.
  rewrite !mlookup_mupdate_other by first [exact (not_eq_sym Hnf) | exact (not_eq_sym Hpf)]. rewrite Hm. cbn.
  unfold s_popn, upd_meta. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma free_ring_nbrs : forall X R U s fm pr nx, Inv X R U s -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree pr nx) ->
  memb fm X = false /\ forall q, (pr = Some q \/ nx = Some q) -> memb q X = false /\ exists a b, MT s q = Some (MFree a b).
Proof.
  intros X R U s fm pr nx HI Hf Hm. destruct (inv_rings HI) as ((ms & FR & Fall) & _ & _). rewrite Hf in FR.
  destruct (ring_head_In _ _ _ FR) as [Hin _].
  destruct (ring_links _ _ _ fm FR Hin) as (p' & n' & E).
  assert (Mfx : MTX X s fm = Some (MFree pr nx)).
  { unfold flinks in E. destruct (MTX X s fm) as [x|] eqn:Ex; [|discriminate]. unfold MTX in Ex. destruct (memb fm X); [discriminate|]. rewrite Hm in Ex. exact (eq_sym Ex). }
  assert (Nfm : memb fm X = false) by (unfold MTX in Mfx; destruct (memb fm X); [discriminate | reflexivity]).
  unfold flinks in E. rewrite Mfx in E. injection E as -> ->.
  destruct (MngLt.cycle_members _ _ fm p' n' (proj1 FR) Hin ltac:(unfold flinks; rewrite Mfx; reflexivity)) as (Pp & Pn).
  split; [exact Nfm|]. intros q Hq.
  assert (Hqm : In q ms) by (destruct Hq as [E|E]; injection E as <-; assumption).
  destruct (ring_links _ _ _ q FR Hqm) as (a & b & Eq). unfold flinks in Eq. destruct (MTX X s q) as [[a' b'| |am]|] eqn:Ex; try discriminate.
  unfold MTX in Ex. destruct (memb q X) eqn:Em; [discriminate|]. split; [reflexivity|]. exists a', b'. exact Ex.
Qed.

(* [comment removed for export] *)
Lemma pop_facts : forall X R U s fm s', Inv X R U s -> dequeue_head HFreeMeta s = IRet (Some fm, s') ->
  Inv (fm :: X) R U s' /\ memb fm X = false /\ MT s' fm = Some (MFree None None) /\
  (forall g am, usedX (fm :: X) s' g am <-> usedX X s g am) /\ ub_same s s' /\ st_active s' = st_active s.
Proof.
  intros X R U s fm s' HI E.
  pose proof (dequeue_head_free_spec X R U s
     (fun r => fst r = Some fm -> Inv (fm :: X) R U (snd r) /\ memb fm X = false /\ MT (snd r) fm = Some (MFree None None) /\
        (forall g am, usedX (fm :: X) (snd r) g am <-> usedX X s g am) /\ ub_same s (snd r) /\ st_active (snd r) = st_active s) HI) as H.
  rewrite E in H. cbn [itok fst snd] in H. apply H; [| |reflexivity].
  - intros _ _ E2. discriminate E2.
  - intros m s2 H1 H2 H3 H4 H5 H6 H7 E2. injection E2 as <-. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [exact H6|]. split; [exact H7 | exact H5].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition prev_cell (g : sptr) (o : option sptr) : mcell := MCell (LMem (padd g META_prev)) 8 (optr o).
Definition next_cell (g : sptr) (o : option sptr) : mcell := MCell (LMem (padd g META_next)) 8 (optr o).

Lemma cov_upd_free : forall s g pr nx pr' nx', KS s -> MT s g = Some (MFree pr nx) ->
  forall c, In c (image (set_meta s g (MFree pr' nx'))) -> In c (image s) \/ c = prev_cell g pr' \/ c = next_cell g nx'.
Proof.
  intros s g pr nx pr' nx' HK Hg c Hc. assert (Hk : In g (keys s)) by (eapply MT_keys; exact Hg).
  destruct (cov_set_free s g pr' nx' c HK Hk Hc) as [H|H]; [left; exact H|].
  destruct (msc_free_links g pr nx pr' nx' c H) as [H2|[H2|H2]].
  - left. exact (msc_key_in_image s g _ c HK Hg H2).
  - right. left. exact H2.
  - right. right. exact H2.
Qed.

Lemma mupdate_back : forall l g x, mlookup l g = Some x -> mupdate l g x = l.
Proof.
  induction l as [|[q y] t IH]; intros g x H; cbn in *; [discriminate|].
  destruct (sptr_eqb g q) eqn:E; [injection H as ->; apply sptr_eqb_eq in E; subst; reflexivity|]. rewrite IH by exact H. reflexivity.
Qed.

Lemma set_meta_back : forall s g x, MT s g = Some x -> set_meta s g x = s.
Proof. intros s g x H. unfold set_meta, MT in *. rewrite (mupdate_back _ _ _ H). destruct s. reflexivity. Qed.

Lemma rev_upd_free : forall s g pr nx pr' nx', KS s -> MT s g = Some (MFree pr nx) ->
  forall c, In c (image s) -> In c (image (set_meta s g (MFree pr' nx'))) \/ c = prev_cell g pr \/ c = next_cell g nx.
Proof.
  intros s g pr nx pr' nx' HK Hg c Hc. assert (Hk : In g (keys s)) by (eapply MT_keys; exact Hg).
  set (s' := set_meta s g (MFree pr' nx')).
  assert (HK' : KS s') by (apply KS_set_meta; assumption).
  assert (Hg' : MT s' g = Some (MFree pr' nx')) by apply MT_set_same.
  assert (E : set_meta s' g (MFree pr nx) = s).
  { unfold s', set_meta. cbn [st_metas set_metas]. rewrite mupdate_twice2. exact (set_meta_back s g _ Hg). }
  rewrite <- E in Hc. exact (cov_upd_free s' g pr' nx' pr nx HK' Hg' c Hc).
Qed.

Lemma cov_fmh_image : forall s v c, In c (image (set_free_meta_head v s)) -> In c (image s) \/ c = fmh_cell v.
Proof.
  intros s v c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (cov_fmh s v c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right.
    rewrite (areas_cells_ext s (set_free_meta_head v s) _ (fun q => eq_refl)) in Hc. exact Hc.
Qed.

Lemma rev_fmh_image : forall s v c, In c (image s) -> In c (image (set_free_meta_head v s)) \/ c = fmh_cell (st_free_meta_head s).
Proof.
  intros s v c Hc. assert (E : set_free_meta_head (st_free_meta_head s) (set_free_meta_head v s) = s) by (destruct s; reflexivity).
  rewrite <- E in Hc. exact (cov_fmh_image (set_free_meta_head v s) (st_free_meta_head s) c Hc).
Qed.

Lemma KS_fmh : forall s v, KS s -> KS (set_free_meta_head v s).
Proof. intros s v H. exact H. Qed.

Lemma MT_fmh : forall s v g, MT (set_free_meta_head v s) g = MT s g.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM2.
Context {fx : FPState}.

#[using="Type"] Lemma nc_key_place : forall L s m sp0 K q, NC L [] [] s m sp0 K -> In q (keys s) ->
  1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= sp0 - K /\
  (loc_addr L (LMem q) + 40 <= 0x10000 \/ 0x99000 <= loc_addr L (LMem q)) /\ loc_addr L (LMem q) mod 8 = 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros L s m sp0 K q N Hq. exact (nc_mplace _ _ _ _ _ _ _ N q Hq). Qed.

Definition pop1_mem (m : word -> option byte) : word -> option byte := wbytes m (wa (0 + 621736)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem seg_amf1 : forall L s m R rom sp0 K spf can ra s0 s1 s2 s3 s4 fm pr,
  am_frame R m spf can ra s0 s1 s2 s3 s4 -> NC L [] [] s m sp0 K ->
  st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree pr (Some fm)) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R', msteps SEGS (mkst R (wa 0x53a94) m rom) (mkst R' (wa 0x53cd4) (pop1_mem m) rom) /\
    getr R' 10 = wa (loc_addr L (LMem fm)) /\ am_frame R' (pop1_mem m) spf can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [1; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K spf can ra s0 s1 s2 s3 s4 fm pr F N Hi Hf Hm Mpg.
  pose proof N as [HR HEX _ HK Hctx _ _ _ _ _ _ _ _ _].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Hk : In fm (keys s)) by (eapply MT_keys; exact Hm).
  destruct (nc_key_place L s m sp0 K fm N Hk) as (P1 & P2 & P3 & P4).
  set (af := loc_addr L (LMem fm)) in *.
  pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hs2. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  assert (P : mt1f1_pre R m af).
  { constructor; [exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | clear - P1 P2 Hs2 HK1; lia | exact P4 | | exact Mpg | | |].
    - rewrite Z.add_0_l. exact (nc_init_rd L s m sp0 K N Hi).
    - pose proof (rx_fmh L s m [] HR HEO Hctx) as H. rewrite Hf in H. exact H.
    - pose proof (rx_fnext L s m [] HR HEO HK fm pr (Some fm) Hm) as H. cbn [onum] in H. exact H.
    - intros d k Hd Hk'. rewrite Z.add_0_l. exact (rx_fmh_wr L s m [] HR HEO Hctx d k Hd Hk'). }
  destruct (mt1f1_pmf1a R m rom af P ltac:(constructor)) as (R' & Hms & A8 & A10 & A11 & A19 & Ak).
  change (mt1f1_mem_pmf1a m R af) with (pop1_mem m) in Hms.
  exists R'. split; [exact Hms|]. split; [exact A10|].
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. apply Ak. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'. }
  split.
  - apply (am_frame_mem R' m); [| intros x Hx; unfold pop1_mem; rewrite MngWb.wbytes_out by (pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F); side); reflexivity
                               | intros x Hx; unfold pop1_mem; rewrite MngWb.wbytes_out by side; reflexivity].
    apply (am_frame_regs R R' m spf can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R' R _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R' R _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  - intros k Hk'. apply KK. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'.
Qed.

Definition popn_mem (m : word -> option byte) (nx pv : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv))) (wa (0 + 621736)) (word_to_le_bytes 8 (wa nx)).

#[using="Type"] Theorem seg_amfn : forall L s m R rom sp0 K can ra s0 s1 s2 s3 s4 fm p n,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> NC L [] [] s m sp0 K ->
  st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree (Some p) (Some n)) -> n <> fm -> p <> fm ->
  In p (keys s) -> In n (keys s) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R', msteps SEGS (mkst R (wa 0x53a94) m rom) (mkst R' (wa 0x53cd4) (popn_mem m (loc_addr L (LMem n)) (loc_addr L (LMem p))) rom) /\
    getr R' 10 = wa (loc_addr L (LMem fm)) /\ am_frame R' (popn_mem m (loc_addr L (LMem n)) (loc_addr L (LMem p))) sp0 can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [1; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K can ra s0 s1 s2 s3 s4 fm p n F N Hi Hf Hm Hnf Hpf Hkp Hkn Mpg.
  pose proof N as [HR HEX _ HK Hctx _ _ _ _ _ _ _ _ HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Hk : In fm (keys s)) by (eapply MT_keys; exact Hm).
  destruct (nc_key_place L s m sp0 K fm N Hk) as (P1 & P2 & P3 & P4).
  destruct (nc_key_place L s m sp0 K p N Hkp) as (Q1 & Q2 & Q3 & Q4).
  destruct (nc_key_place L s m sp0 K n N Hkn) as (S1 & S2 & S3 & S4).
  pose proof (HMD p fm Hkp Hk Hpf) as D1. pose proof (HMD n fm Hkn Hk Hnf) as D2.
  destruct (MT_of_key s p Hkp) as (xp & Mp). destruct (MT_of_key s n Hkn) as (xn & Mn).
  set (af := loc_addr L (LMem fm)) in *. set (an := loc_addr L (LMem n)) in *. set (ap := loc_addr L (LMem p)) in *.
  pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hs2. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  assert (P : mt1f_pre R m af an ap).
  { constructor; [exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | clear - P1 P2 Hs2 HK1; lia | clear - S1 S2 Hs2 HK1; lia | clear - Q1 Q2 Hs2 HK1; lia | exact P4
                 | | exact Mpg | | | | | | | | | | ].
    - rewrite Z.add_0_l. exact (nc_init_rd L s m sp0 K N Hi).
    - pose proof (rx_fmh L s m [] HR HEO Hctx) as H. rewrite Hf in H. exact H.
    - exact (rx_fnext L s m [] HR HEO HK fm (Some p) (Some n) Hm).
    - exact (rx_fprev L s m [] HR HEO HK fm (Some p) (Some n) Hm).
    - intros d k Hd Hk'. rewrite Z.add_0_l. exact (rx_fmh_wr L s m [] HR HEO Hctx d k Hd Hk').
    - intros d k Hd Hk'. replace (ap + 8 + d) with (ap + (8 + d)) by ring. apply (rx_msc_wr L s m [] HR HEO HK p xp Mp); lia.
    - intros d k Hd Hk'. replace (an + 0 + d) with (an + d) by ring. apply (rx_msc_wr L s m [] HR HEO HK n xn Mn); lia.
    - clear - Q1 Q3. lia.
    - clear - S1 S3. lia.
    - clear - D1. lia.
    - clear - D2. lia. }
  destruct (mt1f_pmfn R m rom af an ap P) as (R' & Hms & A8 & A10 & A11 & A12 & A19 & Ak).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mt1z.AXF_mt1f.RES_pmfn fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R (VALS_mt1f af an ap) 33 an eq_refl eq_refl) by (clear - S1 S2 Hs2 HK1; lia).
    rewrite (zatom R (VALS_mt1f af an ap) 32 af eq_refl eq_refl) by (clear - P1 P2 Hs2 HK1; lia).
    apply Z.eqb_neq. rewrite !Z.mod_small by (clear - P1 P2 S1 S2 Hs2 HK1; lia). clear - D2. lia. }
  change (mt1f_mem_pmfn m R af an ap) with (popn_mem m an ap) in Hms.
  exists R'. split; [exact Hms|]. split; [exact A10|].
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. apply Ak. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'. }
  pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp.
  split.
  - apply (am_frame_mem R' m); [| intros x Hx; unfold popn_mem; rewrite !MngWb.wbytes_out by side; reflexivity
                               | intros x Hx; unfold popn_mem; rewrite !MngWb.wbytes_out by side; reflexivity].
    apply (am_frame_regs R R' m sp0 can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R' R _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R' R _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  - intros k Hk'. apply KK. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma in_image_front' : forall s c, In c (ctx_cells s ++ areas_cells s (st_areas s)) -> In c (image s).
Proof. LiaFast.lf_pins LiaFast.u0. intros s c H. rewrite image_parts, app_assoc. apply in_app_iff. left. exact H. Qed.

#[using="Type"] Lemma memb_of_In : forall (g : sptr) X, In g X -> memb g X = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros g X H. unfold memb. apply existsb_exists. exists g. split; [exact H | apply sptr_eqb_refl]. Qed.

#[using="Type"] Lemma pop1_mem_out : forall m x, 0 <= x < 2^64 -> ~ (621736 <= x < 621744) -> pop1_mem m (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m x Hx Hn. unfold pop1_mem. rewrite MngWb.wbytes_out by side. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem am_pop1 : forall HTOP X R U L s m regs rom sp0 K ra fm pr,
  CUT HTOP X R U L s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree pr (Some fm)) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R' m', msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R' (wa ra) m' rom) /\
    getr R' 10 = wa (loc_addr L (LMem fm)) /\
    (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (fm :: X) R U L (s_pop1 s fm) m' sp0 K /\ GROW sp0 K L s m L (s_pop1 s fm) m' /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m regs rom sp0 K ra fm pr C R2 R1 Hra Hi Hf Hm Mpg.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Hk : In fm (keys s)) by (eapply MT_keys; exact Hm).
  destruct (nc_key_place L s m sp0 K fm N Hk) as (P1 & P2 & P3 & P4).
  set (af := loc_addr L (LMem fm)) in *.
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (R1' & can & Hms1 & F1 & K1 & MOUT1 & GR1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (N1 : NC L [] [] s m1 sp0 K) by (apply (NC_stackw L s m m1 sp0 K N GR1); intros x Hx Hn; apply MOUT1; [exact Hx | lia]).
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (first [lia | (intros x Hx; cbn in Hx; apply MOUT1; lia)]). exact Mpg. }
  (* [comment removed for export] *)
  destruct (seg_amf1 L s m1 R1' rom sp0 K sp0 can _ _ _ _ _ _ fm pr F1 N1 Hi Hf Hm Mpg1) as (R2' & Hms2 & B10 & F2 & K2).
  set (m2 := pop1_mem m1) in *.
  assert (G2' : mem_grows m1 m2) by (unfold m2, pop1_mem; apply wbytes_grows).
  (* [comment removed for export] *)
  assert (W16 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m2 (wa (af + 0 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m m2); [exact (mem_grows_trans _ _ _ GR1 G2')|].
    replace (af + 0 + d) with (af + d) by ring. exact (rx_msc_wr L s m [] HR HEO HK fm _ Hm d k Hd ltac:(lia)). }
  assert (Era : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; lia).
  assert (Hra' : bv_unsigned (getr regs 1) = 0x542a0 \/ bv_unsigned (getr regs 1) = 0x53ec4) by (rewrite Era; exact Hra).
  assert (D1 : af + 16 <= sp0 - 56 \/ sp0 <= af) by (clear - P2 HK1; lia).
  assert (D2 : af + 16 <= 621568 \/ 621576 <= af) by (clear - P3; lia).
  destruct (seg_ame R2' m2 rom sp0 can _ _ _ _ _ _ af F2 B10 ltac:(clear - P1 P2 Hsp2 HK1; lia) P4 W16 D1 D2 Hra')
    as (R3 & Hms3 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K3).
  set (m3 := am_ep_mem m2 af) in *.
  assert (GR3 : mem_grows m2 m3) by (unfold m3, am_ep_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))).
  rewrite Era in Hms3. exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|]. split; [exact C10|].
  split; [exact (am_regs regs R1' R2' R3 sp0 R2 K1 K2 K3 C1 C2 C8 C9 C18 C19 C20)|].
  (* [comment removed for export] *)
  destruct (pop_facts X R U s fm (s_pop1 s fm) HI (deqh_pop1 s fm pr Hf Hm)) as (HI2 & NX & MT2 & EU2 & UB2 & EA2).
  assert (HX2 : XNM (fm :: X) (s_pop1 s fm)).
  { intros x [<-|Hx]; [right; exact MT2|].
    assert (Hxk : x <> fm) by (intros ->; rewrite (memb_of_In fm X Hx) in NX; discriminate).
    unfold s_pop1. rewrite MT_upd_other by exact Hxk. exact (HX x Hx). }
  set (Cnew := [fmh_cell None; prev_cell fm None; next_cell fm None]).
  set (s1 := set_free_meta_head None s).
  assert (HK1' : KS s1) by exact HK. assert (Hm1 : MT s1 fm = Some (MFree pr (Some fm))) by exact Hm.
  assert (MOUT3 : forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> ~ (621736 <= x < 621744) -> ~ (af <= x < af + 16) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 Hsp2 HK1 Hx H3; lia). unfold m2. rewrite pop1_mem_out by (clear - Hx H2; lia).
    apply MOUT1; assumption. }
  assert (MG : mem_grows m m3) by exact (mem_grows_trans _ _ _ GR1 (mem_grows_trans _ _ _ G2' GR3)).
  cut (CUT HTOP (fm :: X) R U L (s_pop1 s fm) m3 sp0 K /\ GROW sp0 K L s m L (s_pop1 s fm) m3);
    [intros (CC & GG); split; [exact CC | split; [exact GG | exact MG]]|].
  apply (silent_step HTOP X R U (fm :: X) R U L s (s_pop1 s fm) m m3 sp0 K Cnew C HI2 HX2 eq_refl).
  - intros fpr Hfpr. left. exact Hfpr.
  - intros c Hcn. destruct (cov_upd_free s1 fm pr (Some fm) None None HK1' Hm1 c Hcn) as [H|[H|H]].
    + destruct (cov_fmh_image s None c H) as [H2|H2]; [left; exact H2 | right; subst c; cbn [In]; memb].
    + right. subst c. cbn [In]. memb.
    + right. subst c. cbn [In]. memb.
  - intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[]]]].
    + exact (fmh_cell_in (s_pop1 s fm)).
    + apply (msc_key_in_image (s_pop1 s fm) fm _ _ (KS_of_Inv _ _ _ _ HI2) MT2). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image (s_pop1 s fm) fm _ _ (KS_of_Inv _ _ _ _ HI2) MT2). cbn [meta_slot_cells In]. memb.
  - intros c Hcn. destruct (rev_fmh_image s None c Hcn) as [H|H].
    + destruct (rev_upd_free s1 fm pr (Some fm) None None HK1' Hm1 c H) as [H2|[H2|H2]]; [left; exact H2| |].
      * right. exists (prev_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
      * right. exists (next_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
    + right. exists (fmh_cell None). split; [cbn [In]; memb|]. subst c. reflexivity.
  - apply Forall_forall. intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[]]]].
    + apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m3)); [cbn [mc_w fmh_cell]; lia | |].
      * unfold m2, pop1_mem. replace (0 + 621736) with (loc_addr L (mc_loc (fmh_cell None))) by (cbn; rewrite Hctx; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w fmh_cell]; lia | cbn [mc_loc fmh_cell loc_addr]; rewrite Hctx; unfold CTX_free_meta_head; lia
                        | cbn [mc_loc mc_w fmh_cell loc_addr Z.of_nat Pos.of_succ_nat]; rewrite Hctx; unfold CTX_free_meta_head; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, fmh_cell in Ha. cbn [mc_loc mc_w loc_addr fst snd] in Ha. rewrite Hctx in Ha. unfold CTX_free_meta_head in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 P3 Hsp2 HK1 Ha; lia). reflexivity.
    + unfold m3, am_ep_mem. replace (af + 0) with (loc_addr L (mc_loc (prev_cell fm None))) by (cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; reflexivity).
      apply holds_wb; [intros z E; discriminate | cbn [mc_w prev_cell]; lia | cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; clear - P1; lia
                      | cbn [mc_loc mc_w prev_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
    + apply (cell_holds_frame L (bview SEGS (wbytes m2 (wa (af + 8)) (word_to_le_bytes 8 (wa 0)))) (bview SEGS m3)); [cbn [mc_w next_cell]; lia | |].
      * replace (af + 8) with (loc_addr L (mc_loc (next_cell fm None))) by (cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w next_cell]; lia | cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; clear - P1; lia
                        | cbn [mc_loc mc_w next_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, next_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_next in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_8 by (clear - P1 P2 Hsp2 HK1 Ha; lia). reflexivity.
  - exact MG.
  - intros x Hx Hne'.
    assert (CASES : (sp0 - K <= x < sp0) \/ (621736 <= x < 621744) \/ (af <= x < af + 8) \/ (af + 8 <= x < af + 16)).
    { destruct (range_dec x (sp0 - 56) 56) as [XA|XA]; [left; clear - XA HK1; lia|].
      destruct (range_dec x 621736 8) as [XB|XB]; [right; left; lia|].
      destruct (range_dec x af 16) as [XC|XC]; [destruct (Z_lt_ge_dec x (af + 8)); [right; right; left; lia | right; right; right; lia]|].
      exfalso. apply Hne'. apply MOUT3; [exact Hx | replace sp0 with (sp0 - 56 + 56) at 2 by ring; exact XA | exact XB | exact XC]. }
    destruct CASES as [A|[B|[B|B]]]; [left; exact A|right..].
    + exists (fmh_cell None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, fmh_cell. cbn [mc_loc mc_w loc_addr fst snd]. rewrite Hctx. unfold CTX_free_meta_head. clear - B. lia.
    + exists (prev_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, prev_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_prev. clear - B. lia.
    + exists (next_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, next_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_next. clear - B. lia.
Qed.


#[using="Type"] Lemma popn_mem_out : forall m nx pv x, 0 <= pv -> pv + 16 <= 2^64 -> 0 <= nx -> nx + 8 <= 2^64 -> 0 <= x < 2^64 ->
  ~ (621736 <= x < 621744) -> ~ (pv + 8 <= x < pv + 16) -> ~ (nx <= x < nx + 8) -> popn_mem m nx pv (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m nx pv x H1 H2 H3 H4 Hx A B C. unfold popn_mem. rewrite !MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Lemma popn_mem_pv : forall m nx pv x, 0 <= pv -> pv + 16 <= 2^64 -> 0 <= nx -> nx + 8 <= 2^64 -> 0 <= x < 2^64 ->
  ~ (621736 <= x < 621744) -> pv + 8 <= x < pv + 16 -> ~ (nx <= x < nx + 8) ->
  popn_mem m nx pv (wa x) = wbytes m (wa (pv + 8)) (word_to_le_bytes 8 (wa nx)) (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m nx pv x H1 H2 H3 H4 Hx A B C. unfold popn_mem. rewrite !MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Lemma popn_mem_nx : forall m nx pv x, 0 <= nx -> nx + 8 <= 2^64 -> 0 <= x < 2^64 -> ~ (621736 <= x < 621744) -> nx <= x < nx + 8 ->
  popn_mem m nx pv (wa x) = wbytes (wbytes m (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv)) (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m nx pv x H1 H2 Hx A B. unfold popn_mem. rewrite MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Theorem am_popn : forall HTOP X R U L s m regs rom sp0 K ra fm p n pp np pn nn,
  CUT HTOP X R U L s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree (Some p) (Some n)) -> n <> fm -> p <> fm -> p <> n ->
  MT s p = Some (MFree pp np) -> MT s n = Some (MFree pn nn) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R' m', msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R' (wa ra) m' rom) /\
    getr R' 10 = wa (loc_addr L (LMem fm)) /\
    (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (fm :: X) R U L (s_popn s fm p n pp nn) m' sp0 K /\ GROW sp0 K L s m L (s_popn s fm p n pp nn) m' /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m regs rom sp0 K ra fm p n pp np pn nn C R2 R1 Hra Hi Hf Hm Hnf Hpf Hpn Hp Hn Mpg.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Hk : In fm (keys s)) by (eapply MT_keys; exact Hm).
  assert (Hkp : In p (keys s)) by (eapply MT_keys; exact Hp). assert (Hkn : In n (keys s)) by (eapply MT_keys; exact Hn).
  destruct (nc_key_place L s m sp0 K fm N Hk) as (P1 & P2 & P3 & P4).
  destruct (nc_key_place L s m sp0 K p N Hkp) as (Q1 & Q2 & Q3 & Q4).
  destruct (nc_key_place L s m sp0 K n N Hkn) as (S1 & S2 & S3 & S4).
  pose proof (HMD p fm Hkp Hk Hpf) as D1'. pose proof (HMD n fm Hkn Hk Hnf) as D2'. pose proof (HMD p n Hkp Hkn Hpn) as D3'.
  set (af := loc_addr L (LMem fm)) in *. set (an := loc_addr L (LMem n)) in *. set (ap := loc_addr L (LMem p)) in *.
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (R1' & can & Hms1 & F1 & K1 & MOUT1 & GR1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (N1 : NC L [] [] s m1 sp0 K) by (apply (NC_stackw L s m m1 sp0 K N GR1); intros x Hx Hn'; apply MOUT1; [exact Hx | lia]).
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (first [lia | (intros x Hx; cbn in Hx; apply MOUT1; lia)]). exact Mpg. }
  (* [comment removed for export] *)
  destruct (seg_amfn L s m1 R1' rom sp0 K can _ _ _ _ _ _ fm p n F1 N1 Hi Hf Hm Hnf Hpf Hkp Hkn Mpg1) as (R2' & Hms2 & B10 & F2 & K2).
  fold an ap af in Hms2, B10, F2.
  set (m2 := popn_mem m1 an ap) in *.
  assert (G2' : mem_grows m1 m2) by (unfold m2, popn_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _)))).
  (* [comment removed for export] *)
  assert (W16 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m2 (wa (af + 0 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m m2); [exact (mem_grows_trans _ _ _ GR1 G2')|].
    replace (af + 0 + d) with (af + d) by ring. exact (rx_msc_wr L s m [] HR HEO HK fm _ Hm d k Hd ltac:(lia)). }
  assert (Era : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; lia).
  assert (Hra' : bv_unsigned (getr regs 1) = 0x542a0 \/ bv_unsigned (getr regs 1) = 0x53ec4) by (rewrite Era; exact Hra).
  assert (D1 : af + 16 <= sp0 - 56 \/ sp0 <= af) by (clear - P2 HK1; lia).
  assert (D2 : af + 16 <= 621568 \/ 621576 <= af) by (clear - P3; lia).
  destruct (seg_ame R2' m2 rom sp0 can _ _ _ _ _ _ af F2 B10 ltac:(clear - P1 P2 Hsp2 HK1; lia) P4 W16 D1 D2 Hra')
    as (R3 & Hms3 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K3).
  set (m3 := am_ep_mem m2 af) in *.
  assert (GR3 : mem_grows m2 m3) by (unfold m3, am_ep_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))).
  rewrite Era in Hms3. exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|]. split; [exact C10|].
  split; [exact (am_regs regs R1' R2' R3 sp0 R2 K1 K2 K3 C1 C2 C8 C9 C18 C19 C20)|].
  (* [comment removed for export] *)
  destruct (pop_facts X R U s fm (s_popn s fm p n pp nn) HI (deqh_popn s fm p n pp np pn nn Hf Hm Hnf Hpf Hpn Hp Hn)) as (HI2 & NX & MT2 & EU2 & UB2 & EA2).
  destruct (free_ring_nbrs X R U s fm (Some p) (Some n) HI Hf Hm) as (_ & NB).
  destruct (NB p (or_introl eq_refl)) as (NXp & _). destruct (NB n (or_intror eq_refl)) as (NXn & _).
  assert (HX2 : XNM (fm :: X) (s_popn s fm p n pp nn)).
  { intros x [<-|Hx]; [right; exact MT2|].
    assert (Hxk : x <> fm) by (intros ->; rewrite (memb_of_In fm X Hx) in NX; discriminate).
    assert (Hxp : x <> p) by (intros ->; rewrite (memb_of_In p X Hx) in NXp; discriminate).
    assert (Hxn : x <> n) by (intros ->; rewrite (memb_of_In n X Hx) in NXn; discriminate).
    unfold s_popn. rewrite MT_upd_other by exact Hxk. rewrite MT_fmh. rewrite !MT_upd_other by assumption. exact (HX x Hx). }
  set (Cnew := [fmh_cell (Some n); next_cell p (Some n); prev_cell n (Some p); prev_cell fm None; next_cell fm None]).
  set (s1 := upd_meta p (MFree pp (Some n)) s). set (s2 := upd_meta n (MFree (Some p) nn) s1).
  set (s3 := set_free_meta_head (Some n) s2).
  assert (HKs1 : KS s1) by (apply KS_set_meta; assumption).
  assert (Ek1 : keys s1 = keys s) by exact (keys_set_meta s p _ Hkp).
  assert (HKs2 : KS s2) by (apply KS_set_meta; [exact HKs1 | rewrite Ek1; exact Hkn]).
  assert (HKs3 : KS s3) by exact HKs2.
  assert (Mn1 : MT s1 n = Some (MFree pn nn)) by (unfold s1; rewrite MT_upd_other by exact (not_eq_sym Hpn); exact Hn).
  assert (Mfm3 : MT s3 fm = Some (MFree (Some p) (Some n))).
  { unfold s3, s2, s1. rewrite MT_fmh. rewrite !MT_upd_other by first [exact (not_eq_sym Hnf) | exact (not_eq_sym Hpf)]. exact Hm. }
  assert (HK4 : KS (s_popn s fm p n pp nn)) by exact (KS_of_Inv _ _ _ _ HI2).
  assert (M4p : MT (s_popn s fm p n pp nn) p = Some (MFree pp (Some n))).
  { unfold s_popn. rewrite MT_upd_other by exact Hpf. rewrite MT_fmh. rewrite MT_upd_other by exact Hpn. apply MT_upd_same. }
  assert (M4n : MT (s_popn s fm p n pp nn) n = Some (MFree (Some p) nn)).
  { unfold s_popn. rewrite MT_upd_other by exact Hnf. rewrite MT_fmh. apply MT_upd_same. }
  assert (Rap : 0 <= ap /\ ap + 16 <= 2^64) by (clear - Q1 Q2 Hsp2 HK1; lia). assert (Ran : 0 <= an /\ an + 8 <= 2^64) by (clear - S1 S2 Hsp2 HK1; lia).
  assert (MOUT3 : forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> ~ (621736 <= x < 621744) -> ~ (ap + 8 <= x < ap + 16) -> ~ (an <= x < an + 8) ->
                     ~ (af <= x < af + 16) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3 H4 H5. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 Hsp2 HK1 Hx H5; lia). unfold m2.
    rewrite popn_mem_out by (first [exact H2 | exact H3 | exact H4 | lia]). apply MOUT1; assumption. }
  assert (MG : mem_grows m m3) by exact (mem_grows_trans _ _ _ GR1 (mem_grows_trans _ _ _ G2' GR3)).
  cut (CUT HTOP (fm :: X) R U L (s_popn s fm p n pp nn) m3 sp0 K /\ GROW sp0 K L s m L (s_popn s fm p n pp nn) m3);
    [intros (CC & GG); split; [exact CC | split; [exact GG | exact MG]]|].
  apply (silent_step HTOP X R U (fm :: X) R U L s (s_popn s fm p n pp nn) m m3 sp0 K Cnew C HI2 HX2 eq_refl).
  - intros fpr Hfpr. left. exact Hfpr.
  - intros c Hcn. destruct (cov_upd_free s3 fm (Some p) (Some n) None None HKs3 Mfm3 c Hcn) as [H|[H|H]]; [|right; subst c; cbn [In]; memb | right; subst c; cbn [In]; memb].
    destruct (cov_fmh_image s2 (Some n) c H) as [H2|H2]; [|right; subst c; cbn [In]; memb].
    destruct (cov_upd_free s1 n pn nn (Some p) nn HKs1 Mn1 c H2) as [H3|[H3|H3]]; [| right; subst c; cbn [In]; memb |].
    + destruct (cov_upd_free s p pp np pp (Some n) HK Hp c H3) as [H4|[H4|H4]]; [left; exact H4 | | right; subst c; cbn [In]; memb].
      left. subst c. apply (msc_key_in_image s p _ _ HK Hp). cbn [meta_slot_cells In]. memb.
    + left. subst c. apply (msc_key_in_image s n _ _ HK Hn). cbn [meta_slot_cells In]. memb.
  - intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + exact (fmh_cell_in (s_popn s fm p n pp nn)).
    + apply (msc_key_in_image _ p _ _ HK4 M4p). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ n _ _ HK4 M4n). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ fm _ _ HK4 MT2). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ fm _ _ HK4 MT2). cbn [meta_slot_cells In]. memb.
  - intros c Hcn.
    destruct (rev_upd_free s p pp np pp (Some n) HK Hp c Hcn) as [H|[H|H]].
    2: { left. subst c. apply (msc_key_in_image _ p _ _ HK4 M4p). cbn [meta_slot_cells In]. memb. }
    2: { right. exists (next_cell p (Some n)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    destruct (rev_upd_free s1 n pn nn (Some p) nn HKs1 Mn1 c H) as [H2|[H2|H2]].
    2: { right. exists (prev_cell n (Some p)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    2: { left. subst c. apply (msc_key_in_image _ n _ _ HK4 M4n). cbn [meta_slot_cells In]. memb. }
    destruct (rev_fmh_image s2 (Some n) c H2) as [H3|H3].
    2: { right. exists (fmh_cell (Some n)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    destruct (rev_upd_free s3 fm (Some p) (Some n) None None HKs3 Mfm3 c H3) as [H4|[H4|H4]]; [left; exact H4 | |].
    + right. exists (prev_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
    + right. exists (next_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
  - apply Forall_forall. intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m3)); [cbn [mc_w fmh_cell]; lia | |].
      * unfold m2, popn_mem. replace (0 + 621736) with (loc_addr L (mc_loc (fmh_cell (Some n)))) by (cbn; rewrite Hctx; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w fmh_cell]; lia | cbn [mc_loc fmh_cell loc_addr]; rewrite Hctx; unfold CTX_free_meta_head; lia
                        | cbn [mc_loc mc_w fmh_cell loc_addr Z.of_nat Pos.of_succ_nat]; rewrite Hctx; unfold CTX_free_meta_head; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, fmh_cell in Ha. cbn [mc_loc mc_w loc_addr fst snd] in Ha. rewrite Hctx in Ha. unfold CTX_free_meta_head in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 P3 Hsp2 HK1 Ha; lia). reflexivity.
    + apply (cell_holds_frame L (bview SEGS (wbytes m1 (wa (ap + 8)) (word_to_le_bytes 8 (wa an)))) (bview SEGS m3)); [cbn [mc_w next_cell]; lia | |].
      * replace (ap + 8) with (loc_addr L (mc_loc (next_cell p (Some n)))) by (cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w next_cell]; lia | cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; clear - Q1; lia
                        | cbn [mc_loc mc_w next_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; clear - Q1 Q2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, next_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_next in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 Q1 Q2 Hsp2 HK1 Ha D1'; lia). unfold m2.
        rewrite popn_mem_pv by (first [(clear - Ha; lia) | (clear - Ha D3'; lia) | (clear - Ha D3' P1 P2 Q1 Q2 S1 S2 Hsp2 HK1; lia) | lia]). reflexivity.
    + apply (cell_holds_frame L (bview SEGS (wbytes (wbytes m1 (wa (ap + 8)) (word_to_le_bytes 8 (wa an))) (wa (an + 0)) (word_to_le_bytes 8 (wa ap)))) (bview SEGS m3)); [cbn [mc_w prev_cell]; lia | |].
      * replace (an + 0) with (loc_addr L (mc_loc (prev_cell n (Some p)))) by (cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w prev_cell]; lia | cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; clear - S1; lia
                        | cbn [mc_loc mc_w prev_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; clear - S1 S2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, prev_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_prev in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 S1 S2 Hsp2 HK1 Ha D2'; lia). unfold m2.
        rewrite popn_mem_nx by (first [(clear - Ha; lia) | (clear - Ha P1 P2 Q1 Q2 S1 S2 Hsp2 HK1; lia) | lia]). reflexivity.
    + unfold m3, am_ep_mem. replace (af + 0) with (loc_addr L (mc_loc (prev_cell fm None))) by (cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; reflexivity).
      apply holds_wb; [intros z E; discriminate | cbn [mc_w prev_cell]; lia | cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; clear - P1; lia
                      | cbn [mc_loc mc_w prev_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
    + apply (cell_holds_frame L (bview SEGS (wbytes m2 (wa (af + 8)) (word_to_le_bytes 8 (wa 0)))) (bview SEGS m3)); [cbn [mc_w next_cell]; lia | |].
      * replace (af + 8) with (loc_addr L (mc_loc (next_cell fm None))) by (cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w next_cell]; lia | cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; clear - P1; lia
                        | cbn [mc_loc mc_w next_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, next_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_next in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_8 by (clear - P1 P2 Hsp2 HK1 Ha; lia). reflexivity.
  - exact MG.
  - intros x Hx Hne'.
    assert (CASES : (sp0 - K <= x < sp0) \/ (621736 <= x < 621744) \/ (ap + 8 <= x < ap + 16) \/ (an <= x < an + 8) \/ (af <= x < af + 8) \/ (af + 8 <= x < af + 16)).
    { destruct (range_dec x (sp0 - 56) 56) as [XA|XA]; [left; clear - XA HK1; lia|].
      destruct (range_dec x 621736 8) as [XB|XB]; [right; left; lia|].
      destruct (range_dec x (ap + 8) 8) as [XP|XP]; [right; right; left; lia|].
      destruct (range_dec x an 8) as [XN|XN]; [right; right; right; left; lia|].
      destruct (range_dec x af 16) as [XC|XC]; [destruct (Z_lt_ge_dec x (af + 8)); [right; right; right; right; left; lia | right; right; right; right; right; lia]|].
      exfalso. apply Hne'. apply MOUT3; [exact Hx | replace sp0 with (sp0 - 56 + 56) at 2 by ring; exact XA | exact XB
                                        | replace (ap + 16) with (ap + 8 + 8) by ring; exact XP | exact XN | exact XC]. }
    destruct CASES as [A|[B|[B|[B|[B|B]]]]]; [left; exact A|right..].
    + exists (fmh_cell (Some n)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, fmh_cell. cbn [mc_loc mc_w loc_addr fst snd]. rewrite Hctx. unfold CTX_free_meta_head. clear - B. lia.
    + exists (next_cell p (Some n)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, next_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_next. clear - B. lia.
    + exists (prev_cell n (Some p)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, prev_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_prev. clear - B. lia.
    + exists (prev_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, prev_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_prev. clear - B. lia.
    + exists (next_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, next_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_next. clear - B. lia.
Qed.

#[using="Type"] Theorem am_pop2 : forall HTOP X R U L s m regs rom sp0 K ra fm xm px nxx,
  CUT HTOP X R U L s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  st_init_done s = true -> st_free_meta_head s = Some fm -> MT s fm = Some (MFree (Some xm) (Some xm)) -> xm <> fm ->
  MT s xm = Some (MFree px nxx) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R' m', msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R' (wa ra) m' rom) /\
    getr R' 10 = wa (loc_addr L (LMem fm)) /\
    (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (fm :: X) R U L (s_pop2 s fm xm) m' sp0 K /\ GROW sp0 K L s m L (s_pop2 s fm xm) m' /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m regs rom sp0 K ra fm xm px nxx C R2 R1 Hra Hi Hf Hm Hnf Hn Mpg.
  set (p := xm) in *. set (n := xm) in *. assert (Hpf : p <> fm) by exact Hnf. assert (Hp : MT s p = Some (MFree px nxx)) by exact Hn.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Hk : In fm (keys s)) by (eapply MT_keys; exact Hm).
  assert (Hkp : In p (keys s)) by (eapply MT_keys; exact Hp). assert (Hkn : In n (keys s)) by (eapply MT_keys; exact Hn).
  destruct (nc_key_place L s m sp0 K fm N Hk) as (P1 & P2 & P3 & P4).
  destruct (nc_key_place L s m sp0 K p N Hkp) as (Q1 & Q2 & Q3 & Q4).
  destruct (nc_key_place L s m sp0 K n N Hkn) as (S1 & S2 & S3 & S4).
  pose proof (HMD p fm Hkp Hk Hpf) as D1'. pose proof (HMD n fm Hkn Hk Hnf) as D2'.
  set (af := loc_addr L (LMem fm)) in *. set (an := loc_addr L (LMem n)) in *. set (ap := loc_addr L (LMem p)) in *.
  assert (Ean : an = ap) by reflexivity.
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (R1' & can & Hms1 & F1 & K1 & MOUT1 & GR1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (N1 : NC L [] [] s m1 sp0 K) by (apply (NC_stackw L s m m1 sp0 K N GR1); intros x Hx Hn'; apply MOUT1; [exact Hx | lia]).
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (first [lia | (intros x Hx; cbn in Hx; apply MOUT1; lia)]). exact Mpg. }
  (* [comment removed for export] *)
  destruct (seg_amfn L s m1 R1' rom sp0 K can _ _ _ _ _ _ fm p n F1 N1 Hi Hf Hm Hnf Hpf Hkp Hkn Mpg1) as (R2' & Hms2 & B10 & F2 & K2).
  fold an ap af in Hms2, B10, F2.
  set (m2 := popn_mem m1 an ap) in *.
  assert (G2' : mem_grows m1 m2) by (unfold m2, popn_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _)))).
  (* [comment removed for export] *)
  assert (W16 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m2 (wa (af + 0 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m m2); [exact (mem_grows_trans _ _ _ GR1 G2')|].
    replace (af + 0 + d) with (af + d) by ring. exact (rx_msc_wr L s m [] HR HEO HK fm _ Hm d k Hd ltac:(lia)). }
  assert (Era : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; lia).
  assert (Hra' : bv_unsigned (getr regs 1) = 0x542a0 \/ bv_unsigned (getr regs 1) = 0x53ec4) by (rewrite Era; exact Hra).
  assert (D1 : af + 16 <= sp0 - 56 \/ sp0 <= af) by (clear - P2 HK1; lia).
  assert (D2 : af + 16 <= 621568 \/ 621576 <= af) by (clear - P3; lia).
  destruct (seg_ame R2' m2 rom sp0 can _ _ _ _ _ _ af F2 B10 ltac:(clear - P1 P2 Hsp2 HK1; lia) P4 W16 D1 D2 Hra')
    as (R3 & Hms3 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K3).
  set (m3 := am_ep_mem m2 af) in *.
  assert (GR3 : mem_grows m2 m3) by (unfold m3, am_ep_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))).
  rewrite Era in Hms3. exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|]. split; [exact C10|].
  split; [exact (am_regs regs R1' R2' R3 sp0 R2 K1 K2 K3 C1 C2 C8 C9 C18 C19 C20)|].
  (* [comment removed for export] *)
  destruct (pop_facts X R U s fm (s_pop2 s fm xm) HI (deqh_pop2 s fm xm px nxx Hf Hm Hnf Hn)) as (HI2 & NX & MT2 & EU2 & UB2 & EA2).
  destruct (free_ring_nbrs X R U s fm (Some p) (Some n) HI Hf Hm) as (_ & NB).
  destruct (NB p (or_introl eq_refl)) as (NXp & _). destruct (NB n (or_intror eq_refl)) as (NXn & _).
  assert (HX2 : XNM (fm :: X) (s_pop2 s fm xm)).
  { intros x0 [<-|Hx]; [right; exact MT2|].
    assert (Hxk : x0 <> fm) by (intros ->; rewrite (memb_of_In fm X Hx) in NX; discriminate).
    assert (Hxn : x0 <> n) by (intros ->; rewrite (memb_of_In n X Hx) in NXn; discriminate).
    unfold s_pop2. rewrite MT_upd_other by exact Hxk. rewrite MT_fmh. rewrite !MT_upd_other by assumption. exact (HX x0 Hx). }
  set (Cnew := [fmh_cell (Some n); next_cell p (Some n); prev_cell n (Some p); prev_cell fm None; next_cell fm None]).
  set (s1 := upd_meta xm (MFree (Some xm) (Some xm)) s).
  set (s3 := set_free_meta_head (Some xm) s1).
  assert (HKs1 : KS s1) by (apply KS_set_meta; assumption).
  assert (HKs3 : KS s3) by exact HKs1.
  assert (Mfm3 : MT s3 fm = Some (MFree (Some p) (Some n))).
  { unfold s3, s1. rewrite MT_fmh. rewrite !MT_upd_other by first [exact (not_eq_sym Hnf) | exact (not_eq_sym Hpf)]. exact Hm. }
  assert (HK4 : KS (s_pop2 s fm xm)) by exact (KS_of_Inv _ _ _ _ HI2).
  assert (M4n : MT (s_pop2 s fm xm) n = Some (MFree (Some p) (Some n))).
  { unfold s_pop2. rewrite MT_upd_other by exact Hnf. rewrite MT_fmh. apply MT_upd_same. }
  assert (M4p : MT (s_pop2 s fm xm) p = Some (MFree (Some p) (Some n))) by exact M4n.
  assert (Rap : 0 <= ap /\ ap + 16 <= 2^64) by (clear - Q1 Q2 Hsp2 HK1; lia). assert (Ran : 0 <= an /\ an + 8 <= 2^64) by (clear - S1 S2 Hsp2 HK1; lia).
  assert (MOUT3 : forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> ~ (621736 <= x < 621744) -> ~ (ap + 8 <= x < ap + 16) -> ~ (an <= x < an + 8) ->
                     ~ (af <= x < af + 16) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3 H4 H5. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 Hsp2 HK1 Hx H5; lia). unfold m2.
    rewrite popn_mem_out by (first [exact H2 | exact H3 | exact H4 | lia]). apply MOUT1; assumption. }
  assert (MG : mem_grows m m3) by exact (mem_grows_trans _ _ _ GR1 (mem_grows_trans _ _ _ G2' GR3)).
  cut (CUT HTOP (fm :: X) R U L (s_pop2 s fm xm) m3 sp0 K /\ GROW sp0 K L s m L (s_pop2 s fm xm) m3);
    [intros (CC & GG); split; [exact CC | split; [exact GG | exact MG]]|].
  apply (silent_step HTOP X R U (fm :: X) R U L s (s_pop2 s fm xm) m m3 sp0 K Cnew C HI2 HX2 eq_refl).
  - intros fpr Hfpr. left. exact Hfpr.
  - intros c Hcn. destruct (cov_upd_free s3 fm (Some p) (Some n) None None HKs3 Mfm3 c Hcn) as [H|[H|H]]; [|right; subst c; cbn [In]; memb | right; subst c; cbn [In]; memb].
    destruct (cov_fmh_image s1 (Some n) c H) as [H2|H2]; [|right; subst c; cbn [In]; memb].
    destruct (cov_upd_free s xm px nxx (Some xm) (Some xm) HK Hn c H2) as [H3|[H3|H3]]; [left; exact H3 | right; subst c; cbn [In]; memb | right; subst c; cbn [In]; memb].
  - intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + exact (fmh_cell_in (s_pop2 s fm xm)).
    + apply (msc_key_in_image _ p _ _ HK4 M4p). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ n _ _ HK4 M4n). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ fm _ _ HK4 MT2). cbn [meta_slot_cells In]. memb.
    + apply (msc_key_in_image _ fm _ _ HK4 MT2). cbn [meta_slot_cells In]. memb.
  - intros c Hcn.
    destruct (rev_upd_free s xm px nxx (Some xm) (Some xm) HK Hn c Hcn) as [H|[H|H]].
    2: { right. exists (prev_cell n (Some p)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    2: { right. exists (next_cell p (Some n)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    destruct (rev_fmh_image s1 (Some n) c H) as [H3|H3].
    2: { right. exists (fmh_cell (Some n)). split; [cbn [In]; memb|]. subst c. reflexivity. }
    destruct (rev_upd_free s3 fm (Some p) (Some n) None None HKs3 Mfm3 c H3) as [H4|[H4|H4]]; [left; exact H4 | |].
    + right. exists (prev_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
    + right. exists (next_cell fm None). split; [cbn [In]; memb|]. subst c. reflexivity.
  - apply Forall_forall. intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m3)); [cbn [mc_w fmh_cell]; lia | |].
      * unfold m2, popn_mem. replace (0 + 621736) with (loc_addr L (mc_loc (fmh_cell (Some n)))) by (cbn; rewrite Hctx; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w fmh_cell]; lia | cbn [mc_loc fmh_cell loc_addr]; rewrite Hctx; unfold CTX_free_meta_head; lia
                        | cbn [mc_loc mc_w fmh_cell loc_addr Z.of_nat Pos.of_succ_nat]; rewrite Hctx; unfold CTX_free_meta_head; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, fmh_cell in Ha. cbn [mc_loc mc_w loc_addr fst snd] in Ha. rewrite Hctx in Ha. unfold CTX_free_meta_head in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 P3 Hsp2 HK1 Ha; lia). reflexivity.
    + apply (cell_holds_frame L (bview SEGS (wbytes m1 (wa (ap + 8)) (word_to_le_bytes 8 (wa an)))) (bview SEGS m3)); [cbn [mc_w next_cell]; lia | |].
      * replace (ap + 8) with (loc_addr L (mc_loc (next_cell p (Some n)))) by (cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w next_cell]; lia | cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; clear - Q1; lia
                        | cbn [mc_loc mc_w next_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; clear - Q1 Q2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, next_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_next in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 Q1 Q2 Hsp2 HK1 Ha D1'; lia). unfold m2.
        rewrite popn_mem_pv by (first [(clear - Ha; lia) | (clear - Ha Ean; lia) | (clear - Ha Ean P1 P2 Q1 Q2 S1 S2 Hsp2 HK1; lia) | lia]). reflexivity.
    + apply (cell_holds_frame L (bview SEGS (wbytes (wbytes m1 (wa (ap + 8)) (word_to_le_bytes 8 (wa an))) (wa (an + 0)) (word_to_le_bytes 8 (wa ap)))) (bview SEGS m3)); [cbn [mc_w prev_cell]; lia | |].
      * replace (an + 0) with (loc_addr L (mc_loc (prev_cell n (Some p)))) by (cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w prev_cell]; lia | cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; clear - S1; lia
                        | cbn [mc_loc mc_w prev_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; clear - S1 S2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, prev_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_prev in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_out by (clear - P1 P2 S1 S2 Hsp2 HK1 Ha D2'; lia). unfold m2.
        rewrite popn_mem_nx by (first [(clear - Ha; lia) | (clear - Ha P1 P2 Q1 Q2 S1 S2 Hsp2 HK1; lia) | lia]). reflexivity.
    + unfold m3, am_ep_mem. replace (af + 0) with (loc_addr L (mc_loc (prev_cell fm None))) by (cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; reflexivity).
      apply holds_wb; [intros z E; discriminate | cbn [mc_w prev_cell]; lia | cbn [mc_loc prev_cell]; rewrite loc_padd; unfold META_prev; clear - P1; lia
                      | cbn [mc_loc mc_w prev_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
    + apply (cell_holds_frame L (bview SEGS (wbytes m2 (wa (af + 8)) (word_to_le_bytes 8 (wa 0)))) (bview SEGS m3)); [cbn [mc_w next_cell]; lia | |].
      * replace (af + 8) with (loc_addr L (mc_loc (next_cell fm None))) by (cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w next_cell]; lia | cbn [mc_loc next_cell]; rewrite loc_padd; unfold META_next; clear - P1; lia
                        | cbn [mc_loc mc_w next_cell Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; clear - P1 P2 Hsp2 HK1; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range, next_cell in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite loc_padd in Ha. unfold META_next in Ha.
        apply MngWb.bview_ext. unfold m3. rewrite am_ep_mem_8 by (clear - P1 P2 Hsp2 HK1 Ha; lia). reflexivity.
  - exact MG.
  - intros x Hx Hne'.
    assert (CASES : (sp0 - K <= x < sp0) \/ (621736 <= x < 621744) \/ (ap + 8 <= x < ap + 16) \/ (an <= x < an + 8) \/ (af <= x < af + 8) \/ (af + 8 <= x < af + 16)).
    { destruct (range_dec x (sp0 - 56) 56) as [XA|XA]; [left; clear - XA HK1; lia|].
      destruct (range_dec x 621736 8) as [XB|XB]; [right; left; lia|].
      destruct (range_dec x (ap + 8) 8) as [XP|XP]; [right; right; left; lia|].
      destruct (range_dec x an 8) as [XN|XN]; [right; right; right; left; lia|].
      destruct (range_dec x af 16) as [XC|XC]; [destruct (Z_lt_ge_dec x (af + 8)); [right; right; right; right; left; lia | right; right; right; right; right; lia]|].
      exfalso. apply Hne'. apply MOUT3; [exact Hx | replace sp0 with (sp0 - 56 + 56) at 2 by ring; exact XA | exact XB
                                        | replace (ap + 16) with (ap + 8 + 8) by ring; exact XP | exact XN | exact XC]. }
    destruct CASES as [A|[B|[B|[B|[B|B]]]]]; [left; exact A|right..].
    + exists (fmh_cell (Some n)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, fmh_cell. cbn [mc_loc mc_w loc_addr fst snd]. rewrite Hctx. unfold CTX_free_meta_head. clear - B. lia.
    + exists (next_cell p (Some n)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, next_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_next. clear - B. lia.
    + exists (prev_cell n (Some p)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, prev_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_prev. clear - B. lia.
    + exists (prev_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, prev_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_prev. clear - B. lia.
    + exists (next_cell fm None). split; [cbn [In]; memb|]. unfold in_rng, cell_range, next_cell. cbn [mc_loc mc_w fst snd]. rewrite loc_padd. unfold META_next. clear - B. lia.
Qed.
End AM2.
