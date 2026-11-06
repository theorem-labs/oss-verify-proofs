(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngCtx MngCtx2 MngShape MngMK AXG_as1 AXG_as5 AXG_am8 AXG_ag0 AXG_ag1 AXG_ag4 AXG_asq AXG_ag16.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMK OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag4 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asq OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma wk_ibind_inv : forall {fx : FPState} segs FORB HTOP rom {A B : Type} (t : itree astate A) (k : A -> itree astate B) L regs pc m
    (Q : @wpost B),
  wk segs FORB HTOP rom L regs pc m (ibind t k) Q ->
  wk (R := A) segs FORB HTOP rom L regs pc m t (fun L' a regs' pc' m' => wk segs FORB HTOP rom L' regs' pc' m' (k a) Q).
Proof.
  intros fx segs FORB HTOP rom A B t k. induction t as [r | q s kt IH | f]; intros L regs pc m Q H; cbn in *.
  - exists regs, pc, m. split; [apply mst_refl | exact H].
  - destruct q;
      try (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1; split; [exact Hm|]; split; [exact He|];
           intros eff ans L' Ho; apply IH; apply Hk; exact Ho).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. apply IH. exact Hr.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma AMI_mono : forall L m sp sp', sp' <= sp -> AMI L m sp -> AMI L m sp'.
Proof. intros L m sp sp' H (AUXV & RND & typs & E & A & B). exists AUXV, RND, typs. split; [exact E|]. lia. Qed.

Lemma AMI_GROW : forall HTOP X R U L s m L' s' m' sp0 K, CUT HTOP X R U L' s' m' sp0 K -> GROW sp0 K L s m L' s' m' ->
  AMI L m sp0 -> AMI L' m' sp0.
Proof.
  intros HTOP X R U L s m L' s' m' sp0 K C G (AUXV & RND & typs & E & A & B).
  pose proof G as (HE & _ & _ & SI & _).
  assert (ABOVE : forall x, sp0 <= x < 2^64 -> m' (wa x) = m (wa x)) by exact (GROWX_above (fun _ => False) HTOP X R U L s m L' s' m' sp0 K (GROWX_of_GROW _ _ _ _ _ _ _ _ _ G) C).
  destruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  exists AUXV, RND, typs. split; [|exact (conj A B)].
  assert (RD : forall x n, sp0 <= x -> x + Z.of_nat n <= 2^64 -> rdn SEGS m' (wa x) n = rdn SEGS m (wa x) n).
  { intros x n H1 H2. apply rdn_frame_n; [pose proof (nc_sp1 _ _ _ _ _ _ _ (ct_nc _ _ _ _ _ _ _ _ _ C)); pose proof (nc_K _ _ _ _ _ _ _ (ct_nc _ _ _ _ _ _ _ _ _ C)); lia | exact H2|].
    intros y Hy. apply ABOVE. lia. }
  split; [rewrite (rdn_frame_n m m' 613992 8) by (first [lia | (intros y Hy; apply SI; lia)]); exact E1|].
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split; [intros i Hi; destruct (E5 i Hi) as (T1 & T2 & T3); split; [exact T1|]; split;
          [rewrite RD by lia; exact T2 | intros H25; rewrite RD by lia; exact (T3 H25)]|].
  split; [rewrite RD by lia; exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
  rewrite RD by lia. rewrite (proj1 (proj2 (proj2 HE))). exact E11.
Qed.

(* [comment removed for export] *)
Section AMINIT.
Local Open Scope mm_scope.
#[using="Type"] Lemma alloc_meta_init : forall X R U s, Inv X R U s -> itok (alloc_meta s) (fun r => st_init_done (snd r) = true).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X R U s HI.
  unfold alloc_meta. mbinds. apply itok_modify. msimp.
  set (s0 := set_init_done true s).
  assert (HI0 : Inv X R U s0) by (apply Inv_set_init_done; exact HI).
  mbinds. eapply dequeue_head_free_spec; [exact HI0 | |].
  - intros Hfh Hnofree. msimp. mbinds. apply itok_get. msimp.
    assert (TAKE : forall s1, Inv X R U s1 -> st_init_done s1 = true -> 0 < st_avail_meta_count s1 ->
              itok ((s2 <- get ;;
                     put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
                     setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s1) (fun r => st_init_done (snd r) = true)).
    { intros s1 HI1 Hi1 Hc1. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_setslot'. msimp. apply itok_ret.
      cbn. exact Hi1. }
    destruct (0 <? st_avail_meta_count s0) eqn:Ec.
    + apply Z.ltb_lt in Ec. mbinds. apply itok_ret. msimp. cbn [negb]. apply TAKE; [exact HI0 | reflexivity | exact Ec].
    + apply Z.ltb_ge in Ec. pose proof (inv_keys HI0) as (_ & _ & _ & _ & Krange).
      assert (Hm0 : st_avail_meta_count s0 = 0) by lia.
      apply itok_bind. eapply new_area_spec; [exact HI0 | exact Hm0 | reflexivity |].
      intros ok s1 HI1 Fr1 Em1 Hi1 Hok. msimp. destruct ok; cbn [negb].
      * apply TAKE; [exact HI1 | exact Hi1 | apply Hok; reflexivity].
      * apply itok_ret. cbn. exact Hi1.
  - intros m s' HI' NX Mm Sb Ea EU UB. msimp. apply itok_ret. cbn. destruct Sb as (E1 & _). rewrite E1. reflexivity.
Qed.
End AMINIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma markers_incl : forall s s', (forall q a, In (q, a) (used_metas s') -> In (q, a) (used_metas s)) ->
  forall c, In c (markers s') -> In c (markers s).
Proof.
  intros s s' H c Hc. unfold markers in *. apply in_flat_map in Hc as [[q a] [Hq Hc]]. apply in_flat_map. exists (q, a). split; [exact (H q a Hq) | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma used_after_am : forall X R U s s' m, Inv X R U s -> XNU X s -> Inv (m :: X) R U s' -> XNU (m :: X) s' ->
  (forall g am, usedX (m :: X) s' g am <-> usedX X s g am) -> forall q a, In (q, a) (used_metas s') -> In (q, a) (used_metas s).
Proof.
  intros X R U s s' m HI HXU HI' HXU' EU q a Hq.
  apply (proj2 (used_metas_usedX_X X R U s q a HI HXU)). apply EU. exact (proj1 (used_metas_usedX_X (m :: X) R U s' q a HI' HXU') Hq).
Qed.

Lemma UGROW_same : forall s s' sc, st_usage s' = st_usage s -> UGROW s s' sc.
Proof. intros s s' sc E. split; intros c Hc; unfold usage_of, znth; rewrite E; lia. Qed.

Lemma UGROW_pre : forall s s2 s' sc, st_usage s2 = st_usage s -> UGROW s2 s' sc -> UGROW s s' sc.
Proof. intros s s2 s' sc E (A & B). split; intros c Hc; pose proof (A c) as A'; pose proof (B c) as B'; unfold usage_of, znth in *; rewrite E in *; auto. Qed.

(* [comment removed for export] *)
Lemma as_frame_regs : forall R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  (forall k, In k [2; 8; 18; 20; 21; 22; 23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  as_frame R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9.
Proof.
  intros R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F K. destruct F. constructor; try assumption.
  all: first [ (regk K 2%nat; assumption) | (regk K 8%nat; assumption) | (regk K 18%nat; assumption) | (regk K 20%nat; assumption)
             | (regk K 21%nat; assumption) | (regk K 22%nat; assumption) | (regk K 23%nat; assumption) ].
Qed.

(* [comment removed for export] *)
Lemma rdn_SI : forall m m' a n, SI m m' -> 0x10000 <= a -> a + Z.of_nat n <= 0x95ed8 -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof. intros m m' a n S H1 H2. apply rdn_frame_n; [lia | lia |]. intros y Hy. apply S; lia. Qed.

Lemma TABS_SI : forall m m', SI m m' -> TABS m -> TABS m'.
Proof.
  intros m m' S (T1 & T2). split.
  - intros sc k Hsc Hk. rewrite (rdn_SI m m') by (first [exact S | cbn [Z.of_nat Pos.of_succ_nat]; lia]). exact (T1 sc k Hsc Hk).
  - intros k Hk. rewrite (rdn_SI m m') by (first [exact S | cbn [Z.of_nat Pos.of_succ_nat]; lia]). exact (T2 k Hk).
Qed.

Lemma DBT_SI : forall m m', SI m m' -> DBT m -> DBT m'.
Proof. intros m m' S D j Hj. rewrite (rdn_SI m m') by (first [exact S | cbn [Z.of_nat Pos.of_succ_nat]; lia]). exact (D j Hj). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section S6.
Variables (mt : sptr) (s2 : astate) (sc req : Z).
Local Notation s6 := (ag_s6 mt s2 sc req).
Local Notation cnt := (fst (ag_plan s2 sc req)).
Local Notation am6 := (am_set_links (Some mt) (Some mt) (new_am (SP (length (st_regions s2)) 0) sc cnt (ag_aidx sc cnt)
                         (snd (ag_plan s2 sc req) / 4096) slot_zero)).

#[using="Type"] Lemma s6_lookup : forall q, q <> mt -> mlookup (st_metas s6) q = mlookup (st_metas s2) q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros q Hq. pose proof (s3_same s2 sc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em3 & _).
  unfold ag_s6, ins_st, ag_s5. cbn [st_metas set_active set_metas set_usage set_mmap_counter set_regions].
  rewrite !mlookup_mupdate_other by exact Hq. rewrite Em3. reflexivity.
Qed.

#[using="Type"] Lemma s6_lookup_mt : mlookup (st_metas s6) mt = Some (MUsed am6).
Proof. LiaFast.lf_pins LiaFast.u0.
  pose proof (s3_same s2 sc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Er3).
  unfold ag_s6, ins_st, ag_s5. cbn [st_metas set_active set_metas set_usage set_mmap_counter set_regions]. rewrite mlookup_mupdate_same. rewrite Er3. reflexivity.
Qed.

#[using="Type"] Lemma s6_keys : In mt (keys s2) -> keys s6 = keys s2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Hk. pose proof (s3_same s2 sc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em3 & _).
  unfold keys, ag_s6, ins_st, ag_s5. cbn [st_metas set_active set_metas set_usage set_mmap_counter set_regions].
  rewrite Em3. rewrite map_fst_mupdate_In; [apply map_fst_mupdate_In; exact Hk|]. rewrite map_fst_mupdate_In by exact Hk. exact Hk.
Qed.

#[using="Type"] Lemma s6_used : List.NoDup (keys s2) -> In mt (keys s2) -> forall q a, In (q, a) (used_metas s6) ->
  In (q, a) (used_metas s2) \/ (q = mt /\ a = am6).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ND Hk q a Hq. assert (ND6 : List.NoDup (keys s6)) by (rewrite s6_keys by exact Hk; exact ND).
  apply (used_metas_iff s6 q a ND6) in Hq. unfold MT in Hq.
  destruct (sptr_eq_dec q mt) as [->|Hne].
  - right. rewrite s6_lookup_mt in Hq. injection Hq as <-. split; reflexivity.
  - left. rewrite (s6_lookup q Hne) in Hq. apply (used_metas_iff s2 q a ND). exact Hq.
Qed.

#[using="Type"] Lemma s6_markers : List.NoDup (keys s2) -> In mt (keys s2) -> forall c, In c (markers s6) -> In c (markers s2) \/ c = gend_cell am6.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ND Hk c Hc. unfold markers in Hc. apply in_flat_map in Hc as [[q a] [Hq Hc]]. cbn [snd] in Hc.
  destruct (s6_used ND Hk q a Hq) as [H | (-> & ->)].
  - left. unfold markers. apply in_flat_map. exists (q, a). split; [exact H | exact Hc].
  - right. unfold meta_markers in Hc. apply in_app_iff in Hc as [Hc|[<-|[]]]; [|reflexivity].
    exfalso. apply in_flat_map in Hc as [i [_ Hc]]. unfold nth_slot in Hc. cbn [am_slots am_set_links new_am] in Hc. rewrite nth_repeat' in Hc.
    destruct (Nat.ltb _ _); cbn in Hc; destruct Hc.
Qed.

#[using="Type"] Lemma s6_active : length (st_active s2) = 48%nat -> 0 <= sc <= 47 -> active_hd s6 sc = Some mt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L1 Hsc. pose proof (s3_same s2 sc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eac3 & _).
  unfold active_hd, ag_s6, ins_st, ag_s5. cbn [st_active set_active set_metas set_usage set_mmap_counter set_regions].
  apply nth_lupd_same. rewrite Eac3, L1. lia.
Qed.

#[using="Type"] Lemma s6_usage : length (st_usage s2) = 48%nat -> 0 <= sc <= 47 -> forall c, 0 <= c ->
  usage_of s6 c = if c =? sc then usage_of s2 sc + cnt else usage_of s2 c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L2 Hsc c Hc. pose proof (s3_same s2 sc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eus3 & _).
  unfold usage_of at 1, znth, ag_s6, ins_st, ag_s5. cbn [st_usage set_active set_metas set_usage set_mmap_counter set_regions]. unfold zset.
  destruct (c =? sc) eqn:E.
  - apply Z.eqb_eq in E. subst c. rewrite nth_zupd_same by (rewrite Eus3, L2; lia). unfold usage_of, znth. cbn [st_usage set_mmap_counter set_regions]. rewrite Eus3. reflexivity.
  - apply Z.eqb_neq in E. rewrite nth_zupd_other by lia. rewrite Eus3. reflexivity.
Qed.
End S6.
