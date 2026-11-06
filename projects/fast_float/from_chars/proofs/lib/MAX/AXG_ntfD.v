(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS MngGM
                        AXF_eez AXG_ntfm AXG_ntfg AXG_nQ AXG_ntfP AXG_ntfDm MngMk_c1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk :=
  split; [exact Hms|]; split; [exact Ht|]; split; [exact N'|]; split; [exact F'|]; split; [exact HRS|]; split; [exact HZ|];
  split; [exact Hg|]; split; [exact FR|]; split; [exact R10'|]; split; [exact R18'|]; split; [exact Hk|].

(* [comment removed for export] *)
Section MK.
Variables (s : astate) (g : sptr) (am : ameta).
Hypothesis Mg : MT s g = Some (MUsed am).
#[using="Mg"] Lemma mks_dq1 : forall sc, MKS (s_dq1 s g sc am) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros sc. unfold s_dq1. eapply MKS_trans; [apply (MKS_setm_same _ g am); [exact Mg | reflexivity]|]. apply MKS_metas. reflexivity.
Qed.
#[using="Mg"] Lemma mks_dq3 : forall pr ampr nx amnx, pr <> g -> nx <> g -> pr <> nx -> MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  MKS (s_dq3 s g am pr ampr nx amnx) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros pr ampr nx amnx Hpg Hng Hpn Mp Mn. unfold s_dq3.
  eapply MKS_trans; [apply (MKS_setm_same _ g am); [rewrite !MT_set_other by congruence; exact Mg | reflexivity]|].
  eapply MKS_trans; [apply (MKS_setm_same _ nx amnx); [rewrite MT_set_other by congruence; exact Mn | reflexivity]|].
  apply (MKS_setm_same s pr ampr); [exact Mp | reflexivity].
Qed.
#[using="Mg"] Lemma mks_dq3s : forall h amh, h <> g -> MT s h = Some (MUsed amh) -> MKS (s_dq3s s g am h amh) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros h amh Hhg Mh. unfold s_dq3s.
  eapply MKS_trans; [apply (MKS_setm_same _ g am); [rewrite MT_set_other by congruence; exact Mg | reflexivity]|].
  apply (MKS_setm_same s h amh); [exact Mh | reflexivity].
Qed.
#[using="Mg"] Lemma mks_dq2 : forall sc pr ampr nx amnx, pr <> g -> nx <> g -> pr <> nx -> MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  MKS (s_dq2 s g sc am pr ampr nx amnx) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros sc pr ampr nx amnx Hpg Hng Hpn Mp Mn. unfold s_dq2.
  eapply MKS_trans; [apply (MKS_setm_same _ nx (am_set_links (Some pr) (am_next amnx) amnx)); [rewrite MT_set_other by congruence; apply MT_set_same | reflexivity]|].
  eapply MKS_trans; [apply (MKS_setm_same _ g am); [change (MT (set_meta (set_meta s pr (MUsed (am_set_links (am_prev ampr) (Some nx) ampr))) nx
      (MUsed (am_set_links (Some pr) (am_next amnx) amnx))) g = Some (MUsed am)); rewrite !MT_set_other by congruence; exact Mg | reflexivity]|].
  eapply MKS_trans; [apply MKS_metas; reflexivity|].
  eapply MKS_trans; [apply (MKS_setm_same _ nx amnx); [rewrite MT_set_other by congruence; exact Mn | reflexivity]|].
  apply (MKS_setm_same s pr ampr); [exact Mp | reflexivity].
Qed.
#[using="Mg"] Lemma mks_dq2s : forall sc h amh, h <> g -> MT s h = Some (MUsed amh) -> MKS (s_dq2s s g sc am h amh) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros sc h amh Hhg Mh. unfold s_dq2s.
  eapply MKS_trans; [apply (MKS_setm_same _ h (am_set_links (Some h) (Some h) amh)); [rewrite MT_set_other by congruence; apply MT_set_same | reflexivity]|].
  eapply MKS_trans; [apply (MKS_setm_same _ g am); [change (MT (set_meta s h (MUsed (am_set_links (Some h) (Some h) amh))) g = Some (MUsed am));
      rewrite MT_set_other by congruence; exact Mg | reflexivity]|].
  eapply MKS_trans; [apply MKS_metas; reflexivity|].
  apply (MKS_setm_same s h amh); [exact Mh | reflexivity].
Qed.
End MK.

Section DEQ.
Context {fx : FPState}.

#[using="Type"] Theorem ntf_deq : forall L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g am i,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  Inv X (Some (g, i)) U s -> usedX X s g am ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = true ->
  exists R' m' sA, msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, sA) /\ NC L X EXC sA m' sp0 K /\ ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\
    RS L sA s /\ (forall x, In x X -> MT sA x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R /\ DQP X U s g am sA /\ MKS sA s /\
    st_regions sA = st_regions s /\ st_areas sA = st_areas s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g am i N F R10 R12 R18 HI Hu Hcond.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. apply memb_false_notIn in NXg.
  apply andb_prop in Hcond as [Hmask _]. apply Z.eqb_eq in Hmask.
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _ & _).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  pose proof (inv_ctx HI) as (Cla & _).
  destruct (am_next am) as [nx|] eqn:Enx.
  2:{ destruct (seg_dq0 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am N F R10 R12 R18 Mg Hscr Enx) as (R' & Hms & Ht & F' & R10' & R18' & Hk).
      exists R', m, s. fin11 Hms Ht N F' (RS_refl L s) (fun (x : sptr) (_ : In x X) => @eq_refl _ (MT s x)) (mem_grows_refl m) (FRM_refl L s sp0 K m) R10' R18' Hk.
      split; [exact (deq_model' X U s g i am s HI Hu Hmask Ht) | split; [apply MKS_refl | split; reflexivity]]. }
  assert (Hsc : 0 <= am_sc am < 48).
  { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
  destruct (inv_rings HI) as (_ & A & _). destruct (A (am_sc am) Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  assert (Hgm : In g ms) by (apply (Mem g am Hu eq_refl); rewrite Enx; intros E; discriminate).
  assert (Lg : alinks X s (am_sc am) g = Some (am_prev am, Some nx)) by (unfold alinks; rewrite Hu, Z.eqb_refl, Enx; reflexivity).
  destruct (ring_links _ _ _ g Rg Hgm) as (pr & nx' & Lg'). rewrite Lg in Lg'. injection Lg' as Epr Enx'. subst nx'.
  rewrite Epr in Lg.
  destruct (sptr_eq_dec nx g) as [->|Hnxg].
  { pose proof (ring_self _ _ _ g _ Rg Hgm Lg) as Ha.
    destruct (seg_dq1 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am N F R10 R12 R18 Mg NXg Hsc Cla Enx Ha)
      as (R' & m' & Hms & Ht & N' & F' & HRS & HZ & Hg & FR & R10' & R18' & Hk).
    exists R', m', (s_dq1 s g (am_sc am) am). fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk.
    split; [exact (deq_model' X U s g i am _ HI Hu Hmask Ht) | split; [exact (mks_dq1 s g am Mg _) | split; reflexivity]]. }
  assert (Hprg : pr <> g).
  { intros ->. destruct (ring_prev_next _ _ _ g g _ Rg Hgm Lg) as (pp & Lp). rewrite Lg in Lp. injection Lp as _ E. exact (Hnxg E). }
  pose proof (ring_next_In _ _ _ g _ nx Rg Hgm Lg) as Hnxm. pose proof (ring_prev_In _ _ _ g pr _ Rg Hgm Lg) as Hprm.
  destruct (ring_links _ _ _ nx Rg Hnxm) as (p1 & n1 & Lnx). destruct (alinks_used _ _ _ _ _ Lnx) as (amnx & Unx & Snx & _).
  destruct (ring_links _ _ _ pr Rg Hprm) as (p2 & n2 & Lpr). destruct (alinks_used _ _ _ _ _ Lpr) as (ampr & Upr & Spr & _).
  pose proof (usedX_MT _ _ _ _ Unx) as [Mnx NXnx]. apply memb_false_notIn in NXnx.
  pose proof (usedX_MT _ _ _ _ Upr) as [Mpr NXpr]. apply memb_false_notIn in NXpr.
  destruct (masks_range_inv _ _ _ s nx amnx HI Unx) as (_ & RFnx & _ & _ & _).
  pose proof (inv_groups HI nx amnx Unx) as ((GlNx & GaNx & _) & _).
  destruct (osptr_eqb (active_hd s (am_sc am)) (Some g)) eqn:Eh.
  - apply osptr_eqb_eq in Eh.
    assert (Havnx : am_avail amnx = 0).
    { destruct (Z.eq_dec (am_avail amnx) 0) as [E|E]; [exact E|]. exfalso. pose proof (Q1 nx amnx Unx Snx E) as E2. rewrite Eh in E2. injection E2 as E3. exact (Hnxg (eq_sym E3)). }
    assert (Raix : 0 <= am_aidx amnx <= 31) by (clear - GlNx GaNx; lia).
    destruct (sptr_eq_dec pr nx) as [->|Hprnx].
    + destruct (seg_dq2s L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am nx amnx N F R10 R12 R18 Mg NXg Hsc Cla Enx Epr Hnxg Mnx NXnx Eh Havnx Raix RFnx)
        as (R' & m' & Hms & Ht & N' & F' & HRS & HZ & Hg & FR & R10' & R18' & Hk).
      exists R', m', (s_dq2s s g (am_sc am) am nx amnx). fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk.
      split; [exact (deq_model' X U s g i am _ HI Hu Hmask Ht) | split; [exact (mks_dq2s s g am Mg _ nx amnx Hnxg Mnx) | split; reflexivity]].
    + destruct (seg_dq2 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx N F R10 R12 R18 Mg NXg Hsc Cla Enx Epr Hnxg Hprg Hprnx Mpr Mnx NXpr NXnx Eh Havnx Raix RFnx)
        as (R' & m' & Hms & Ht & N' & F' & HRS & HZ & Hg & FR & R10' & R18' & Hk).
      exists R', m', (s_dq2 s g (am_sc am) am pr ampr nx amnx). fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk.
      split; [exact (deq_model' X U s g i am _ HI Hu Hmask Ht) | split; [exact (mks_dq2 s g am Mg _ pr ampr nx amnx Hprg Hnxg Hprnx Mpr Mnx) | split; reflexivity]].
  - assert (Eh' : active_hd s (am_sc am) <> Some g) by (intros E; rewrite E in Eh; cbn in Eh; rewrite sptr_eqb_refl in Eh; discriminate).
    destruct (active_hd s (am_sc am)) as [hd|] eqn:Ehd.
    2:{ exfalso. pose proof (ring_None _ _ Rg) as E. rewrite E in Hgm. exact Hgm. }
    assert (Hhdg : hd <> g) by (intros ->; exact (Eh' eq_refl)).
    destruct (ring_head_In _ _ _ Rg) as (Hhdm & _). destruct (ring_links _ _ _ hd Rg Hhdm) as (p3 & n3 & Lhd).
    destruct (alinks_used _ _ _ _ _ Lhd) as (amhd & Uhd & _ & _). pose proof (usedX_MT _ _ _ _ Uhd) as [Mhd _].
    pose proof (MT_Some_In_keys _ _ _ Mhd) as Khd.
    destruct (sptr_eq_dec pr nx) as [->|Hprnx].
    + destruct (seg_dq3s L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am nx amnx hd N F R10 R12 R18 Mg NXg Hsc Cla Enx Epr Hnxg Mnx NXnx Ehd Hhdg Khd)
        as (R' & m' & Hms & Ht & N' & F' & HRS & HZ & Hg & FR & R10' & R18' & Hk).
      exists R', m', (s_dq3s s g am nx amnx). fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk.
      split; [exact (deq_model' X U s g i am _ HI Hu Hmask Ht) | split; [exact (mks_dq3s s g am Mg nx amnx Hnxg Mnx) | split; reflexivity]].
    + destruct (seg_dq3 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx hd N F R10 R12 R18 Mg NXg Hsc Cla Enx Epr Hnxg Hprg Hprnx Mpr Mnx NXpr NXnx Ehd Hhdg Khd)
        as (R' & m' & Hms & Ht & N' & F' & HRS & HZ & Hg & FR & R10' & R18' & Hk).
      exists R', m', (s_dq3 s g am pr ampr nx amnx). fin11 Hms Ht N' F' HRS HZ Hg FR R10' R18' Hk.
      split; [exact (deq_model' X U s g i am _ HI Hu Hmask Ht) | split; [exact (mks_dq3 s g am Mg pr ampr nx amnx Hprg Hnxg Hprnx Mpr Mnx) | split; reflexivity]].
Qed.
End DEQ.
