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
                        AXF_eez AXG_ntfm AXG_nE AXG_ntfP MngMk_c1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma osptr_eq_dec : forall a b : option sptr, {a = b} + {a <> b}.
Proof. decide equality; apply sptr_eq_dec. Qed.

Ltac fin8 Hms Hex Ht N' HRS HZ Hg FR :=
  split; [exact Hms|]; split; [exact Hex|]; split; [exact Ht|]; split; [exact N'|]; split; [exact HRS|]; split; [exact HZ|]; split; [exact Hg|]; split; [exact FR|].

(* [comment removed for export] *)
Section MK.
Variables (s : astate) (g : sptr) (am : ameta) (i : Z).
Hypothesis Mg : MT s g = Some (MUsed am).
#[using="Mg"] Lemma mks_e12 : MKS (ntf_e12 s g am i) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0). apply (MKS_setm_same s g am); [exact Mg | reflexivity]. Qed.
#[using="Mg"] Lemma mks_e3 : MKS (ntf_e3 s g am i) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0). unfold ntf_e3. eapply MKS_trans; [apply MKS_metas; reflexivity|]. apply (MKS_setm_same s g am); [exact Mg | reflexivity]. Qed.
#[using="Mg"] Lemma mks_e4 : forall h amh hp amhp, h <> g -> hp <> g -> hp <> h -> MT s h = Some (MUsed amh) -> MT s hp = Some (MUsed amhp) ->
  MKS (ntf_e4 s g am i h amh hp amhp) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros h amh hp amhp Hhg Hpg Hph Mh Mhp. unfold ntf_e4.
  eapply MKS_trans; [apply (MKS_setm_same _ h amh); [rewrite !MT_set_other by congruence; exact Mh | reflexivity]|].
  eapply MKS_trans; [apply (MKS_setm_same _ hp amhp); [rewrite MT_set_other by congruence; exact Mhp | reflexivity]|].
  apply (MKS_setm_same s g am); [exact Mg | reflexivity].
Qed.
#[using="Mg"] Lemma mks_e4s : forall h amh, h <> g -> MT s h = Some (MUsed amh) -> MKS (ntf_e4s s g am i h amh) s.
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  intros h amh Hhg Mh. unfold ntf_e4s.
  eapply MKS_trans; [apply (MKS_setm_same _ h amh); [rewrite MT_set_other by congruence; exact Mh | reflexivity]|].
  apply (MKS_setm_same s g am); [exact Mg | reflexivity].
Qed.
End MK.

Section ELSE.
Context {fx : FPState}.

#[using="Type"] Theorem ntf_else : forall L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa (bv_swrap 32 (2^i)) -> getr R 12 = wa (am_sc am) ->
  getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) ->
  Inv X (Some (g, i)) U s -> usedX X s g am ->
  ((am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) <> Some g -> am_freed am <> 0) ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  exists R' m' s', msteps SEGS (mkst R (wa 0x51a2c) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 0 0 /\
    nontrivial_free (S f) g i s = IRet (None, s') /\ NC L X EXC s' m' sp0 K /\
    RS L s' s /\ (forall x, In x X -> MT s' x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\ MKS s' s /\
    st_regions s' = st_regions s /\ st_areas s' = st_areas s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 HI Hu HR2g Hcond.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. apply memb_false_notIn in NXg.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & _ & _). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  destruct (masks_range_inv _ _ _ s g am HI Hu) as (RA & RF & Rl & Rs & Rm).
  destruct (else_branch_facts X U s g i am HI Hu Hcond) as [Hsc _].
  pose proof (inv_ctx HI) as (Cla & _).
  assert (Ri : 0 <= i <= 31) by (clear - Hi Rl; lia).
  destruct (Z.eq_dec (Z.lor (am_freed am) (am_avail am)) 0) as [M0|M0].
  2:{ destruct (seg_e12 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 Mg NXg Ri Hsc RA RF Hcond (or_introl M0))
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR).
      exists R', m', (ntf_e12 s g am i). fin8 Hms Hex Ht N' HRS HZ Hg FR. split; [exact (mks_e12 s g am i Mg) | split; reflexivity]. }
  assert (Hav0 : am_avail am = 0 /\ am_freed am = 0) by (apply Z.lor_eq_0_iff in M0; tauto).
  destruct (osptr_eq_dec (active_hd s (am_sc am)) (Some g)) as [Ha|Ha].
  { destruct (seg_e12 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 Mg NXg Ri Hsc RA RF Hcond (or_intror (conj M0 Ha)))
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR).
      exists R', m', (ntf_e12 s g am i). fin8 Hms Hex Ht N' HRS HZ Hg FR. split; [exact (mks_e12 s g am i Mg) | split; reflexivity]. }
  assert (Hunl : am_prev am = None /\ am_next am = None).
  { destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; try (split; reflexivity);
      exfalso; apply (HR2g ltac:(discriminate) Ha); exact (proj2 Hav0). }
  destruct Hunl as [Hp Hn].
  destruct (active_hd s (am_sc am)) as [h|] eqn:Eh.
  2:{ destruct (seg_e3 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 Mg NXg Ri Hsc RA RF Cla Hcond M0 Hp Hn Eh)
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR).
      exists R', m', (ntf_e3 s g am i). fin8 Hms Hex Ht N' HRS HZ Hg FR. split; [exact (mks_e3 s g am i Mg) | split; reflexivity]. }
  assert (Hhg : h <> g) by (intros ->; exact (Ha eq_refl)).
  destruct (inv_rings HI) as (_ & A & _). destruct (A (am_sc am) Hsc) as (ms & Rg & Mem & _).
  rewrite Eh in Rg. destruct (ring_head_In _ _ _ Rg) as (Hhm & _).
  destruct (ring_links _ _ _ h Rg Hhm) as (pr & nx & Lh).
  unfold alinks, MTX in Lh. destruct (memb h X) eqn:Xh; [discriminate|]. destruct (MT s h) as [[hp' hn'| |amh]|] eqn:Mh; try discriminate.
  destruct (am_sc amh =? am_sc am) eqn:Esch; [|discriminate]. injection Lh as Eph Enh.
  assert (NXh : ~ In h X) by (apply memb_false_notIn; exact Xh).
  assert (Lh' : alinks X s (am_sc am) h = Some (Some pr, Some nx)) by (unfold alinks, MTX; rewrite Xh, Mh, Esch, Eph, Enh; reflexivity).
  pose proof (ring_prev_In _ _ _ h pr (Some nx) Rg Hhm Lh') as Hpm.
  destruct (ring_links _ _ _ pr Rg Hpm) as (pp & pn & Lp).
  unfold alinks, MTX in Lp. destruct (memb pr X) eqn:Xp; [discriminate|]. destruct (MT s pr) as [[pq pw| |amhp]|] eqn:Mp; try discriminate.
  assert (NXp : ~ In pr X) by (apply memb_false_notIn; exact Xp).
  assert (Hpg : pr <> g).
  { intros ->. rewrite Mg in Mp. injection Mp as <-. assert (Hu2 : usedX X s g am) by exact Hu.
    pose proof (proj1 (Mem g am Hu2 eq_refl) Hpm) as E. rewrite Hp, Hn in E. exact (E eq_refl). }
  destruct (sptr_eq_dec pr h) as [->|Hph].
  - destruct (seg_e4s L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh N F R10 R11 R12 R13 Mg NXg Ri Hsc RA RF Hcond M0 Hp Hn Eh Hhg Mh Eph NXh)
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR).
    exists R', m', (ntf_e4s s g am i h amh). fin8 Hms Hex Ht N' HRS HZ Hg FR. split; [exact (mks_e4s s g am i Mg h amh Hhg Mh) | split; reflexivity].
  - destruct (seg_e4 L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh pr amhp N F R10 R11 R12 R13 Mg NXg Ri Hsc RA RF Hcond M0 Hp Hn Eh Hhg Mh Eph Hpg Hph Mp NXh NXp)
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR).
    exists R', m', (ntf_e4 s g am i h amh pr amhp). fin8 Hms Hex Ht N' HRS HZ Hg FR. split; [exact (mks_e4 s g am i Mg h amh pr amhp Hhg Hpg Hph Mh Mp) | split; reflexivity].
Qed.
End ELSE.
