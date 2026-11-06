(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngGM AXG_ntfm AXG_ntfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ MngNtfM MngNtfS AXF_eez AXG_nQ AXG_nM AXG_nF AXG_ntfP MngMk_c1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac fin8 Hms Hex Ht N' HRS HZ Hg FR :=
  split; [exact Hms|]; split; [exact Hex|]; split; [exact Ht|]; split; [exact N'|]; split; [exact HRS|]; split; [exact HZ|]; split; [exact Hg|]; split; [exact FR|].

Lemma mks_fm0 : forall s4 g, MKS (s_fm0 s4 g) s4.
Proof. intros s4 g. unfold s_fm0. eapply MKS_trans; [apply MKS_metas; reflexivity | apply MKS_setm_free]. Qed.
Lemma mks_fm1 : forall s4 g h hp hpp hn, MKS (s_fm1 s4 g h hp hpp hn) s4.
Proof. intros. unfold s_fm1. eapply MKS_trans; [apply MKS_setm_free|]. eapply MKS_trans; [apply MKS_setm_free | apply MKS_setm_free]. Qed.
Lemma mks_fm1s : forall s4 g h, MKS (s_fm1s s4 g h) s4.
Proof. intros. unfold s_fm1s. eapply MKS_trans; [apply MKS_setm_free | apply MKS_setm_free]. Qed.

Section FMP.
Context {fx : FPState}.

#[using="Type"] Theorem ntf_fm : forall L X EXC U s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len,
  NC L (g :: X) (LMem (am_mem a4) :: EXC) s4 m sp0 K -> EXC_z X s4 EXC -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa len -> getr R 12 = wa base -> getr R 18 = wa 0x97c98 ->
  MT s4 g = Some (MUsed a4) -> ~ In g X -> 0 <= base <= 2^64-1 -> 0 <= len <= 2^64-1 ->
  Inv (g :: X) None U s4 ->
  exists R' m' s5, msteps SEGS (mkst R (wa 0x5396c) m rom) (mkst R' (wa 0x53a58) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 base len /\
    free_meta g s4 = IRet (tt, s5) /\ NC L X EXC s5 m' sp0 K /\ RS L s5 s4 /\
    (forall x, In x X -> MT s5 x = MT s4 x) /\ mem_grows m m' /\ FRM L s4 sp0 K m m' /\ MKS s5 s4 /\
    st_regions s5 = st_regions s4 /\ st_areas s5 = st_areas s4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC U s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len N HEXo F R10 R11 R12 R18 Mg NXg Rb Rl HI.
  destruct (inv_rings HI) as ((ms & FR & Fall) & _ & _).
  destruct (st_free_meta_head s4) as [h|] eqn:Eh.
  2:{ destruct (seg_fm0 L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len N HEXo F R10 R11 R12 R18 Mg NXg Eh Rb Rl)
        as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FRM5).
      exists R', m', (s_fm0 s4 g). fin8 Hms Hex Ht N' HRS HZ Hg FRM5. split; [apply mks_fm0 | split; reflexivity]. }
  destruct (ring_head_In _ _ _ FR) as (Hhm & _).
  destruct (ring_links _ _ _ h FR Hhm) as (hp & hn & Lh).
  destruct (flinks_free _ _ _ _ Lh) as (pr' & nx' & Xh & Mh & E). injection E as <- <-.
  assert (Hhg : h <> g) by (intros ->; cbn in Xh; rewrite sptr_eqb_refl in Xh; discriminate).
  destruct (ring_prev_next _ _ _ h hp _ FR Hhm Lh) as (hpp & Lhp).
  destruct (sptr_eq_dec hp h) as [Eph|Hph].
  - subst hp. rewrite Lh in Lhp. injection Lhp as _ Ehn. subst hn.
    destruct (seg_fm1s L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h N HEXo F R10 R11 R12 R18 Mg NXg Rb Rl Eh Hhg Mh)
      as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FRM5).
    exists R', m', (s_fm1s s4 g h). fin8 Hms Hex Ht N' HRS HZ Hg FRM5. split; [apply mks_fm1s | split; reflexivity].
  - destruct (flinks_free _ _ _ _ Lhp) as (pp' & np' & Xhp & Mhp & E). injection E as <- <-.
    assert (Hpg : hp <> g) by (intros ->; cbn in Xhp; rewrite sptr_eqb_refl in Xhp; discriminate).
    destruct (seg_fm1 L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h hp hpp (Some hn) N HEXo F R10 R11 R12 R18 Mg NXg Rb Rl Eh Hhg Hpg Hph Mh Mhp)
      as (R' & m' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FRM5).
    exists R', m', (s_fm1 s4 g h hp hpp (Some hn)). fin8 Hms Hex Ht N' HRS HZ Hg FRM5. split; [apply mks_fm1 | split; reflexivity].
Qed.
End FMP.
