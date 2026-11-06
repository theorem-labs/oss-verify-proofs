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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngExc MngNtfPre MngNtfC.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMeta MngNtfM MngNtfS.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma footprint_ctx_len' : forall s rg, In rg (footprint s) -> fst rg = LCtx 0 -> snd rg = CTX_SIZE.
Proof.
  intros s rg Hrg E. unfold footprint in Hrg. destruct Hrg as [<-|Hrg]; [reflexivity|].
  apply in_app_iff in Hrg as [Hrg|Hrg].
  - apply in_map_iff in Hrg as (a & <- & _). discriminate.
  - apply in_flat_map in Hrg as (k & _ & Hk). destruct (region_of s k) as [rg'|]; [|destruct Hk].
    destruct (rg_kind rg'); try destruct Hk. destruct (rg_live rg'); [|destruct Hk]. destruct Hk as [<-|[]]. discriminate.
Qed.

Theorem NC_of_heap : forall L s m sp0 K, WF s -> repr L s (bview SEGS m) -> ly_ctx L = 0x97c98 -> nenv m ->
  stk_ok SEGS m (wa sp0) K -> 1024 <= K -> 2^20 <= sp0 - K -> sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= sp0 - K) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  NC L [] [] s m sp0 K.
Proof.
  intros L s m sp0 K HW HR Hctx Henv HS HK1 Hsp1 Hsp2 Hsp3 HFP HAP.
  pose proof HR as (HL & HC & HFM).
  constructor.
  - exact (repr_x_of_repr L s _ HW HR).
  - intros l [].
  - intros x [].
  - exact (KS_of_WF s HW).
  - exact Hctx.
  - exact Henv.
  - exact HS.
  - exact HK1.
  - exact Hsp1.
  - exact Hsp2.
  - exact Hsp3.
  - intros c Hc. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
    pose proof (proj2 (proj2 (proj2 HL)) rg Hrg) as R. pose proof (HFP rg Hrg) as S.
    unfold range_incl, cell_range, crange in *. cbn [fst snd] in *.
    unfold cplace. split; [lia|]. split; [lia|].
    destruct (loc_eq_dec (fst rg) (LCtx 0)) as [E|E].
    + left. pose proof (footprint_ctx_len' s rg Hrg E) as EL. rewrite E in Hincl. rewrite EL in Hincl.
      cbn [loc_addr] in Hincl. rewrite Hctx in Hincl. unfold CTX_SIZE in Hincl. lia.
    + right. pose proof (HAP rg Hrg E) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia.
  - intros q Hq.
    destruct (meta_geom L s q (sp0 - K + 1024) HW HL Hq ltac:(intros rg Hrg; pose proof (HFP rg Hrg); lia) HAP)
      as (a & _ & _ & _ & G1 & G2 & _ & G3 & G4).
    split; [exact G1|]. split; [lia|]. split; [exact G3 | exact G4].
  - intros q1 q2 H1 H2 Hne. exact (metas_disjoint L s q1 q2 HW HL H1 H2 Hne).
Qed.
