(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngWk AXG_ag0 AXG_mwm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition dr_s1 (s : astate) (n : Z) : astate := set_regions (st_regions s ++ [mkRegion RkMap (page_round (n + IB + UNIT)) [] true]) s.
Definition dr_s2 (s : astate) (n : Z) : astate := sq_st (dr_s1 s n).
Definition dr_s4 (g : sptr) (s3 : astate) (r : nat) (maplen : Z) : astate := set_metas (mupdate (st_metas s3) g (MUsed (direct_am r maplen))) s3.
Definition dr_s5 (g : sptr) (s3 : astate) (r : nat) (maplen : Z) : astate :=
  set_mmap_counter (Z.land (st_mmap_counter (dr_s4 g s3 r maplen) + 1) (2^32 - 1)) (dr_s4 g s3 r maplen).

Lemma malloc_direct_tree : forall n s, MMAP_THRESHOLD <= n <= 2^26 ->
  exists K Kd, malloc n s = IAsk (KMmapRW (n + IB + UNIT)) s K /\ K 1 = ibind (alloc_meta (dr_s2 s n)) Kd /\
    forall mt s3, Kd (Some mt, s3) = ef_tail mt 0 n (dr_s5 mt s3 (length (st_regions s)) (page_round (n + IB + UNIT) / 4096)).
Proof.
  intros n s Hn. unfold malloc.
  replace (size_overflows n) with false by (unfold size_overflows; symmetry; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  unfold bind at 1, ask. cbn [ibind]. eexists. eexists. split; [reflexivity|]. split.
  - cbv beta. cbn [Z.eqb negb]. unfold new_region, bind, get, put, ret, step_seq, modify. cbn [ibind]. reflexivity.
  - intros mt s3. reflexivity.
Qed.

Lemma areas_cells_regions : forall s rs l, areas_cells (set_regions rs s) l = areas_cells s l.
Proof. intros s rs l. induction l as [|a t IH]; [reflexivity|]. cbn [areas_cells]. rewrite IH. reflexivity. Qed.

Lemma image_dr_s1 : forall s n, MallocInv.image (dr_s1 s n) = MallocInv.image s.
Proof. intros s n. unfold MallocInv.image, dr_s1. rewrite areas_cells_regions. reflexivity. Qed.
