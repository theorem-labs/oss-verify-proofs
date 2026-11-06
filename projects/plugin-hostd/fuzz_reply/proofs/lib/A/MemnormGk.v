(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormGk.v (a working branch 30a1993588f, c5 + memnorm; file sha256 247ba870c9f9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10: the kernel-answer law (MemnormG.v klaw, over LPS's sstep_cfg) at every kernel request the
   frozen Allocate / Deallocate chain answers through a node, at the node lemmas the chain uses.  Image-free.
   rule 24: no function proved (kind: generic run invariant, kernel-answer law instances).

   The requests (YG00.v:96-103) and their nodes in the chain:
   - KMapUser / KMapFreeArray / KMapPtrArray: a MAP_FIXED rw grant, YG0c.v:69 commit_node3 (used at AGjt.v:781,
     YFjt.v:766, YFkn.v:839, CLrefillB3.v:846, AFjt.v:773, AFkn.v:849); the answer memory is zfill (klaw_commit3).
   - KMmapSec: an anonymous rw mmap the kernel places, YF05.v:149 anon_node (AGjs.v:584, AGk0.v:443, AFjs.v:584); the
     answer memory is zfill at the placed address (klaw_anon).
   - KMunmapSec: munmap, YFfn.v:21 munmap_node (DGif1dr.v:262, AFg8.v:353); the answer memory is unfill
     (klaw_munmap).
   - KShadowRemap: asked only behind needs_remap, whose node goals the chain closes by contradiction from the size
     bound (AGk0.v:1033 TAILgB, YFk1.v:1076-1079); no node, no law needed.
   - KDepot: answered without a kernel step (YG0d.v:81); MemnormG.amreal_m_depot carries P.
   Each grant law takes the model's reserved list as the image's (YG0n.v:313 ALedger.al_reserved), the image below
   kLowMemEnd (segs_low, YG0d.v:482 in_img), and alloc_top below TASK_SIZE. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0i YK15 YK18 YK0v YK00 YK13 YP0n YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0c YF05 YFfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import MemnormG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* KMapUser / KMapFreeArray / KMapPtrArray: YG0c.v:69 commit_node3's premises, plus the reserved list and the top *)
Theorem klaw_commit3 : forall (hole : bool) regs (pc : word) mem rom md (flags addr : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (if hole then region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true
  else region_free (vm_reserved (m_vmmaps md)) addr n = true /\ map_contains (vm_maps (m_vmmaps md)) addr n = true) ->
  (if hole then mmap_noreserve_backed_ok flags md (page_round_up_Z len) = true else mmap_fixed_rw_budget_ok flags md addr n = true) ->
  vm_reserved (m_vmmaps md) = segments_reserved segs ->
  alloc_top (m_vmmaps md) <= TASK_SIZE ->
  klaw segs (YAkMemnorm.memnorm segs) (mkCfg (pend_at regs pc mem rom) md).
Proof.
intros hole regs pc mem rom md flags addr len Hh H17 H10 Hal Hpos H11 Hlen Hce H12 H13 Hcore H14 H15 n Hplace Hbud
  RES TOP.
destruct (YG0c.commit_node3 segs hole regs pc mem rom md flags addr len Hh H17 H10 Hal Hpos H11 Hlen Hce H12 H13 Hcore
  H14 H15 Hplace Hbud) as (I & nx & bit & i0 & NODE & _ & OUT).
apply (klaw_node segs _ _ I _ nx NODE). intros i HM.
destruct (OUT i) as (md_i & _ & _ & _ & NX & _). rewrite NX. cbn [cfg_ms ms_mem mkst].
cbn [cfg_ms ms_mem pend_at] in HM.
assert (Pn : 0 <= page_round_up_Z len)
  by (unfold page_round_up_Z, page_size; pose proof (Z.div_pos (len + 4096 - 1) 4096 ltac:(lia) ltac:(lia)); lia).
pose proof (u64_range addr) as Ra.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; unfold TASK_SIZE in TOP; lia).
apply (memnorm_zfill_reserved segs addr n mem segs_low HM).
- rewrite <- RES. destruct hole; [exact (region_free_app_l _ _ addr n Hplace) | exact (proj1 Hplace)].
- rewrite Un. lia.
Qed.

(* KMmapSec: YF05.v:149 anon_node's premises, plus the reserved list and the top *)
Theorem klaw_anon : forall regs (pc : word) mem rom md (flags : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin md a nZ = true) -> mmap_noreserve_backed_ok flags md nZ = true ->
  vm_reserved (m_vmmaps md) = segments_reserved segs ->
  alloc_top (m_vmmaps md) <= TASK_SIZE ->
  klaw segs (YAkMemnorm.memnorm segs) (mkCfg (pend_at regs pc mem rom) md).
Proof.
intros regs pc mem rom md flags len Hh H17 H10 H11 Hlen H12 H13 Hcore H14 H15 nZ n Hex Hb RES TOP.
destruct (YF05.anon_node segs regs pc mem rom md flags len Hh H17 H10 H11 Hlen H12 H13 Hcore H14 H15 Hex Hb)
  as (I & nx & bit & ga & i0 & NODE & _ & OUT).
apply (klaw_node segs _ _ I _ nx NODE). intros i HM.
destruct (OUT i) as (md_i & _ & _ & _ & Hg & NX & _). rewrite NX. cbn [cfg_ms ms_mem mkst].
cbn [cfg_ms ms_mem pend_at] in HM.
unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [_ Hce].
apply Z.leb_le in Hce.
assert (Pn : 0 <= nZ)
  by (unfold nZ, page_round_up_Z, page_size; pose proof (Z.div_pos (len + 4096 - 1) 4096 ltac:(lia) ltac:(lia)); lia).
pose proof (u64_range (ga i)) as Ra.
assert (Un : bv_unsigned n = nZ) by (unfold n; apply u64_lit; unfold TASK_SIZE in TOP; lia).
apply (memnorm_zfill_reserved segs (ga i) n mem segs_low HM).
- rewrite <- RES. exact (region_free_app_l _ _ (ga i) n Hrf).
- rewrite Un. lia.
Qed.

(* KMunmapSec: YFfn.v:21 munmap_node's premises; an unmap needs nothing more *)
Theorem klaw_munmap : forall regs (pc : word) mem rom md (a : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> bv_unsigned a mod page_size = 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned a + page_round_up_Z len <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  klaw segs (YAkMemnorm.memnorm segs) (mkCfg (pend_at regs pc mem rom) md).
Proof.
intros regs pc mem rom md a len Hh H17 H10 Hal H11 Hlen Hnw Hhas.
pose proof (YFfn.munmap_node segs regs pc mem rom md a len Hh H17 H10 Hal H11 Hlen Hnw Hhas) as NODE.
apply (klaw_node segs _ _ unit _ _ NODE). intros [] HM.
cbn [cfg_ms ms_mem mkst]. cbn [cfg_ms ms_mem pend_at] in HM.
exact (memnorm_unfill segs a _ mem HM).
Qed.

(* the same laws at any invariant P closed under memnorm keeps (MemnormG.v srr_inv_call; e.g. the keep form
   fun m => memnorm mem0 -> memnorm m, srr_inv_call_imp) *)
Corollary klaw_commit3_call : forall P, srr_inv_call segs P ->
  forall (hole : bool) regs (pc : word) mem rom md (flags addr : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (if hole then region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true
  else region_free (vm_reserved (m_vmmaps md)) addr n = true /\ map_contains (vm_maps (m_vmmaps md)) addr n = true) ->
  (if hole then mmap_noreserve_backed_ok flags md (page_round_up_Z len) = true else mmap_fixed_rw_budget_ok flags md addr n = true) ->
  vm_reserved (m_vmmaps md) = segments_reserved segs ->
  alloc_top (m_vmmaps md) <= TASK_SIZE ->
  klaw segs P (mkCfg (pend_at regs pc mem rom) md).
Proof. intros P HC. intros. apply (klaw_call segs P _ HC). eapply klaw_commit3; eassumption. Qed.

Corollary klaw_anon_call : forall P, srr_inv_call segs P ->
  forall regs (pc : word) mem rom md (flags : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin md a nZ = true) -> mmap_noreserve_backed_ok flags md nZ = true ->
  vm_reserved (m_vmmaps md) = segments_reserved segs ->
  alloc_top (m_vmmaps md) <= TASK_SIZE ->
  klaw segs P (mkCfg (pend_at regs pc mem rom) md).
Proof. intros P HC. intros. apply (klaw_call segs P _ HC). eapply klaw_anon; eassumption. Qed.

Corollary klaw_munmap_call : forall P, srr_inv_call segs P ->
  forall regs (pc : word) mem rom md (a : word) (len : Z),
  m_halted md = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> bv_unsigned a mod page_size = 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned a + page_round_up_Z len <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  klaw segs P (mkCfg (pend_at regs pc mem rom) md).
Proof. intros P HC. intros. apply (klaw_call segs P _ HC). eapply klaw_munmap; eassumption. Qed.
End c.
