(* CARRIED from commit cf036de67ecc74aaaec7382281ce053532205122,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfCallKeep.v, sha256 6adebc212ec96af0441fe5b8c3d96732518ab60314c6afa9b509b00434307919 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree name lib/A; a sentence is split at a directory change, the module order kept.
*)
(* The memory keep across a cf allocator call: arodata_ok_cf (YG0dcf.v) at a leaf's post (part 3c: memnorm is gone)
   memory, from the same two facts at its call memory (a Theorem Labs lane, cf layer field round 3; writer a Theorem Labs lane, 2026-10-30;
   names and statements agreed with CfF1 and RealSegA through a Theorem Labs lane, NAMES.md (sha256 af9af045ca47; internal record)).
   rule 24: no function proved (kind: keep lemmas over contract leaves).
   - arodata: YG0dcf.arodata_keep_cf over the leaf's RAW frame, at X := the owned sets at both states, the stack
     window and the leaf's exception set. A non-owned RELRO byte misses each: arodata_keep_cf's relro_apart_cf gives
     the owned sets and the errbuf extents (xs_cf), relro_not_scratch_cf the stack window, and
     YGcfRodata.relro_not_block_cf the leaf's blocks. The last needs the model fact that the block is a block of its
     state: BLK for a new block (malloc's, realloc's), the contract's own premise for a freed one (afree_realizes_cf's
     `p = PNull \/ In (p, n) (blocks S)`, arealloc_realizes_cf_rh's `In (p, n_old) (blocks S)`). The proofs are
     YGcfRodata's malloc_leaf_arodata_cf / free_leaf_arodata_cf, stated at ARcf + the stack premise instead of the
     whole acall_pre_cf.
   Image-free: no numeral, no image module. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRodata.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfRodata.v. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

(* 1. malloc. BLK: the model fact that the result names the new block (malloc_cf's), as in
   YGcfRodata.malloc_leaf_arodata_cf. *)
Lemma malloc_leaf_keep_cf : forall ly S Hp W regs mem md n r W' c',
  ARcf segs B ly S Hp W mem md -> relro_seg_t segs -> errno_relro_t B ->
  ly_stk_lo ly + ASTACK <= spZ regs ->
  (fst r <> PNull -> exists k, In k (st_chunks (snd r)) /\ ck_state k = CAllocated /\ ck_user k = fst r /\ ck_req k = n) ->
  arodata_ok_cf segs B mem ->
  malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' ->
  at_mem_cf segs c' (fun mem' => arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md n r W' c' A RS ER STK BLK RO
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & RAW).
subst c'. apply at_mem_cf_cfg.
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
      Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[[NN Hb]|X]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + exact (YGcfRodata.relro_not_block_cf B ly' (snd r) _ _ (fst r) n a (proj1 A') (BLK NN) I' Hb).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
- exact RO.
Qed.

(* 2. free. The freed block is a block of the call state (afree_realizes_cf's premise). *)
Lemma free_leaf_keep_cf : forall ly S Hp W regs mem md p n r W' c',
  ARcf segs B ly S Hp W mem md -> relro_seg_t segs -> errno_relro_t B ->
  ly_stk_lo ly + ASTACK <= spZ regs ->
  (p = PNull \/ In (p, n) (blocks S)) ->
  arodata_ok_cf segs B mem ->
  free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' ->
  at_mem_cf segs c' (fun mem' => arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md p n r W' c' A RS ER STK HP RO
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & RAW).
subst c'. apply at_mem_cf_cfg.
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[NN Hb]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + destruct HP as [HP|HP]; [exact (NN HP)|].
    exact (YGcfRodata.relro_not_block_cf B ly S _ _ p n a (proj1 A) (YGcfRodata.blocks_chunk_cf S p n HP) I Hb).
- intros x NX. apply RAW; intros Y; apply NX; tauto.
- exact RO.
Qed.

(* 3. free, primed (YG0dcfR.free_leaf_cf_rh): its raw frame is the released leaf's; ARcf at the
   post is acall_post_cf_rh's first conjunct. *)
Lemma free_leaf_keep_cf_rh : forall ly S Hp W regs mem md p n r W' c',
  ARcf segs B ly S Hp W mem md -> relro_seg_t segs -> errno_relro_t B ->
  ly_stk_lo ly + ASTACK <= spZ regs ->
  (p = PNull \/ In (p, n) (blocks S)) ->
  arodata_ok_cf segs B mem ->
  free_leaf_cf_rh segs B ly S Hp W regs mem md p n r W' c' ->
  at_mem_cf segs c' (fun mem' => arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md p n r W' c' A RS ER STK HP RO
  (ly' & regs' & mem' & md' & Hc & POST & _ & _ & RAW).
rewrite (acall_post_cf_rh_unfold segs B) in POST. destruct POST as (A' & _).
subst c'. apply at_mem_cf_cfg.
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[NN Hb]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + destruct HP as [HP|HP]; [exact (NN HP)|].
    exact (YGcfRodata.relro_not_block_cf B ly S _ _ p n a (proj1 A) (YGcfRodata.blocks_chunk_cf S p n HP) I Hb).
- intros x NX. apply RAW; intros Y; apply NX; tauto.
- exact RO.
Qed.

(* 4. realloc of a live block, primed (YG0dcfR.realloc_leaf_cf_rh). The old block is a block of the call state
   (arealloc_realizes_cf_rh's premise, YG0dcfR.v:106); BLK names the new one. The post's ghost set is
   realloc_hp_cf's. *)
Lemma realloc_leaf_keep_cf_rh : forall ly S Hp W regs mem md p n_old n r W' c',
  ARcf segs B ly S Hp W mem md -> relro_seg_t segs -> errno_relro_t B ->
  ly_stk_lo ly + ASTACK <= spZ regs ->
  In (p, n_old) (blocks S) ->
  (fst r <> PNull -> exists k, In k (st_chunks (snd r)) /\ ck_state k = CAllocated /\ ck_user k = fst r /\ ck_req k = n) ->
  arodata_ok_cf segs B mem ->
  realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c' ->
  at_mem_cf segs c' (fun mem' => arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md p n_old n r W' c' A RS ER STK HP BLK RO
  (ly' & regs' & mem' & md' & Hc & POST & _ & _ & _ & _ & _ & _ & RAW).
rewrite (acall_post_cf_rh_unfold segs B) in POST. destruct POST as (A' & _).
subst c'. apply at_mem_cf_cfg.
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) (realloc_hp_cf B ly p (fst r) Hp) W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
      \/ (fst r <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old)
      \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[[NN Hb]|[[_ Hb]|X]]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + exact (YGcfRodata.relro_not_block_cf B ly' (snd r) _ _ (fst r) n a (proj1 A') (BLK NN) I' Hb).
  + exact (YGcfRodata.relro_not_block_cf B ly S _ _ p n_old a (proj1 A) (YGcfRodata.blocks_chunk_cf S p n_old HP) I Hb).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
- exact RO.
Qed.

End K.
