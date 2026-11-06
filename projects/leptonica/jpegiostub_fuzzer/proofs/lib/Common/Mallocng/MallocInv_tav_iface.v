(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf4 MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops
  MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_aspieces.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Record tavrel (A A' : astate) (sc : Z) : Prop := {
  tv_live : a_live A' = a_live A;
  tv_areas : a_areas A' = a_areas A;
  tv_pages : a_pages A' = a_pages A;
  tv_mblocks : a_mblocks A' = a_mblocks A;
  tv_xmaps : a_xmaps A' = a_xmaps A;
  tv_fl : a_freelist A' = a_freelist A;
  tv_brk_lo : a_brk_lo A' = a_brk_lo A;
  (* [comment removed for export] *)
  tv_act : forall c, c <> sc -> a_active A' c = a_active A c;
  tv_act_sub : forall x, In x (a_active A' sc) -> In x (a_active A sc);
  (* [comment removed for export] *)
  tv_ctx : forall k, cvalid k -> k <> KActive sc -> ~ ctx_heur k -> a_ctx A' k = a_ctx A k;
  (* [comment removed for export] *)
  tv_grp : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     exists mt0 aib0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 slx /\
       mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  tv_grp_back : forall x mt0 aib0 slx, a_meta A x = Some mt0 -> mt_role mt0 = RGroup aib0 slx ->
     exists mtx aibx, a_meta A' x = Some mtx /\ mt_role mtx = RGroup aibx slx /\
       mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  tv_other : forall x mt0, a_meta A x = Some mt0 -> (forall aib sl, mt_role mt0 <> RGroup aib sl) -> a_meta A' x = Some mt0;
  tv_other_back : forall x mtx, a_meta A' x = Some mtx -> (forall aib sl, mt_role mtx <> RGroup aib sl) -> a_meta A x = Some mtx;
  tv_dom : forall x, dom A' x <-> dom A x
}.

Lemma tavrel_refl : forall A sc, tavrel A A sc.
Proof.
  intros A sc. constructor; auto; try tauto.
  - intros x mtx aibx slx Hx Hr. exists mtx, aibx. auto.
  - intros x mt0 aib0 slx Hx Hr. exists mt0, aib0. auto.
Qed.

(* [comment removed for export] *)
Definition try_avail_spec : Prop :=
  forall (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc : Z) (K : option (word * word) -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s -> 0 <= sc < 48 ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc -> a_active A' sc = [] ->
       tsafe (K None s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (m : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st),
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc ->
       a_active A' sc <> [] -> m = hd 0 (a_active A' sc) ->
       a_meta A' m = Some mt -> mt_role mt = RGroup aib slots -> mt_avail mt <> 0 ->
       tsafe (K (Some (Z_to_bv 64 m, w32 (mt_avail mt))) s') P) ->
    tsafe ((ta <- as_tryavail (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (a_ctx A (KActive sc))) ;; K ta) s) P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ring_dry (A : astate) (sc : Z) : Prop :=
  a_active A sc = [] \/
  exists h mt, a_active A sc = [h] /\ a_meta A h = Some mt /\ mt_avail mt = 0 /\ mt_freed mt = 0.

(* [comment removed for export] *)
Definition try_avail_specD : Prop :=
  forall (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc : Z) (K : option (word * word) -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s -> 0 <= sc < 48 ->
    (forall s' A',
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc -> a_active A' sc = [] ->
       ring_dry A sc ->
       tsafe (K None s') P) ->
    (forall s' A' (m : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st),
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc ->
       a_active A' sc <> [] -> m = hd 0 (a_active A' sc) ->
       a_meta A' m = Some mt -> mt_role mt = RGroup aib slots -> mt_avail mt <> 0 ->
       tsafe (K (Some (Z_to_bv 64 m, w32 (mt_avail mt))) s') P) ->
    tsafe ((ta <- as_tryavail (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (a_ctx A (KActive sc))) ;; K ta) s) P.

Lemma try_avail_specD_spec : try_avail_specD -> try_avail_spec.
Proof.
  intros TD R sp0 argv envp cb D A s sc K P HII Hsc HN HS.
  apply (TD R sp0 argv envp cb D A s sc K P HII Hsc); [| exact HS].
  intros s' A' H1 H2 H3 H4 _. exact (HN s' A' H1 H2 H3 H4).
Qed.

End WithLayout.
