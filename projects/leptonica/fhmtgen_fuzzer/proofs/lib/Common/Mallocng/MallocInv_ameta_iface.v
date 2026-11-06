(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition UsOK (A : astate) : Prop :=
  forall sc, 0 <= sc < 48 -> a_ctx A (KUsage sc) = usage_of A sc.

(* [comment removed for export] *)
Definition spare (A : astate) : Z :=
  a_ctx A KAmc + Z.of_nat (length (a_freelist A)).

Record II (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
          (A : astate) (s : mstate) : Prop := {
  ii_is : IS sp0 argv envp cb A s;
  ii_vm : VMok A (ms_vm s);
  ii_av : AvOK A;
  ii_us : UsOK A;
  ii_dd : deads A D
}.

Global Arguments ii_is {sp0 argv envp cb D A s} _.
Global Arguments ii_vm {sp0 argv envp cb D A s} _.
Global Arguments ii_av {sp0 argv envp cb D A s} _.
Global Arguments ii_us {sp0 argv envp cb D A s} _.
Global Arguments ii_dd {sp0 argv envp cb D A s} _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record AMvm (A A' : astate) (s s' : mstate) : Prop := {
  amv_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  amv_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  amv_newdom : forall x b sz, dom A' x -> ~ dom A x -> In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true ->
    ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned sz);
  amv_budget : a_areas A = [] -> vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + 12288
}.

Lemma AMvm_refl : forall A s, AMvm A A s s.
Proof.
  intros A s. constructor; auto.
  all: try (intros x b sz H Hn; exfalso; exact (Hn H)).
  all: intros; llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_budget (A : astate) (s : mstate) : Prop :=
  0 < spare A \/
  (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
   (0 < a_ctx A KAac \/ (a_areas A = [] /\ exists a, grant_ok_na_vm (ms_vm s) a 8192 = true))).
(* [comment removed for export] *)

Definition alloc_meta_spec : Prop :=
  forall (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> gsame A A' -> AMvm A A' s s' ->
       spare A = 0 -> a_areas A' = a_areas A ->
       (W = WOk -> ~ am_budget A s) ->
       tsall W (K (Z_to_bv 64 0) s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (m : Z),
       II sp0 argv envp cb (m :: D) A' s' -> FR A s A' s' -> got_meta A D A' m -> AMvm A A' s s' ->
       ((0 < spare A /\ ms_vm s' = ms_vm s /\ a_areas A' = a_areas A /\ spare A' = spare A - 1)
        \/ (spare A = 0 /\ a_areas A' = a_areas A ++ [m - 24] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])) ->
       tsall W (K (Z_to_bv 64 m) s') P) ->
    tsall W ((x <- m_alloc_meta sp ;; K x) s) P.

End WithLayout.
