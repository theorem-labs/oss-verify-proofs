(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf4 MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops
  MallocInv_hints MallocInv_sc3 MallocInv_ameta_iface MallocInv_ametax_iface MallocInv_ntfree MallocInv_ntpost MallocInv_aspieces MallocSureCap.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record agfail (A A' : astate) (m : Z) : Prop := {
  af_live : a_live A' = a_live A;
  af_areas : a_areas A' = a_areas A;
  af_pages : a_pages A' = a_pages A;
  af_mblocks : a_mblocks A' = a_mblocks A;
  af_xmaps : a_xmaps A' = a_xmaps A;
  af_active : a_active A' = a_active A;
  af_brk_lo : a_brk_lo A' = a_brk_lo A;
  af_ctx : forall k, cvalid k -> k <> KFmh -> ~ ctx_heur k -> a_ctx A' k = a_ctx A k;
  af_grp : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A x = Some mtx;
  af_grp_back : forall x mt0 aib0 sl0, a_meta A x = Some mt0 -> mt_role mt0 = RGroup aib0 sl0 -> a_meta A' x = Some mt0;
  af_m : exists mf, a_meta A' m = Some mf /\ mt_role mf = RFree;
  af_dom : forall x, dom A' x <-> dom A x;
  (* [comment removed for export] *)
  af_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> x <> m -> a_meta A' x = Some mt;
  af_fl : a_freelist A' = a_freelist A ++ [m]
}.

(* [comment removed for export] *)
Record aghand (A A' : astate) (m p L : Z) : Prop := {
  ah_live : a_live A' = a_live A;
  ah_areas : a_areas A' = a_areas A;
  ah_pages : a_pages A' = a_pages A;
  ah_mblocks : a_mblocks A' = a_mblocks A;
  ah_fl : a_freelist A' = a_freelist A;
  ah_active : a_active A' = a_active A;
  ah_brk_lo : a_brk_lo A' = a_brk_lo A;
  ah_xmaps : a_xmaps A' = (p, L) :: a_xmaps A;
  ah_ctx : forall k, cvalid k -> ~ ctx_heur k -> a_ctx A' k = a_ctx A k;
  ah_other : forall x, x <> m -> a_meta A' x = a_meta A x;
  ah_m : exists md, a_meta A' m = Some md /\ mt_role md = RDead /\ mt_f md FW32 = L /\
           (forall fl, fl <> FW32 -> mt_f md fl = 0);
  ah_dom : forall x, dom A' x <-> dom A x
}.

(* [comment removed for export] *)
Record agframe (A : astate) (s s' : mstate) (p L : Z) : Prop := {
  agf_lo : ms_lo s' = ms_lo s;
  agf_hi : ms_hi s' = ms_hi s;
  agf_vm : ms_vm s' = vm_mmap (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s);
  agf_mem : forall a : word, ~ owned_of A (u a) -> ~ (p <= u a < p + L) -> ms_mem s' a = ms_mem s a;
  agf_live : forall q n (a : word), a_live A q = Some n -> q <= u a < q + n -> ms_mem s' a = ms_mem s a;
  agf_mapped : forall a : word, ms_mem s a <> None -> ms_mem s' a <> None
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition as_cnt_spec : Prop :=
  forall (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc usage size : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s -> 0 <= sc < 48 -> size = 16 * size_class sc -> 0 <= usage < 2^64 ->
    (forall cnt, In cnt (cnt_cands sc) -> 1 <= cnt <= 32 -> size * cnt < 2^20 ->
       (cnt = 1 -> sc mod 4 = 3 /\ (2032 < size -> (size + 16) mod 4096 = 0)) ->
       tsafe (K (Z_to_bv 64 cnt) s) P) ->
    tsafe ((c <- as_cnt (Z_to_bv 64 sc) (Z_to_bv 64 usage) (Z_to_bv 64 size) ;; K c) s) P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_mmap_spec : Prop :=
  forall (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc req m usage size cnt1 : Z) (md : meta_rec)
         (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb (m :: D) A s ->
    a_meta A m = Some md -> mt_role md = RDead -> (forall fl, mt_f md fl = 0) -> ~ In m D ->
    0 <= sc < 48 -> a_active A sc = [] -> size = 16 * size_class sc ->
    0 <= req -> req + 4 <= size -> 0 <= usage < 2^64 ->
    1 <= cnt1 <= 32 -> size * cnt1 < 2^20 -> 2048 < size * cnt1 + 16 ->
    (cnt1 = 1 -> sc mod 4 = 3 /\ (size + 16) mod 4096 = 0) ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> ms_vm s' = ms_vm s -> agfail A A' m ->
       (W = WOk -> exists len, 0 < len <= 2^21 /\ forall a, mmap_grant_ok MMrw (ms_vm s) a len = false) ->
       (* [comment removed for export] *)
       (W <> WFail -> refusalP (grp_cap sc) (ms_vm s)) ->
       tsall W (K wm1 s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (p L cnt aidx : Z),
       II sp0 argv envp cb (m :: D) A' s' -> agframe A s s' p L -> aghand A A' m p L ->
       page_aligned p -> heap_range p (p + L) -> 0 < L -> L mod 4096 = 0 ->
       In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps (ms_vm s')) ->
       region_free (vm_noaccess (ms_vm s')) (Z_to_bv 64 p) (Z_to_bv 64 L) = true ->
       (forall x, p <= x < p + L -> ~ dom A' x) ->
       (forall a : word, p <= u a < p + L -> ms_mem s' a = Some (Z_to_bv 8 0)) ->
       1 <= cnt <= 32 -> size * cnt < 2^20 -> (1 < cnt -> size * cnt + 16 <= L) -> (cnt = 1 -> req + 20 <= L) -> 0 <= aidx <= cnt - 1 ->
       (cnt = 1 -> 256 <= size_class sc \/ L - 16 <= size) -> (cnt = 1 -> L < 2^20 + 16) ->
       (aidx < cnt - 1 -> 7 <= sc) ->
       (* [comment removed for export] *)
       (W = WFail -> False) ->
       (* [comment removed for export] *)
       (forall a : word, p <= u a < p + L -> ms_mem s a = None) ->
       (* [comment removed for export] *)
       (exists (ns : bool) (usage2 c2 : Z),
          ((sc < 7 \/ 38 < sc) -> ns = false) /\ (31 < sc -> usage2 = usage) /\ 0 <= usage2 < 2^64 /\ 1 <= c2 <= 32 /\
          cnt2w (Z_to_bv 64 sc) (Z_to_bv 64 usage2) (Z_to_bv 64 4096) (Z_to_bv 64 (size * cnt1)) (Z_to_bv 64 cnt1) ns = Z_to_bv 64 c2 /\
          cn3w ns (Z_to_bv 64 c2) (Z_to_bv 64 (page_round_up_Z (size * c2 + 16))) (Z_to_bv 64 req) (Z_to_bv 64 4096) (Z_to_bv 64 size) (Z_to_bv 64 usage2)
            = (Z_to_bv 64 cnt, Z_to_bv 64 L)) ->
       (* [comment removed for export] *)
       L < 2^21 -> L <= grp_cap sc -> L <= size * cnt + 4111 ->
       tsall W ((r <- as_tail (Z_to_bv 64 sc) (Z_to_bv 64 m) (Z_to_bv 64 p) (Z_to_bv 64 aidx) (Z_to_bv 64 cnt)
                             (Z_to_bv 64 (LOCKA + 8 * sc)) (Z_to_bv 64 (caddr (KActive sc))) ;; K r) s') P) ->
    tsall W ((r <- as_mmap (Z_to_bv 64 sc) (Z_to_bv 64 req) (Z_to_bv 64 m) (Z_to_bv 64 usage) (Z_to_bv 64 4096)
                           (Z_to_bv 64 size) (Z_to_bv 64 cnt1) (Z_to_bv 64 (size * cnt1))
                           (Z_to_bv 64 (LOCKA + 8 * sc)) (Z_to_bv 64 (caddr (KActive sc))) ;; K r) s) P.

End WithLayout.
