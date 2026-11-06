(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf
  MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_tables MallocInv_hints
  MallocInv_ameta_iface MallocInv_ametax_iface MallocInv_aslot_iface MallocSureCap MallocSurePot.
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
Record malloc_keep (A A' : astate) (m0 : word -> option byte) : Prop := {
  mk_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> a_meta A' x = Some mt;
  mk_dom : forall x, dom A x -> dom A' x;
  mk_newdom : forall x, dom A' x -> dom A x \/ m0 (Z_to_bv 64 x) = None \/ (exists pg, (In pg (a_areas A') \/ In pg (a_pages A')) /\ pg <= x < pg + 4096);
  mk_xmaps : a_xmaps A' = a_xmaps A;
  (* [comment removed for export] *)
  mk_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib' sl', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl' /\
      mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt /\ length sl' = length sl /\
      (forall j st, nth_error sl j = Some st -> st <> SIdle -> nth_error sl' j = Some st);
  (* [comment removed for export] *)
  mk_acct : (a_areas A = [] \/ 4 <= spare A) ->
    (a_areas A' = a_areas A /\ spare A - 4 <= spare A') \/
    (a_areas A = [] /\ (exists pg, a_areas A' = [pg]) /\ 96 <= spare A')
}.

(* [comment removed for export] *)
Record malloc_vm (A : astate) (n : Z) (s s' : mstate) : Prop := {
  mv_fixed : vm_fixed (ms_vm s) (ms_vm s');
  mv_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  mv_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  (* [comment removed for export] *)
  mv_budget : (a_areas A = [] \/ 4 <= spare A) ->
    vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + n + 2^23
}.

(* [comment removed for export] *)
Record malloc_fail (A A' : astate) (m0 : word -> option byte) : Prop := {
  mf_keep : malloc_keep A A' m0;
  mf_live : a_live A' = a_live A;
  mf_slots : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl;
  mf_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl';
  (* [comment removed for export] *)
  mf_acct0 : (a_areas A' = a_areas A /\ spare A <= spare A') \/
             (spare A < 4 /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 100 <= spare A')
}.

(* [comment removed for export] *)
Record malloc_okrel (A A' : astate) (n res : Z) (m0 : word -> option byte) (s' : mstate) (g idx off : Z) : Prop := {
  mo_keep : malloc_keep A A' m0;
  mo_live : forall q, a_live A' q = (if Z.eq_dec q res then Some n else a_live A q);
  mo_fresh : a_live A res = None;
  mo_g : exists mt aib sl, a_meta A' g = Some mt /\ mt_role mt = RGroup aib sl /\ 0 <= idx <= mt_last mt /\
           nth_error sl (Z.to_nat idx) = Some (SLive off n) /\ res = slot_start mt idx + 16 * off /\
           (mt_sc mt < 48 \/ mt_sc mt = 63);
  (* [comment removed for export] *)
  mo_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl) \/
    x = g \/ (x <> g /\ (mt_sc mt' = 15 \/ mt_sc mt' = 19 \/ mt_sc mt' = 23));
  (* [comment removed for export] *)
  mo_gfresh : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (forall mt aib sl, a_meta A g = Some mt -> mt_role mt <> RGroup aib sl) ->
    idx = 0 /\ sl' = SLive off n :: repeat SIdle (Z.to_nat (mt_last mt')) /\
    (* [comment removed for export] *)
    ((MMAP_THRESHOLD <= n \/ 2032 < 16 * size_class (mt_sc mt')) ->
       forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> g ->
         exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl) /\
    (* [comment removed for export] *)
    (MMAP_THRESHOLD <= n -> mt_sc mt' = 63 /\ mt_last mt' = 0 /\ 0 < mt_maplen mt' /\ grp_map_len mt' = page_round_up_Z (n + 20)) /\
    (* [comment removed for export] *)
    (n < MMAP_THRESHOLD -> 32 <= size_to_class_z n -> mt_sc mt' = size_to_class_z n) /\
    (* [comment removed for export] *)
    (n < MMAP_THRESHOLD -> 38 < mt_sc mt' -> mt_sc mt' mod 4 <> 3 -> usage_of A (mt_sc mt') = 0 ->
       (16384 <= page_round_up_Z (n + 20) \/ page_round_up_Z (n + 20) < 16 * size_class (mt_sc mt') + 16) ->
       mt_last mt' = 0 /\ 0 < mt_maplen mt' /\ mt_stride mt' + 16 = page_round_up_Z (n + 20));
  (* [comment removed for export] *)
  mo_zero : zgroup A' res -> forall a : word, res <= u a < res + n -> ms_mem s' a = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  mo_acct1 : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (MMAP_THRESHOLD <= n \/ 2032 < 16 * size_class (mt_sc mt')) ->
    (a_areas A' = a_areas A /\ spare A - 1 <= spare A') \/
    (spare A < 4 /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 99 <= spare A')
}.

Definition malloc_rel (A A' : astate) (n : Z) (res : word) (m0 : word -> option byte) (s' : mstate) : Prop :=
  (u res = 0 /\ malloc_fail A A' m0) \/
  (u res <> 0 /\ exists g idx off, malloc_okrel A A' n (u res) m0 s' g idx off).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition malloc_noroom (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (n : Z) : Prop :=
  (* [comment removed for export] *)
  aslot_noroom sp0 argv envp cb A s \/
  (* [comment removed for export] *)
  (MMAP_THRESHOLD <= n /\ forall a, mmap_grant_ok MMrw (ms_vm s) a (page_round_up_Z (n + 20)) = false) \/
  (* [comment removed for export] *)
  (MMAP_THRESHOLD <= n /\ exists A1 s1, II sp0 argv envp cb [] A1 s1 /\ FR A s A1 s1 /\
      (forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s1))) /\
      vm_live_bytes (ms_vm s1) <= vm_live_bytes (ms_vm s) + page_round_up_Z (n + 20) /\
      a_areas A1 = a_areas A /\ spare A1 = spare A /\ ~ am_budget A1 s1 /\
      (forall x, a_meta A1 x = a_meta A x) /\ (exists b, a_xmaps A1 = [(b, page_round_up_Z (n + 20))])).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition malloc_growS (n : Z) (A A' : astate) (s s' : mstate) : Prop :=
  sgrow 5 (malloc_db n) 4 A A' (ms_vm s) (ms_vm s') /\
  (* [comment removed for export] *)
  pgrow (malloc_dp n) A A' (ms_vm s) (ms_vm s').

(* [comment removed for export] *)
Definition malloc_noroomS (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (n : Z) (A : astate) (s : mstate) : Prop :=
  snoroom sp0 argv envp cb 5 (malloc_db n) 4 (n + 4115) (malloc_db n) A s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition malloc_specW : Prop :=
  forall (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte)
         (A : astate) (s : mstate) (sp : word) (n : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb [] A s -> a_xmaps A = [] -> ACT48 A ->
    (forall i, 0 <= i < 8 -> ms_mem s (Z_to_bv 64 (LOCKA + i)) = None) ->
    0 <= n < 2^61 ->
    (* [comment removed for export] *)
    (forall s' A' (res : word),
       II sp0 argv envp cb [] A' s' -> FR A s A' s' -> a_xmaps A' = [] -> ACT48 A' ->
       (forall i, 0 <= i < 8 -> ms_mem s' (Z_to_bv 64 (LOCKA + i)) = None) ->
       malloc_vm A n s s' ->
       malloc_rel A A' n res (ms_mem s) s' ->
       (W = WFail -> u res <> 0 -> aslot_had_idle A) ->
       (W = WOk -> u res = 0 -> malloc_noroom sp0 argv envp cb A s n) ->
       (* [comment removed for export] *)
       malloc_growS n A A' s s' ->
       (W <> WFail -> u res = 0 -> malloc_noroomS sp0 argv envp cb n A s) ->
       tsall W (K res s') P) ->
    tsall W ((r <- m_malloc sp (Z_to_bv 64 n) ;; K r) s) P.

End WithLayout.
