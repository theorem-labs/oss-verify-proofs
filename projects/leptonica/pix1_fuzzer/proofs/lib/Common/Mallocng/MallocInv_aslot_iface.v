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
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_tables MallocInv_hints MallocInv_ameta_iface MallocInv_ametax_iface MallocSureCap MallocSurePot.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record aslot_keep (A A' : astate) (sc : Z) (m0 : word -> option byte) : Prop := {
  (* [comment removed for export] *)
  ak_live : a_live A' = a_live A;
  (* [comment removed for export] *)
  ak_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> a_meta A' x = Some mt;
  (* [comment removed for export] *)
  ak_dom : forall x, dom A x -> dom A' x;
  ak_newdom : forall x, dom A' x -> dom A x \/ m0 (Z_to_bv 64 x) = None \/ (exists pg, (In pg (a_areas A') \/ In pg (a_pages A')) /\ pg <= x < pg + 4096);
  (* [comment removed for export] *)
  ak_act : forall c, c <> sc -> nest_rank c <= nest_rank sc -> a_active A' c = a_active A c;
  (* [comment removed for export] *)
  ak_xmaps : a_xmaps A' = a_xmaps A;
  (* [comment removed for export] *)
  ak_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib' sl', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl' /\
      mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt /\ length sl' = length sl /\
      (forall j st, nth_error sl j = Some st -> st <> SIdle -> nth_error sl' j = Some st);
  (* [comment removed for export] *)
  ak_acct : (a_areas A = [] \/ 4 - nest_rank sc <= spare A) ->
    (a_areas A' = a_areas A /\ spare A - (4 - nest_rank sc) <= spare A') \/
    (a_areas A = [] /\ (exists pg, a_areas A' = [pg]) /\ 100 - (4 - nest_rank sc) <= spare A')
}.

(* [comment removed for export] *)
Record aslot_fail (A A' : astate) (sc : Z) (m0 : word -> option byte) : Prop := {
  af_keep : aslot_keep A A' sc m0;
  af_slots : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl;
  af_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl';
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  af_acct0 : (a_areas A' = a_areas A /\ spare A <= spare A') \/
             (spare A < 4 - nest_rank sc /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 100 <= spare A')
}.

(* [comment removed for export] *)
Record aslot_ok (A A' : astate) (sc req g idx : Z) (m0 : word -> option byte) (s' : mstate) : Prop := {
  ao_keep : aslot_keep A A' sc m0;
  (* [comment removed for export] *)
  ao_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl) \/
    x = g \/ (x <> g /\ mt_sc mt' < 48 /\ nest_rank sc < nest_rank (mt_sc mt'));
  (* [comment removed for export] *)
  ao_idle : forall mt aib sl, a_meta A g = Some mt -> mt_role mt = RGroup aib sl -> nth_error sl (Z.to_nat idx) = Some SIdle;
  (* [comment removed for export] *)
  ao_gfresh : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (forall mt aib sl, a_meta A g = Some mt -> mt_role mt <> RGroup aib sl) ->
    idx = 0 /\ sl' = STaken :: repeat SIdle (Z.to_nat (mt_last mt'));
  (* [comment removed for export] *)
  ao_nonest : 2032 < 16 * size_class sc -> forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' -> x <> g ->
    exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl;
  (* [comment removed for export] *)
  ao_single : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (forall mt aib sl, a_meta A g = Some mt -> mt_role mt <> RGroup aib sl) ->
    38 < sc -> sc mod 4 <> 3 -> usage_of A sc = 0 ->
    (16384 <= page_round_up_Z (req + 20) \/ page_round_up_Z (req + 20) < 16 * size_class sc + 16) ->
    mt_last mt' = 0 /\ 0 < mt_maplen mt' /\ mt_stride mt' + 16 = page_round_up_Z (req + 20);
  (* [comment removed for export] *)
  ao_zero : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    mt_stride mt' < 16 * size_class sc ->
    forall a : word, slot_start mt' 0 <= u a < slot_end mt' 0 -> ms_mem s' a = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  ao_acct1 : 2032 < 16 * size_class sc ->
    (a_areas A' = a_areas A /\ spare A - 1 <= spare A') \/
    (spare A < 4 - nest_rank sc /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 99 <= spare A')
}.

(* [comment removed for export] *)
Record aslot_vm (A : astate) (sc : Z) (s s' : mstate) : Prop := {
  av_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  av_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  av_budget : (a_areas A = [] \/ 4 - nest_rank sc <= spare A) ->
    vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + (4 - nest_rank sc) * 2^21
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition refusal (h : VmMaps) : Prop :=
  exists len, 0 < len <= 2^21 /\ forall a, mmap_grant_ok MMrw h a len = false.

(* [comment removed for export] *)
Definition aslot_noroom (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) : Prop :=
  (4 <= spare A -> refusal (ms_vm s)) /\
  (a_areas A = [] ->
     ~ (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
        (0 < a_ctx A KAac \/ exists a, grant_ok_na_vm (ms_vm s) a 8192 = true))
     \/ exists h2, am_delta (ms_vm s) h2 /\ refusal h2).

(* [comment removed for export] *)
Definition aslot_had_idle (A : astate) : Prop :=
  exists x mt aib sl j, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt < 48 /\ nth_error sl j = Some SIdle.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aslot_growS (sc : Z) (A A' : astate) (s s' : mstate) : Prop :=
  sgrow (5 - nest_rank sc) ((4 - nest_rank sc) * 8192 + grp_cap sc) (4 - nest_rank sc) A A' (ms_vm s) (ms_vm s') /\
  (* [comment removed for export] *)
  pgrow (acostS sc) A A' (ms_vm s) (ms_vm s').

(* [comment removed for export] *)
Definition aslot_noroomS (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (sc : Z) (A : astate) (s : mstate) : Prop :=
  snoroom sp0 argv envp cb (4 - nest_rank sc) ((4 - nest_rank sc) * 8192 + grp_cap sc) (4 - nest_rank sc) 0 (grp_cap sc) A s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition alloc_slot_specW : Prop :=
  forall (fuel : nat) (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (sc req : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    0 <= sc < 48 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
    4 - nest_rank sc <= Z.of_nat fuel ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_fail A A' sc (ms_mem s) -> aslot_vm A sc s s' ->
       (W = WOk -> aslot_noroom sp0 argv envp cb A s) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' -> (W <> WFail -> aslot_noroomS sp0 argv envp cb sc A s) ->
       tsall W (K wm1 s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (g idx : Z) mt aib slots,
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_ok A A' sc req g idx (ms_mem s) s' -> aslot_vm A sc s s' ->
       a_ctx A' (KActive sc) = g -> g = hd 0 (a_active A' sc) -> a_active A' sc <> [] ->
       a_meta A' g = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = sc ->
       0 <= idx <= mt_last mt -> nth_error slots (Z.to_nat idx) = Some STaken ->
       req + 4 <= mt_stride mt ->
       (16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (req + 20))) ->
       (W = WFail -> aslot_had_idle A) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' ->
       tsall W (K (Z_to_bv 64 idx) s') P) ->
    tsall W ((x <- m_alloc_slot fuel sp (Z_to_bv 64 sc) (Z_to_bv 64 req) ;; K x) s) P.

(* [comment removed for export] *)
Definition alloc_slot_spec : Prop :=
  forall (fuel : nat) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (sc req : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    0 <= sc < 48 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
    4 - nest_rank sc <= Z.of_nat fuel ->
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_fail A A' sc (ms_mem s) -> aslot_vm A sc s s' ->
       tsafe (K wm1 s') P) ->
    (forall s' A' (g idx : Z) mt aib slots,
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_ok A A' sc req g idx (ms_mem s) s' -> aslot_vm A sc s s' ->
       a_ctx A' (KActive sc) = g -> g = hd 0 (a_active A' sc) -> a_active A' sc <> [] ->
       a_meta A' g = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = sc ->
       0 <= idx <= mt_last mt -> nth_error slots (Z.to_nat idx) = Some STaken ->
       req + 4 <= mt_stride mt ->
       (16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (req + 20))) ->
       tsafe (K (Z_to_bv 64 idx) s') P) ->
    tsafe ((x <- m_alloc_slot fuel sp (Z_to_bv 64 sc) (Z_to_bv 64 req) ;; K x) s) P.

Lemma alloc_slot_spec_of_W : alloc_slot_specW -> alloc_slot_spec.
Proof.
  intros HW fuel R sp0 argv envp cb D A s sp sc req K P HII Hsc Hreq Hfit Hfuel HF HS.
  apply tsafe_of_tsall. apply (HW fuel WAll R sp0 argv envp cb D A s sp sc req K P HII Hsc Hreq Hfit Hfuel).
  - intros s' A' H1 H2 H3 H4 _ _ _. apply tsall_of_tsafe. exact (HF s' A' H1 H2 H3 H4).
  - intros s' A' g idx mt aib slots H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 _ _. apply tsall_of_tsafe.
    exact (HS s' A' g idx mt aib slots H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aslot_keep_refl : forall A sc m0, 0 <= nest_rank sc <= 3 -> aslot_keep A A sc m0.
Proof.
  intros A sc m0 Hr. constructor; auto.
  - intros x mt aib sl Hx Hr'. exists mt, aib, sl. repeat split; auto.
  - intros _. left. split; [reflexivity | lia].
Qed.

Lemma aslot_had_idle_transfer : forall A A',
  (forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
     exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl' /\ mt_w32 mt = mt_w32 mt') ->
  aslot_had_idle A' -> aslot_had_idle A.
Proof.
  intros A A' Hb (x & mt' & aib' & sl' & j & Hx & Hr & Hsc & Hj).
  destruct (Hb x mt' aib' sl' Hx Hr) as (mt & aib & Hx0 & Hr0 & Hw). exists x, mt, aib, sl', j.
  unfold mt_sc in *. rewrite Hw. auto.
Qed.

End WithLayout.
