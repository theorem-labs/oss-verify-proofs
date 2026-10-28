(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Heap contract of the ubsan target at vm_limit = target_alloc_limit (2^39 = nbr_limit).
   At that limit no budget refusal is absorbed, so every allocation is paid in bytes: the small specs of
   HeapIface (malloc n <= 2^27, aligned_alloc16, free, free_null, frame, wf, perm) are kept as they are, and the
   big-allocation spec HeapIfaceX.malloc_x_spec (call-count debit only) is replaced by malloc_u_spec_at: the shape of
   HeapIface.malloc_spec with the size bound 2^27 replaced by NB (byte debit `debit L cr n`). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare HeapIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* Largest request of malloc_u_spec. The library's largest request is a sink-string regrow, at most
   2 * CL_u + 8 = 38,654,705,734 bytes with CL_u = 2^34 + 2^31 + 31. NBU is bounded above by the address-room
   argument of the heap instance: (K0U + NSEG + 1) mappings of up to NBU + overhead bytes each must fit below
   alloc_top >= 0x7fff7f800000 next to 2^39 live bytes. *)
Definition NBU : Z := 5 * 2 ^ 33.

(* Initial call credit (hl_K0) of the ubsan heap layout: 400 calls of KPM = 8 events. It also bounds the number of
   live mappings (count of vm_reserved ++ vm_maps <= K0U + NSEG), which the address-room argument needs. *)
Definition K0U : Z := 3200.

(* Global byte cap of the live heap mappings: live_bytes (vm_maps VM) + snd cr <= CAPG. The kernel's backing count
   covers only vm_maps (image segments and stack are not counted), so CAPG = nbr_limit = 2^39 fits
   target_alloc_limit. *)
Definition CAPG : Z := 2 ^ 39.

(* Initial byte credit (hl_B0) of the ubsan heap layout: all of CAPG (vm_maps = [] at init_vm). *)
Definition B0U : Z := 2 ^ 39.

Section IfaceU.
Variable L : heap_layout.
Variable scfg : SpuriousCfg.
Variable HI : heap_iface.

(* Big allocation with byte debit: malloc_spec with `0 < n <= 2 ^ 27` replaced by `0 < n <= NB`. *)
Definition malloc_u_spec_at (NB : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NB ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition malloc_u_spec : Prop := malloc_u_spec_at NBU.

(* The small spec is the case n <= 2^27 of the big one. *)
Lemma malloc_spec_of_u : forall NB, 2 ^ 27 <= NB -> malloc_u_spec_at NB -> malloc_spec L scfg HI.
Proof.
  intros NB HNB MU fx R M model LB cr n K Hh H1 H2 H3 Hn Hnr Hcr Htp Hra Hsk HK0 CONT.
  exact (MU fx R M model LB cr n K Hh H1 H2 H3 Hn ltac:(lia) Hcr Htp Hra Hsk HK0 CONT).
Qed.

(* Everything the ubsan library needs from the heap. *)
Record heap_iface_u_ok : Prop := HIUOK {
  hiu_ok : heap_iface_ok L scfg HI;
  hiu_malloc_u : malloc_u_spec
}.

End IfaceU.
