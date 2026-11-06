(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare HeapIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition debit_k (L : heap_layout) (cr : credit) : credit := (fst cr - hl_k_per_malloc L, snd cr).

(* [comment removed for export] *)
Definition malloc_x_spec_at (NB : Z) (L : heap_layout) (scfg : SpuriousCfg) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n < NB ->
    hl_k_per_malloc L <= fst cr ->
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
        hi_heap HI ((A, n) :: LB) (debit_k L cr) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition malloc_x_spec := malloc_x_spec_at (2 ^ 48).
