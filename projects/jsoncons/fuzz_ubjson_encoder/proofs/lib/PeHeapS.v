(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Export HeIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEHS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable lim : Z.

Definition OPNEW_SCR : Z := 16 + 8224.
Definition OPDEL_SCR : Z := 8224.

(* [comment removed for export] *)
Definition opnewF_spec (NMAX : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> credit_okR cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition opnewS_spec (NMAX : Z) : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> 1 <= fst cr ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (fst cr - 1, snd cr) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition opdelS_spec_at (pc : Z) : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (B n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    In (B, n) LB -> getr R 10%bv = Z_to_bv 64 B ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove B LB) sp OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove B LB) (fst cr + 1, snd cr) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Definition opdelS_spec : Prop := opdelS_spec_at (pa_opdel A).
Definition opdelS_sized_spec : Prop := opdelS_spec_at (pa_opdel_sized A).
End Specs.
End PEHS.
