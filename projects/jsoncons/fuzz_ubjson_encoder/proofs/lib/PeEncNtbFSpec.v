(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface L5Defs L5Core PmLayout PmModel PmSpecs PeCLayout PeCSink.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PENTBF.
Section WithImage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
Abbreviation sink_at := (PESK.sink_at segs L acc ann).

(* [comment removed for export] *)
Definition ntbf_spec (pc kb : Z) (P : PESK.sink_policy) : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (rr o sp r h : Z) (k : PESK.sink),
    hi_heap HI (PESK.sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    PMSP.entry A L R M sp r 2 ->
    getr R 10%bv = Z_to_bv 64 rr -> L5.u64_at segs M rr o -> rr mod 8 = 0 -> sp <= rr -> rr + 8 <= hl_sptop L ->
    (o + 24 <= rr \/ rr + 8 <= o) ->
    sink_at P M o k -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PESK.sp_hb P h -> PESK.sk_z k + kb <= h ->
    PMSP.credit_le (PESK.sink_pot P (PESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (k' : PESK.sink),
        regs_preserved R R' -> PESK.sk_z k' = PESK.sk_z k + kb ->
        sink_at P M' o k' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 2) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PESK.sink_pot P (PESK.sk_c k)) (PESK.sink_pot P (PESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (PESK.sink_own k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
End WithImage.
End PENTBF.
