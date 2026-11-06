(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5DefsA L5CoreA
     PmLayout PmLayoutA PmModel PmSpecs PmSpecsA PeCLayout PeCSink PeCSinkA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PENTBB.
Section WithImage.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation sink_atA := (PESKA.sink_atA segs L ar).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation cfg := (@PMSPA.cfg segs).

(* [comment removed for export] *)
Definition ntb_specB (pc kb : Z) (P : PESKA.sink_policyA) : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (rr o sp r h : Z) (k : PESK.sink),
    ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryA R M sp r 2 -> PMSPA.ffroomA 2 FF LK -> PMSPA.ffrsA FF sp -> sp mod 32 = 0 ->
    getr R 11%bv = Z_to_bv 64 rr -> L5.u64_at segs M rr o -> rr mod 8 = 0 -> PMSPA.aobjA FF rr 8 -> PMSPA.accA M rr 8 ->
    (o + 24 <= rr \/ rr + 8 <= o) ->
    sink_atA P M o k -> PMSPA.aobjA FF o 24 -> o mod 8 = 0 ->
    PESKA.spa_hb P h -> PESK.sk_z k + kb <= h ->
    PMSP.credit_le (PESKA.spa_pot P (PESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (k' : PESK.sink),
        regs_preserved R R' -> PESK.sk_z k' = PESK.sk_z k + kb ->
        sink_atA P M' o k' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 2) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End WithImage.
End PENTBB.
