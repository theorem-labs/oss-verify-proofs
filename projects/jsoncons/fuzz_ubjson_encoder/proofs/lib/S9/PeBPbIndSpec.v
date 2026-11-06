(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCSinkA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEPBI.
Section WithImage.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Definition pvz_ok (FF : list fframe) (M : word -> option byte) (sp o pv : Z) : Prop :=
  L5.defined M pv 1 /\ (pv + 1 <= o \/ o + 24 <= pv)
  /\ ((sp <= pv /\ pv + 1 <= ar_sptop ar /\ byte_at M (HeapIfaceA.S pv) 0)
      \/ (exists base, PMSPA.aobjA FF base 8 /\ base mod 8 = 0 /\ base <= pv < base + 8 /\ PMSPA.accA M base 8)).

Definition push_back_indZ_specA (pc : Z) (P : PESKA.sink_policyA) : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (q rr o pv sp r : Z) (k : PESK.sink),
    ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 1 -> PMSPA.ffroomA 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 q -> getr R 11%bv = Z_to_bv 64 pv ->
    L5.u64_at segs M q rr -> rr mod 8 = 0 -> 0 < rr -> L5.u64_at segs M rr o -> 0 < o ->
    L5.defined M q 8 -> PMSPA.accA M q 8 -> PMSPA.aobjA FF q 8 -> q mod 8 = 0 ->
    PMSPA.aobjA FF rr 8 -> L5.defined M rr 8 -> PMSPA.accA M rr 8 ->
    PESKA.sink_atA segs L ar P M o k ->
    PMSPA.aobjA FF o 24 -> o mod 8 = 0 ->
    pvz_ok FF M sp o pv ->
    (PESK.sk_z k = PESK.sk_c k ->
        0 < PESK.cap_next (PESK.sk_c k) <= PESKA.spa_nmax P
        /\ acredit_ok L (PESKA.spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k))
        /\ PMSP.credit_le (PESKA.spa_pot P (PESK.cap_next (PESK.sk_c k))) (adebit L (PESKA.spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k)))) ->
    PMSP.credit_le (PESKA.spa_pot P (PESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        PESKA.sink_atA segs L ar P M' o (PESK.sk_push k b') ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c (PESK.sk_push k b'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own (PESK.sk_push k b') ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
End WithImage.
End PEPBI.
