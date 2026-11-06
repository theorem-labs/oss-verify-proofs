(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSinkA PeCModelA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECDTA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable P : PESKA.sink_policyA.

Abbreviation accA := PMSPA.accA.
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation cfg := (@PMSPA.cfg segs).

Definition sink_rest (k : PESK.sink) (LB : list (Z * Z)) : list (Z * Z) := if PESK.sk_c k =? 0 then LB else lb_remove (PESK.sk_b k) LB.
Definition estk_rest (en : PEC.enc) (LB : list (Z * Z)) : list (Z * Z) := if PEC.en_k en =? 0 then LB else lb_remove (PEC.en_b en) LB.

Definition tcell_ok (FF : list fframe) (M : word -> option byte) (sp t v : Z) : Prop :=
  t mod 8 = 0 /\ L5.defined M t 8 /\ accA M t 8 /\ L5.u64_at segs M t v /\ sp <= t /\ t + 8 <= ar_sptop ar.

Definition sink_dtor_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t o sp r : Z) (k : PESK.sink),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> tcell_ok FF M sp t o ->
    aobjA FF o 24 -> o mod 8 = 0 ->
    PESKA.sink_atA segs L ar P M o k -> incl (PESK.sink_own k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (sink_rest k LB) FF sp (PMSPA.pm_scr 1) [(o, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (sink_rest k LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

Definition estk_dtor_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t ov fb sp r : Z) (en : PEC.enc),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> tcell_ok FF M sp t (ov + 24) ->
    aobjA FF ov 56 -> ov mod 8 = 0 ->
    PECA.enc_atA segs E L ar M ov fb en -> incl (PEC.enc_own en) LB ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (estk_rest en LB) FF sp (PMSPA.pm_scr 1) [(ov + 24, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (estk_rest en LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.
End PECDTA.
