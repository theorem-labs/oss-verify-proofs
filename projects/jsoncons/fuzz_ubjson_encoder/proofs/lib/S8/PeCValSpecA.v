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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVSA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation pm_scr := PMSPA.pm_scr.
Abbreviation cfg := (@PMSPA.cfg segs).

Definition validate_fun_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (p n sp r : Z) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n -> aacc M p n -> (forall a, p <= a < p + n -> ahid Aw model (Z_to_bv 64 a) = false /\ ahid Aw model (Z_to_bv 64 (S a)) = false) ->
    (n = 0 \/ sp <= p \/ p + n <= sp - pm_scr 0) ->
    PMSTA.base_okA segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (v : Z),
        regs_preserved R R' -> L5.frame_but [(sp - pm_scr 0, pm_scr 0)] M M' -> mem_grows M M' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
        getr R' 11%bv = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

Lemma scan_of_fun pc : validate_fun_spec pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (p n sp r : Z) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n -> aacc M p n -> (forall a, p <= a < p + n -> ahid Aw model (Z_to_bv 64 a) = false /\ ahid Aw model (Z_to_bv 64 (S a)) = false) ->
    (n = 0 \/ sp <= p \/ p + n <= sp - pm_scr 0) ->
    PMSTA.base_okA segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' -> L5.frame_but [(sp - pm_scr 0, pm_scr 0)] M M' -> mem_grows M M' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Proof.
  intros VF fx R M model K LB FF LK Aw cr p n sp r l H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 KONT.
  eapply (VF fx R M model K LB FF LK Aw cr p n sp r l); try eassumption.
  intros fx' R' M' model' v P1 P2 P3 P4 P5 P6 _ _ _. exact (KONT fx' R' M' model' P1 P2 P3 P4 P5 P6).
Qed.
End Specs.
End PECVSA.
