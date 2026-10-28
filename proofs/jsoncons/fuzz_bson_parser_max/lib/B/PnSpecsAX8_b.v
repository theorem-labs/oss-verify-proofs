(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAX_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSAX8.
(* [comment removed for export] *)
Lemma ann_full_of_blk (M : word -> option byte) (b c : Z) : shadow_blk M b c -> PMSPA.annA M b c c.
Proof. intros (Z0 & P1). split; [exact Z0|]. split; [exact P1|]. intros j Hj. exfalso. lia. Qed.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation v8_at := (PGV8.v8_at segs PMSPA.accA PMSPA.annA).
Local Abbreviation v8_hdr := (PNSAX.v8_hdr segs).

Definition ann_increase_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v k : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 k -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_at M v x -> 0 <= k -> PGV8.v8_size x + k <= PGV8.v8_cap x ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        v8_hdr M' v x -> PMSPA.accA M' v 24 ->
        (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M' b (n + k) /\ PMSPA.annA M' b (n + k) c) ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition ann_new_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v sz : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 sz -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_hdr M v x -> PGV8.v8_size x = sz ->
    (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.annA M b c c) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> v8_at M' v x ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

End Specs.
End PNSAX8.
