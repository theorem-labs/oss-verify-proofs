(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSAXC.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation bvec_at := (PNM.bvec_at segs PMSPA.accA PMSPA.annA).
Local Abbreviation v8_at := (PGV8.v8_at segs PMSPA.accA PMSPA.annA).

(* Entry at pc with x10 = v, a vector of states: continues at r with no states in it; of the caller's cells only
   v + 8 changes. *)
Definition vec_clear_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PNM.bstate) (sp r : Z),
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    bvec_at M v b k stk -> PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> bvec_at M' v b k [] -> PMSPA.accA M' v 24 ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* Entry at pc with x10 = v, a byte vector x: continues at r with v holding v8_clear x and the block bytes unchanged;
   of the caller's cells only v + 8 changes. *)
Definition clear_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_at M v x ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> v8_at M' v (PGV8.v8_clear x) ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

End Specs.
End PNSAXC.
