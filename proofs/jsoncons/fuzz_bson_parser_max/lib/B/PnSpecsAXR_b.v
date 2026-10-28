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

Module PNSAXR.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation bvec_at := (PNM.bvec_at segs PMSPA.accA PMSPA.annA).
Local Abbreviation BSZ := PNM.BSZ.

(* bvec_at M v b k stk without the end cell at v + 8. *)
Definition bvec_hole (M : word -> option byte) (v b k : Z) (stk : list PNM.bstate) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 16) (b + BSZ * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length stk) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (BSZ * 2 ^ k) /\ PMSPA.accA M b (BSZ * Z.of_nat (length stk))
  /\ PMSPA.annA M b (BSZ * Z.of_nat (length stk)) (BSZ * 2 ^ k)
  /\ (forall i, (i < length stk)%nat -> PNM.bstate_at segs M (b + BSZ * Z.of_nat i) (nth i stk PNM.bs_root)).

(* Entry of a push of a root state onto a vector v that has room (length stk < 2 ^ k): the function stores the
   new state at b + BSZ * length stk and the new end b + BSZ * (length stk + 1) at v + 8, and returns to r. *)
Definition push_root_fast_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PNM.bstate)
         (det : Z * Z * Z) (sp r : Z),
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    bvec_at M v b k stk -> Z.of_nat (length stk) < 2 ^ k ->
    PMSTA.base_okA segs A M ->
    PNSAX.cells_root segs ar FF sp v M R det ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        bvec_at M' v b k (stk ++ [PNSAX.mk_root det 0]) -> (v + 24 <= b \/ b + BSZ * 2 ^ k <= v) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA segs A M' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* Entry of a push of a root state onto an empty vector v (the cells at v, v + 8 and v + 16 hold 0): the function
   allocates a buffer b' of BSZ bytes, stores the new state at b' and returns to r with x10 = b' + BSZ, the new
   end, which the caller stores at v + 8. *)
Definition push_root_slow_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v : Z)
         (det : Z * Z * Z) (sp r : Z),
    ri_inv HI LBX FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    L5.u64_at segs M v 0 -> L5.u64_at segs M (v + 8) 0 -> L5.u64_at segs M (v + 16) 0 ->
    PMSTA.base_okA segs A M ->
    PNSAX.cells_root segs ar FF sp v M R det ->
    acredit_ok L cr BSZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (b' : Z),
        regs_preserved R R' ->
        getr R' 10%bv = Z_to_bv 64 (b' + BSZ) -> 4096 <= b' -> b' + BSZ < 2 ^ 47 ->
        bvec_hole M' v b' 0 [PNSAX.mk_root det 0] ->
        (v + 24 <= b' \/ b' + BSZ <= v) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA segs A M' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b' 0 ++ LBX) FF LK' (adebit L cr BSZ) Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition push_cont_slow_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PNM.bstate)
         (own : list (Z * Z)) (det : Z * Z) (sp r : Z),
    ri_inv HI (own ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PNSAX.vec_pre segs M v b k stk own -> PNSAX.dom_cont k stk own -> PNSAX.full_or_empty k stk own -> k <= 10 ->
    PMSTA.base_okA segs A M ->
    PNSAX.cells_cont segs ar FF sp v M R det ->
    acredit_ok L cr (BSZ * 2 ^ (PNSAX.k_next b k)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (b' lenv : Z),
        regs_preserved R R' -> 0 <= lenv < 2 ^ 64 ->
        getr R' 10%bv = Z_to_bv 64 (b' + BSZ * (Z.of_nat (length stk) + 1)) -> 4096 <= b' ->
        b' + BSZ * 2 ^ PNSAX.k_next b k < 2 ^ 47 ->
        bvec_at M' v b' (PNSAX.k_next b k) (stk ++ [PNSAX.mk_cont det lenv]) ->
        (v + 24 <= b' \/ b' + BSZ * 2 ^ PNSAX.k_next b k <= v) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA segs A M' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b' (PNSAX.k_next b k) ++ LBX) FF LK' (adebit L cr (BSZ * 2 ^ PNSAX.k_next b k)) Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

End Specs.
End PNSAXR.
