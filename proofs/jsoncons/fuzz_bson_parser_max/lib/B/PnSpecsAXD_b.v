(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceABx PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnStatics PnStaticsA PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSAXD.
(* [comment removed for export] *)
Lemma shadow6 (M : word -> option byte) (first : Z) : first mod 8 = 0 -> PMSPA.accA M first 48 -> shadow_zero M first 6.
Proof.
  intros F8 ACC j Hj. destruct (ACC (first + 8 * j + 7) ltac:(lia)) as [Z0 | (v & Bv & Hv & Hm)].
  - replace (S first + j) with (S (first + 8 * j + 7)); [exact Z0|]. unfold S.
    replace (first + 8 * j + 7) with (7 + (first / 8 + j) * 8) by (rewrite (Z.div_mod first 8) at 1 by lia; rewrite F8; lia).
    rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
  - exfalso. replace (first + 8 * j + 7) with (7 + (first / 8 + j) * 8) in Hm by (rewrite (Z.div_mod first 8) at 1 by lia; rewrite F8; lia).
    rewrite Z.mod_add in Hm by lia. change (7 mod 8) with 7 in Hm. lia.
Qed.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation accA := PMSPA.accA.
Local Abbreviation berr_ok := (PNSTA.berr_okA segs A AA AN).
Local Abbreviation entryA := (PMSPA.entryA A L ar).
Local Abbreviation aobjA := PMSPA.aobjA.
Local Abbreviation ffrsA := PMSPA.ffrsA.
Local Abbreviation pm_scr := PMSPA.pm_scr.
Local Abbreviation cfg := (@PMSP.cfg segs).
Local Abbreviation ffroomB := (PGSA.ffroomB PNRA.FCB).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dec128_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (first vp sp r : Z) (ax : PNST.bax),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 3 -> ffroomB 3 FF LK -> ffrsA FF sp -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 first -> getr R 11%bv = Z_to_bv 64 (first + 42) -> getr R 12%bv = Z_to_bv 64 vp ->
    (exists B m, In (B, m) LB /\ B <= first /\ first + 42 <= B + m) -> L5.defined M first 42 ->
    sp <= vp -> vp + 16 <= ar_sptop ar -> L5.defined M vp 16 -> accA M vp 16 -> first mod 8 = 0 -> accA M first 48 -> vp mod 8 = 0 ->
    PMSTA.base_okA segs A M -> berr_ok M ax ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (ptr : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> first <= ptr <= first + 42 ->
        L5.defined M' first 42 -> berr_ok M' (PNST.bax_add_dec ax) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 3) ((first, 42) :: (if PNST.bax_dec ax then [] else PNST.dec_W A AN)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_dec128 AN) M model) K.

End Specs.
End PNSAXD.
