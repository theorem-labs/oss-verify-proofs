(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan AsanUbsan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8.
Module PnATsSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition NANOS : Z := 1000000000.
(* [comment removed for export] *)
Definition MULU_A : Z := 0xcce0c.
Definition ADDU64_A : Z := 0xc99fc.
Definition WRS_A : Z := 0xd3d10.
Definition MULU_B : Z := 0xcae8c.
Definition ADDU64_B : Z := 0xcb924.
Definition WRS_B : Z := 0xc7b0c.
(* [comment removed for export] *)
Definition MULU_H : Z := 4.
Definition ADD_H : Z := 5.
Definition WRS_H : Z := 6.

(* [comment removed for export] *)
Definition wlen (v0 v1 : Z) : nat := if Z.eqb v1 0 then (if Z.eqb v0 0 then 0%nat else 1%nat) else 2%nat.
Definition wfb (fb v0 v1 : Z) : Z := if (Z.eqb v0 0 && Z.eqb v1 0)%bool then Z.land fb 253 else fb.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation HV := (PMSPA.HV L ar).

(* [comment removed for export] *)
Definition binl_at (M : word -> option byte) (o fb : Z) (len : nat) (v0 v1 : Z) : Prop :=
  L5.big_at segs M o (L5.BO fb len (L5.BInl v0 v1)) /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64.

(* [comment removed for export] *)
Definition mulu_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (v0 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 NANOS ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 0 -> (len <= 1)%nat -> (len = 0%nat -> v0 = 0) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (lo hi : Z),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        lo + 2 ^ 64 * hi = v0 * NANOS -> binl_at M' o (wfb fb lo hi) (wlen lo hi) lo hi ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition add64_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o y fb : Z) (len : nat) (v0 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 y -> 0 <= y -> v0 + y < 2 ^ 64 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 0 -> (len <= 1)%nat -> (len = 0%nat -> v0 = 0) -> Z.testbit fb 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        binl_at M' o fb (wlen (v0 + y) 0) (v0 + y) 0 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition ws1_postA (len : nat) (x x' : PM.vstr) : Prop :=
  match x, x' with
  | PM.VShort _, PM.VShort _ => len = 0%nat
  | PM.VShort _, PM.VLong c' _ _ => (1 <= len)%nat /\ c' = 26
  | PM.VLong c _ p, PM.VLong c' _ p' => c' = c /\ p' = p
  | PM.VLong _ _ _, PM.VShort _ => False
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ts_text (M : word -> option byte) (ot : Z) (x : PM.vstr) : Prop :=
  exists bs, L5.bytes_at segs M (PM.vs_data ot x) bs /\ Z.of_nat (length bs) = PM.vs_size x /\ Forall (fun b => b = 45 \/ 48 <= b <= 57) bs.
Definition ws1_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o ot fb : Z) (len : nat) (v0 : Z) (x : PM.vstr),
    ri_inv HI (PM.vs_own x ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 ot ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> binl_at M o fb len v0 0 -> len = wlen v0 0 ->
    PMSPA.aobjA FF ot 24 -> ot mod 8 = 0 -> (o + 32 <= ot \/ ot + 24 <= o) ->
    PM.vstr_at segs PMSPA.accA M ot x -> PM.vs_size x = 0 ->
    PMSTA.base_okA segs A M ->
    PMSP.credit_le (PMSPA.scA L (PQMA.pot_textM HV x)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (x' : PM.vstr) (cr' : credit),
        regs_preserved R R' ->
        PM.vstr_at segs PMSPA.accA M' ot x' -> 1 <= PM.vs_size x' <= 21 -> ts_text M' ot x' -> ws1_postA len x x' ->   (* [comment removed for export] *)
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(ot, 24)] M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_textM HV x)) (PMSPA.scA L (PQMA.pot_textM HV x')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vs_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.
End PQATSS.

(* [comment removed for export] *)
Module PQATSSa.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition mulu_spec : Prop := PQATSS.mulu_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS.MULU_A PQATSS.MULU_H.
Definition add64_spec : Prop := PQATSS.add64_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS.ADDU64_A PQATSS.ADD_H.
Definition ws1_spec : Prop := PQATSS.ws1_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS.WRS_A PQATSS.WRS_H.
End Names.
End PQATSSa.

(* [comment removed for export] *)
Module PQATSSb.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition mulu_spec : Prop := PQATSS.mulu_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS.MULU_B PQATSS.MULU_H.
Definition add64_spec : Prop := PQATSS.add64_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS.ADDU64_B PQATSS.ADD_H.
Definition ws1_spec : Prop := PQATSS.ws1_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS.WRS_B PQATSS.WRS_H.
End Names.
End PQATSSb.

End PnATsSpecs.
Module PnATsCone.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSC.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Definition RESERVE_A : Z := 0xca420.
Definition RESIZE_A : Z := 0xca024.
Definition REDUCE_A : Z := 0xcad98.
Definition COPYD_A : Z := 0xcc9d8.
Definition COPYW_A : Z := 0xcb6a0.
Definition CMP_A : Z := 0xcc1d8.
Definition ASSIGN_A : Z := 0xc9ea4.
(* [comment removed for export] *)
Definition RSV_H : Z := 2.
Definition RZ_H : Z := 3.
Definition RED_H : Z := 3.
Definition CPY_H : Z := 3.
Definition CMP_H : Z := 3.
Definition ASG_H : Z := 4.
Definition DIVIDE_A : Z := 0xc799c.
Definition DIV_H : Z := 5.
Definition TEN19 : Z := 10000000000000000000.
(* [comment removed for export] *)
Definition dv_ql (v0 : Z) : nat := if Z.eqb (v0 / TEN19) 0 then 0%nat else 1%nat.
Definition dv_q0 (v0 : Z) : Z := if Z.eqb (v0 / TEN19) 0 then v0 else v0 / TEN19.
Definition dv_rl (v0 : Z) : nat := if Z.eqb (v0 mod TEN19) 0 then 0%nat else 1%nat.
Definition dv_r0 (v0 r0 : Z) : Z := if Z.eqb (v0 mod TEN19) 0 then r0 else v0 mod TEN19.
Definition dv_r1 (v0 r1 : Z) (lenr : nat) : Z := if Z.eqb (v0 mod TEN19) 0 then r1 else if Nat.eqb lenr 0 then 0 else r1.
(* [comment removed for export] *)
Definition cmp3 (x0 y0 : Z) : Z := if x0 <? y0 then 18446744073709551615 else if y0 <? x0 then 1 else 0.
(* [comment removed for export] *)
Definition asg_fb (fb fbs : Z) (lens : nat) : Z := if Nat.eqb lens 0 then fb else Z.lor (Z.land fbs 2) (Z.land fb 253).
Definition asg_w0 (d0 s0 : Z) (lens : nat) : Z := if Nat.eqb lens 0 then d0 else s0.
Definition asg_w1 (d1 : Z) (lend lens : nat) : Z := if Nat.eqb lens 0 then d1 else if Nat.eqb lend 0 then 0 else d1.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition reserveI_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= 2 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' o fb len v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition resizeI_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> Z.of_nat len < n <= 2 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' o fb (Z.to_nat n) (if Nat.eqb len 0 then 0 else v0) 0 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition reduce_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 -> (len = 2%nat \/ (len = 1%nat /\ v1 = 0)) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        binl_at M' o (PQATSS.wfb fb v0 v1) (PQATSS.wlen v0 v1) v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
(* [comment removed for export] *)
Definition resizeL_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= Z.of_nat len -> (len <= 1)%nat ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' o fb (Z.to_nat n) v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition copyI_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    PMSPA.aobjA FF d 32 -> d mod 8 = 0 -> PMSPA.accA M d 32 ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> binl_at M s fb len v0 v1 ->
    (d + 32 <= s \/ s + 32 <= d) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (fb' : Z),
        regs_preserved R R' ->
        binl_at M' d fb' len v0 v1 -> Z.land fb' 2 = Z.land fb 2 -> binl_at M' s fb len v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition cmp11_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r x y fbx fby : Z) (x0 x1 y0 y1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 x -> getr R (reg 11) = Z_to_bv 64 y ->
    PMSPA.aobjA FF x 32 -> x mod 8 = 0 -> PMSPA.accA M x 32 -> binl_at M x fbx 1%nat x0 x1 -> Z.testbit fbx 1 = false ->
    PMSPA.aobjA FF y 32 -> y mod 8 = 0 -> PMSPA.accA M y 32 -> binl_at M y fby 1%nat y0 y1 -> Z.testbit fby 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 (cmp3 x0 y0) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition assignI_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb fbs : Z) (lend lens : nat) (d0 d1 s0 s1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    PMSPA.aobjA FF d 32 -> d mod 8 = 0 -> PMSPA.accA M d 32 -> binl_at M d fb lend d0 d1 -> (lend <= 1)%nat ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> binl_at M s fbs lens s0 s1 -> (lens <= 1)%nat ->
    (d + 32 <= s \/ s + 32 <= d) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d ->
        binl_at M' d (asg_fb fb fbs lens) lens (asg_w0 d0 s0 lens) (asg_w1 d1 lend lens) -> binl_at M' s fbs lens s0 s1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
(* [comment removed for export] *)
Definition copyS_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    PMSPA.aobjA FF d 32 -> d mod 8 = 0 -> PMSPA.accA M d 32 ->
    sp <= s -> s + 32 <= ar_sptop ar -> s mod 8 = 0 -> shadow_zero M s 4 -> binl_at M s fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (fb' : Z),
        regs_preserved R R' ->
        binl_at M' d fb' len v0 v1 -> Z.land fb' 2 = Z.land fb 2 -> binl_at M' s fb len v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition divide1_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o dn rr fb fbd fbr : Z) (lenr : nat) (v0 v1 d1 r0 r1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 o -> getr R (reg 13) = Z_to_bv 64 rr ->
    getr R (reg 14) = Z_to_bv 64 1 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> binl_at M o fb 1%nat v0 v1 -> 1 <= v0 ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr lenr r0 r1 -> (lenr <= 1)%nat ->
    (o + 32 <= rr \/ rr + 32 <= o) ->
    sp <= dn -> dn + 32 <= ar_sptop ar -> dn mod 8 = 0 -> shadow_zero M dn 4 -> binl_at M dn fbd 1%nat TEN19 d1 -> Z.testbit fbd 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (fbq fbr' : Z),
        regs_preserved R R' ->
        binl_at M' o fbq (dv_ql v0) (dv_q0 v0) v1 -> Z.land fbq 2 = Z.land fb 2 ->
        binl_at M' rr fbr' (dv_rl v0) (dv_r0 v0 r0) (dv_r1 v0 r1 lenr) -> Z.land fbr' 2 = Z.land fb 2 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32); (rr, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.
End PQATSC.

(* [comment removed for export] *)
Module PQATSCa.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition reserveI_spec : Prop := PQATSC.reserveI_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESERVE_A PQATSC.RSV_H.
Definition resizeI_spec : Prop := PQATSC.resizeI_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESIZE_A PQATSC.RZ_H.
Definition reduce_spec : Prop := PQATSC.reduce_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.REDUCE_A PQATSC.RED_H.
Definition resizeL_spec : Prop := PQATSC.resizeL_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESIZE_A PQATSC.RZ_H.
Definition copyD_spec : Prop := PQATSC.copyI_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.COPYD_A PQATSC.CPY_H.
Definition copyW_spec : Prop := PQATSC.copyI_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.COPYW_A PQATSC.CPY_H.
Definition cmp11_spec : Prop := PQATSC.cmp11_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.CMP_A PQATSC.CMP_H.
Definition assignI_spec : Prop := PQATSC.assignI_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.ASSIGN_A PQATSC.ASG_H.
Definition copyS_spec : Prop := PQATSC.copyS_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.COPYD_A PQATSC.CPY_H.
Definition divide1_spec : Prop := PQATSC.divide1_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.DIVIDE_A PQATSC.DIV_H.
End Names.
End PQATSCa.

End PnATsCone.
Module PnATs12Specs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PQATSG.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Definition RZ_A : Z := 0xca024.       (* [comment removed for export] *)
Definition RSV_A : Z := 0xca420.      (* [comment removed for export] *)
Definition ARSV_A : Z := 0xca674.     (* [comment removed for export] *)
Definition RUP_A : Z := 0xcaa84.      (* [comment removed for export] *)
Definition RED_A : Z := 0xcad98.      (* [comment removed for export] *)
Definition CMP_A : Z := 0xcc1d8.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPNEW_RA_A : Z := 0x14f7bc.
Definition OPNEW_RA_B : Z := 0x15439c.
(* [comment removed for export] *)
Definition RZ3_H : Z := 4.
Definition RSV3_H : Z := 3.
Definition ARSV_H : Z := 2.
Definition RUP_H : Z := 1.
Definition CMPX_H : Z := 1.

(* [comment removed for export] *)
Definition GKEYS (LR : HAR.layoutR) (gra : Z) : list (list Z) := [HAR.akey (HAR.hlr_pc_malloc LR) [gra]; [HAR.hlr_pc_malloc LR]].
(* [comment removed for export] *)
Definition gcost (L : asan_layout) (warm : bool) (n : Z) : credit :=
  if warm then (1, 0) else (hl_k_per_malloc L, hl_b_lin L * n + hl_b_overhead L).
Definition gcostD (L : asan_layout) (gk : list Z) (D : list (list Z)) (n : Z) : credit := gcost L (HAR.warm_ok gk D n) n.
(* [comment removed for export] *)
Definition gpre (L : asan_layout) (LR : HAR.layoutR) (gra : Z) (D : list (list Z)) (n : Z) (cr : credit) : Prop :=
  forall gk, In gk (GKEYS LR gra) -> PMSP.credit_le (gcostD L gk D n) cr.

(* [comment removed for export] *)
Definition cmpx0v (fbx : Z) (lenx : nat) : Z := if Nat.eqb lenx 0%nat then 0 else if Z.testbit fbx 1 then 2 ^ 64 - 1 else 1.

(* [comment removed for export] *)
Inductive wsh : Type := WInl (fb : Z) (len : nat) (v0 v1 : Z) | WDyn (fb p : Z) (v0 v1 : Z).
Definition ws_len (h : wsh) : nat := match h with WInl _ len _ _ => len | WDyn _ _ _ _ => 2%nat end.
Definition ws_own (h : wsh) : list (Z * Z) := match h with WInl _ _ _ _ => [] | WDyn _ p _ _ => [(p, 64)] end.
Definition ws_this_atA (segs : list Segment) (M : word -> option byte) (o : Z) (h : wsh) : Prop :=
  match h with
  | WInl fb len v0 v1 => PQATSS.binl_at segs M o fb len v0 v1 /\ len = PQATSS.wlen v0 v1 /\ (len = 2%nat -> 1 <= v1 <= 2 ^ 30)
  | WDyn fb p v0 v1 => L5.big_at segs M o (L5.BO fb 2%nat (L5.BDyn 8 p)) /\ p mod 16 = 0
                       /\ L5.u64_at segs M p v0 /\ L5.u64_at segs M (p + 8) v1 /\ 0 <= v0 < 2 ^ 64 /\ 1 <= v1 <= 2 ^ 30
                       /\ L5.defined M p 64 /\ PMSPA.accA M p 64
  end.

Section Std.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition roundup_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r i : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 i -> 0 <= i < 2 ^ 60 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 (8 * (i / 8) + 8) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition reduceD32_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb p w0 w1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    L5.big_at segs M o (L5.BO fb 3%nat (L5.BDyn 8 p)) -> In (p, 64) LB -> PMSPA.accA M p 64 -> L5.defined M p 64 ->
    L5.u64_at segs M p w0 -> L5.u64_at segs M (p + 8) w1 -> L5.u64_at segs M (p + 16) 0 -> 0 <= w0 < 2 ^ 64 -> 1 <= w1 < 2 ^ 64 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        L5.big_at segs M' o (L5.BO fb 2%nat (L5.BDyn 8 p)) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition cmpx0_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r x y fbx fby : Z) (lenx : nat) (x0 x1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 x -> getr R (reg 11) = Z_to_bv 64 y ->
    PMSPA.aobjA FF x 32 -> x mod 8 = 0 -> PMSPA.accA M x 32 -> binl_at M x fbx lenx x0 x1 ->
    PMSPA.aobjA FF y 32 -> y mod 8 = 0 -> PMSPA.accA M y 32 -> binl_at M y fby 0%nat 0 0 -> Z.testbit fby 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 (cmpx0v fbx lenx) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Std.

Section Fam.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HIk : list (list Z) -> asan_iface.
Variable LR : HAR.layoutR.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition opnewU_specF (gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (n sp r : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    getr R (reg 10) = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    gpre L LR gra D n cr ->
    getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) -> L5CA.astk ar M sp PMSPA.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (Aw' : list (Z * Z)) (cr' : credit) (q : Z) (gk : list Z),
        getr R' (reg 10) = Z_to_bv 64 q -> regs_preserved R R' -> In gk (GKEYS LR gra) ->
        L5CA.afresh L ar LB (FF ++ LK) M' q n ->
        L5CA.ahpres L ar LB FF sp PMSPA.OPNEW_SCR [] M M' ->
        PMSP.credit_keep cr cr' (gcostD L gk D n) PMSP.cr0 ->
        model_rt model model' -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) ((q, n) :: LB) FF LK cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition areserve3_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb1 : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 3 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    L5.u8_at segs M o fb1 -> 0 <= fb1 < 256 -> L5.u64_at segs M (o + 8) 0 -> L5.u64_at segs M (o + 16) 0 -> L5.u64_at segs M (o + 24) 0 ->
    PMSTA.base_okA segs A M ->
    gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (p : Z) (gk : list Z),
        regs_preserved R R' -> In gk (GKEYS LR gra) ->
        L5.u64_at segs M' (o + 16) 8 -> L5.u64_at segs M' (o + 24) p ->
        L5CA.afresh L ar LB (FF ++ LK') M' p 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o + 16, 16)] M M' ->
        PMSP.credit_keep cr cr' (gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) ((p, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition reserve3_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb v0 v1 : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 3 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> binl_at M o fb 2%nat v0 v1 ->
    PMSTA.base_okA segs A M ->
    gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (p : Z) (gk : list Z),
        regs_preserved R R' -> In gk (GKEYS LR gra) ->
        L5.big_at segs M' o (L5.BO (Z.lor fb 1) 2%nat (L5.BDyn 8 p)) -> L5.u64_at segs M' p v0 -> L5.u64_at segs M' (p + 8) v1 ->
        L5CA.afresh L ar LB (FF ++ LK') M' p 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        PMSP.credit_keep cr cr' (gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) ((p, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition resize3_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb v0 v1 : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 3 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> binl_at M o fb 2%nat v0 v1 ->
    PMSTA.base_okA segs A M ->
    gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (p : Z) (gk : list Z),
        regs_preserved R R' -> In gk (GKEYS LR gra) ->
        L5.big_at segs M' o (L5.BO (Z.lor fb 1) 3%nat (L5.BDyn 8 p)) ->
        L5.u64_at segs M' p v0 -> L5.u64_at segs M' (p + 8) v1 -> L5.u64_at segs M' (p + 16) 0 ->
        L5CA.afresh L ar LB (FF ++ LK') M' p 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        PMSP.credit_keep cr cr' (gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) ((p, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Fam.
End PQATSG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PQATSS2.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Definition LT0_A : Z := 0xd4448.
Definition ADDU2_A : Z := 0xd4678.
Definition SUB_A : Z := 0xcaed8.
Definition LT0_B : Z := 0xc81d8.
Definition ADDU2_B : Z := 0xcc4e0.
Definition SUB_B : Z := 0xc8418.
Definition LT0_H : Z := 2.
Definition ADD2_H : Z := 5.
Definition SUB_H : Z := 6.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).
Abbreviation ws_this_atA := (PQATSG.ws_this_atA segs).

(* [comment removed for export] *)
Definition lt0_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 0 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 -> (len = 0%nat -> Z.testbit fb 1 = false) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 (Z.b2z (Z.testbit fb 1)) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition addu21_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o y fb : Z) (len : nat) (v0 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 0 -> len = PQATSS.wlen v0 0 -> Z.testbit fb 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (lo hi : Z),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        lo + 2 ^ 64 * hi = v0 + y mod 2 ^ 32 -> ws_this_atA M' o (PQATSG.WInl fb (PQATSS.wlen lo hi) lo hi) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition subbig1_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o o2 fbx fby : Z) (leny : nat) (x0 y0 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 o2 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> PMSPA.aobjA FF o2 32 -> o2 mod 8 = 0 -> PMSPA.accA M o2 32 -> (o + 32 <= o2 \/ o2 + 32 <= o) ->
    binl_at M o fbx 1%nat x0 0 -> 1 <= x0 -> Z.testbit fbx 1 = true ->
    binl_at M o2 fby leny y0 0 -> leny = PQATSS.wlen y0 0 -> Z.testbit fby 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (lo hi : Z),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        lo + 2 ^ 64 * hi = x0 + y0 -> ws_this_atA M' o (PQATSG.WInl fbx (PQATSS.wlen lo hi) lo hi) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.

Section Fam.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HIk : list (list Z) -> asan_iface.
Variable LR : HAR.layoutR.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).
Abbreviation ws_this_atA := (PQATSG.ws_this_atA segs).

(* [comment removed for export] *)
Definition addu22_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o y fb v0 v1 : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    ws_this_atA M o (PQATSG.WInl fb 2%nat v0 v1) -> Z.testbit fb 1 = false -> v0 + 2 ^ 64 * v1 + y mod 2 ^ 32 < 2 ^ 94 ->
    PMSTA.base_okA segs A M ->
    PQATSG.gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (p lo hi : Z) (gk : list Z),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o -> In gk (PQATSG.GKEYS LR gra) ->
        lo + 2 ^ 64 * hi = v0 + 2 ^ 64 * v1 + y mod 2 ^ 32 -> ws_this_atA M' o (PQATSG.WDyn (Z.lor fb 1) p lo hi) ->
        L5CA.afresh L ar LB (FF ++ LK') M' p 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        PMSP.credit_keep cr cr' (PQATSG.gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) (PQATSG.ws_own (PQATSG.WDyn (Z.lor fb 1) p lo hi) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition subbig2_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o o2 fbx fby : Z) (leny : nat) (x0 x1 y0 : Z)
         (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 o2 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> PMSPA.aobjA FF o2 32 -> o2 mod 8 = 0 -> PMSPA.accA M o2 32 -> (o + 32 <= o2 \/ o2 + 32 <= o) ->
    ws_this_atA M o (PQATSG.WInl fbx 2%nat x0 x1) -> Z.testbit fbx 1 = true ->
    binl_at M o2 fby leny y0 0 -> leny = PQATSS.wlen y0 0 -> Z.testbit fby 1 = false -> x0 + 2 ^ 64 * x1 + y0 < 2 ^ 94 ->
    PMSTA.base_okA segs A M ->
    PQATSG.gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (p lo hi : Z) (gk : list Z),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o -> In gk (PQATSG.GKEYS LR gra) ->
        lo + 2 ^ 64 * hi = x0 + 2 ^ 64 * x1 + y0 -> ws_this_atA M' o (PQATSG.WDyn (Z.lor fbx 1) p lo hi) ->
        L5CA.afresh L ar LB (FF ++ LK') M' p 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        PMSP.credit_keep cr cr' (PQATSG.gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) (PQATSG.ws_own (PQATSG.WDyn (Z.lor fbx 1) p lo hi) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Fam.
End PQATSS2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PQATSGa.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (LR : HAR.layoutR).
Definition GKEYS : list (list Z) := PQATSG.GKEYS LR PQATSG.OPNEW_RA_A.
Definition roundup_spec : Prop := PQATSG.roundup_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSG.RUP_A PQATSG.RUP_H.
Definition reduceD32_spec : Prop := PQATSG.reduceD32_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSG.RED_A PQATSC.RED_H.
Definition cmpx0_spec : Prop := PQATSG.cmpx0_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSG.CMP_A PQATSG.CMPX_H.
Definition opnewU_spec : Prop := PQATSG.opnewU_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSG.OPNEW_RA_A.
Definition areserve3_spec : Prop := PQATSG.areserve3_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSG.ARSV_A PQATSG.ARSV_H PQATSG.OPNEW_RA_A.
Definition reserve3_spec : Prop := PQATSG.reserve3_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSG.RSV_A PQATSG.RSV3_H PQATSG.OPNEW_RA_A.
Definition resize3_spec : Prop := PQATSG.resize3_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSG.RZ_A PQATSG.RZ3_H PQATSG.OPNEW_RA_A.
End Names.
End PQATSGa.

Module PQATSS2a.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (LR : HAR.layoutR).
Definition lt0_spec : Prop := PQATSS2.lt0_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS2.LT0_A PQATSS2.LT0_H.
Definition addu21_spec : Prop := PQATSS2.addu21_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS2.ADDU2_A PQATSS2.ADD2_H.
Definition subbig1_spec : Prop := PQATSS2.subbig1_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS2.SUB_A PQATSS2.SUB_H.
Definition addu22_spec : Prop := PQATSS2.addu22_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSS2.ADDU2_A PQATSS2.ADD2_H PQATSG.OPNEW_RA_A.
Definition subbig2_spec : Prop := PQATSS2.subbig2_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSS2.SUB_A PQATSS2.SUB_H PQATSG.OPNEW_RA_A.
End Names.
End PQATSS2a.

(* [comment removed for export] *)
Module PQATSS2b.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (LR : HAR.layoutR).
Definition lt0_spec : Prop := PQATSS2.lt0_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS2.LT0_B PQATSS2.LT0_H.
Definition addu21_spec : Prop := PQATSS2.addu21_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS2.ADDU2_B PQATSS2.ADD2_H.
Definition subbig1_spec : Prop := PQATSS2.subbig1_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS2.SUB_B PQATSS2.SUB_H.
Definition addu22_spec : Prop := PQATSS2.addu22_specF RSEGS PnLayoutA.ADDR_B L ar HIk LR PQATSS2.ADDU2_B PQATSS2.ADD2_H PQATSG.OPNEW_RA_B.
Definition subbig2_spec : Prop := PQATSS2.subbig2_specF RSEGS PnLayoutA.ADDR_B L ar HIk LR PQATSS2.SUB_B PQATSS2.SUB_H PQATSG.OPNEW_RA_B.
End Names.
End PQATSS2b.

End PnATs12Specs.
Module PnATs12SpecsW2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12Specs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSW2.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition WRS2_H : Z := 6.
Definition TEN19 : Z := PQATSC.TEN19.

(* [comment removed for export] *)
Definition bdyn_at (segs : list Segment) (M : word -> option byte) (s fb : Z) (len : nat) (p v0 v1 : Z) : Prop :=
  L5.big_at segs M s (L5.BO fb len (L5.BDyn 8 p)) /\ p mod 16 = 0 /\ L5.u64_at segs M p v0 /\ L5.u64_at segs M (p + 8) v1
  /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 /\ L5.defined M p 64 /\ PMSPA.accA M p 64.

(* [comment removed for export] *)
Definition ws2_postL (x x' : PM.vstr) : Prop :=
  match x, x' with
  | PM.VShort _, PM.VLong c' _ _ => c' = 48
  | PM.VLong c _ p, PM.VLong c' _ p' => (45 <= c /\ c' = c /\ p' = p) \/ (c <= 44 /\ c' = 48)
  | _, PM.VShort _ => False
  end.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition ws2i_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o ot fb : Z) (v0 v1 : Z) (x : PM.vstr),
    ri_inv HI (PM.vs_own x ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 ot ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> PQATSG.ws_this_atA segs M o (PQATSG.WInl fb 2%nat v0 v1) ->
    PMSPA.aobjA FF ot 24 -> ot mod 8 = 0 -> (o + 32 <= ot \/ ot + 24 <= o) ->
    PM.vstr_at segs PMSPA.accA M ot x -> PM.vs_size x = 0 ->
    PMSTA.base_okA segs A M ->
    PMSP.credit_le (PMSPA.scA L (PQMA.pot_textM HV x)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (x' : PM.vstr) (cr' : credit),
        regs_preserved R R' ->
        PM.vstr_at segs PMSPA.accA M' ot x' -> 1 <= PM.vs_size x' <= 30 -> PQATSS.ts_text segs M' ot x' -> ws2_postL x x' ->   (* [comment removed for export] *)
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(ot, 24)] M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_textM HV x)) (PMSPA.scA L (PQMA.pot_textM HV x')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vs_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition divide2i_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o dn rr fb fbd fbr : Z) (lenr : nat) (v0 v1 d1 r0 r1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 o -> getr R (reg 13) = Z_to_bv 64 rr ->
    getr R (reg 14) = Z_to_bv 64 1 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> binl_at M o fb 2%nat v0 v1 -> 1 <= v1 <= 2 ^ 30 ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr lenr r0 r1 -> (lenr <= 1)%nat ->
    (o + 32 <= rr \/ rr + 32 <= o) ->
    sp <= dn -> dn + 32 <= ar_sptop ar -> dn mod 8 = 0 -> shadow_zero M dn 4 -> binl_at M dn fbd 1%nat TEN19 d1 -> Z.testbit fbd 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (fbq fbr' : Z),
        regs_preserved R R' ->
        binl_at M' o fbq 1%nat ((v0 + 2 ^ 64 * v1) / TEN19) v1 -> Z.land fbq 2 = Z.land fb 2 ->
        binl_at M' rr fbr' (PQATSS.wlen ((v0 + 2 ^ 64 * v1) mod TEN19) 0) ((v0 + 2 ^ 64 * v1) mod TEN19) 0 -> Z.land fbr' 2 = Z.land fb 2 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32); (rr, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.

Section Fam.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HIk : list (list Z) -> asan_iface.
(* [comment removed for export] *)
Variable tsw : list (list Z) -> Z -> Z -> list Z -> credit.
Variable tdv2 : list (list Z) -> Z -> Z -> list Z -> credit.
Variable tdv1 : list (list Z) -> Z -> Z -> list Z -> credit.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition ws2d_specF (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o ot fb p : Z) (v0 v1 : Z) (x : PM.vstr)
         (D : list (list Z)) (RC : list Z),
    ri_inv (HIk D) (PM.vs_own x ++ PQATSG.ws_own (PQATSG.WDyn fb p v0 v1) ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    HAR.rchain L ar M sp (bv_unsigned (getr R (reg 8))) RC -> bv_unsigned (getr R (reg 8)) <> sp + 8 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 ot ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 -> PQATSG.ws_this_atA segs M o (PQATSG.WDyn fb p v0 v1) ->
    PMSPA.aobjA FF ot 24 -> ot mod 8 = 0 -> (o + 32 <= ot \/ ot + 24 <= o) ->
    PM.vstr_at segs PMSPA.accA M ot x -> PM.vs_size x = 0 ->
    PMSTA.base_okA segs A M ->
    PMSP.credit_le (PM.credit_add (PMSPA.scA L (PM.credit_add (PQMA.pot_textM HV x) PQMA.TSRES)) (tsw D sp r RC)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (x' : PM.vstr) (cr' : credit) (D' : list (list Z)),
        regs_preserved R R' ->
        PM.vstr_at segs PMSPA.accA M' ot x' -> 1 <= PM.vs_size x' <= 30 -> PQATSS.ts_text segs M' ot x' -> ws2_postL x x' ->   (* [comment removed for export] *)
        L5CA.ahpres L ar (PQATSG.ws_own (PQATSG.WDyn fb p v0 v1) ++ LB) FF sp (PMSPA.pm_scr h) [(ot, 24)] M M' ->
        PMSP.credit_keep cr cr' (PM.credit_add (PMSPA.scA L (PQMA.pot_textM HV x)) (tsw D sp r RC))
                                (PM.credit_add (PMSPA.scA L (PQMA.pot_textM HV x')) (tsw D' sp r RC)) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> incl D D' ->
        ri_inv (HIk D') (PM.vs_own x' ++ PQATSG.ws_own (PQATSG.WDyn fb p v0 v1) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition tsw_laws (TSWMAX : credit) : Prop :=
  (forall D sp r RC, PMSP.credit_le PMSP.cr0 (tsw D sp r RC) /\ PMSP.credit_le (tsw D sp r RC) TSWMAX)
  /\ (forall D D' sp r RC, incl D D' -> PMSP.credit_le (tsw D' sp r RC) (tsw D sp r RC)).

(* [comment removed for export] *)
Definition divide2d_specF (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o p dn rr fb fbd fbr : Z) (lenr : nat) (v0 v1 d1 r0 r1 : Z)
         (D : list (list Z)) (RC : list Z),
    ri_inv (HIk D) ((p, 64) :: LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    HAR.rchain L ar M sp (bv_unsigned (getr R (reg 8))) RC -> bv_unsigned (getr R (reg 8)) <> sp + 8 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 o -> getr R (reg 13) = Z_to_bv 64 rr ->
    getr R (reg 14) = Z_to_bv 64 1 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    bdyn_at segs M o fb 2%nat p v0 v1 -> 1 <= v1 <= 2 ^ 30 ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr lenr r0 r1 -> (lenr <= 1)%nat ->
    (o + 32 <= rr \/ rr + 32 <= o) ->
    sp <= dn -> dn + 32 <= ar_sptop ar -> dn mod 8 = 0 -> shadow_zero M dn 4 -> binl_at M dn fbd 1%nat TEN19 d1 -> Z.testbit fbd 1 = false ->
    PMSTA.base_okA segs A M ->
    PMSP.credit_le (PM.credit_add (PMSPA.scA L PQMA.TSRES) (tdv2 D sp r RC)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (D' : list (list Z)) (fbq fbr' : Z),
        regs_preserved R R' ->
        bdyn_at segs M' o fbq 1%nat p ((v0 + 2 ^ 64 * v1) / TEN19) v1 -> Z.land fbq 2 = Z.land fb 2 ->
        binl_at M' rr fbr' (PQATSS.wlen ((v0 + 2 ^ 64 * v1) mod TEN19) 0) ((v0 + 2 ^ 64 * v1) mod TEN19) 0 -> Z.land fbr' 2 = Z.land fb 2 ->
        L5CA.ahpres L ar ((p, 64) :: LB) FF sp (PMSPA.pm_scr h) [(o, 32); (rr, 32); (p, 8)] M M' ->
        PMSP.credit_keep cr cr' (tdv2 D sp r RC) (tdv2 D' sp r RC) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> incl D D' ->
        ri_inv (HIk D') ((p, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition divide1d_specF (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o p dn rr fb fbd fbr : Z) (lenr : nat) (q q1 d1 r0 r1 : Z)
         (D : list (list Z)) (RC : list Z),
    ri_inv (HIk D) ((p, 64) :: LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    HAR.rchain L ar M sp (bv_unsigned (getr R (reg 8))) RC -> bv_unsigned (getr R (reg 8)) <> sp + 8 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 o -> getr R (reg 13) = Z_to_bv 64 rr ->
    getr R (reg 14) = Z_to_bv 64 1 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    bdyn_at segs M o fb 1%nat p q q1 -> 1 <= q < TEN19 ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr lenr r0 r1 -> (lenr <= 1)%nat ->
    (o + 32 <= rr \/ rr + 32 <= o) ->
    sp <= dn -> dn + 32 <= ar_sptop ar -> dn mod 8 = 0 -> shadow_zero M dn 4 -> binl_at M dn fbd 1%nat TEN19 d1 -> Z.testbit fbd 1 = false ->
    PMSTA.base_okA segs A M ->
    PMSP.credit_le (PM.credit_add (PMSPA.scA L PQMA.TSRES) (tdv1 D sp r RC)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (D' : list (list Z)) (fbq fbr' r1' : Z),
        regs_preserved R R' ->
        bdyn_at segs M' o fbq 0%nat p q q1 -> Z.land fbq 2 = Z.land fb 2 ->
        binl_at M' rr fbr' 1%nat q r1' -> Z.land fbr' 2 = Z.land fb 2 ->
        L5CA.ahpres L ar ((p, 64) :: LB) FF sp (PMSPA.pm_scr h) [(o, 32); (rr, 32)] M M' ->
        PMSP.credit_keep cr cr' (tdv1 D sp r RC) (tdv1 D' sp r RC) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> incl D D' ->
        ri_inv (HIk D') ((p, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Fam.
End PQATSW2.

(* [comment removed for export] *)
Module PQATSW2a.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (tsw tdv2 tdv1 : list (list Z) -> Z -> Z -> list Z -> credit).
Definition ws2i_spec : Prop := PQATSW2.ws2i_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSS.WRS_A PQATSW2.WRS2_H.
Definition divide2i_spec : Prop := PQATSW2.divide2i_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.DIVIDE_A PQATSC.DIV_H.
Definition ws2d_spec : Prop := PQATSW2.ws2d_specF RSEGS PnLayoutA.ADDR_A L ar HIk tsw PQATSS.WRS_A PQATSW2.WRS2_H.
Definition divide2d_spec : Prop := PQATSW2.divide2d_specF RSEGS PnLayoutA.ADDR_A L ar HIk tdv2 PQATSC.DIVIDE_A PQATSC.DIV_H.
Definition divide1d_spec : Prop := PQATSW2.divide1d_specF RSEGS PnLayoutA.ADDR_A L ar HIk tdv1 PQATSC.DIVIDE_A PQATSC.DIV_H.
End Names.
End PQATSW2a.

(* [comment removed for export] *)
Module PQATSW2b.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (tsw : list (list Z) -> Z -> Z -> list Z -> credit).
Definition ws2i_spec : Prop := PQATSW2.ws2i_specG RSEGS PnLayoutA.ADDR_B L ar HI PQATSS.WRS_B PQATSW2.WRS2_H.
Definition ws2d_spec : Prop := PQATSW2.ws2d_specF RSEGS PnLayoutA.ADDR_B L ar HIk tsw PQATSS.WRS_B PQATSW2.WRS2_H.
End Names.
End PQATSW2b.

End PnATs12SpecsW2.
Module PnATsTsw.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12Specs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12SpecsW2.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSTW.
(* [comment removed for export] *)
Definition WS_FREE_RA : Z := 0xd4130.
Definition DIV_FREE0_RA : Z := 0xc8360.
Definition DIV_FREE1_RA : Z := 0xc850c.
Definition RA_DIVW : Z := 0xd3f0c.
(* [comment removed for export] *)
Definition CMAL : credit := (8, 2097344).
(* [comment removed for export] *)
Definition SLACK : credit := (1, 0).
Definition TSWMAX : credit := (2 * 8 + 15 + 1, 2 * 2097344).

(* [comment removed for export] *)
Definition fkeys3 (p0f s r : Z) (RC : list Z) : list (list Z) := [[p0f]; HAR.akey p0f [s]; HAR.akey p0f (s :: r :: RC)].
(* [comment removed for export] *)
Definition fkeysd (p0f s r : Z) (RC : list Z) : list (list Z) := fkeys3 p0f s RA_DIVW [] ++ fkeys3 p0f s RA_DIVW (r :: RC).

Definition csum (l : list credit) : credit := fold_right PM.credit_add PMSP.cr0 l.
Definition kcost (c : credit) (D : list (list Z)) (k : list Z) : credit := if HAR.kin k D then PMSP.cr0 else c.
Definition pmal (LR : HAR.layoutR) (D : list (list Z)) : credit := csum (map (kcost CMAL D) (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A)).
Definition pfree (D : list (list Z)) (ks : list (list Z)) : credit := csum (map (kcost (1, 0) D) ks).

(* [comment removed for export] *)
Definition TSW (LR : HAR.layoutR) (D : list (list Z)) (r : Z) (RC : list Z) : credit :=
  PM.credit_add SLACK (PM.credit_add (pmal LR D)
    (pfree D (fkeys3 (HAR.hlr_pc_free LR) WS_FREE_RA r RC ++ fkeysd (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC ++ fkeysd (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC))).
(* [comment removed for export] *)
Definition TDV2 (LR : HAR.layoutR) (D : list (list Z)) (r : Z) (RC : list Z) : credit :=
  PM.credit_add (pmal LR D) (pfree D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC ++ fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC)).
(* [comment removed for export] *)
Definition TDV1 (LR : HAR.layoutR) (D : list (list Z)) (r : Z) (RC : list Z) : credit :=
  PM.credit_add (pmal LR D) (pfree D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kcost_rng c D k : 0 <= fst c -> 0 <= snd c -> 0 <= fst (kcost c D k) <= fst c /\ 0 <= snd (kcost c D k) <= snd c.
Proof. intros H1 H2. unfold kcost. destruct (HAR.kin k D); cbn; lia. Qed.
Lemma kcost_anti c D D' k : 0 <= fst c -> 0 <= snd c -> incl D D' -> fst (kcost c D' k) <= fst (kcost c D k) /\ snd (kcost c D' k) <= snd (kcost c D k).
Proof.
  intros H1 H2 INC. unfold kcost. destruct (HAR.kin k D) eqn:E.
  - assert (E' : HAR.kin k D' = true).
    { unfold HAR.kin in E |- *. rewrite existsb_exists in E. destruct E as (x & Hx & Ex). rewrite existsb_exists. exists x. split; [apply INC; exact Hx| exact Ex]. }
    rewrite E'. cbn. lia.
  - destruct (HAR.kin k D'); cbn; lia.
Qed.
Lemma csum_rng c D ks : 0 <= fst c -> 0 <= snd c ->
  0 <= fst (csum (map (kcost c D) ks)) <= Z.of_nat (length ks) * fst c /\ 0 <= snd (csum (map (kcost c D) ks)) <= Z.of_nat (length ks) * snd c.
Proof.
  intros H1 H2. induction ks as [|k ks IH]; [cbn; lia|].
  cbn [map csum fold_right length]. fold (csum (map (kcost c D) ks)). unfold PM.credit_add. cbn [fst snd].
  pose proof (kcost_rng c D k H1 H2) as (A & B). rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma csum_anti c D D' ks : 0 <= fst c -> 0 <= snd c -> incl D D' ->
  fst (csum (map (kcost c D') ks)) <= fst (csum (map (kcost c D) ks)) /\ snd (csum (map (kcost c D') ks)) <= snd (csum (map (kcost c D) ks)).
Proof.
  intros H1 H2 INC. induction ks as [|k ks IH]; [cbn; lia|].
  cbn [map csum fold_right]. fold (csum (map (kcost c D) ks)). fold (csum (map (kcost c D') ks)). unfold PM.credit_add. cbn [fst snd].
  pose proof (kcost_anti c D D' k H1 H2 INC) as (A & B). lia.
Qed.

Lemma tsw_laws_ok (LR : HAR.layoutR) : PQATSW2.tsw_laws (fun D (_ : Z) r RC => TSW LR D r RC) TSWMAX.
Proof.
  split.
  - intros D sp r RC. unfold TSW, SLACK, pmal, pfree, PMSP.credit_le, PM.credit_add, TSWMAX, PMSP.cr0. cbn [fst snd].
    pose proof (csum_rng CMAL D (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A) ltac:(cbn; lia) ltac:(cbn; lia)) as (A & B).
    change (Z.of_nat (length (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A))) with 2 in A, B. change (fst CMAL) with 8 in A. change (snd CMAL) with 2097344 in B.
    match goal with |- context [csum (map (kcost (1, 0) D) ?ks)] =>
      pose proof (csum_rng (1, 0) D ks ltac:(cbn; lia) ltac:(cbn; lia)) as (A' & B'); change (Z.of_nat (length ks)) with 15 in A', B' end.
    change (fst (1, 0)) with 1 in A'. change (snd (1, 0)) with 0 in B'. lia.
  - intros D D' sp r RC INC. unfold TSW, SLACK, pmal, pfree, PMSP.credit_le, PM.credit_add. cbn [fst snd].
    pose proof (csum_anti CMAL D D' (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A) ltac:(cbn; lia) ltac:(cbn; lia) INC) as (A & B).
    match goal with |- context [csum (map (kcost (1, 0) D) ?ks)] => pose proof (csum_anti (1, 0) D D' ks ltac:(cbn; lia) ltac:(cbn; lia) INC) as (A' & B') end.
    lia.
Qed.

(* [comment removed for export] *)
Lemma credit_add_0_l (x : credit) : PM.credit_add PMSP.cr0 x = x.
Proof. destruct x as [a b]. unfold PM.credit_add, PMSP.cr0. cbn. f_equal; lia. Qed.
Lemma csum_app c D ks ks' : csum (map (kcost c D) (ks ++ ks')) = PM.credit_add (csum (map (kcost c D) ks)) (csum (map (kcost c D) ks')).
Proof.
  induction ks as [|k ks IH].
  - cbn [map app]. change (csum []) with PMSP.cr0. symmetry. apply credit_add_0_l.
  - cbn [map app csum fold_right]. fold (csum (map (kcost c D) (ks ++ ks'))). fold (csum (map (kcost c D) ks)). fold (csum (map (kcost c D) ks')).
    rewrite IH. unfold PM.credit_add. cbn [fst snd]. f_equal; lia.
Qed.
Lemma tdv2_le_tsw LR D r RC (RCd : list Z) : (RCd = [] \/ RCd = r :: RC) -> PMSP.credit_le (TDV2 LR D RA_DIVW RCd) (TSW LR D r RC).
Proof.
  intros CASES. unfold TDV2, TSW, SLACK, pfree, fkeysd. rewrite !csum_app. unfold PMSP.credit_le, PM.credit_add. cbn [fst snd].
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) WS_FREE_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia)) as (A0 & B0).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA RA_DIVW []) ltac:(cbn; lia) ltac:(cbn; lia)) as (A1 & B1).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA RA_DIVW (r :: RC)) ltac:(cbn; lia) ltac:(cbn; lia)) as (A2 & B2).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA RA_DIVW []) ltac:(cbn; lia) ltac:(cbn; lia)) as (A3 & B3).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA RA_DIVW (r :: RC)) ltac:(cbn; lia) ltac:(cbn; lia)) as (A4 & B4).
  destruct CASES as [-> | ->]; lia.
Qed.
Lemma tdv1_le_tsw LR D r RC (RCd : list Z) : (RCd = [] \/ RCd = r :: RC) -> PMSP.credit_le (TDV1 LR D RA_DIVW RCd) (TSW LR D r RC).
Proof.
  intros CASES. unfold TDV1, TSW, SLACK, pfree, fkeysd. rewrite !csum_app. unfold PMSP.credit_le, PM.credit_add. cbn [fst snd].
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) WS_FREE_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia)) as (A0 & B0).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA RA_DIVW []) ltac:(cbn; lia) ltac:(cbn; lia)) as (A1 & B1).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA RA_DIVW (r :: RC)) ltac:(cbn; lia) ltac:(cbn; lia)) as (A2 & B2).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA RA_DIVW []) ltac:(cbn; lia) ltac:(cbn; lia)) as (A3 & B3).
  pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA RA_DIVW (r :: RC)) ltac:(cbn; lia) ltac:(cbn; lia)) as (A4 & B4).
  destruct CASES as [-> | ->]; lia.
Qed.
Lemma tdv_laws LR :
  (forall D r RC, PMSP.credit_le PMSP.cr0 (TDV2 LR D r RC) /\ PMSP.credit_le PMSP.cr0 (TDV1 LR D r RC))
  /\ (forall D D' r RC, incl D D' -> PMSP.credit_le (TDV2 LR D' r RC) (TDV2 LR D r RC) /\ PMSP.credit_le (TDV1 LR D' r RC) (TDV1 LR D r RC)).
Proof.
  split.
  - intros D r RC. unfold TDV2, TDV1, pmal, pfree, PMSP.credit_le, PM.credit_add, PMSP.cr0. cbn [fst snd].
    pose proof (csum_rng CMAL D (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A) ltac:(cbn; lia) ltac:(cbn; lia)) as (A & B).
    pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC ++ fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia)) as (A1 & B1).
    pose proof (csum_rng (1, 0) D (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia)) as (A2 & B2).
    lia.
  - intros D D' r RC INC. unfold TDV2, TDV1, pmal, pfree, PMSP.credit_le, PM.credit_add. cbn [fst snd].
    pose proof (csum_anti CMAL D D' (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A) ltac:(cbn; lia) ltac:(cbn; lia) INC) as (A & B).
    pose proof (csum_anti (1, 0) D D' (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC ++ fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia) INC) as (A1 & B1).
    pose proof (csum_anti (1, 0) D D' (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC) ltac:(cbn; lia) ltac:(cbn; lia) INC) as (A2 & B2).
    lia.
Qed.
(* [comment removed for export] *)
Lemma cmal_gcost {SCFG_P : ScfgP} (L : asan_layout) (C : asan_statics_cells) : PMA.layout L C -> PQATSG.gcost L false 64 = CMAL.
Proof. intros LY. pose proof (PMA.ly_cost L C LY) as (HK & HL & HB). unfold PQATSG.gcost, CMAL. rewrite HK, HL, HB. reflexivity. Qed.
End PQATSTW.

End PnATsTsw.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module PnATsTdvK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12Specs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12SpecsW2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsTsw.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSTK.
Import PQATSTW. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma kin_cons k x D : HAR.kin k (x :: D) = (if list_eq_dec Z.eq_dec x k then true else false) || HAR.kin k D.
Proof. unfold HAR.kin. cbn [existsb]. reflexivity. Qed.
Lemma kcost_cons c D x k : kcost c (x :: D) k = (if list_eq_dec Z.eq_dec x k then PMSP.cr0 else kcost c D k).
Proof. unfold kcost. rewrite kin_cons. destruct (list_eq_dec Z.eq_dec x k); cbn [orb]; reflexivity. Qed.
Lemma incl_cons_r {A} (x : A) (D : list A) : incl D (x :: D).
Proof. intros y Hy. right. exact Hy. Qed.

(* [comment removed for export] *)
Lemma csum_drop c D x ks : 0 <= fst c -> 0 <= snd c -> In x ks -> HAR.kin x D = false ->
  fst (csum (map (kcost c (x :: D)) ks)) + fst c <= fst (csum (map (kcost c D) ks))
  /\ snd (csum (map (kcost c (x :: D)) ks)) + snd c <= snd (csum (map (kcost c D) ks)).
Proof.
  intros H1 H2 IN NK. induction ks as [|k ks IH]; [destruct IN|].
  cbn [map csum fold_right]. fold (csum (map (kcost c D) ks)). fold (csum (map (kcost c (x :: D)) ks)). unfold PM.credit_add. cbn [fst snd].
  pose proof (csum_anti c D (x :: D) ks H1 H2 (incl_cons_r x D)) as (A1 & A2).
  pose proof (kcost_anti c D (x :: D) k H1 H2 (incl_cons_r x D)) as (B1 & B2).
  destruct IN as [-> | IN].
  - assert (E1 : kcost c (x :: D) x = PMSP.cr0).
    { rewrite kcost_cons. destruct (list_eq_dec Z.eq_dec x x) as [_|NE]; [reflexivity| exfalso; apply NE; reflexivity]. }
    assert (E2 : kcost c D x = c) by (unfold kcost; rewrite NK; reflexivity).
    rewrite E1, E2. unfold PMSP.cr0. cbn [fst snd]. lia.
  - destruct (IH IN) as (C1 & C2). lia.
Qed.

Section Keep.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (C : asan_statics_cells) (LR : HAR.layoutR).
Hypothesis LY : PMA.layout L C.
Variables (D : list (list Z)) (r : Z) (RC : list Z).
Local Notation T Dx := (TDV2 LR Dx r RC).
Local Notation GK := (PQATSG.GKEYS LR PQATSG.OPNEW_RA_A).
Local Notation KS := (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC ++ fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC).

(* [comment removed for export] *)
Definition inv (cr : credit) (Dk : list (list Z)) (crk : credit) (s : Z) : Prop :=
  fst cr - fst (T D) + fst (T Dk) <= fst crk + s /\ snd cr - snd (T D) + snd (T Dk) <= snd crk.

Lemma inv_start cr : inv cr D cr 0.
Proof. unfold inv. lia. Qed.

Lemma T_anti Dk x : fst (T (x :: Dk)) <= fst (T Dk) /\ snd (T (x :: Dk)) <= snd (T Dk).
Proof.
  destruct (proj2 (tdv_laws LR) Dk (x :: Dk) r RC (incl_cons_r x Dk)) as ((A1 & A2) & _). split; [exact A1| exact A2].
Qed.

(* [comment removed for export] *)
Lemma inv_malloc cr Dk crk s gk crk' :
  inv cr Dk crk s -> In gk GK -> PMSP.credit_keep crk crk' (PQATSG.gcostD L gk Dk 64) PMSP.cr0 -> inv cr (gk :: Dk) crk' (s + 1).
Proof.
  intros (I1 & I2) KIN (K1 & K2). unfold PQATSG.gcostD, HAR.warm_ok in K1, K2. change (HAR.NW_LO <=? 64) with true in K1, K2. change (64 <=? HAR.NW_HI) with true in K1, K2.
  rewrite !andb_true_r in K1, K2. unfold PMSP.cr0 in K1, K2. cbn [fst snd] in K1, K2.
  pose proof (T_anti Dk gk) as (A1 & A2).
  destruct (HAR.kin gk Dk) eqn:E.
  - unfold PQATSG.gcost in K1, K2. cbn [fst snd] in K1, K2. unfold inv. lia.
  - rewrite (cmal_gcost L C LY) in K1, K2. unfold CMAL in K1, K2. cbn [fst snd] in K1, K2.
    assert (DROP : fst (T (gk :: Dk)) + 8 <= fst (T Dk) /\ snd (T (gk :: Dk)) + 2097344 <= snd (T Dk)).
    { unfold TDV2, pmal, pfree, PM.credit_add. cbn [fst snd].
      pose proof (csum_drop CMAL Dk gk GK ltac:(cbn; lia) ltac:(cbn; lia) KIN E) as (B1 & B2). change (fst CMAL) with 8 in B1. change (snd CMAL) with 2097344 in B2.
      pose proof (csum_anti (1, 0) Dk (gk :: Dk) KS ltac:(cbn; lia) ltac:(cbn; lia) (incl_cons_r gk Dk)) as (B3 & B4). lia. }
    unfold inv. lia.
Qed.

(* [comment removed for export] *)
Lemma inv_free cr Dk crk s Kt :
  inv cr Dk crk s -> In Kt KS -> inv cr (Kt :: Dk) (if HAR.warm_ok Kt Dk 64 then (fst crk + 1, snd crk) else crk) (s - 1).
Proof.
  intros (I1 & I2) KIN. unfold HAR.warm_ok. change (HAR.NW_LO <=? 64) with true. change (64 <=? HAR.NW_HI) with true. rewrite !andb_true_r.
  pose proof (T_anti Dk Kt) as (A1 & A2).
  destruct (HAR.kin Kt Dk) eqn:E.
  - unfold inv. cbn [fst snd]. lia.
  - assert (DROP : fst (T (Kt :: Dk)) + 1 <= fst (T Dk)).
    { unfold TDV2, pmal, pfree, PM.credit_add. cbn [fst snd].
      pose proof (csum_drop (1, 0) Dk Kt KS ltac:(cbn; lia) ltac:(cbn; lia) KIN E) as (B1 & _). change (fst (1, 0)) with 1 in B1.
      pose proof (csum_anti CMAL Dk (Kt :: Dk) GK ltac:(cbn; lia) ltac:(cbn; lia) (incl_cons_r Kt Dk)) as (B3 & B4). lia. }
    unfold inv. lia.
Qed.

(* [comment removed for export] *)
Lemma tdv2_keep cr cr1 cr2 gk1 gk2 Kt1 Kt2 :
  In gk1 GK -> In gk2 GK ->
  PMSP.credit_keep cr cr1 (PQATSG.gcostD L gk1 D 64) PMSP.cr0 ->
  PMSP.credit_keep cr1 cr2 (PQATSG.gcostD L gk2 (gk1 :: D) 64) PMSP.cr0 ->
  In Kt1 (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE0_RA r RC) -> In Kt2 (fkeys3 (HAR.hlr_pc_free LR) DIV_FREE1_RA r RC) ->
  let D2 := gk2 :: gk1 :: D in
  let cr3 := (if HAR.warm_ok Kt1 D2 64 then (fst cr2 + 1, snd cr2) else cr2) in
  let D3 := Kt1 :: D2 in
  let cr4 := (if HAR.warm_ok Kt2 D3 64 then (fst cr3 + 1, snd cr3) else cr3) in
  PMSP.credit_keep cr cr4 (TDV2 LR D r RC) (TDV2 LR (Kt2 :: D3) r RC) /\ incl D (Kt2 :: D3).
Proof.
  intros KIN1 KIN2 CK1 CK2 HK1 HK2. cbn zeta.
  pose proof (inv_malloc cr D cr 0 gk1 cr1 (inv_start cr) KIN1 CK1) as I1.
  pose proof (inv_malloc cr (gk1 :: D) cr1 (0 + 1) gk2 cr2 I1 KIN2 CK2) as I2.
  pose proof (inv_free cr (gk2 :: gk1 :: D) cr2 (0 + 1 + 1) Kt1 I2 ltac:(apply in_or_app; left; exact HK1)) as I3.
  pose proof (inv_free cr (Kt1 :: gk2 :: gk1 :: D) _ (0 + 1 + 1 - 1) Kt2 I3 ltac:(apply in_or_app; right; exact HK2)) as I4.
  destruct I4 as (J1 & J2). split.
  { unfold PMSP.credit_keep. destruct (HAR.warm_ok Kt2 (Kt1 :: gk2 :: gk1 :: D) 64); destruct (HAR.warm_ok Kt1 (gk2 :: gk1 :: D) 64); cbn [fst snd] in J1, J2 |- *; lia. }
  intros x Hx. do 4 right. exact Hx.
Qed.
End Keep.
End PQATSTK.

End PnATsTdvK.
Module PnATsCone4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSC4.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
(* [comment removed for export] *)
Definition SHL_A : Z := 0xccb40.
Definition NORM_A : Z := 0xcc390.
Definition UNNORM_A : Z := 0xcc920.
Definition SUBMUL_A : Z := 0xcc6c8.
Definition DDQ_A : Z := 0xcc5c8.
(* [comment removed for export] *)
Definition SHL_H : Z := 3.
Definition NORM_H : Z := 4.
Definition UNNORM_H : Z := 4.
Definition SUBMUL_H : Z := 4.
Abbreviation TEN19 := PQATSC.TEN19.
(* [comment removed for export] *)
Definition rv1 (len : nat) (v1 : Z) : Z := if Nat.eqb len 2%nat then v1 else 0.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Definition reduceX_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 -> (len = 2%nat \/ len = 1%nat) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        binl_at M' o (PQATSS.wfb fb v0 (rv1 len v1)) (PQATSS.wlen v0 (rv1 len v1)) v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition resizeL2_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= Z.of_nat len -> (len <= 2)%nat ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' o fb (Z.to_nat n) v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition cmp21i_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r x y fbx fby : Z) (x0 x1 y0 y1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 x -> getr R (reg 11) = Z_to_bv 64 y ->
    PMSPA.aobjA FF x 32 -> x mod 8 = 0 -> PMSPA.accA M x 32 -> binl_at M x fbx 2%nat x0 x1 -> Z.testbit fbx 1 = false ->
    PMSPA.aobjA FF y 32 -> y mod 8 = 0 -> PMSPA.accA M y 32 -> binl_at M y fby 1%nat y0 y1 -> Z.testbit fby 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition copyR_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    sp <= d -> d + 32 <= ar_sptop ar -> d mod 8 = 0 -> shadow_zero M d 4 -> L5.defined M d 32 ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> binl_at M s fb len v0 v1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (fb' : Z),
        regs_preserved R R' ->
        binl_at M' d fb' len v0 v1 -> Z.land fb' 2 = Z.land fb 2 -> binl_at M' s fb len v0 v1 -> shadow_zero M' d 4 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition shl0_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 0 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    binl_at M o fb len v0 v1 -> ((len = 1%nat /\ 1 <= v0) \/ (len = 2%nat /\ 1 <= v1)) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        binl_at M' o fb len v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition normalize0_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r th dn nm ax fbd fbn : Z) (d0 d1 n0 n1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 th -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 nm -> getr R (reg 13) = Z_to_bv 64 ax ->
    PMSPA.aobjA FF dn 32 -> dn mod 8 = 0 -> PMSPA.accA M dn 32 -> binl_at M dn fbd 1%nat d0 d1 -> 2 ^ 63 <= d0 ->
    PMSPA.aobjA FF nm 32 -> nm mod 8 = 0 -> PMSPA.accA M nm 32 -> binl_at M nm fbn 2%nat n0 n1 -> 1 <= n1 ->
    (dn + 32 <= nm \/ nm + 32 <= dn) ->
    sp <= ax - 4 -> ax + 4 <= ar_sptop ar -> ax mod 8 = 4 -> shadow_zero M (ax - 4) 1 -> L5.defined M (ax - 4) 8 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 0 ->
        binl_at M' dn fbd 1%nat d0 d1 -> binl_at M' nm fbn 2%nat n0 n1 -> L5.u32_at segs M' ax 0 -> shadow_zero M' (ax - 4) 1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(dn, 32); (nm, 32); (ax, 4)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition unnorm0_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r th rr fbr : Z) (r0 r1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 th -> getr R (reg 11) = Z_to_bv 64 rr -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 0 ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr 2%nat r0 r1 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' rr (PQATSS.wfb fbr r0 r1) (PQATSS.wlen r0 r1) r0 r1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(rr, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition submulT_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r th rr dd aq fbr fbd : Z) (lend : nat) (x0 x1 b1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 th -> getr R (reg 11) = Z_to_bv 64 (rr + 16) -> getr R (reg 12) = Z_to_bv 64 (dd + 16) -> getr R (reg 13) = Z_to_bv 64 1 ->
    getr R (reg 14) = Z_to_bv 64 aq ->
    PMSPA.aobjA FF rr 32 -> rr mod 8 = 0 -> PMSPA.accA M rr 32 -> binl_at M rr fbr 2%nat x0 x1 -> 1 <= x1 <= 2 ^ 30 ->
    PMSPA.aobjA FF dd 32 -> dd mod 8 = 0 -> PMSPA.accA M dd 32 -> binl_at M dd fbd lend TEN19 b1 ->
    (rr + 32 <= dd \/ dd + 32 <= rr) ->
    sp <= aq -> aq + 8 <= ar_sptop ar -> aq mod 8 = 0 -> shadow_zero M aq 1 -> L5.u64_at segs M aq ((x0 + 2 ^ 64 * x1) / TEN19) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        binl_at M' rr fbr 2%nat ((x0 + 2 ^ 64 * x1) mod TEN19) 0 -> binl_at M' dd fbd lend TEN19 b1 ->
        L5.u64_at segs M' aq ((x0 + 2 ^ 64 * x1) / TEN19) -> shadow_zero M' aq 1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(rr, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition assign2_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb fbs : Z) (lend : nat) (d0 d1 s0 s1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    PMSPA.aobjA FF d 32 -> d mod 8 = 0 -> PMSPA.accA M d 32 -> binl_at M d fb lend d0 d1 -> (lend <= 1)%nat ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> binl_at M s fbs 2%nat s0 s1 ->
    (d + 32 <= s \/ s + 32 <= d) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d ->
        binl_at M' d (PQATSC.asg_fb fb fbs 2%nat) 2%nat s0 s1 -> binl_at M' s fbs 2%nat s0 s1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Specs.
End PQATSC4.

(* [comment removed for export] *)
Module PQATSC4a.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition reduceX_spec (h : Z) : Prop := PQATSC4.reduceX_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.REDUCE_A h.
Definition resizeL2_spec : Prop := PQATSC4.resizeL2_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESIZE_A PQATSC.RZ_H.
Definition cmp21i_spec : Prop := PQATSC4.cmp21i_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.CMP_A PQATSC.CMP_H.
Definition copyR_spec : Prop := PQATSC4.copyR_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.COPYD_A PQATSC.CPY_H.
Definition shl0_spec : Prop := PQATSC4.shl0_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC4.SHL_A PQATSC4.SHL_H.
Definition normalize0_spec : Prop := PQATSC4.normalize0_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC4.NORM_A PQATSC4.NORM_H.
Definition unnorm0_spec : Prop := PQATSC4.unnorm0_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC4.UNNORM_A PQATSC4.UNNORM_H.
Definition submulT_spec : Prop := PQATSC4.submulT_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC4.SUBMUL_A PQATSC4.SUBMUL_H.
Definition assign2_spec : Prop := PQATSC4.assign2_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.ASSIGN_A PQATSC.ASG_H.
End Names.
End PQATSC4a.

End PnATsCone4.
Module PnATsCone5.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12Specs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12SpecsW2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsCone4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQATSC5.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition CPYX_A : Z := 0xcb80c.     (* [comment removed for export] *)
Definition CPYX_H : Z := 3.           (* [comment removed for export] *)

Section Fam.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable HIk : list (list Z) -> asan_iface.
Variable LR : HAR.layoutR.
Abbreviation cfg := (@PMSPA.cfg segs).
Abbreviation binl_at := (PQATSS.binl_at segs).

(* [comment removed for export] *)
Abbreviation bdyn_at := (PQATSW2.bdyn_at segs).

(* [comment removed for export] *)
Definition cpdst (FF : list fframe) (M : word -> option byte) (sp d : Z) : Prop :=
  (PMSPA.aobjA FF d 32 /\ PMSPA.accA M d 32) \/ (sp <= d /\ d + 32 <= ar_sptop ar /\ shadow_zero M d 4 /\ L5.defined M d 32).

(* [comment removed for export] *)
Definition copyXd_specF (pc h gra : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb : Z) (len : nat) (p v0 v1 : Z) (D : list (list Z)),
    ri_inv (HIk D) LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    cpdst FF M sp d -> d mod 8 = 0 ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> bdyn_at M s fb len p v0 v1 -> (len = 1%nat \/ len = 2%nat) ->
    In (p, 64) LB -> (d + 32 <= s \/ s + 32 <= d) ->
    PMSTA.base_okA segs A M ->
    PQATSG.gpre L LR gra D 64 cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (q fb' q1 : Z) (gk : list Z),
        regs_preserved R R' -> In gk (PQATSG.GKEYS LR gra) ->
        bdyn_at M' d fb' len q v0 q1 -> (len = 2%nat -> q1 = v1) -> Z.land fb' 2 = Z.land fb 2 ->
        bdyn_at M' s fb len p v0 v1 ->
        L5CA.afresh L ar LB (FF ++ LK') M' q 64 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        PMSP.credit_keep cr cr' (PQATSG.gcostD L gk D 64) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv (HIk (gk :: D)) ((q, 64) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition cmp21d_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r x y fbx fby : Z) (p x0 x1 y0 y1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 x -> getr R (reg 11) = Z_to_bv 64 y ->
    PMSPA.aobjA FF x 32 -> x mod 8 = 0 -> PMSPA.accA M x 32 -> bdyn_at M x fbx 2%nat p x0 x1 -> Z.testbit fbx 0 = true -> Z.testbit fbx 1 = false ->
    In (p, 64) LB ->
    PMSPA.aobjA FF y 32 -> y mod 8 = 0 -> PMSPA.accA M y 32 -> binl_at M y fby 1%nat y0 y1 -> Z.testbit fby 1 = false ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition reduceXd_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o fb : Z) (len : nat) (p v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    bdyn_at M o fb len p v0 v1 -> Z.testbit fb 0 = true -> In (p, 64) LB ->
    ((len = 1%nat /\ 1 <= v0) \/ (len = 2%nat /\ 1 <= v1)) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 o ->
        bdyn_at M' o fb len p v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition reserveD_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (p v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= 8 ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    L5.big_at segs M o (L5.BO fb len (L5.BDyn 8 p)) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition resizeDd_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r o n fb : Z) (len : nat) (p v0 v1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= Z.of_nat len -> (len <= 2)%nat ->
    PMSPA.aobjA FF o 32 -> o mod 8 = 0 -> PMSPA.accA M o 32 ->
    bdyn_at M o fb len p v0 v1 -> In (p, 64) LB ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' ->
        bdyn_at M' o fb (Z.to_nat n) p v0 v1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(o, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition normalize0d_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r th dn nm ax fbd fbn : Z) (d0 d1 pn n0 n1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 th -> getr R (reg 11) = Z_to_bv 64 dn -> getr R (reg 12) = Z_to_bv 64 nm -> getr R (reg 13) = Z_to_bv 64 ax ->
    PMSPA.aobjA FF dn 32 -> dn mod 8 = 0 -> PMSPA.accA M dn 32 -> binl_at M dn fbd 1%nat d0 d1 -> 2 ^ 63 <= d0 ->
    PMSPA.aobjA FF nm 32 -> nm mod 8 = 0 -> PMSPA.accA M nm 32 -> bdyn_at M nm fbn 2%nat pn n0 n1 -> In (pn, 64) LB -> 1 <= n1 ->
    (dn + 32 <= nm \/ nm + 32 <= dn) ->
    sp <= ax - 4 -> ax + 4 <= ar_sptop ar -> ax mod 8 = 4 -> shadow_zero M (ax - 4) 1 -> L5.defined M (ax - 4) 8 ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 0 ->
        binl_at M' dn fbd 1%nat d0 d1 -> bdyn_at M' nm fbn 2%nat pn n0 n1 -> L5.u32_at segs M' ax 0 -> shadow_zero M' (ax - 4) 1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(dn, 32); (nm, 32); (ax, 4)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition assign2d_specG (pc h : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r d s fb fbs : Z) (lend : nat) (d0 d1 pn s0 s1 : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r h -> PGSA.ffroomB PQRA.FCM h FF LK -> PMSPA.ffrsA FF sp -> sp mod 16 = 0 ->
    getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 11) = Z_to_bv 64 s ->
    PMSPA.aobjA FF d 32 -> d mod 8 = 0 -> PMSPA.accA M d 32 -> binl_at M d fb lend d0 d1 -> (lend <= 1)%nat ->
    PMSPA.aobjA FF s 32 -> s mod 8 = 0 -> PMSPA.accA M s 32 -> bdyn_at M s fbs 2%nat pn s0 s1 -> In (pn, 64) LB ->
    (d + 32 <= s \/ s + 32 <= d) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
        regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d ->
        binl_at M' d (PQATSC.asg_fb fb fbs 2%nat) 2%nat s0 s1 -> bdyn_at M' s fbs 2%nat pn s0 s1 ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr h) [(d, 32)] M M' ->
        model_rt model model' -> incl LK' LK -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK' cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End Fam.
End PQATSC5.

(* [comment removed for export] *)
Module PQATSC5a.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Names.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (HIk : list (list Z) -> asan_iface) (LR : HAR.layoutR).
Definition copyXd_spec : Prop := PQATSC5.copyXd_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSC5.CPYX_A PQATSC5.CPYX_H PQATSG.OPNEW_RA_A.
(* [comment removed for export] *)
Definition copyXdD_spec : Prop := PQATSC5.copyXd_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSC.COPYD_A PQATSC.CPY_H PQATSG.OPNEW_RA_A.
Definition copyXdW_spec : Prop := PQATSC5.copyXd_specF RSEGS PnLayoutA.ADDR_A L ar HIk LR PQATSC.COPYW_A PQATSC.CPY_H PQATSG.OPNEW_RA_A.
Definition cmp21d_spec : Prop := PQATSC5.cmp21d_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.CMP_A PQATSC.CMP_H.
Definition reduceXd_spec (h : Z) : Prop := PQATSC5.reduceXd_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.REDUCE_A h.
Definition reserveD_spec : Prop := PQATSC5.reserveD_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESERVE_A PQATSC.RSV_H.
Definition resizeDd_spec : Prop := PQATSC5.resizeDd_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.RESIZE_A PQATSC.RZ_H.
Definition normalize0d_spec : Prop := PQATSC5.normalize0d_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC4.NORM_A PQATSC4.NORM_H.
Definition assign2d_spec : Prop := PQATSC5.assign2d_specG RSEGS PnLayoutA.ADDR_A L ar HI PQATSC.ASSIGN_A PQATSC.ASG_H.
End Names.
End PQATSC5a.

End PnATsCone5.
