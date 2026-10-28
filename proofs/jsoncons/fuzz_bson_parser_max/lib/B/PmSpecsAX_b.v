(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSAX.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation vec_at := (PM.vec_at segs PMSPA.accA PMSPA.annA).

(* [comment removed for export] *)
Definition vec_pre (M : word -> option byte) (v b k : Z) (stk : list PM.pstate) (own : list (Z * Z)) : Prop :=
  (L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0 /\ b = 0 /\ k = 0 /\ stk = [] /\ own = [])
  \/ (vec_at M v b k stk /\ own = PM.vec_own b k).
Definition vec_empty (b : Z) (own : list (Z * Z)) : Prop := own = [].

(* [comment removed for export] *)
Definition push_out (full : bool) (b k : Z) (stk : list PM.pstate) (own : list (Z * Z)) (b' k' : Z) (cr cr' : credit) : Prop :=
  (own <> [] /\ Z.of_nat (length stk) < 2 ^ k /\ full = false /\ b' = b /\ k' = k /\ cr' = cr)
  \/ ((own = [] \/ Z.of_nat (length stk) = 2 ^ k) /\ k' = (if Z.eqb b 0 then 0 else k + 1) /\ cr' = adebit L cr (32 * 2 ^ k')).

(* [comment removed for export] *)
Definition arg_ok (FF : list fframe) (sp v p n : Z) : Prop := (PMSPA.aobjA FF p n \/ (sp <= p /\ p + n <= ar_sptop ar)) /\ (p + n <= v \/ v + 24 <= p).

(* [comment removed for export] *)
Definition push_spec_at (pc : Z) (full : bool) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> PM.pstate -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (own : list (Z * Z))
         (c : PM.pstate) (sp r : Z),
    ri_inv HI (own ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    vec_pre M v b k stk own -> (full = true -> own <> [] /\ Z.of_nat (length stk) = 2 ^ k) -> ((own = [] \/ Z.of_nat (length stk) = 2 ^ k) -> k <= 10) ->
    cells FF sp v M R c ->
    ((own = [] \/ Z.of_nat (length stk) = 2 ^ k) -> acredit_ok L cr (32 * 2 ^ (if Z.eqb b 0 then 0 else k + 1))) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (b' k' : Z) (cr' : credit),
        regs_preserved R R' -> vec_at M' v b' k' (stk ++ [c]) -> PMSPA.accA M' v 24 ->
        push_out full b k stk own b' k' cr cr' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vec_own b' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition cells_mi (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (c : PM.pstate) : Prop :=
  exists p1 p2 m n, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ p1 mod 4 = 0 /\ p2 mod 4 = 0
    /\ PMSPA.accA M p1 4 /\ PMSPA.accA M p2 4 /\ arg_ok FF sp v p1 4 /\ arg_ok FF sp v p2 4 /\ byte_at M (HeapIfaceA.S p1) 0 /\ byte_at M (HeapIfaceA.S p2) 0
    /\ L5.u32_at segs M p1 m /\ L5.u32_at segs M p2 n /\ 0 <= m < 2 ^ 31 /\ 0 <= n < 2 ^ 31
    /\ c = PM.PS m n 0 0.
Definition cells_ms (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (c : PM.pstate) : Prop :=
  exists p1 p2 m n, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ p1 mod 4 = 0 /\ p2 mod 8 = 0
    /\ PMSPA.accA M p1 4 /\ PMSPA.accA M p2 8 /\ arg_ok FF sp v p1 4 /\ arg_ok FF sp v p2 8 /\ byte_at M (HeapIfaceA.S p1) 0 /\ byte_at M (HeapIfaceA.S p2) 0
    /\ L5.u32_at segs M p1 m /\ L5.u64_at segs M p2 n /\ 0 <= m < 2 ^ 31 /\ 0 <= n < 2 ^ 64
    /\ c = PM.PS m n 0 0.
(* [comment removed for export] *)
Definition cells_msu (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (c : PM.pstate) : Prop :=
  exists p1 p2 p3 m n t, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ getr R 13%bv = Z_to_bv 64 p3 /\ p1 mod 4 = 0 /\ p2 mod 8 = 0
    /\ PMSPA.accA M p1 4 /\ PMSPA.accA M p2 8 /\ PMSPA.accA M p3 1 /\ arg_ok FF sp v p1 4 /\ arg_ok FF sp v p2 8 /\ arg_ok FF sp v p3 1
    /\ byte_at M (HeapIfaceA.S p1) 0 /\ byte_at M (HeapIfaceA.S p2) 0 /\ (byte_at M (HeapIfaceA.S p3) 1 /\ p3 mod 8 = 0) /\ L5.u32_at segs M p1 m /\ L5.u64_at segs M p2 n /\ L5.u8_at segs M p3 t
    /\ 0 <= m < 2 ^ 31 /\ 0 <= n < 2 ^ 64 /\ 0 <= t < 256 /\ c = PM.PS m n t 0.

Definition cells_miu (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (c : PM.pstate) : Prop :=
  exists p1 p2 p3 m n t, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ getr R 13%bv = Z_to_bv 64 p3 /\ p1 mod 4 = 0 /\ p2 mod 4 = 0
    /\ PMSPA.accA M p1 4 /\ PMSPA.accA M p2 4 /\ PMSPA.accA M p3 1 /\ arg_ok FF sp v p1 4 /\ arg_ok FF sp v p2 4 /\ arg_ok FF sp v p3 1
    /\ byte_at M (HeapIfaceA.S p1) 0 /\ byte_at M (HeapIfaceA.S p2) 0 /\ byte_at M (HeapIfaceA.S p3) 0 /\ L5.u32_at segs M p1 m /\ L5.u32_at segs M p2 n /\ L5.u8_at segs M p3 t
    /\ 0 <= m < 2 ^ 31 /\ 0 <= n < 2 ^ 31 /\ 0 <= t < 256 /\ c = PM.PS m n t 0.

Definition push_mi_spec : Prop := push_spec_at (paa_esp_mi AA) false cells_mi.
Definition push_miu_spec : Prop := push_spec_at (paa_esp_miu AA) false cells_miu.      (* [comment removed for export] *)
Definition push_ms_spec : Prop := push_spec_at (paa_esp_ms AA) false cells_ms.
Definition push_msu_spec : Prop := push_spec_at (paa_esp_msu AA) false cells_msu.

(* [comment removed for export] *)
Definition ann_shrink_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k old : Z) (stk : list PM.pstate) (sp r : Z),
    ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    Z.of_nat (length stk) <= old <= 2 ^ k ->
    (* [comment removed for export] *)
    L5.u64_at segs M v b -> L5.u64_at segs M (v + 8) (b + 32 * Z.of_nat (length stk)) -> L5.u64_at segs M (v + 16) (b + 32 * 2 ^ k) ->
    0 <= k <= 11 -> b mod 16 = 0 -> L5.defined M b (32 * 2 ^ k) -> PMSPA.accA M b (32 * old) -> PMSPA.annA M b (32 * old) (32 * 2 ^ k) ->
    (forall i, (i < length stk)%nat -> PM.pstate_at segs M (b + 32 * Z.of_nat i) (nth i stk PM.ps_root)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> vec_at M' v b k stk -> PMSPA.accA M' v 24 ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R (paa_ann_shrink AA) M model) K.

(* [comment removed for export] *)
Definition ann_delete_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (sp r : Z),
    ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    vec_at M v b k stk ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5.defined M' b (32 * 2 ^ k) -> PMSPA.accA M' b (32 * 2 ^ k) ->
        (forall i, (i < length stk)%nat -> PM.pstate_at segs M' (b + 32 * Z.of_nat i) (nth i stk PM.ps_root)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R (paa_ann_delete AA) M model) K.

End Specs.
End PMSAX.
