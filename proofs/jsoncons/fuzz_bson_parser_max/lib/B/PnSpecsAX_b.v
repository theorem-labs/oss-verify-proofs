(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSAX.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation bvec_at := (PNM.bvec_at segs PMSPA.accA PMSPA.annA).
Local Abbreviation BSZ := PNM.BSZ.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vec_pre (M : word -> option byte) (v b k : Z) (stk : list PNM.bstate) (own : list (Z * Z)) : Prop :=
  (L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0 /\ b = 0 /\ k = 0 /\ stk = [] /\ own = [])
  \/ (bvec_at M v b k stk /\ own = PNM.bvec_own b k).

(* [comment removed for export] *)
Definition full_or_empty (k : Z) (stk : list PNM.bstate) (own : list (Z * Z)) : Prop := own = [] \/ Z.of_nat (length stk) = 2 ^ k.
Definition k_next (b k : Z) : Z := if Z.eqb b 0 then 0 else k + 1.
Definition push_out (b k : Z) (stk : list PNM.bstate) (own : list (Z * Z)) (b' k' : Z) (cr cr' : credit) : Prop :=
  (own <> [] /\ Z.of_nat (length stk) < 2 ^ k /\ b' = b /\ k' = k /\ cr' = cr)
  \/ (full_or_empty k stk own /\ k' = k_next b k /\ cr' = adebit L cr (BSZ * 2 ^ k')).

(* [comment removed for export] *)
Definition arg_ok (FF : list fframe) (sp v p n : Z) : Prop :=
  (PMSPA.aobjA FF p n \/ (sp <= p /\ p + n <= ar_sptop ar)) /\ (p + n <= v \/ v + 24 <= p).
(* [comment removed for export] *)
Definition arg_cell (M : word -> option byte) (FF : list fframe) (sp v p n : Z) : Prop :=
  p mod n = 0 /\ PMSPA.accA M p n /\ arg_ok FF sp v p n /\ byte_at M (HeapIfaceA.S p) 0.

(* [comment removed for export] *)
Definition push_spec_at (pc : Z) (X : Type) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> X -> Prop)
           (mk : X -> Z -> PNM.bstate) (dom : Z -> list PNM.bstate -> list (Z * Z) -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PNM.bstate) (own : list (Z * Z))
         (det : X) (sp r : Z),
    ri_inv HI (own ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    vec_pre M v b k stk own -> dom k stk own -> (full_or_empty k stk own -> k <= 10) ->
    PMSTA.base_okA segs A M ->           (* [comment removed for export] *)
    cells FF sp v M R det ->
    (full_or_empty k stk own -> acredit_ok L cr (BSZ * 2 ^ (k_next b k))) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (b' k' lenv : Z) (cr' : credit),
        regs_preserved R R' -> 0 <= lenv < 2 ^ 64 ->
        bvec_at M' v b' k' (stk ++ [mk det lenv]) -> PMSPA.accA M' v 24 -> PMSTA.base_okA segs A M' ->
        push_out b k stk own b' k' cr cr' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition cells_cont (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (det : Z * Z) : Prop :=
  exists p1 p2 p3, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ getr R 13%bv = Z_to_bv 64 p3
    /\ arg_cell M FF sp v p1 4 /\ arg_cell M FF sp v p2 4 /\ arg_cell M FF sp v p3 8
    /\ L5.u32_at segs M p1 (fst det) /\ L5.defined M p2 4 /\ L5.u64_at segs M p3 (snd det)
    /\ 0 <= fst det < 2 ^ 31 /\ 0 <= snd det < 2 ^ 64.
Definition mk_cont (det : Z * Z) (lenv : Z) : PNM.bstate := PNM.BS (fst det) lenv (snd det) 0 0.

(* [comment removed for export] *)
Definition cells_root (FF : list fframe) (sp v : Z) (M : word -> option byte) (R : bvmap 5 word) (det : Z * Z * Z) : Prop :=
  exists p1 p2 p3, getr R 11%bv = Z_to_bv 64 p1 /\ getr R 12%bv = Z_to_bv 64 p2 /\ getr R 13%bv = Z_to_bv 64 p3
    /\ arg_cell M FF sp v p1 4 /\ arg_cell M FF sp v p2 4 /\ arg_cell M FF sp v p3 4
    /\ L5.u32_at segs M p1 (fst (fst det)) /\ L5.u32_at segs M p2 (snd (fst det)) /\ L5.u32_at segs M p3 (snd det)
    /\ 0 <= fst (fst det) < 2 ^ 31 /\ 0 <= snd (fst det) < 2 ^ 31 /\ 0 <= snd det < 2 ^ 31.
Definition mk_root (det : Z * Z * Z) (lenv : Z) : PNM.bstate := PNM.BS (fst (fst det)) (snd (fst det)) (snd det) 0 0.

Definition dom_cont (k : Z) (stk : list PNM.bstate) (own : list (Z * Z)) : Prop := own <> [].
Definition dom_root (k : Z) (stk : list PNM.bstate) (own : list (Z * Z)) : Prop := own = [] \/ Z.of_nat (length stk) < 2 ^ k.
Definition push_cont_spec (pc : Z) : Prop := push_spec_at pc (Z * Z) cells_cont mk_cont dom_cont.
Definition push_root_spec (pc : Z) : Prop := push_spec_at pc (Z * Z * Z) cells_root mk_root dom_root.

(* [comment removed for export] *)
Definition ann_shrink_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k old : Z) (stk : list PNM.bstate) (sp r : Z),
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    Z.of_nat (length stk) <= old <= 2 ^ k ->
    (* [comment removed for export] *)
    L5.u64_at segs M v b -> L5.u64_at segs M (v + 8) (b + BSZ * Z.of_nat (length stk)) -> L5.u64_at segs M (v + 16) (b + BSZ * 2 ^ k) ->
    0 <= k <= 11 -> b mod 16 = 0 -> L5.defined M b (BSZ * 2 ^ k) -> PMSPA.accA M b (BSZ * old) -> PMSPA.annA M b (BSZ * old) (BSZ * 2 ^ k) ->
    (forall i, (i < length stk)%nat -> PNM.bstate_at segs M (b + BSZ * Z.of_nat i) (nth i stk PNM.bs_root)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> bvec_at M' v b k stk -> PMSPA.accA M' v 24 ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition ann_delete_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PNM.bstate) (sp r : Z),
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    bvec_at M v b k stk ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5.defined M' b (BSZ * 2 ^ k) -> PMSPA.accA M' b (BSZ * 2 ^ k) ->
        (forall i, (i < length stk)%nat -> PNM.bstate_at segs M' (b + BSZ * Z.of_nat i) (nth i stk PNM.bs_root)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Local Abbreviation ffroomB := (PGSA.ffroomB PNRA.FCB).
Definition vec_dtor_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PNM.bstate),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA A L ar R M sp r 1 -> ffroomB 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at segs M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    bvec_at M v b k stk -> In (b, PNM.BSZ * 2 ^ k) LB ->
    PMSTA.base_okA segs A M ->           (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> PMSTA.base_okA segs A M' ->
        L5CA.ahpres L ar (lb_remove b LB) FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove b LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition vu8_dtor_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v sp r : Z) (x : PGV8.v8),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA A L ar R M sp r 1 -> ffroomB 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at segs M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    PGV8.v8_at segs PMSPA.accA PMSPA.annA M v x -> incl (PGV8.v8_own x) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (PNRA.lb_remove_v8 x LB) FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNRA.lb_remove_v8 x LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition v8_hdr (M : word -> option byte) (v : Z) (x : PGV8.v8) : Prop :=
  L5.defined M v 24 /\
  match x with
  | PGV8.V8Null => L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0
  | PGV8.V8Blk b n c => L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
                       /\ 0 <= n <= c /\ 1 <= c <= 2 ^ 27 /\ 4096 <= b /\ b mod 16 = 0 /\ L5.defined M b c
  end.
Local Abbreviation v8_at := (PGV8.v8_at segs PMSPA.accA PMSPA.annA).

Definition ann_shrink_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v old : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_hdr M v x -> PGV8.v8_size x <= old <= PGV8.v8_cap x ->
    (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M b old /\ PMSPA.annA M b old c) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> v8_at M' v x ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition ann_delete_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_at M v x ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        v8_hdr M' v x -> PMSPA.accA M' v 24 ->
        (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M' b c) ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

End Specs.
End PNSAX.
