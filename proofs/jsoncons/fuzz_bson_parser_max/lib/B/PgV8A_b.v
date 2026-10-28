(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceABx PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGV8A.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable FC : list Z.          (* [comment removed for export] *)

Abbreviation accA := (PMSPA.accA).
Definition annA : (word -> option byte) -> Z -> Z -> Z -> Prop := fun M b u c => HAJ.ann_shadow M b u c.
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation nullis_at := (PM.nullis_at segs A accA).
Abbreviation src_fields_at := (PM.src_fields_at segs accA).
Abbreviation v8_atA := (PGV8.v8_at segs accA annA).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation pm_scr := PMSPA.pm_scr.
Abbreviation ffroomB := (PGSA.ffroomB FC).
Abbreviation ofr := PGSA.ofr.
Abbreviation HV := (PMSPA.HV L ar).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vu8_grow_spec (pc : Z) (is_append : bool) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v a sp r g : Z) (x : PGV8.v8),
    ri_inv HI (PGV8.v8_own x ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 a -> aobjA FF v 24 -> v mod 8 = 0 -> accA M v 24 ->
    v8_atA M v x -> PGV8.v8_ok x g ->
    (* [comment removed for export] *)
    (if is_append then 1 <= a /\ PGV8.v8_size x + a < 2 ^ 64 else 0 <= a < 2 ^ 64) ->
    PGV8.v8_grow_ok x (if is_append then PGV8.v8_size x + a else a) ->
    PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 HV x g)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PGV8.v8) (g' : Z) (cr' : credit),
        regs_preserved R R' -> v8_atA M' v x' -> PGV8.v8_size x' = (if is_append then PGV8.v8_size x + a else a) -> PGV8.v8_ok x' g' ->
        PGV8.v8_cap x <= PGV8.v8_cap x' ->
        (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
        (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (if is_append then PGV8.v8_size x + a else a)) ->   (* [comment removed for export] *)
        L5CA.ahpres L ar LB FF sp (pm_scr 1) [(v, 24)] M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PGV8.pot_v8 HV x g)) (PMSPA.scA L (PGV8.pot_v8 HV x' g')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
Definition vu8_resize_spec (pc : Z) : Prop := vu8_grow_spec pc false.
Definition vu8_append_spec (pc : Z) : Prop := vu8_grow_spec pc true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation vowner := PGV8.vowner.
Abbreviation vw_at := PGV8.vw_at.
Abbreviation vw_os := PGV8.vw_os.
Abbreviation vw_ois := PGV8.vw_ois.
Abbreviation vw_ov := PGV8.vw_ov.
Abbreviation vw_lo := PGV8.vw_lo.
Abbreviation vw_hi := PGV8.vw_hi.
Record vowner_ok (V : vowner) : Prop := {
  vo_src : forall M src x g OB, vw_at V M src x g OB ->
             src_fields_at M (vw_os V) (vw_ois V) (vw_ois V + 16) src /\ nullis_at M (vw_os V + 8) /\ L5.defined M (vw_os V) 296
             /\ v8_atA M (vw_ov V) x /\ PGV8.v8_ok x g;
  vo_lay : vw_lo V <= vw_os V /\ vw_os V + 296 <= vw_hi V /\ vw_lo V <= vw_ois V /\ vw_ois V + 272 <= vw_hi V
           /\ vw_lo V <= vw_ov V /\ vw_ov V + 24 <= vw_hi V /\ vw_hi V <= ar_sptop ar /\ vw_hi V <= 2 ^ 47
           /\ vw_os V mod 8 = 0 /\ vw_ois V mod 8 = 0 /\ vw_ov V mod 8 = 0 /\ 4096 <= vw_lo V
           /\ (vw_os V + 296 <= vw_ois V \/ vw_ois V + 272 <= vw_os V)
           /\ (vw_ov V + 24 <= vw_os V \/ vw_os V + 296 <= vw_ov V) /\ (vw_ov V + 24 <= vw_ois V \/ vw_ois V + 272 <= vw_ov V);
  (* [comment removed for export] *)
  vo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (x x' : PGV8.v8) (g g' : Z) (OB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (VM : vml),
             ofr FF (vw_lo V) (vw_hi V) -> vw_at V M src x g OB ->
             ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= vw_lo V \/ vw_hi V <= fst b) (PM.src_own src ++ PGV8.v8_own x ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (PGV8.v8_own x) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= vw_lo V \/ vw_hi V <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)
                              /\ app_mem (fst r) (snd r)) Wx ->      (* [comment removed for export] *)
             L5CA.ahpres L ar (OB ++ LBX) FF sp scr (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)] ++ Wx) M M' ->
             src_fields_at M' (vw_os V) (vw_ois V) (vw_ois V + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             v8_atA M' (vw_ov V) x' -> PGV8.v8_ok x' g' ->
             vw_at V M' src' x' g' OB
}.
(* [comment removed for export] *)
Definition src_of_vw (V : vowner) (x : PGV8.v8) (g : Z) : PGS.owner :=
  {| PGS.ow_at := fun M src OB' => exists OB, OB' = PGV8.v8_own x ++ OB /\ vw_at V M src x g OB;
     PGS.ow_os := vw_os V; PGS.ow_ois := vw_ois V; PGS.ow_lo := vw_lo V; PGS.ow_hi := vw_hi V;
     PGS.ow_win := fun M src OB' p k => 0 <= k /\ exists b n c, x = PGV8.V8Blk b n c /\ b <= p /\ p + k <= b + n |}.
       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_span_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : PGV8.v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomB 6 FF LK -> ffrsA FF sp ->
    ofr FF (vw_lo V) (vw_hi V) ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (vw_ov V) -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> PGV8.v8_room x (PM.unread src sm) ->
    PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 HV x g)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        PMSP.consumed src src' sm sm' = n ->
        ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PGV8.v8_own x' ++ OB) ptr n) ->
        L5.defined M' ptr n -> accA M' ptr n ->
        (n = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 6) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PGV8.pot_v8 HV x g)) (PMSPA.scA L (PGV8.pot_v8 HV x' g')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : PGV8.v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 5 -> ffroomB 5 FF LK -> ffrsA FF sp ->
    ofr FF (vw_lo V) (vw_hi V) ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 (vw_ov V) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> PGV8.v8_size x = 0 -> PGV8.v8_room x (PM.unread src sm) ->
    PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 HV x g)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> PGV8.v8_size x' = d ->
        (d = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 5) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PGV8.pot_v8 HV x g)) (PMSPA.scA L (PGV8.pot_v8 HV x' g')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Specs.
End PGV8A.
