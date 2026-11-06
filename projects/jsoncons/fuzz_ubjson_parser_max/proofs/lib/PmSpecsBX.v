(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
L5KnA L5LazyA L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSBX.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition reader_read_spec : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 11 -> PMSPA.ffroomA 11 FF LK -> PMSPA.ffrsA FF sp -> PMSPA.frame_okA FF fb -> sp mod 32 = 0 ->
getr R 10%bv = Z_to_bv 64 (PMSPA.o_p A fb) -> getr R 11%bv = Z_to_bv 64 (PMSPA.o_ec A fb) ->
PMSPA.run_pre segs A AA M fb s str sm e -> incl (PM.vs_own str) LBX -> (1 <= length (PM.p_stk s))%nat ->
PMSPA.ec_at segs M (PMSPA.o_ec A fb) 0 cat -> PMSPA.accA M (PMSPA.o_p A fb + 384) 8 ->
PM.unread (PM.p_src s) sm < 2 ^ 26 ->
PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (PMSPA.pst_reset s))) cr ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
(s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R R' ->
PMSPA.parse_post segs A AA M' fb (PMSPA.pst_reset s) s' str sm sm' e e' ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 11) (PMSPA.W_run A fb) M M' ->
PMSPA.credit_keep cr cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (PMSPA.pst_reset s))) PMSPA.cr0 ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R (pa_reader_read A) M model) K.
Definition slow_spec_at (pc : Z) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> PM.pstate -> Prop) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (own : list (Z * Z))
(c : PM.pstate) (sp r : Z),
ri_inv HI (own ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
PMSAX.vec_pre segs M v b k stk own -> (own = [] \/ Z.of_nat (length stk) = 2 ^ k) -> k <= 10 ->
cells FF sp v M R c ->
acredit_ok L cr (32 * 2 ^ (if Z.eqb b 0 then 0 else k + 1)) ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
(b' k' : Z) (cr' : credit),
regs_preserved R R' -> PM.vec_at segs PMSPA.accA PMSPA.annA M' v b' k' (stk ++ [c]) -> PMSPA.accA M' v 24 ->
k' = (if Z.eqb b 0 then 0 else k + 1) -> cr' = adebit L cr (32 * 2 ^ k') ->
getr R' 10%bv = Z_to_bv 64 (b' + 32 * Z.of_nat (length (stk ++ [c]))) ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vec_own b' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
Definition cone_spec_at (pc : Z) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> PM.pstate -> Prop) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate)
(c : PM.pstate) (sp r : Z),
ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
PM.vec_at segs PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) < 2 ^ k ->
cells FF sp v M R c ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
regs_preserved R R' -> PM.vec_at segs PMSPA.accA PMSPA.annA M' v b k (stk ++ [c]) -> PMSPA.accA M' v 24 ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
Definition ann_shrink_spec_at (pc : Z) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k old : Z) (stk : list PM.pstate) (sp r : Z),
ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
Z.of_nat (length stk) <= old <= 2 ^ k ->
L5.u64_at segs M v b -> L5.u64_at segs M (v + 8) (b + 32 * Z.of_nat (length stk)) -> L5.u64_at segs M (v + 16) (b + 32 * 2 ^ k) ->
0 <= k <= 11 -> b mod 16 = 0 -> L5.defined M b (32 * 2 ^ k) -> PMSPA.accA M b (32 * old) -> PMSPA.annA M b (32 * old) (32 * 2 ^ k) ->
(forall i, (i < length stk)%nat -> PM.pstate_at segs M (b + 32 * Z.of_nat i) (nth i stk PM.ps_root)) ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
regs_preserved R R' -> PM.vec_at segs PMSPA.accA PMSPA.annA M' v b k stk -> PMSPA.accA M' v 24 ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
Definition ann_delete_spec_at (pc : Z) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (sp r : Z),
ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
PM.vec_at segs PMSPA.accA PMSPA.annA M v b k stk ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
regs_preserved R R' ->
L5.defined M' b (32 * 2 ^ k) -> PMSPA.accA M' b (32 * 2 ^ k) ->
(forall i, (i < length stk)%nat -> PM.pstate_at segs M' (b + 32 * Z.of_nat i) (nth i stk PM.ps_root)) ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
Definition vec_clear_spec_at (pc : Z) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (sp r : Z),
ri_inv HI (PM.vec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
PM.vec_at segs PMSPA.accA PMSPA.annA M v b k stk ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
regs_preserved R R' -> PM.vec_at segs PMSPA.accA PMSPA.annA M' v b k [] -> PMSPA.accA M' v 24 ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
End Specs.
End PMSBX.
Module PMBX.
Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition reader_read_spec := @PMSBX.reader_read_spec SCFG_P PMB.RSEGS PMB.AD PMB.AAD L ar HI.
Definition slow_mi_spec := @PMSBX.slow_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI (paa_esp_mi PMB.AAD) (PMSAX.cells_mi PMB.RSEGS ar).
Definition slow_miu_spec := @PMSBX.slow_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI (paa_esp_miu PMB.AAD) (PMSAX.cells_miu PMB.RSEGS ar).
Definition slow_ms_spec := @PMSBX.slow_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI (paa_esp_ms PMB.AAD) (PMSAX.cells_ms PMB.RSEGS ar).
Definition slow_msu_spec := @PMSBX.slow_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI (paa_esp_msu PMB.AAD) (PMSAX.cells_msu PMB.RSEGS ar).
Definition cone_mi_spec := @PMSBX.cone_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xac324 (PMSAX.cells_mi PMB.RSEGS ar).
Definition cone_miu_spec := @PMSBX.cone_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xadd40 (PMSAX.cells_miu PMB.RSEGS ar).
Definition cone_msu_spec := @PMSBX.cone_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xb35d4 (PMSAX.cells_msu PMB.RSEGS ar).
Definition cone_ms_spec := @PMSBX.cone_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xb39e4 (PMSAX.cells_ms PMB.RSEGS ar).
Definition ann_shrink_spec := @PMSBX.ann_shrink_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xab054.
Definition ann_delete_spec := @PMSBX.ann_delete_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xaaf98.
Definition vec_clear_spec := @PMSBX.vec_clear_spec_at SCFG_P PMB.RSEGS PMB.AD L ar HI 0xaaf04.
End Names.
End PMBX.
