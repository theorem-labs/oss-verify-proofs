(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core
     L5KnA L5LazyA L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecs PmSpecsA
     PeCLayout PeCSink PeCStatics PeCModel PeCSpecs PeCSinkA PeCStaticsA PeCModelA PeCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECTXSA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation frame_ok5 := PECA.frame_ok5.

(* [comment removed for export] *)
Definition cstr_resize_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o n sp r tg : Z) (s : PM.vstr),
    ri_inv HI (PM.vs_own s ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> aobjA FF o 24 -> o mod 8 = 0 ->
    PM.vstr_at segs accA M o s -> PM.tb_ok s tg -> 0 <= n <= PM.vs_size s + PM.CHUNK -> n < 2 ^ 26 + PM.CHUNK ->
    PMSP.credit_le (scA (PM.pot_text HV s tg)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.vstr) (tg' : Z) (cr' : credit),
        regs_preserved R R' -> PM.vstr_at segs accA M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
        (forall l, Z.of_nat (length l) <= Z.min n (PM.vs_size s) -> L5.bytes_at segs M (PM.vs_data o s) l -> L5.bytes_at segs M' (PM.vs_data o s') l) ->
        (n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' tg')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R (pa_str_resize A) M model) K.

(* [comment removed for export] *)
Definition csrd_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb len : Z) (pl tl : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 5 -> ffroomA 5 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 16 ->
    getr R 10%bv = Z_to_bv 64 (PMSPA.o_src A fb) -> getr R 11%bv = Z_to_bv 64 (PMSPA.o_tb A fb) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    PM.parser_at segs A accA annA M (PMSPA.o_p A fb) (PMSPA.o_is A fb) s -> PM.iss_at segs A accA M (PMSPA.o_is A fb) str sm ->
    PMSTA.base_okA segs A M -> accA M (PMSPA.o_p A fb) PECA.RDR_BYTES -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> PM.unread (PM.p_src s) sm < 2 ^ 26 -> PM.vs_size (PM.p_tb s) + PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    PECS.payload_ok pl -> PEC.content_ok segs A M fb pl (PM.p_src s) str sm ->
    Z.of_nat (length tl) = PM.vs_size (PM.p_tb s) -> L5.bytes_at segs M (PM.vs_data (PMSPA.o_tb A fb) (PM.p_tb s)) tl ->
    PMSP.credit_le (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSPA.consumed (PM.p_src s) (PM.p_src s') sm sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s) + d ->
        d = Z.min len (PM.unread (PM.p_src s) sm) ->
        L5.bytes_at segs M' (PM.vs_data (PMSPA.o_tb A fb) (PM.p_tb s')) (tl ++ UbjRef.slice pl (PEC.pos_of pl (PM.p_src s) sm) d) ->
        PM.parser_at segs A accA annA M' (PMSPA.o_p A fb) (PMSPA.o_is A fb) s' -> PM.iss_at segs A accA M' (PMSPA.o_is A fb) str sm' ->
        PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' ->
        PEC.content_ok segs A M' fb pl (PM.p_src s') str sm' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 5) (PMSPA.W_srcf A fb ++ [(PMSPA.o_tb A fb, 24)]) M M' ->
        PMSP.credit_keep cr cr' (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) (scA (PM.pot_text HV (PM.p_tb s') (PM.p_tg s'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R (pa_srd_read A) M model) K.

End Specs.
End PECTXSA.
