(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCStatics PeCModel PeCSinkA PeCStaticsA PeCModelA PeCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRRZ.
Section SpecZ.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable P : PESKA.sink_policyA.
Definition reader_read_specZ : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA A L ar R M sp r 11 ->
    PMSPA.ffroomA 11 FF LK -> PMSPA.ffrsA FF sp -> PECA.frame_ok5 FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (PMSPA.o_p A fb) -> getr R 11%bv = Z_to_bv 64 (PMSPA.o_ec A fb) ->
    PM.parser_at segs A PMSPA.accA PMSPA.annA M (PMSPA.o_p A fb) (PMSPA.o_is A fb) s /\ PM.iss_at segs A PMSPA.accA M (PMSPA.o_is A fb) str sm
    /\ PECA.enc_atA segs E L ar M (PMSPA.o_v A fb) fb en /\ L5.u64_at segs M (PMSPA.o_p A fb + 384) (PMSPA.o_v A fb)
    /\ PESKA.sink_atA segs L ar P M (PESK.o_sink E fb) k /\ PMSTA.base_okA segs A M /\ PESTA.err_okA segs A AA E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
    /\ PEC.content_ok segs A M fb p (PM.p_src s) str sm /\ PMSPA.ec_at segs M (PMSPA.o_ec A fb) 0 cat
    /\ PMSPA.accA M (PMSPA.o_p A fb) PECA.RDR_BYTES ->
    (1 <= length (PM.p_stk s))%nat -> PEC.pos_of p (PM.p_src s) sm = 0 ->
    PM.sr_rem (PM.p_src s) = 0 ->
    PEC.en_stk en = [] -> PEC.en_depth en = 0 -> PESK.sk_z k = 0 ->
    incl (PM.vs_own str) LBX ->
    PECSPA.payload_ok p -> (forall n, PESKA.spa_hb P (s_hi (run n p UbjRef.init))) ->
    PMSP.credit_le (PECA.pot_allA L ar P (PMSPA.pst_reset s) en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n : nat)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        halted (run n p UbjRef.init) = true ->
        PM.parser_at segs A PMSPA.accA PMSPA.annA M' (PMSPA.o_p A fb) (PMSPA.o_is A fb) s' /\ PM.iss_at segs A PMSPA.accA M' (PMSPA.o_is A fb) str sm'
        /\ PECA.enc_atA segs E L ar M' (PMSPA.o_v A fb) fb en' /\ PESKA.sink_atA segs L ar P M' (PESK.o_sink E fb) k'
        /\ PMSTA.base_okA segs A M' /\ PESTA.err_okA segs A AA E M' e' /\ L5.defined M' (PMSPA.o_ec A fb) 16
        /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 11) (PEC.W_crun A E fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_allA L ar P (PMSPA.pst_reset s) en k) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R (pa_reader_read A) M model) K.

End SpecZ.
End PECRRZ.
