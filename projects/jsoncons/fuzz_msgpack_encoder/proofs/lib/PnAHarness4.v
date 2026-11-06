(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnAHarnessKit4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAHarnessP2.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA4.
Import L5A. Import L5CA. Import L5SAR. Import PQHAS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
          (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 160) (V2 - 160) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487392 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

(* [comment removed for export] *)
Local Notation mparser_at := (PQMA.mparser_at RSEGS PMA.AD PMSPA.accA PQRA.annA (pa_vp_parser PMA.AD)).
Local Notation adaptor_at := (PQMA.adaptor_at RSEGS PMA.AD PMSPA.accA PQRA.annA (qa_vp_adaptor PnLayoutQA.QADDR_A)).
Lemma aobj_fbB FF0 fb a n : PNRA.frame_okB FF0 fb -> fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF0 a n.
Proof.
  intros ((rs & Hf) & _) X1 X2. exists (fb, 5, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
Qed.
Lemma stage4 (RDC : PQRAa.reader_ctor_spec L ar HI) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (K : TSet)
      (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (n : Z) (g : PMST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 V2 cls F -> K [] ->
  PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M5 ->
  getr R5 (reg 1) = Z_to_bv 64 0xaf4b4 -> getr R5 (reg 10) = Z_to_bv 64 (F + 592) -> getr R5 (reg 11) = Z_to_bv 64 (F + 96) ->
  getr R5 (reg 12) = Z_to_bv 64 (F + 496) -> getr R5 (reg 13) = Z_to_bv 64 (F + 1168) -> getr R5 (reg 14) = Z_to_bv 64 (V2 - 112) ->
  getr R5 (reg 18) = Z_to_bv 64 2147450880 -> getr R5 (reg 20) = Z_to_bv 64 1024 -> getr R5 (reg 22) = Z_to_bv 64 (F + 432) ->
  getr R5 (reg 23) = Z_to_bv 64 (F + 520) -> getr R5 (reg 24) = Z_to_bv 64 (F + 496) -> getr R5 (reg 25) = Z_to_bv 64 (F + 592) ->
  getr R5 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M5 s s' sm -> PM.vs_size s' = n -> PM.sm_g sm = PM.vs_data (F + 96 + 80) s' -> PM.sm_st sm = 0 ->
  PQHAK5.hse0 L ar F M5 ->
  L5.u64_at RSEGS M5 (F + 1168) 1379592 -> L5.u64_at RSEGS M5 (F + 1176) 1379632 -> L5.u32_at RSEGS M5 (F + 1184) 1024 ->
  shadow_zero M5 (F + 432) 3 -> shadow_zero M5 (F + 496) 7 -> shadow_zero M5 (F + 592) 63 -> shadow_zero M5 (F + 1168) 3 ->
  L5.u64_at RSEGS M5 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M5 (V2 - 136) F ->
  PMSPA.credit_le (PMSPA.scA L (PQRHA.rdr_cost (PMSPA.HV L ar))) cr5 ->
  (forall (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (qc b b' : Z),
      Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 V2 cls F ->
      PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M6 ->
      getr R6 (reg 1) = Z_to_bv 64 0xaf4d8 -> getr R6 (reg 18) = Z_to_bv 64 2147450880 -> getr R6 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R6 (reg 21) = Z_to_bv 64 (F + 96) -> getr R6 (reg 22) = Z_to_bv 64 (F + 432) -> getr R6 (reg 23) = Z_to_bv 64 (F + 520) ->
      getr R6 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R6 (reg 25) = Z_to_bv 64 (F + 592) -> getr R6 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M6 s s' sm -> PM.vs_size s' = n -> PM.sm_g sm = PM.vs_data (F + 96 + 80) s' -> PM.sm_st sm = 0 ->
      PQHAK4.hpar4 F M6 (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ->
      PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PQRHA.rdr_cost (PMSPA.HV L ar))) PMSPA.cr0 ->
      PQHAK5.hse0 L ar F M6 ->
      L5.u32_at RSEGS M6 (F + 1232) 0 -> shadow_zero M6 (F + 1232) 2 -> shadow_zero M6 (F + 432) 3 -> shadow_zero M6 (F + 496) 7 ->
      L5.u64_at RSEGS M6 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M6 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xf8930 M6 model6) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0xafeac M5 model5) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R13 R14 R18 R20 R22 R23 R24 R25 R26 HB5 SZ5 SMG SMST HSE5 O1168 O1176 O1184 SZK SZE SZP SZO HSTKa HSTKb CRD KONT.
  pose proof HB5 as (VS0 & IS0 & SZI).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M5 model5 LK5 cr5 A5 BI)
    as ((VW5 & VIC5 & VSB5 & VUAR5 & VMS5) & VOWN5 & (VFD5 & VFW5 & VFSW5 & VFLC5 & VFLW5) & (FLCc5 & FLV5 & FV5 & SPV5 & FSV5)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (FDEF5 : L5.defined M5 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A5 model5) M5 F 2048 FV5)); exact VFD5).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PQRAa.reader_ctor_spec, PQRHA.reader_ctor_spec in RDC. unfold PQRA.o_a, PQRA.o_p, PQRA.o_is, PQRA.o_v, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is, PmSpecs.PMSP.o_v in RDC.
  cbn [pa_reader_ctor pa_off_p pa_off_is pa_off_v pa_vp_opts qa_off_a qa_off_vref PQRAa.AD PQRAa.AQ PMA.AD ADDR_A PnLayoutQA.QADDR_A] in RDC.
  change PQMA.MAX_DEPTH with 1024 in RDC. change PQRHA.RSIZE with 504 in RDC. change PQRHA.RDRC_H with 7 in RDC.
  apply (RDC fx5 R5 M5 model5 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK5 A5 cr5 (V2 - 160) 0xaf4b4 F (F + 1168) s' sm B1 B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_roomB; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { pose proof (Z.div_mod V2 32 ltac:(clear; lia)) as DM. rewrite V2A, Z.add_0_r in DM. replace (V2 - 160) with ((V2 / 32 * 2 - 10) * 16) by (clear - DM; lia). apply Z.mod_mul. clear; lia. }
  { exact (PQHASK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { rewrite L5K.rl13. exact R13. }
  { apply (aobj_fbB FF' F (F + 1168) 24 (PQHASK.callee_frame FF V2 F FAL)); lia. }
  { right. clear. lia. }
  { clear - FAL. lia. }
  { split; [exact O1168|]. split; [replace (F + 1168 + 16) with (F + 1184) by lia; exact O1184| apply (L5.defined_sub M5 F 2048 (F + 1168) 24 FDEF5); lia]. }
  { apply (PMARS1.acc_of_shadow_zero M5 (F + 1168) 3 (F + 1168) 24 SZO); [clear - FM8; lia| lia| lia]. }
  { apply (L5.defined_sub M5 F 2048 (F + 592) 504 FDEF5); lia. }
  { apply (PMARS1.acc_of_shadow_zero M5 (F + 592) 63 (F + 592) 504 SZP); [clear - FM8; lia| lia| lia]. }
  { exact IS0. }
  { exact LSB. }
  { exact LSL. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' qc b b' cr' RP' PAT AAT VREF HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 7) with 26624 in HP'.
  replace (F + 592 + 400) with (F + 992) in AAT, VREF by (clear; lia). replace (F + 592 + 496) with (F + 1088) in VREF by (clear; lia).
  rewrite app_assoc in HH'.
  assert (WFI : PQHAK2.wfi F [(F + 592, 504)]) by (apply PQHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PQHAK2.wfi_nil]).
  assert (LS' : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M').
  { apply (PQHAK.ls_ahpres L C LY _ ar _ FF' (V2 - 160) _ [(F + 592, 504)] M5 M' HP'); [| exact LS].
    apply PQHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PQHAK.far_nil]. }
  assert (BI' : Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W (PM.vs_own s' ++ PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) _ M5 model5 LK5 cr5 A5 M' model' LK' cr' Aw' 26624 [(F + 592, 504)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R5 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y19 & Y21 & Y27 & Y3 & Y4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R5 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 1024) by (rewrite (cs_of_preserved R5 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R5 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R5 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R5 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R5 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R5 R' 26 RP') by inl; exact R26).
  (* [comment removed for export] *)
  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M5 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M5 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (FIN5 : In (F, 5, V2 - 160 + 32) (FF' ++ LK5)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (HB' : PQHAK5.hbaseN F M' s s' sm).
  { eapply PQHAK5.hbaseN_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB5 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | apply incl_refl | (intros x Hx; apply in_or_app; left; exact Hx)
      | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil]) | lia ]. }
  pose proof HB' as (VS' & IS' & _).
  assert (HSE' : PQHAK5.hse0 L ar F M').
  { eapply PQHAK5.hse0_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HSE5 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | apply incl_refl | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil]) | lia ]. }
  assert (SZK' : shadow_zero M' (F + 432) 3)
    by (apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 26624 [(F + 592, 504)] M5 M' (F, 5, V2 - 160 + 32) F (F + 432) 3 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZK]).
  assert (SZE' : shadow_zero M' (F + 496) 7)
    by (apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 26624 [(F + 592, 504)] M5 M' (F, 5, V2 - 160 + 32) F (F + 496) 7 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZE]).
  assert (SZP' : shadow_zero M' (F + 592) 63)
    by (apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 26624 [(F + 592, 504)] M5 M' (F, 5, V2 - 160 + 32) F (F + 592) 63 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZP]).
  assert (SZI' : shadow_zero M' (F + 96) 34)
    by (apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 26624 [(F + 592, 504)] M5 M' (F, 5, V2 - 160 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZI]).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (OFI : 65536 + 6971392 <= F \/ F + 2048 <= 65536) by (clear - FR; lia).
  assert (OFL : 65536 + 6971392 <= fl \/ fl + 1 <= 65536) by (clear - FLR; lia).
  LeanFeed.pfeed ident:(P) (PQAHP2.qhaG_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32 | exact OFI | exact OFL
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PQAHP2.aligned; exact V2A) ]).
  destruct P as (fx6 & R6 & M6v & MG6 & eFR & eFZ & (eMS & eKS & eR1 & eR20 & eR24 & EQ)).
  set (W6 := fun a => F + 1232 <= a < F + 1232 + 4 \/ F / 8 + 2147451026 <= a < F / 8 + 2147451026 + 3 \/ F / 8 + 2147451034 <= a < F / 8 + 2147451034 + 2).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx6 R' 0xaf4b4 R6 0xf8930 M6v W6 K HH' AM' eMS MG6).
  { intros a Ha Hna. apply eFZ; [exact Ha|..]; intros X; apply Hna; subst W6; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W6; cbn beta in Wa. split.
    - destruct Wa as [Wa|[Wa|Wa]].
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H' M6 = M6v) in VIS6.
  decompose [and] EQ. clear EQ.
  assert (BI6 : Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M6 model6 W6 BI' HH6 AM6 MRT6 MGM6 FR6).
    intros a Wa. subst W6; cbn beta in Wa. right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI6 : rinvH R R6 V2 cls F) by (apply (rinvH_ks R R' R6 V2 cls F PQAHP2.KS_qhaG RI' eKS); vm_compute; reflexivity).
  assert (LS6 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M6).
  { apply (PQHAK.ls_piece _ M' M6 W6 FR6); [| exact LS']. intros a Wa. subst W6; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF6 : PQHAK2.pfoot F (V2 - 160) V2 W6) by (intros a Wa; subst W6; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA32 : PQHAK2.oav W6 (F + 32) 24) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA96 : PQHAK2.oav W6 (F + 96) 272) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA464 : PQHAK2.oav W6 (F + 592) 400) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA864 : PQHAK2.oav W6 (F + 992) 96) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA504 : PQHAK2.oav W6 (F + 592) 504) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA496 : PQHAK2.oav W6 (F + 496) 56) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA432 : PQHAK2.oav W6 (F + 432) 24) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (Q1232 : (F + 1232) / 8 + HeapIfaceA.SB = F / 8 + 2147451034) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VS6 : PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s).
  { apply (PQHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 32) s);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx| clear - FR; lia| clear - FR; lia| exact OA32| exact VS']. }
  assert (IS6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 (F + 96) s' sm).
  { apply (PQHAK2.iss_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 96) s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| exact OA96| exact IS']. }
  assert (PA6 : mparser_at M6 (F + 592) (F + 96) (PQRHA.mparser_init qc b)).
  { apply (PQHAK4.mparser_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 592) (F + 96));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; unfold PQMA.PSIZE; lia| exact OA464| exact PAT]. }
  assert (AA6 : adaptor_at M6 (F + 992) (F + 496) (PQRHA.ast_init b')).
  { apply (PQHAK4.adaptor_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 992) (F + 496));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; exact Hx| clear - FR; lia| clear - FR; unfold PQMA.ASIZE; lia| exact OA864| exact AAT]. }
  assert (HB6 : PQHAK5.hbaseN F M6 s s' sm).
  { exact (conj VS6 (conj IS6 ltac:(apply (PQHAK2.shz_agA M' M6 (F + 96) 272 (F + 96) 34 (PQHAK.agA_frame M' M6 W6 (F + 96) 272 FR6 ltac:(clear - FR; lia) ltac:(clear - FR; lia) OA96)); [lia| lia| clear - FM8; lia| lia| exact (proj2 (proj2 HB'))]))). }
  assert (HSE6 : PQHAK5.hse0 L ar F M6) by (apply (PQHAK5.hse0_piece L ar F FHF W6 M' M6 FR6); [exact OA432| exact OA496| exact HSE']).
  assert (FR6lo : forall a, 0 <= a < 2 ^ 64 -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) -> ~ (F + 1232 <= a < F + 1236) -> M6 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hr Hn. apply FR6; [exact Ha|]. subst W6; cbn beta. intros X. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hr. clear - Hr Hn X FBD. lia. }
  assert (HSTKa6 : L5.u64_at RSEGS M6 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M' M6 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
    intros i Hi; apply FR6lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (HSTKb6 : L5.u64_at RSEGS M6 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M' M6 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
    intros i Hi; apply FR6lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia]. }
  assert (AGR6 : PMFA.agA M' M6 (F + 592) 504) by (apply (PQHAK.agA_frame M' M6 W6 (F + 592) 504 FR6); [clear - FR; lia| clear - FR; lia| exact OA504]).
  assert (AVF : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PQHAK.avis_sub H' F 2048 (F + d) k FV'); lia).
  assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H' q k)
    by (intros q k Hd1 Hd2; apply (PQHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 q k FSV'); unfold HeapIfaceA.SB; lia).
  apply (KONT fx6 R6 M6 model6 LK' cr' Aw' qc b b' BI6 RI6 LS6).
  - exact eR1.
  - rewrite (eKS 18%nat) by inl. exact Y18.
  - exact eR20.
  - rewrite (eKS 21%nat) by inl. exact Y21.
  - rewrite (eKS 22%nat) by inl. exact Y22.
  - rewrite (eKS 23%nat) by inl. exact Y23.
  - exact eR24.
  - rewrite (eKS 25%nat) by inl. exact Y25.
  - rewrite (eKS 26%nat) by inl. exact Y26.
  - exact HB6.
  - exact SZ5.
  - exact SMG.
  - exact SMST.
  - split; [exact PA6| split; [exact AA6| split]].
    + apply (PQHAK2.u64_agA M' M6 (F + 592) 504 (F + 1088) _ AGR6); [lia| lia| lia| lia| exact VREF].
    + apply (PQHAK2.acc_of_shz M6 (F + 592) 63 (F + 592) 504); [| clear - FM8; lia| clear - FR; lia| lia| lia].
      apply (PQHAK2.shz_frame M' M6 W6 (F + 592) 63 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZP'].
      intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (E592 : (F + 592) / 8 = F / 8 + 74) by (clear - FM8; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      rewrite E592 in X. clear - X Hj FBD FR FBIG. lia.
  - assert (E0 : PMSPA.scA L PmSpecs.PMSP.cr0 = PMSPA.cr0) by (unfold PMSPA.scA, PmSpecs.PMSP.cr0, PMSPA.cr0; cbn [fst snd]; rewrite Z.mul_0_r; reflexivity).
    rewrite E0 in CK'. exact CK'.
  - exact HSE6.
  - apply (PQHAK.u32_vis H' M6 M6v (F + 1232) _ VV6 (AVF 1232 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PQHAK.shz_vis H' M6 M6v (F + 1232) 2 (F / 8 + 2147451034) VV6 (AVS (F / 8 + 2147451034) 2 ltac:(lia) ltac:(lia)) Q1232 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1) by (clear - Hj; lia).
    destruct J as [J|J]; subst j; gmem.
  - apply (PQHAK2.shz_frame M' M6 W6 (F + 432) 3 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZK'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E432 : (F + 432) / 8 = F / 8 + 54) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E432 in X. clear - X Hj FBD FR FBIG. lia.
  - apply (PQHAK2.shz_frame M' M6 W6 (F + 496) 7 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZE'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E496 : (F + 496) / 8 = F / 8 + 62) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E496 in X. clear - X Hj FBD FR FBIG. lia.
  - exact HSTKa6.
  - exact HSTKb6.
Qed.
End Stage.
End SCFG_1.
End PQHA4.
