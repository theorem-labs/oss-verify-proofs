(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnAHarnessKit4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA8.
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

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PQHAK2.wapart_nil | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil])]])
  | (apply PQHAK2.wapart_nil) | lia ].

Lemma stage8 (RDD : PQRAa.reader_dtor_spec L ar HI) (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (K : TSet)
      (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (s9 : PQMA.mpst) (st9 : NEMA.aest) (g : PMST.st) :
  Bv W (PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 V2 cls F -> K [] ->
  PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M9 ->
  getr R9 (reg 1) = Z_to_bv 64 0xaf508 -> getr R9 (reg 10) = Z_to_bv 64 (F + 592) -> getr R9 (reg 18) = Z_to_bv 64 2147450880 ->
  getr R9 (reg 20) = Z_to_bv 64 18446744073709551608 -> getr R9 (reg 21) = Z_to_bv 64 (F + 96) -> getr R9 (reg 22) = Z_to_bv 64 (F + 432) ->
  getr R9 (reg 23) = Z_to_bv 64 (F + 520) -> getr R9 (reg 24) = Z_to_bv 64 18446744073709551608 -> getr R9 (reg 25) = Z_to_bv 64 (F + 592) ->
  getr R9 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M9 s s' sm -> PQHAK4.hpar4 F M9 s9 (NEMA.ae_a st9) -> PQMA.mgrow_ok s9 -> NEMA.ae_ok st9 -> PQHAK5.hseF L ar F M9 (NEMA.ae_e st9) (NEMA.ae_s st9) ->
  L5.u64_at RSEGS M9 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M9 (V2 - 136) F ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
      Bv W ((NEM.enc_own (NEMA.ae_e st9) ++ NESK.sink_own (NEMA.ae_s st9)) ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr9 Aw' -> rinvH R R' V2 cls F ->
      PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M' ->
      getr R' (reg 18) = Z_to_bv 64 2147450880 -> getr R' (reg 20) = Z_to_bv 64 18446744073709551608 -> getr R' (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R' (reg 22) = Z_to_bv 64 (F + 432) -> getr R' (reg 23) = Z_to_bv 64 (F + 520) -> getr R' (reg 24) = Z_to_bv 64 18446744073709551608 ->
      getr R' (reg 25) = Z_to_bv 64 (F + 592) -> getr R' (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M' s s' sm -> PQHAK5.hseF L ar F M' (NEMA.ae_e st9) (NEMA.ae_s st9) ->
      L5.u64_at RSEGS M' (V2 - 144) (F + 32) -> L5.u64_at RSEGS M' (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx' R' 0xaf508 M' model') K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xaff54 M9 model9) K.
Proof.
  intros BI RI K0 LS R1a R10 R18 R20 R21 R22 R23 R24 R25 R26 HB0 HP0 GROW AEOK HSE0 HSTKa HSTKb KONT.
  pose proof AEOK as (AOK & _ & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (EK := NEM.enc_own (NEMA.ae_e st9) ++ NESK.sink_own (NEMA.ae_s st9)).
  set (LBXc := EK ++ PM.vs_own s' ++ PM.vs_own s). set (LBX := LBXc ++ LB).
  assert (EQL : PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s = PQRA.mown s9 (NEMA.ae_a st9) ++ LBXc).
  { unfold LBXc, EK, PNRNA.mown, PQRA.mown, NEMA.aeown. rewrite <- !app_assoc. reflexivity. }
  assert (B1' : ri_inv HI (PQRA.mown s9 (NEMA.ae_a st9) ++ LBX) FF' LK9 cr9 A9 M9 (vml_of model9)) by (unfold LBX; rewrite app_assoc, <- EQL; exact B1).
  pose proof HB0 as (VS0 & IS0 & VI0). pose proof HP0 as (PA0 & AA0 & REF0 & ACC0).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PQRAa.reader_dtor_spec, PQRHA.reader_dtor_spec in RDD.
  unfold PQRA.o_a, PQRA.o_p, PQRA.o_is, PQRA.o_v, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is, PmSpecs.PMSP.o_v in RDD.
  cbn [qa_reader_dtor pa_off_p pa_off_is pa_off_v PQRAa.AD PQRAa.AQ PMA.AD ADDR_A qa_off_a PnLayoutQA.QADDR_A] in RDD.
  change PQRHA.RSIZE with 504 in RDD. change PQRHA.RDRD_H with 3 in RDD.
  apply (RDD fx9 R9 M9 model9 K LBX FF' LK9 A9 cr9 (V2 - 160) 0xaf508 F s9 (NEMA.ae_a st9) B1' B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { pose proof (Z.div_mod V2 32 ltac:(clear; lia)) as DM. rewrite V2A, Z.add_0_r in DM. replace (V2 - 160) with ((V2 / 32 * 2 - 10) * 16) by (clear - DM; lia). apply Z.mod_mul. clear; lia. }
  { exact (PQHASK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { exact PA0. }
  { replace (F + 592 + 400) with (F + 992) by lia. exact AA0. }
  { exact ACC0. }
  { exact GROW. }
  { exact AOK. }
  { exact LSB. }
  intros fx' R' M' model' LK' Aw' RP' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 3) with 18432 in HP'.
  set (Wc := [(F + 592, 504)]) in *.
  assert (WcF : forall r, In r Wc -> fst r = F + 592 /\ snd r = 504) by (intros r Hr; subst Wc; destruct Hr as [<-|[]]; split; reflexivity).
  assert (WFI : PQHAK2.wfi F Wc) by (intros r Hr; destruct (WcF r Hr) as (E1 & E2); rewrite E1, E2; left; lia).
  assert (WA : forall o n, (o + n <= F + 592 \/ F + 1096 <= o) -> PQHAK2.wapart Wc o n) by (intros o n Ho r Hr; destruct (WcF r Hr) as (E1 & E2); rewrite E1, E2; lia).
  assert (LS' : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M').
  { apply (PQHAK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 18432 Wc M9 M' HP'); [| exact LS].
    intros r Hr. destruct (WcF r Hr) as (E1 & E2). rewrite E1, E2. right. clear - FR. lia. }
  assert (HH'' : ri_inv HI (LBXc ++ LB) FF' LK' cr9 Aw' M' (vml_of model')) by exact HH'.
  assert (BI' : Bv W LBXc M' model' LK' cr9 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ LBXc _ M9 model9 LK9 cr9 A9 M' model' LK' cr9 Aw' 18432 Wc BI HP' HH'' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. destruct (WcF rr Hr) as (E1 & E2). unfold L5.in_rng in Ha. rewrite E1, E2 in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|].
      unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr Hr Ha. destruct (WcF rr Hr) as (E1 & E2). unfold L5.in_rng in Ha. rewrite E1, E2 in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X. exact X. }
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R9 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y19 & Y21 & Y27 & Y3 & Y4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R9 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R9 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R9 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R9 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R9 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R9 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R9 R' 26 RP') by inl; exact R26).
  (* [comment removed for export] *)
  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. destruct (WcF rr Hr) as (E1 & E2). unfold L5.in_rng. rewrite E1, E2. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M9 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M9 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (FIN9 : In (F, 5, V2 - 160 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  assert (HB' : PQHAK5.hbaseN F M' s s' sm).
  { eapply PQHAK5.hbaseN_callee; first [ exact B1' | exact HP' | exact HB0 | exact FHF | exact FIN9 | exact WFI | (apply WA; lia)
      | (unfold LBX, LBXc, EK; intros x Hx; apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (unfold LBX, LBXc, EK; intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | hsolve ]. }
  assert (HSE' : PQHAK5.hseF L ar F M' (NEMA.ae_e st9) (NEMA.ae_s st9)).
  { eapply PQHAK5.hseF_callee; first [ exact B1' | exact HP' | exact HSE0 | exact FHF | exact FIN9 | exact WFI | (apply WA; lia)
      | (unfold LBX, LBXc, EK; intros x Hx; apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hx)
      | (unfold LBX, LBXc, EK; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | hsolve ]. }
  unfold LBXc, EK in BI'.
  exact (KONT fx' R' M' model' LK' Aw' BI' RI' LS' Y18 Y20 Y21 Y22 Y23 Y24 Y25 Y26 HB' HSE' HSTKa' HSTKb').
Qed.
End Stage.
End SCFG_1.
End PQHA8.
