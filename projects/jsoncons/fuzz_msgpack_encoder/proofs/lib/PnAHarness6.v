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

Module PQHA6.
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

Lemma own_resetA ps : PNM.bparser_own (PNRA.bpst_reset ps) = PNM.bparser_own ps.
Proof.
  destruct ps as [mo dn src bb nb tb ng tg bg sb sk stk]. unfold PNM.bparser_own, PNM.brest_own, PNRA.bpst_reset. cbn.
  destruct bb; destruct nb; destruct tb; reflexivity.
Qed.

Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma stage6 (RST : PQRAa.reset_spec L ar HI) (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (K : TSet)
      (LK7 : list fframe) (cr7 : credit) (A7 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (qc b b' : Z) (g : PMST.st) (v c : Z) :
  Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr7 A7 -> rinvH R R7 V2 cls F -> K [] ->
  PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M7 ->
  getr R7 (reg 1) = Z_to_bv 64 0xaf4e4 -> getr R7 (reg 10) = Z_to_bv 64 (F + 592) -> getr R7 (reg 18) = Z_to_bv 64 2147450880 ->
  getr R7 (reg 20) = Z_to_bv 64 18446744073709551608 -> getr R7 (reg 21) = Z_to_bv 64 (F + 96) -> getr R7 (reg 22) = Z_to_bv 64 (F + 432) ->
  getr R7 (reg 23) = Z_to_bv 64 (F + 520) -> getr R7 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R7 (reg 25) = Z_to_bv 64 (F + 592) ->
  getr R7 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M7 s s' sm -> PQHAK4.hpar4 F M7 (PQRHA.mparser_init qc b) (PQRHA.ast_init b') -> PQHAK4.hec4 F M7 v c -> PQHAK5.hse0 L ar F M7 ->
  L5.u64_at RSEGS M7 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M7 (V2 - 136) F ->
  (forall (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (LK8 : list fframe) (A8 : list (Z * Z)),
      Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK8 cr7 A8 -> rinvH R R8 V2 cls F ->
      PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M8 ->
      getr R8 (reg 1) = Z_to_bv 64 0xaf4f4 -> getr R8 (reg 10) = Z_to_bv 64 (F + 592) -> getr R8 (reg 11) = Z_to_bv 64 (F + 992) ->
      getr R8 (reg 12) = Z_to_bv 64 (F + 1232) -> getr R8 (reg 18) = Z_to_bv 64 2147450880 -> getr R8 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R8 (reg 21) = Z_to_bv 64 (F + 96) -> getr R8 (reg 22) = Z_to_bv 64 (F + 432) -> getr R8 (reg 23) = Z_to_bv 64 (F + 520) ->
      getr R8 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R8 (reg 25) = Z_to_bv 64 (F + 592) -> getr R8 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M8 s s' sm -> PQHAK4.hpar4 F M8 (PQRHA.mparser_init qc b) (PQRHA.ast_init b') -> PQHAK4.hec4 F M8 v c -> PQHAK5.hse0 L ar F M8 ->
      L5.u64_at RSEGS M8 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M8 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xcfdb4 M8 model8) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xcfb7c M7 model7) K.
Proof.
  intros BI RI K0 LS R1a R10 R18 R20 R21 R22 R23 R24 R25 R26 HB0 HP0 HE0 HSE0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (P0 := PQRHA.mparser_init qc b) in *. set (ST0 := PQRHA.ast_init b') in *.
  set (LBXc := PQMA.aown ST0 ++ (PM.vs_own s' ++ PM.vs_own s)). set (LBX := LBXc ++ LB).
  assert (B1' : ri_inv HI (PQMA.mparser_own P0 ++ LBX) FF' LK7 cr7 A7 M7 (vml_of model7)).
  { unfold LBX, LBXc. pose proof B1 as B1x. unfold PQRA.mown in B1x. rewrite <- !app_assoc in B1x. rewrite <- !app_assoc. exact B1x. }
  pose proof HP0 as (PA0 & AA0 & REF0 & ACC0).
  unfold PQRAa.reset_spec, PQRA.reset_spec in RST. unfold PQRA.reset_W, PQRA.o_tb, PQRA.o_bb, PQRA.o_stk, PQRA.o_p, PQRA.o_is, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is in RST.
  cbn [qa_reset pa_off_p pa_off_is PQRAa.AD PQRAa.AQ PMA.AD ADDR_A PnLayoutQA.QADDR_A PQMA.OFF_TB PQMA.OFF_BB PQMA.OFF_STK] in RST.
  apply (RST fx7 R7 M7 model7 K LBX FF' LK7 A7 cr7 (V2 - 160) 0xaf4e4 F P0 B1' B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { pose proof (Z.div_mod V2 32 ltac:(clear; lia)) as DM. rewrite V2A, Z.add_0_r in DM. replace (V2 - 160) with ((V2 / 32 * 2 - 10) * 16) by (clear - DM; lia). apply Z.mod_mul. clear; lia. }
  { exact (PQHASK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { exact PA0. }
  { intros a Ha. apply ACC0. unfold PQMA.PSIZE in Ha. clear - Ha. lia. }
  { exact (proj1 LS). }
  intros fx' R' M' model' LK' Aw' RP' PA' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'. change (PQRA.mpst_reset P0) with P0 in PA'.
  assert (HH'' : ri_inv HI ((PQRA.mown P0 ST0 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK' cr7 Aw' M' (vml_of model')).
  { unfold PQRA.mown. rewrite <- !app_assoc. unfold LBX, LBXc in HH'. rewrite <- !app_assoc in HH'. exact HH'. }
  set (Wc := [(F + 592 + 8, 8); (F + 592 + 328, 24); (F + 592 + 352, 24); (F + 592 + 376, 24)]) in *.
  assert (WcF : forall r, In r Wc -> F + 592 <= fst r /\ fst r + snd r <= F + 992) by (intros r Hr; subst Wc; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; lia).
  assert (WFI : PQHAK2.wfi F Wc) by (intros r Hr; destruct (WcF r Hr); left; lia).
  assert (WA : forall o n, (o + n <= F + 592 \/ F + 992 <= o) -> PQHAK2.wapart Wc o n) by (intros o n Ho r Hr; destruct (WcF r Hr); lia).
  assert (LS' : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M').
  { apply (PQHAK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 Wc M7 M' HP'); [| exact LS].
    intros r Hr. destruct (WcF r Hr). right. clear - H H0 FR. lia. }
  assert (BI' : Bv W (PQRA.mown P0 ST0 ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr7 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ LBXc _ M7 model7 LK7 cr7 A7 M' model' LK' cr7 Aw' 14336 Wc BI HP' HH'' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. unfold tocell. split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|].
      unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha Z1 Z2 FR F8 FBIG. lia.
    - intros a Hc _ rr Hr Ha. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng in Ha. apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R7 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y19 & Y21 & Y27 & Y3 & Y4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R7 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R7 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R7 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R7 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1232)) by (rewrite (cs_of_preserved R7 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R7 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R7 R' 26 RP') by inl; exact R26).
  (* [comment removed for export] *)
  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng. clear - Ha Z1 Z2 FCEIL SLO CLS. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M7 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M7 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (FIN7 : In (F, 5, V2 - 160 + 32) (FF' ++ LK7)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (HB' : PQHAK5.hbaseN F M' s s' sm).
  { eapply PQHAK5.hbaseN_callee; first [ exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia)
      | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (unfold LBX, LBXc; intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | hsolve ]. }
  assert (HSE' : PQHAK5.hse0 L ar F M').
  { eapply PQHAK5.hse0_callee; first [ exact B1 | exact HP' | exact HSE0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia) | hsolve ]. }
  assert (HE' : PQHAK4.hec4 F M' v c).
  { eapply PQHAK4.hec4_callee; first [ exact B1 | exact HP' | exact HE0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia) | hsolve ]. }
  assert (AA' : PQMA.adaptor_at RSEGS PMA.AD PMSPA.accA PQRA.annA (qa_vp_adaptor PnLayoutQA.QADDR_A) M' (F + 992) (F + 496) ST0).
  { eapply PQHAK4.adaptor_keep_callee; first [ exact B1 | exact HP' | exact AA0 | exact FHF | exact FIN7 | exact WFI | (apply WA; unfold PQMA.ASIZE; lia)
      | (intros x Hx; apply in_or_app; left; apply in_or_app; left; unfold PQRA.mown; apply in_or_app; right; exact Hx)
      | (unfold LBX, LBXc; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | (unfold PQMA.ASIZE; lia) | hsolve ]. }
  assert (AGR : PMFA.agA M7 M' (F + 1088) 8).
  { apply (PQHAK2.ff_callee L ar _ FF' (V2 - 160) 14336 Wc M7 M' (F, 5, V2 - 160 + 32) F (F + 1088) 8 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (REF' : L5.u64_at RSEGS M' (F + 1088) (F + 992)) by (apply (PQHAK2.u64_agA M7 M' (F + 1088) 8 (F + 1088) _ AGR); [lia| lia| lia| lia| exact REF0]).
  assert (ACC' : PMSPA.accA M' (F + 592) 504).
  { apply (PQHAK2.acc_of_shz M' (F + 592) 63 (F + 592) 504); [| exact (fb_mod8 F 74 FAL)| clear - FR; lia| lia| lia].
    apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 14336 Wc M7 M' (F, 5, V2 - 160 + 32) F (F + 592) 63 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [lia| lia| exact (fb_mod8 F 74 FAL)| lia|].
    apply (PQHAK2.shz_of_acc M7 (F + 592) 63); [exact ACC0| exact (fb_mod8 F 74 FAL)| clear - FR; lia]. }
  assert (HQ' : PQHAK4.hpar4 F M' P0 ST0) by (split; [exact PA'| split; [exact AA'| split; [exact REF'| exact ACC']]]).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (Q7 : L5.u64_at RSEGS MV' (F + 1088) (F + 992))
    by (apply (proj2 (L5A.u64_at_vis H' M' (F + 1088) (F + 992) (PQHAK.avis_sub H' F 2048 (F + 1088) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact REF').
  LeanFeed.pfeed ident:(P) (PQAHP2.qhaI_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 35%nat => F + 992 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact Q7 | (unfold PQAHP2.aligned; exact V2A) ]).
  destruct P as (fx8 & R8 & M8v & MG8 & gFR & gFZ & (gMS & gKS & gR1 & gR10 & gR11 & gR12)).
  set (W8 := fun a : Z => False).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr7 Aw' M' model' fx' fx8 R' 0xaf4e4 R8 0xcfdb4 M8v W8 K HH'' AM' gMS MG8).
  { intros a Ha Hna. apply gFZ; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8.
  assert (BI8 : Bv W (PQRA.mown P0 ST0 ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK' cr7 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' M8 model8 W8 BI' HH8 AM8 MRT8 MGM8 FR8).
    intros a Wa. destruct Wa. }
  assert (RI8 : rinvH R R8 V2 cls F) by (apply (rinvH_ks R R' R8 V2 cls F PQAHP2.KS_qhaI RI' gKS); vm_compute; reflexivity).
  assert (LS8 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M8) by (apply (PQHAK.ls_piece _ M' M8 W8 FR8); [intros a []| exact LS']).
  assert (PF8 : PQHAK2.pfoot F (V2 - 160) V2 W8) by (intros a []).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (OAX : forall o n, PQHAK2.oav W8 o n) by (intros o n x Hx; split; intros []).
  apply (KONT fx8 R8 M8 model8 LK' Aw' BI8 RI8 LS8).
  - exact gR1.
  - exact gR10.
  - exact gR11.
  - exact gR12.
  - rewrite (gKS 18%nat) by inl. exact Y18.
  - rewrite (gKS 20%nat) by inl. exact Y20.
  - rewrite (gKS 21%nat) by inl. exact Y21.
  - rewrite (gKS 22%nat) by inl. exact Y22.
  - rewrite (gKS 23%nat) by inl. exact Y23.
  - rewrite (gKS 24%nat) by inl. exact Y24.
  - rewrite (gKS 25%nat) by inl. exact Y25.
  - rewrite (gKS 26%nat) by inl. exact Y26.
  - apply (PQHAK5.hbaseN_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W8 M' M8 SLOW SHW FR8 PF8 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX| apply OAX| exact HB'].
  - apply (PQHAK4.hpar4_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W8 M' M8 SLOW SHW FR8 PF8 P0 ST0);
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| apply OAX| exact HQ'].
  - eapply PQHAK4.hec4_piece; first [exact FHF | exact FR8 | exact HE' | apply OAX].
  - apply (PQHAK5.hse0_piece L ar F FHF W8 M' M8 FR8); [apply OAX| apply OAX| exact HSE'].
  - apply (L5C.u64_at_agree RSEGS M' M8 (V2 - 144) (F + 32)); [intros i Hi; apply FR8; [clear - Hi V2R; lia| intros []]| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
  - apply (L5C.u64_at_agree RSEGS M' M8 (V2 - 136) F); [intros i Hi; apply FR8; [clear - Hi V2R; lia| intros []]| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
Qed.
End Stage.
End SCFG_1.
End PQHA6.
