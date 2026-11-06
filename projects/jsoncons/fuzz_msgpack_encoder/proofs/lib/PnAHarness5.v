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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnAHarnessKit4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAHarnessP2.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA5.
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
Hypothesis WSYS : forall a, L5.outside W a -> L5.outside [(0x692330, 2)] a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PQHAK2.wapart_nil | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil])]])
  | (apply PQHAK2.wapart_nil) | lia ].

Lemma stage5 (SYS : PMA.syscat_spec L ar HI) (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (K : TSet)
      (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (p0 : PQMA.mpst) (st0 : PQMA.ast) (g : PMST.st) :
  Bv W (PQRA.mown p0 st0 ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 V2 cls F -> K [] -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M6 ->
  getr R6 (reg 1) = Z_to_bv 64 0xaf4d8 -> getr R6 (reg 18) = Z_to_bv 64 2147450880 -> getr R6 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R6 (reg 21) = Z_to_bv 64 (F + 96) -> getr R6 (reg 22) = Z_to_bv 64 (F + 432) -> getr R6 (reg 23) = Z_to_bv 64 (F + 520) ->
  getr R6 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R6 (reg 25) = Z_to_bv 64 (F + 592) -> getr R6 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M6 s s' sm -> PQHAK4.hpar4 F M6 p0 st0 -> PQHAK5.hse0 L ar F M6 -> L5.u32_at RSEGS M6 (F + 1232) 0 -> shadow_zero M6 (F + 1232) 2 ->
  L5.u64_at RSEGS M6 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M6 (V2 - 136) F ->
  (forall (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (LK7 : list fframe) (A7 : list (Z * Z)),
      Bv W (PQRA.mown p0 st0 ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr6 A7 -> rinvH R R7 V2 cls F ->
      PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M7 ->
      getr R7 (reg 1) = Z_to_bv 64 0xaf4e4 -> getr R7 (reg 10) = Z_to_bv 64 (F + 592) -> getr R7 (reg 18) = Z_to_bv 64 2147450880 ->
      getr R7 (reg 20) = Z_to_bv 64 18446744073709551608 -> getr R7 (reg 21) = Z_to_bv 64 (F + 96) -> getr R7 (reg 22) = Z_to_bv 64 (F + 432) ->
      getr R7 (reg 23) = Z_to_bv 64 (F + 520) -> getr R7 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R7 (reg 25) = Z_to_bv 64 (F + 592) ->
      getr R7 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M7 s s' sm -> PQHAK4.hpar4 F M7 p0 st0 -> PQHAK4.hec4 F M7 0 (pa_syscat_obj PMA.AD) -> PQHAK5.hse0 L ar F M7 ->
      L5.u64_at RSEGS M7 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M7 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xcfb7c M7 model7) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xf8930 M6 model6) K.
Proof.
  intros BI RI K0 LS R1a R18 R20 R21 R22 R23 R24 R25 R26 HB0 HP0 HSE0 EC0 SZE0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PMA.syscat_spec, PMSPA.syscat_spec in SYS. cbn [pa_syscat pa_syscat_guard pa_syscat_obj PMA.AD ADDR_A] in SYS.
  apply (SYS fx6 R6 M6 model6 K ((PQRA.mown p0 st0 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK6 A6 cr6 (V2 - 160) 0xaf4d8 (PMST.st_sys g) B1 B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { exact LSB. }
  { exact LSS. }
  intros fx' R' M' model' LK' Aw' RP' RV' SYS' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  set (Wc := if PMST.st_sys g then [] else [(6890288, 2)]) in *.
  assert (WcL : forall r, In r Wc -> r = (6890288, 2)) by (intros r Hr; subst Wc; destruct (PMST.st_sys g); [destruct Hr| destruct Hr as [<-|[]]; reflexivity]).
  assert (WFI : PQHAK2.wfi F Wc) by (intros r Hr; rewrite (WcL r Hr); right; cbn [fst snd]; lia).
  assert (WA : forall o n, F <= o -> PQHAK2.wapart Wc o n) by (intros o n Ho r Hr; rewrite (WcL r Hr); cbn [fst snd]; clear - Ho FR; lia).
  assert (LS' : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M').
  { apply (PQHAK.ls_ahpres_sys L C LY g ar _ FF' (V2 - 160) 14336 Wc M6 M' HP'); [| exact LS| exact SYS'].
    intros a Ha r Hr Hin. rewrite (WcL r Hr) in Hin. unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    unfold PQHAK.bcell, PQHAK.lcell, PQHAK.ecell in Ha. clear - Ha Hin. lia. }
  assert (BI' : Bv W (PQRA.mown p0 st0 ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr6 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ _ _ M6 model6 LK6 cr6 A6 M' model' LK' cr6 Aw' 14336 Wc BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. rewrite (WcL rr Hr) in Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha SLO SPT; lia|].
      unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8. lia.
    - intros a Hc Ho rr Hr Ha. pose proof (WcL rr Hr) as E. subst rr. exact (WSYS a Ho _ (or_introl eq_refl) Ha).
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R6 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y19 & Y21 & Y27 & Y3 & Y4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R6 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R6 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R6 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R6 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1232)) by (rewrite (cs_of_preserved R6 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R6 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R6 R' 26 RP') by inl; exact R26).
  (* [comment removed for export] *)
  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. rewrite (WcL rr Hr). unfold L5.in_rng; cbn [fst snd]. clear - Ha V2R. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M6 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M6 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (FIN6 : In (F, 5, V2 - 160 + 32) (FF' ++ LK6)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (HB' : PQHAK5.hbaseN F M' s s' sm).
  { eapply PQHAK5.hbaseN_callee; first [ exact B1 | exact HP0 | exact HB0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
      | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | hsolve ]. }
  assert (HSE' : PQHAK5.hse0 L ar F M').
  { eapply PQHAK5.hse0_callee; first [ exact B1 | exact HSE0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia | hsolve ]. }
  assert (HQ' : PQHAK4.hpar4 F M' p0 st0).
  { eapply PQHAK4.hpar4_callee; first [ exact B1 | exact HP' | exact HP0 | exact FHF | exact FIN6 | exact WFI | apply WA; lia
      | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | hsolve ]. }
  assert (AGE : PMFA.agA M6 M' (F + 1232) 16).
  { apply (PQHAK2.ff_callee L ar _ FF' (V2 - 160) 14336 Wc M6 M' (F, 5, V2 - 160 + 32) F (F + 1232) 16 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (EC' : L5.u32_at RSEGS M' (F + 1232) 0) by (apply (PQHAK2.u32_agA M6 M' (F + 1232) 16 (F + 1232) _ AGE); [lia| lia| lia| lia| exact EC0]).
  assert (SZE' : shadow_zero M' (F + 1232) 2) by (apply (PQHAK2.shz_agA M6 M' (F + 1232) 16 (F + 1232) 2 AGE); [lia| lia| clear - FM8; lia| lia| exact SZE0]).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed ident:(P) (PQAHP2.qhaH_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PQAHP2.aligned; exact V2A) ]).
  destruct P as (fx7 & R7 & M7v & MG7 & fFR & fFZ & (fMS & fKS & fR1 & fR10 & fC & fD1 & fD2)).
  set (W7 := fun a => F + 1240 <= a < F + 1240 + 8).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr6 Aw' M' model' fx' fx7 R' 0xaf4d8 R7 0xcfb7c M7v W7 K HH' AM' fMS MG7).
  { intros a Ha Hna. apply fFZ; [exact Ha|..]; intros X; apply Hna; subst W7; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W7; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7. change (mrestrict H' M7 = M7v) in VIS7.
  assert (BI7 : Bv W (PQRA.mown p0 st0 ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK' cr6 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' M7 model7 W7 BI' HH7 AM7 MRT7 MGM7 FR7).
    intros a Wa. subst W7; cbn beta in Wa. right. left. change (ff_bytes 5) with 2048. clear - Wa. lia. }
  assert (RI7 : rinvH R R7 V2 cls F) by (apply (rinvH_ks R R' R7 V2 cls F PQAHP2.KS_qhaH RI' fKS); vm_compute; reflexivity).
  assert (LS7 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M7).
  { apply (PQHAK.ls_piece _ M' M7 W7 FR7); [| exact LS']. intros a Wa. subst W7; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF7 : PQHAK2.pfoot F (V2 - 160) V2 W7) by (intros a Wa; subst W7; cbn beta in Wa; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (OAX : forall o n, F <= o -> o + n <= F + 1240 -> PQHAK2.oav W7 o n).
  { intros o n H1 H2 x Hx. subst W7; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR; lia. }
  assert (HB7 : PQHAK5.hbaseN F M7 s s' sm).
  { apply (PQHAK5.hbaseN_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX; lia| apply OAX; lia| exact HB']. }
  assert (HSE7 : PQHAK5.hse0 L ar F M7) by (apply (PQHAK5.hse0_piece L ar F FHF W7 M' M7 FR7); [apply OAX; lia| apply OAX; lia| exact HSE']).
  assert (HSTKa7 : L5.u64_at RSEGS M7 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M' M7 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
    intros i Hi. apply FR7; [clear - Hi V2R; lia|]. subst W7; cbn beta. intros X. clear - Hi X Q3 CLS. lia. }
  assert (HSTKb7 : L5.u64_at RSEGS M7 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M' M7 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
    intros i Hi. apply FR7; [clear - Hi V2R; lia|]. subst W7; cbn beta. intros X. clear - Hi X Q3 CLS. lia. }
  assert (HQ7 : PQHAK4.hpar4 F M7 p0 st0).
  { apply (PQHAK4.hpar4_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 p0 st0);
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| apply OAX; lia| exact HQ']. }
  assert (U10 : bv_unsigned (getr R' (reg 10)) = 1422600) by (rewrite <- L5K.rl10, RV'; apply L5.unsigned_lit; lia).
  rewrite U10 in fC.
  assert (HE7 : PQHAK4.hec4 F M7 0 (pa_syscat_obj PMA.AD)).
  { cbn [pa_syscat_obj PMA.AD ADDR_A]. split; [|split; [|split]].
    - apply (PQHAK.u32_agree M' M7 (F + 1232) 0); [intros i Hi; apply FR7; [clear - Hi FR; lia| subst W7; cbn beta; clear - Hi; lia]| clear - FR; lia| clear - FR; lia| exact EC'].
    - apply (PQHAK.u64_vis H' M7 M7v (F + 1240) _ VV7 (PQHAK.avis_sub H' F 2048 (F + 1240) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact fC.
    - apply (PQHAK2.shz_frame M' M7 W7 (F + 1232) 2 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| exact SZE'].
      intros j Hj X. subst W7; cbn beta in X. pose proof (PMKA.S_in_shadow (F + 1232) ltac:(clear - FR; lia)) as SX.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hj X SX FBIG FR. lia.
    - pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M7 model7 LK' cr6 Aw' BI7) as (_ & _ & (VFD7 & _) & (_ & _ & FV7 & _)).
      change (ff_bytes 5) with 2048 in VFD7, FV7.
      apply (L5.defined_sub M7 F 2048 (F + 1232) 16); [| lia| lia]. apply (proj1 (L5A.defined_vis (ahid Aw' model7) M7 F 2048 FV7)). exact VFD7. }
  apply (KONT fx7 R7 M7 model7 LK' Aw' BI7 RI7 LS7).
  - exact fR1.
  - exact fR10.
  - rewrite (fKS 18%nat) by inl. exact Y18.
  - rewrite (fKS 20%nat) by inl. exact Y20.
  - rewrite (fKS 21%nat) by inl. exact Y21.
  - rewrite (fKS 22%nat) by inl. exact Y22.
  - rewrite (fKS 23%nat) by inl. exact Y23.
  - rewrite (fKS 24%nat) by inl. exact Y24.
  - rewrite (fKS 25%nat) by inl. exact Y25.
  - rewrite (fKS 26%nat) by inl. exact Y26.
  - exact HB7.
  - exact HQ7.
  - exact HE7.
  - exact HSE7.
  - exact HSTKa7.
  - exact HSTKb7.
Qed.
End Stage.
End SCFG_1.
End PQHA5.
