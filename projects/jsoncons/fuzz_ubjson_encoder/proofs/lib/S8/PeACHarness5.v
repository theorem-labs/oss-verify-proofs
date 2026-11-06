(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA L5CoreAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8 L5AFrameKRS8 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecs PmSpecsA PeSpecsAa PeStepA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCSpecs PeCSpecsA PeCSpecsAa PeACHarnessStmts PeACHarnessKit PeACHarnessKit2 PeACHarnessSK PeACHarnessKit3 PeACHarnessKit4 PeACHarnessP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEACH5.
Import L5A. Import L5CA. Import L5SAR. Import PEACH.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
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

Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis WSYS : forall a, L5.outside W a -> L5.outside [(0x6742b0, 2)] a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| first [apply PEAHK2.wapart_nil | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil])]])
  | (apply PEAHK2.wapart_nil) | lia ].

Variable P : PESKA.sink_policyA.
Variable payload : list byte.
Local Notation n := (PEACH.n payload).
Local Notation p := (PEACH.p payload).
Local Notation parser_at := (PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA).

Lemma stage5 (SYS : PMSPA.syscat_spec RSEGS AD L ar HI) (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (K : TSet)
      (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (qc b : Z) (g : PMST.st) :
  Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 (V2 - 160) F 2147450880 -> K [] -> PESTA.ls_okA RSEGS AD AAD EE g M6 ->
  getr R6 (reg 1) = Z_to_bv 64 0xa8ed4 -> getr R6 (reg 18) = Z_to_bv 64 (F + 520) -> getr R6 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R6 (reg 22) = Z_to_bv 64 (F + 432) -> getr R6 (reg 23) = Z_to_bv 64 (F + 496) -> getr R6 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R6 (reg 25) = Z_to_bv 64 (F + 592) ->
  PEAHK2.hbase F M6 s s' sm -> PM.vs_size s' = n -> L5.bytes_at RSEGS M6 (PM.vs_data (F + 176) s') p -> PEACH.hse0 L ar P F M6 ->
  parser_at M6 (F + 592) (F + 96) (PMSPA.parser_init qc b) -> L5.u64_at RSEGS M6 (F + 976) (F + 496) ->
  L5.u32_at RSEGS M6 (F + 1120) 0 -> shadow_zero M6 (F + 1120) 2 -> shadow_zero M6 (F + 592) 49 ->
  L5.u64_at RSEGS M6 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M6 (V2 - 136) F ->
  (forall (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (LK7 : list fframe) (A7 : list (Z * Z)),
      Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr6 A7 -> rinvH R R7 (V2 - 160) F 2147450880 ->
      PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M7 ->
      getr R7 (reg 1) = Z_to_bv 64 0xa8ee0 -> getr R7 (reg 10) = Z_to_bv 64 (F + 592) -> getr R7 (reg 18) = Z_to_bv 64 (F + 520) -> getr R7 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R7 (reg 22) = Z_to_bv 64 (F + 432) -> getr R7 (reg 23) = Z_to_bv 64 (F + 496) -> getr R7 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R7 (reg 25) = Z_to_bv 64 (F + 592) ->
      PEAHK2.hbase F M7 s s' sm -> L5.bytes_at RSEGS M7 (PM.vs_data (F + 176) s') p -> PEACH.hse0 L ar P F M7 ->
      parser_at M7 (F + 592) (F + 96) (PMSPA.parser_init qc b) -> L5.u64_at RSEGS M7 (F + 976) (F + 496) ->
      PEAHK2.hec F M7 0 (pa_syscat_obj AD) -> shadow_zero M7 (F + 592) 49 ->
      L5.u64_at RSEGS M7 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M7 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xb2304 M7 model7) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xdb064 M6 model6) K.
Proof.
  intros BI RI K0 LS R1a R18 R20 R22 R23 R24 R25 HB0 SZ5 PAYB0 HSE0 PA0 VV0 EC0 SZE0 SZP0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PEAHK2.hf F) by (unfold PEAHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (E592 : (F + 592) / 8 = F / 8 + 74) by (clear - FM8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (LENp : Z.of_nat (length p) = n) by (unfold PEACH.p, PEACH.n; rewrite length_map; reflexivity).
  pose proof LS as (LSB & LSL & LSS & LSE).
  pose proof BI as BIx. pose proof (proj1 BIx) as B1x. rewrite <- !app_assoc in B1x.
  unfold PMSPA.syscat_spec in SYS. cbn [pa_syscat PeCLayoutA.CADDR_A] in SYS.
  apply (SYS fx6 R6 M6 model6 K _ FF' LK6 A6 cr6 (V2 - 160) 0xa8ed4 (PMST.st_sys g) B1 B2 K0).
  { eapply PEAHSK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { exact LSB. }
  { exact LSS. }
  intros fx' R' M' model' LK' Aw' RP' RV' SYS' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  set (Wc := if PMST.st_sys g then [] else [(pa_syscat_guard AD, 2)]) in *.
  assert (WcL : forall r, In r Wc -> r = (6767280, 2)) by (intros r Hr; subst Wc; destruct (PMST.st_sys g); [destruct Hr| destruct Hr as [<-|[]]; reflexivity]).
  assert (WFI : PEAHK2.wfi F Wc) by (intros r Hr; rewrite (WcL r Hr); right; cbn [fst snd]; lia).
  assert (WA : forall o k, F <= o -> PEAHK2.wapart Wc o k) by (intros o k Ho r Hr; rewrite (WcL r Hr); cbn [fst snd]; clear - Ho FR; lia).
  assert (LS' : PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M').
  { apply (PEAHK.ls_ahpres_sys L C LY g ar _ FF' (V2 - 160) 14336 Wc M6 M' HP'); [| exact LS| exact SYS'].
    intros a Ha r Hr Hin. rewrite (WcL r Hr) in Hin. unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    unfold PEAHK.bcell, PEAHK.lcell, PEAHK.ecell in Ha. clear - Ha Hin. lia. }
  assert (BI' : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr6 Aw').
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
  assert (RI' : rinvH R R' (V2 - 160) F 2147450880) by exact (rinvH_pres R R6 R' (V2 - 160) F 2147450880 RI RP').
  pose proof RI' as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R6 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R6 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R6 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R6 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1120)) by (rewrite (cs_of_preserved R6 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R6 R' 25 RP') by inl; exact R25).
  assert (FIN6 : In (F, 5, V2 - 160 + 32) (FF' ++ LK6)) by (apply in_or_app; left; left; reflexivity).

  pose proof B1 as B1y. rewrite (app_assoc (PM.parser_own (PMSPA.parser_init qc b)) (PM.vs_own s' ++ PM.vs_own s) LB) in B1y || idtac.
  assert (HB' : PEAHK2.hbase F M' s s' sm).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN6 | exact WFI | (apply WA; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx) | apply incl_refl | lia ]. }
  assert (HSE' : PEACH.hse0 L ar P F M').
  { eapply PEAHK4.hse0_callee; first [ exact B1 | exact HP' | exact HSE0 | exact FHF | exact FIN6 | exact WFI | exact (or_introl eq_refl) | (left; reflexivity) | (split; reflexivity) | (apply WA; lia) | lia ]. }
  assert (PA' : parser_at M' (F + 592) (F + 96) (PMSPA.parser_init qc b)).
  { eapply PEAHK4.parser_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact PA0 | exact FHF | exact FIN6 | exact WFI | (apply WA; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx) | apply incl_refl | lia ]. }
  assert (AGF : forall o k, F + 32 <= o -> o + k <= F + 2040 -> PMFA.agA M6 M' o k).
  { intros o k H1 H2. apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 14336 Wc M6 M' (F, 5, V2 - 160 + 32) F o k HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (VV' : L5.u64_at RSEGS M' (F + 976) (F + 496)) by (apply (PEAHK2.u64_agA M6 M' (F + 976) 8 (F + 976) _ (AGF (F + 976) 8 ltac:(lia) ltac:(lia))); [lia| lia| lia| lia| exact VV0]).
  assert (EC' : L5.u32_at RSEGS M' (F + 1120) 0) by (apply (PEAHK2.u32_agA M6 M' (F + 1120) 16 (F + 1120) _ (AGF (F + 1120) 16 ltac:(lia) ltac:(lia))); [lia| lia| lia| lia| exact EC0]).
  assert (SZE' : shadow_zero M' (F + 1120) 2) by (apply (PEAHK2.shz_agA M6 M' (F + 1120) 16 (F + 1120) 2 (AGF (F + 1120) 16 ltac:(lia) ltac:(lia))); [lia| lia| clear - FM8; lia| lia| exact SZE0]).
  assert (SZP' : shadow_zero M' (F + 592) 49)
    by (apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 14336 Wc M6 M' (F, 5, V2 - 160 + 32) F (F + 592) 49 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZP0]).
  assert (AGstk' : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. rewrite (WcL rr Hr). unfold L5.in_rng; cbn [fst snd]. clear - Ha V2R. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M6 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M6 M' (V2 - 136) F); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (PAYB' : L5.bytes_at RSEGS M' (PM.vs_data (F + 176) s') p).
  { pose proof HB0 as (_ & ISx & _). pose proof ISx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB0 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M6 M' (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB0].
      intros i Hi. apply (proj1 (AGF (F + 176) 24 ltac:(clear; lia) ltac:(clear; lia))). clear - Hi SZB SZ5; lia.
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      apply (L5C.bytes_at_agree RSEGS M6 M' q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB0].
      intros i Hi. apply (proj1 HP' i). split; [clear - Hi P0 P47 NC SZ5; lia| split].
      + left. exists (q0, c0). split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| cbn [fst snd]; clear - Hi NC SZ5; lia].
      + intros rr Hr. rewrite (WcL rr Hr). unfold L5.in_rng; cbn [fst snd]. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG. clear - Hi PIMG NC SZ5. lia. }

  pose proof (PEACHP2.ahnG_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PEACHP2.aligned; exact V2A) ]).
  destruct PP as (fx7 & R7 & M7v & MG7 & fFR & fFZ & (fMS & fKS & fR1 & fR10 & fC & fD1 & fD2)).
  set (W7 := fun a => F + 1128 <= a < F + 1128 + 8).
  rewrite <- !app_assoc in HH'.
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr6 Aw' M' model' fx' fx7 R' 0xa8ed4 R7 0xb2304 M7v W7 K HH' AM' fMS MG7).
  { intros a Ha Hna. apply fFZ; [exact Ha|..]; intros X; apply Hna; subst W7; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W7; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7. change (mrestrict H' M7 = M7v) in VIS7.
  rewrite !app_assoc in HH7.
  pose proof HH' as HH''. rewrite (app_assoc (PM.vs_own s') (PM.vs_own s) LB) in HH''. rewrite (app_assoc (PM.parser_own (PMSPA.parser_init qc b)) (PM.vs_own s' ++ PM.vs_own s) LB) in HH''.
  assert (BI7 : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK' cr6 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr6 Aw' M7 model7 W7 BI' HH7 AM7 MRT7 MGM7 FR7).
    intros a Wa. subst W7; cbn beta in Wa. right. left. change (ff_bytes 5) with 2048. clear - Wa. lia. }
  assert (RI7 : rinvH R R7 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R' R7 (V2 - 160) F 2147450880 PEACHP2.KS_ahnG RI' fKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS7 : PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M7).
  { apply (PEAHK.ls_piece _ M' M7 W7 FR7); [| exact LS']. intros a Wa. subst W7; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF7 : PEAHK2.pfoot F (V2 - 160) V2 W7) by (intros a Wa; subst W7; cbn beta in Wa; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (OAX : forall o k, F <= o -> o + k <= F + 1128 -> PEAHK2.oav W7 o k).
  { intros o k H1 H2 x Hx. subst W7; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR; lia. }
  assert (HB7 : PEAHK2.hbase F M7 s s' sm).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX; lia| apply OAX; lia| exact HB']. }
  assert (HSE7 : PEACH.hse0 L ar P F M7).
  { apply (PEAHK4.hse0_piece L ar P F FHF W7 M' M7 FR7); [apply OAX; clear; lia| apply OAX; clear; lia| exact HSE']. }
  assert (PA7 : parser_at M7 (F + 592) (F + 96) (PMSPA.parser_init qc b)).
  { apply (PEAHK4.parser_keep_piece L ar C HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W7 M' M7 SLOW SHW FR7 PF7 (F + 592) (F + 96));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX; clear; lia| exact PA']. }
  assert (FR7lo : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 1128 <= a < F + 1136) -> M7 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hn0. apply FR7; [exact Ha|]. subst W7; cbn beta. clear - Hn0. lia. }
  assert (VV7' : L5.u64_at RSEGS M7 (F + 976) (F + 496)) by (apply (L5C.u64_at_agree RSEGS M' M7 (F + 976) _ ltac:(intros i Hi; apply FR7lo; clear - Hi FR; lia)); [clear - FR; lia| clear - FR; lia| exact VV']).
  assert (SZP7 : shadow_zero M7 (F + 592) 49).
  { apply (PEAHK2.shz_frame M' M7 W7 (F + 592) 49 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZP'].
    intros j Hj X. subst W7; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. rewrite E592 in X. clear - X Hj FBD FR FBIG. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia. }
  assert (HSTKa7 : L5.u64_at RSEGS M7 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M' M7 (V2 - 144) (F + 32)); [intros i Hi; apply FR7lo; clear - Hi V2R Q3 CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa']. }
  assert (HSTKb7 : L5.u64_at RSEGS M7 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M' M7 (V2 - 136) F); [intros i Hi; apply FR7lo; clear - Hi V2R Q3 CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb']. }
  assert (PAYB7 : L5.bytes_at RSEGS M7 (PM.vs_data (F + 176) s') p).
  { pose proof HB0 as (_ & ISx & _). pose proof ISx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB' |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M' M7 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB'].
      intros i Hi. apply FR7lo; [clear - Hi FR SZB SZ5; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN6) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M' M7 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB'].
      intros i Hi. apply FR7lo; [clear - Hi P0 P47 NC SZ5; lia| clear - Hi PF NC SZ5; lia]. }
  assert (U10 : bv_unsigned (getr R' (reg 10)) = pa_syscat_obj AD) by (rewrite <- L5K.rl10, RV'; apply L5.unsigned_lit; cbn; lia).
  rewrite U10 in fC.
  assert (HE7 : PEAHK2.hec F M7 0 (pa_syscat_obj AD)).
  { split; [|split; [|split]].
    - apply (PEAHK.u32_agree M' M7 (F + 1120) 0); [intros i Hi; apply FR7lo; [clear - Hi FR; lia| clear - Hi; lia]| clear - FR; lia| clear - FR; lia| exact EC'].
    - apply (PEAHK.u64_vis H' M7 M7v (F + 1128) _ VV7 (PEAHK.avis_sub H' F 2048 (F + 1128) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact fC.
    - apply (PEAHK2.shz_frame M' M7 W7 (F + 1120) 2 FR7); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FR; lia| exact SZE'].
      intros j Hj X. subst W7; cbn beta in X. pose proof (PMKA.S_in_shadow (F + 1120) ltac:(clear - FR; lia)) as SX.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hj X SX FBIG FR. lia.
    - pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M7 model7 LK' cr6 Aw' BI7) as (_ & _ & (VFD7 & _) & (_ & _ & FV7 & _)).
      change (ff_bytes 5) with 2048 in VFD7, FV7.
      apply (L5.defined_sub M7 F 2048 (F + 1120) 16); [| lia| lia]. apply (proj1 (L5A.defined_vis (ahid Aw' model7) M7 F 2048 FV7)). exact VFD7. }
  apply (KONT fx7 R7 M7 model7 LK' Aw' BI7 RI7 LS7).
  - exact fR1.
  - exact fR10.
  - rewrite (fKS 18%nat) by inl. exact Y18.
  - rewrite (fKS 20%nat) by inl. exact Y20.
  - rewrite (fKS 22%nat) by inl. exact Y22.
  - rewrite (fKS 23%nat) by inl. exact Y23.
  - rewrite (fKS 24%nat) by inl. exact Y24.
  - rewrite (fKS 25%nat) by inl. exact Y25.
  - exact HB7.
  - exact PAYB7.
  - exact HSE7.
  - exact PA7.
  - exact VV7'.
  - exact HE7.
  - exact SZP7.
  - exact HSTKa7.
  - exact HSTKb7.
Qed.
End Stage.
End SCFG_1.
End PEACH5.
