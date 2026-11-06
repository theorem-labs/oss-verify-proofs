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

Module PEACH6.
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
Hypothesis FAL : F mod 2048 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| first [apply PEAHK2.wapart_nil | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil])]])
  | (apply PEAHK2.wapart_nil) | lia ].

Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Variable P : PESKA.sink_policyA.
Variable payload : list byte.
Local Notation n := (PEACH.n payload).
Local Notation p := (PEACH.p payload).
Local Notation parser_at := (PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA).

Lemma stage6 (RST : PECSA.reset_spec L ar HI) (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (K : TSet)
      (LK7 : list fframe) (cr7 : credit) (A7 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (qc b : Z) (g : PMST.st) (v c : Z) :
  Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M7 model7 LK7 cr7 A7 -> rinvH R R7 (V2 - 160) F 2147450880 -> K [] ->
  PESTA.ls_okA RSEGS AD AAD EE g M7 ->
  getr R7 (reg 1) = Z_to_bv 64 0xa8ee0 -> getr R7 (reg 10) = Z_to_bv 64 (F + 592) -> getr R7 (reg 18) = Z_to_bv 64 (F + 520) -> getr R7 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R7 (reg 22) = Z_to_bv 64 (F + 432) -> getr R7 (reg 23) = Z_to_bv 64 (F + 496) -> getr R7 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R7 (reg 25) = Z_to_bv 64 (F + 592) ->
  PEAHK2.hbase F M7 s s' sm -> PM.vs_size s' = n -> L5.bytes_at RSEGS M7 (PM.vs_data (F + 176) s') p -> PEACH.hse0 L ar P F M7 ->
  parser_at M7 (F + 592) (F + 96) (PMSPA.parser_init qc b) -> L5.u64_at RSEGS M7 (F + 976) (F + 496) ->
  PEAHK2.hec F M7 v c -> shadow_zero M7 (F + 592) 49 ->
  L5.u64_at RSEGS M7 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M7 (V2 - 136) F ->
  (forall (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (LK8 : list fframe) (A8 : list (Z * Z)),
      Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK8 cr7 A8 -> rinvH R R8 (V2 - 160) F 2147450880 ->
      PESTA.ls_okA RSEGS AD AAD EE g M8 ->
      getr R8 (reg 1) = Z_to_bv 64 0xa8ef0 -> getr R8 (reg 10) = Z_to_bv 64 (F + 592) -> getr R8 (reg 11) = Z_to_bv 64 (F + 496) -> getr R8 (reg 12) = Z_to_bv 64 (F + 1120) ->
      getr R8 (reg 18) = Z_to_bv 64 (F + 520) -> getr R8 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R8 (reg 22) = Z_to_bv 64 (F + 432) -> getr R8 (reg 23) = Z_to_bv 64 (F + 496) -> getr R8 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R8 (reg 25) = Z_to_bv 64 (F + 592) ->
      PEAHK2.hbase F M8 s s' sm -> L5.bytes_at RSEGS M8 (PM.vs_data (F + 176) s') p -> PEACH.hse0 L ar P F M8 ->
      parser_at M8 (F + 592) (F + 96) (PMSPA.pst_reset (PMSPA.parser_init qc b)) -> L5.u64_at RSEGS M8 (F + 976) (F + 496) ->
      PEAHK2.hec F M8 v c -> shadow_zero M8 (F + 592) 49 ->
      L5.u64_at RSEGS M8 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M8 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xb24ec M8 model8) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx7 R7 0xb2304 M7 model7) K.
Proof.
  intros BI RI K0 LS R1a R10 R18 R20 R22 R23 R24 R25 HB0 SZ5 PAYB0 HSE0 PA0 VV0 HE0 SZP0 HSTKa HSTKb KONT.
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
  set (P0 := PMSPA.parser_init qc b) in *.
  set (LBXc := PM.vs_own s' ++ PM.vs_own s). set (LBX := LBXc ++ LB).
  assert (B1' : ri_inv HI (PM.parser_own P0 ++ LBX) FF' LK7 cr7 A7 M7 (vml_of model7)).
  { unfold LBX, LBXc. pose proof B1 as B1x. rewrite <- !app_assoc in B1x. rewrite <- !app_assoc. exact B1x. }
  unfold PECSA.reset_spec, PECSPA.reset_spec in RST. unfold PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_p, PMSPA.o_is in RST.
  cbn [pa_reset pa_off_p pa_off_is PeCLayoutA.CADDR_A] in RST.
  apply (RST fx7 R7 M7 model7 K LBX FF' LK7 A7 cr7 (V2 - 160) 0xa8ee0 F P0 B1' B2 K0).
  { eapply PEAHSK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { exact (PEAHSK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { exact PA0. }
  { subst P0. cbn. lia. }
  intros fx' R' M' model' LK' Aw' RP' PA' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  assert (HH'' : ri_inv HI ((PM.parser_own P0 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK' cr7 Aw' M' (vml_of model')).
  { rewrite <- !app_assoc. unfold LBX, LBXc in HH'. rewrite <- !app_assoc in HH'. exact HH'. }
  set (Wc := [(F + 592 + 8, 8); (F + 592 + 336, 24); (F + 592 + 360, 24)]) in *.
  assert (WcF : forall r, In r Wc -> F + 592 <= fst r /\ fst r + snd r <= F + 976) by (intros r Hr; subst Wc; destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia).
  assert (WFI : PEAHK2.wfi F Wc) by (intros r Hr; destruct (WcF r Hr); left; lia).
  assert (WA : forall o k, (o + k <= F + 592 \/ F + 976 <= o) -> PEAHK2.wapart Wc o k) by (intros o k Ho r Hr; destruct (WcF r Hr); lia).
  assert (LS' : PESTA.ls_okA RSEGS AD AAD EE g M').
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 Wc M7 M' HP'); [| exact LS].
    intros r Hr. destruct (WcF r Hr). right. clear - H H0 FR. lia. }
  assert (BI' : Bv W (PM.parser_own P0 ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr7 Aw').
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
  assert (RI' : rinvH R R' (V2 - 160) F 2147450880) by exact (rinvH_pres R R7 R' (V2 - 160) F 2147450880 RI RP').
  pose proof RI' as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R7 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R7 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R7 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R7 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1120)) by (rewrite (cs_of_preserved R7 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R7 R' 25 RP') by inl; exact R25).
  assert (FIN7 : In (F, 5, V2 - 160 + 32) (FF' ++ LK7)) by (apply in_or_app; left; left; reflexivity).

  assert (HB' : PEAHK2.hbase F M' s s' sm).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (unfold LBX, LBXc; intros x Hx; apply in_or_app; left; exact Hx) | apply incl_refl | lia ]. }
  assert (HE' : PEAHK2.hec F M' v c).
  { eapply PEAHK2.hec_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HE0 | exact FHF | exact FIN7 | exact WFI | (apply WA; lia) | (left; reflexivity) | (split; reflexivity) | lia ]. }
  assert (HSE' : PEACH.hse0 L ar P F M').
  { eapply PEAHK4.hse0_callee; first [ exact B1 | exact HP' | exact HSE0 | exact FHF | exact FIN7 | exact WFI | (left; reflexivity) | (split; reflexivity) | (apply WA; lia) | lia ]. }
  assert (AGR : PMFA.agA M7 M' (F + 976) 8).
  { apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 14336 Wc M7 M' (F, 5, V2 - 160 + 32) F (F + 976) 8 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
  assert (VV' : L5.u64_at RSEGS M' (F + 976) (F + 496)) by (apply (PEAHK2.u64_agA M7 M' (F + 976) 8 (F + 976) _ AGR); [lia| lia| lia| lia| exact VV0]).
  assert (SZP' : shadow_zero M' (F + 592) 49).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 14336 Wc M7 M' (F, 5, V2 - 160 + 32) F (F + 592) 49 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [lia| lia| exact (fb_mod8 F 74 FAL)| lia| exact SZP0]. }
  assert (AGstk' : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng. clear - Ha Z1 Z2 FCEIL SLO CLS. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M7 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M7 M' (V2 - 136) F); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (PAYB' : L5.bytes_at RSEGS M' (PM.vs_data (F + 176) s') p).
  { pose proof HB0 as (_ & ISx & _). pose proof ISx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB0 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      assert (AGS : PMFA.agA M7 M' (F + 176) 24).
      { apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 14336 Wc M7 M' (F, 5, V2 - 160 + 32) F (F + 176) 24 HP' (or_introl eq_refl));
          cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI| apply WA; lia]. }
      apply (L5C.bytes_at_agree RSEGS M7 M' (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB0].
      intros i Hi. apply (proj1 AGS). clear - Hi SZB SZ5; lia.
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (Q0 & Q3' & Q4 & Q5 & QSH & Q47 & QIMG & QFA).
      pose proof (QFA (F, 5, V2 - 160 + 32) FIN7) as QF. cbn [ff_addr ff_class fst snd] in QF. change (ff_bytes 5) with 2048 in QF.
      apply (L5C.bytes_at_agree RSEGS M7 M' q0 p); rewrite ?LENp; [| clear - Q0; lia| clear - Q47 NC SZ5; lia| exact PAYB0].
      intros i Hi. apply (proj1 HP' i). split; [clear - Hi Q0 Q47 NC SZ5; lia| split].
      + left. exists (q0, c0). split; [unfold LBX, LBXc; apply in_or_app; left; apply in_or_app; left; left; reflexivity| cbn [fst snd]; clear - Hi NC SZ5; lia].
      + intros rr Hr. destruct (WcF rr Hr) as (Z1 & Z2). unfold L5.in_rng. clear - Hi QF NC SZ5 Z1 Z2. lia. }

  pose proof (PEACHP2.ahnH_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 35%nat => F + 496 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (Q7 : L5.u64_at RSEGS MV' (F + 976) (F + 496))
    by (apply (proj2 (L5A.u64_at_vis H' M' (F + 976) (F + 496) (PEAHK.avis_sub H' F 2048 (F + 976) 8 FV' ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact VV').
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact Q7 | (unfold PEACHP2.aligned; exact V2A) ]).
  destruct PP as (fx8 & R8 & M8v & MG8 & gFR & gFZ & (gMS & gKS & gR1 & gR10 & gR11 & gR12)).
  set (W8 := fun a : Z => False).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr7 Aw' M' model' fx' fx8 R' 0xa8ee0 R8 0xb24ec M8v W8 K HH'' AM' gMS MG8).
  { intros a Ha Hna. apply gFZ; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8.
  assert (BI8 : Bv W (PM.parser_own P0 ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK' cr7 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr7 Aw' M8 model8 W8 BI' HH8 AM8 MRT8 MGM8 FR8).
    intros a Wa. destruct Wa. }
  assert (RI8 : rinvH R R8 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R' R8 (V2 - 160) F 2147450880 PEACHP2.KS_ahnH RI' gKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS8 : PESTA.ls_okA RSEGS AD AAD EE g M8) by (apply (PEAHK.ls_piece _ M' M8 W8 FR8); [intros a []| exact LS']).
  assert (EQM : forall a, 0 <= a < 2 ^ 64 -> M8 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) by (intros a Ha; apply FR8; [exact Ha| intros []]).
  assert (E8 : M8 = M') by (apply mem_eq_of_agree; exact EQM).
  apply (KONT fx8 R8 M8 model8 LK' Aw' BI8 RI8 LS8).
  - exact gR1.
  - exact gR10.
  - exact gR11.
  - exact gR12.
  - rewrite (gKS 18%nat) by inl. exact Y18.
  - rewrite (gKS 20%nat) by inl. exact Y20.
  - rewrite (gKS 22%nat) by inl. exact Y22.
  - rewrite (gKS 23%nat) by inl. exact Y23.
  - rewrite (gKS 24%nat) by inl. exact Y24.
  - rewrite (gKS 25%nat) by inl. exact Y25.
  - rewrite E8. exact HB'.
  - rewrite E8. exact PAYB'.
  - rewrite E8. exact HSE'.
  - rewrite E8. exact PA'.
  - rewrite E8. exact VV'.
  - rewrite E8. exact HE'.
  - rewrite E8. exact SZP'.
  - rewrite E8. exact HSTKa'.
  - rewrite E8. exact HSTKb'.
Qed.
End Stage.
End SCFG_1.
End PEACH6.
