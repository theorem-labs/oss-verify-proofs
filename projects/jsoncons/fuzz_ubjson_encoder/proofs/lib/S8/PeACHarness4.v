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

Module PEACH4.
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
Hypothesis WLOC : forall a, L5.outside W a -> L5.outside (PMSPA.loc_W AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Variable P : PESKA.sink_policyA.
Variable payload : list byte.
Local Notation n := (PEACH.n payload).
Local Notation p := (PEACH.p payload).
Local Notation parser_at := (PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA).

Lemma stage4 (RDC : PECSA.reader_ctor_spec L ar HI) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (K : TSet)
      (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (g : PMST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 (V2 - 160) F 2147450880 -> K [] -> PMST.st_loc g = true -> PESTA.ls_okA RSEGS AD AAD EE g M5 ->
  getr R5 (reg 1) = Z_to_bv 64 0xa8e94 -> getr R5 (reg 10) = Z_to_bv 64 (F + 592) -> getr R5 (reg 11) = Z_to_bv 64 (F + 96) ->
  getr R5 (reg 12) = Z_to_bv 64 (F + 1056) -> getr R5 (reg 13) = Z_to_bv 64 (V2 - 112) ->
  getr R5 (reg 18) = Z_to_bv 64 (F + 520) -> getr R5 (reg 20) = Z_to_bv 64 1024 -> getr R5 (reg 22) = Z_to_bv 64 (F + 432) ->
  getr R5 (reg 23) = Z_to_bv 64 (F + 496) -> getr R5 (reg 24) = Z_to_bv 64 (F + 1056) -> getr R5 (reg 25) = Z_to_bv 64 (F + 592) ->
  PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s -> PEACH.his_pay payload F M5 s' sm -> PEACH.hse0 L ar P F M5 ->
  L5.u64_at RSEGS M5 (F + 1056) 0x133428 -> L5.u64_at RSEGS M5 (F + 1064) 16777216 -> L5.u64_at RSEGS M5 (F + 1072) 0x133450 -> L5.u32_at RSEGS M5 (F + 1080) 1024 ->
  L5.defined M5 (F + 592) 384 -> shadow_zero M5 (F + 592) 49 -> shadow_zero M5 (F + 1056) 4 ->
  shadow_zero M5 (F + 96) 34 -> shadow_zero M5 (F + 432) 3 -> shadow_zero M5 (F + 496) 7 ->
  L5.u64_at RSEGS M5 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M5 (V2 - 136) F ->
  PMSPA.credit_le (PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) 32))) cr5 ->
  (forall (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (qc b : Z),
      Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 (V2 - 160) F 2147450880 ->
      PESTA.ls_okA RSEGS AD AAD EE g M6 ->
      getr R6 (reg 1) = Z_to_bv 64 0xa8ed4 -> getr R6 (reg 18) = Z_to_bv 64 (F + 520) -> getr R6 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R6 (reg 22) = Z_to_bv 64 (F + 432) -> getr R6 (reg 23) = Z_to_bv 64 (F + 496) -> getr R6 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R6 (reg 25) = Z_to_bv 64 (F + 592) ->
      PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s -> PEACH.his_pay payload F M6 s' sm -> PEACH.hse0 L ar P F M6 ->
      parser_at M6 (F + 592) (F + 96) (PMSPA.parser_init qc b) -> L5.u64_at RSEGS M6 (F + 976) (F + 496) ->
      PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) 32))) PMSPA.cr0 ->
      L5.u32_at RSEGS M6 (F + 1120) 0 -> shadow_zero M6 (F + 1120) 2 -> L5.defined M6 (F + 1120) 16 ->
      shadow_zero M6 (F + 592) 49 -> shadow_zero M6 (F + 96) 34 -> shadow_zero M6 (F + 432) 3 -> shadow_zero M6 (F + 496) 7 ->
      L5.u64_at RSEGS M6 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M6 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xdb064 M6 model6) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0xb153c M5 model5) K.
Proof.
  intros BI RI K0 GL LS R1a R10 R11 R12 R13 R18 R20 R22 R23 R24 R25 VS0 HIS HSE O1056 O1064 O1072 O1080 PDEF SZP SZO SZI SZK SZE HSTKa HSTKb CRD KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M5 model5 LK5 cr5 A5 BI)
    as ((VW5 & VIC5 & VSB5 & VUAR5 & VMS5) & VOWN5 & (VFD5 & VFW5 & VFSW5 & VFLC5 & VFLW5) & (FLCc5 & FLV5 & FV5 & SPV5 & FSV5)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  assert (FDEF5 : L5.defined M5 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A5 model5) M5 F 2048 FV5)); exact VFD5).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PEAHK2.hf F) by (unfold PEAHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (LENp : Z.of_nat (length p) = n) by (unfold PEACH.p, PEACH.n; rewrite length_map; reflexivity).
  assert (FIN5 : In (F, 5, V2 - 160 + 32) (FF' ++ LK5)) by (apply in_or_app; left; left; reflexivity).
  pose proof LS as (LSB & LSL & LSS & LSE). rewrite GL in LSL.
  pose proof HIS as (IS5 & SZ5 & SMG & SMST & PAYB5).

  unfold PECSA.reader_ctor_spec, PECSPA.reader_ctor_spec in RDC. unfold PMSPA.o_p, PMSPA.o_is in RDC.
  cbn [pa_reader_ctor pa_off_p pa_off_is pa_vp_opts PeCLayoutA.CADDR_A] in RDC. change PM.MAX_DEPTH with 1024 in RDC. change PM.MAX_ITEMS with 16777216 in RDC.
  apply (RDC fx5 R5 M5 model5 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK5 A5 cr5 (V2 - 160) 0xa8e94 F (F + 1056) (V2 - 112) s' sm B1 B2 K0).
  { eapply PEAHSK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { exact (PEAHSK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { rewrite L5K.rl13. exact R13. }
  { clear. lia. }
  { exact PDEF. }
  { apply (PEAHK2.acc_of_shz M5 (F + 592) 49 (F + 592) 384 SZP); [| clear - FR; lia| clear; lia| clear; lia].
    replace (F + 592) with (F + 74 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8. }
  { apply (PEAHK2.acc_of_shz M5 (F + 1056) 4 (F + 1056) 32 SZO); [| clear - FR; lia| clear; lia| clear; lia].
    replace (F + 1056) with (F + 132 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact FM8. }
  { exact O1056. }
  { replace (F + 1056 + 8) with (F + 1064) by (clear; lia). exact O1064. }
  { replace (F + 1056 + 24) with (F + 1080) by (clear; lia). exact O1080. }
  { exact IS5. }
  { exact LSB. }
  { exact LSL. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' qc b cr' RP' PAT HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 6) with 24576 in HP'.
  rewrite app_assoc in HH'.
  assert (WFI : PEAHK2.wfi F [(F + 592, 384)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; lia| apply PEAHK2.wfi_nil]).
  assert (LS' : PESTA.ls_okA RSEGS AD AAD EE g M').
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) _ [(F + 592, 384)] M5 M' HP'); [| exact LS].
    apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BI' : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W (PM.vs_own s' ++ PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) _ M5 model5 LK5 cr5 A5 M' model' LK' cr' Aw' 24576 [(F + 592, 384)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' (V2 - 160) F 2147450880) by exact (rinvH_pres R R5 R' (V2 - 160) F 2147450880 RI RP').
  pose proof RI' as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R5 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 1024) by (rewrite (cs_of_preserved R5 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R5 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R5 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1056)) by (rewrite (cs_of_preserved R5 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R5 R' 25 RP') by inl; exact R25).

  assert (HB' : PEAHK2.hbase F M' s s' sm).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact (conj VS0 (conj IS5 SZI)) | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; exact Hx) | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil]) | apply incl_refl | lia ]. }
  pose proof HB' as (VS' & IS' & SZI').
  assert (HSE' : PEACH.hse0 L ar P F M').
  { eapply PEAHK4.hse0_callee; first [ exact B1 | exact HP' | exact HSE | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl) | (split; reflexivity) | (apply PEAHK2.wapart_cons; [cbn [fst snd]; lia| apply PEAHK2.wapart_nil]) | lia ]. }
  assert (AK' : forall a, 0 <= a < 2 ^ 64 -> ((F <= a < F + 592 \/ F + 976 <= a < F + 2040) /\ ~ (F + 24 <= a < F + 32)) -> M' (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha Hr. apply (proj1 HP' a). split; [exact Ha| split].
    - apply (fframe_client L ar _ FF' (V2 - 160) 24576 F 5 (V2 - 160 + 32)); [left; reflexivity|]. change (ff_bytes 5) with 2048. clear - Hr; lia.
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hr. lia. }
  assert (AGstk' : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (O1056' : L5.u64_at RSEGS M' (F + 1056) 0x133428) by (apply (L5C.u64_at_agree RSEGS M5 M' (F + 1056) _ ltac:(intros i Hi; apply AK'; clear - Hi FR; lia)); [clear - FR; lia| clear - FR; lia| exact O1056]).
  assert (O1072' : L5.u64_at RSEGS M' (F + 1072) 0x133450) by (apply (L5C.u64_at_agree RSEGS M5 M' (F + 1072) _ ltac:(intros i Hi; apply AK'; clear - Hi FR; lia)); [clear - FR; lia| clear - FR; lia| exact O1072]).
  assert (SZP' : shadow_zero M' (F + 592) 49).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 24576 [(F + 592, 384)] M5 M' (F, 5, V2 - 160 + 32) F (F + 592) 49 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZP]. }
  assert (SZO' : shadow_zero M' (F + 1056) 4).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 24576 [(F + 592, 384)] M5 M' (F, 5, V2 - 160 + 32) F (F + 1056) 4 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZO]. }
  assert (SZK' : shadow_zero M' (F + 432) 3).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 24576 [(F + 592, 384)] M5 M' (F, 5, V2 - 160 + 32) F (F + 432) 3 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZK]. }
  assert (SZE' : shadow_zero M' (F + 496) 7).
  { apply (PEAHK2.shz_callee L ar _ FF' (V2 - 160) 24576 [(F + 592, 384)] M5 M' (F, 5, V2 - 160 + 32) F (F + 496) 7 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [clear; lia| clear; lia| clear - FM8; lia| clear; lia| exact SZE]. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M5 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M5 M' (V2 - 136) F); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  assert (PAYB' : L5.bytes_at RSEGS M' (PM.vs_data (F + 176) s') p).
  { pose proof IS5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB5 |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M5 M' (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB5].
      intros i Hi. apply AK'; [clear - Hi FR SZB SZ5; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M5 M' q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB5].
      intros i Hi. apply (proj1 HP' i). split; [clear - Hi P0 P47 NC SZ5; lia| split].
      + left. exists (q0, c0). split; [apply in_or_app; left; left; reflexivity| cbn [fst snd]; clear - Hi NC SZ5; lia].
      + intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi PF NC SZ5. lia. }

  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E592 : (F + 592) / 8 = F / 8 + 74) by (clear - FM8; lia).
  assert (Q1120 : (F + 1120) / 8 + HeapIfaceA.SB = F / 8 + 2147451020) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Z122 : L5KA.zeros_at MV' (F / 8 + 2147451002) 1).
  { apply (proj2 (L5A.zeros_at_vis H' M' (F / 8 + 2147451002) 1 (PEAHK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 (F / 8 + 2147451002) 1 FSV' ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
    intros i Hi. pose proof (SZP' (48 + i) ltac:(clear - Hi; lia)) as X. unfold byte_at, HeapIfaceA.S in X. rewrite E592 in X.
    replace (F / 8 + 2147451002 + i) with (F / 8 + 74 + HeapIfaceA.SB + (48 + i)) by (unfold HeapIfaceA.SB; clear; lia). exact X. }
  pose proof (PEACHP2.ahnF_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact Z122 | (unfold PEACHP2.aligned; exact V2A) ]).
  destruct PP as (fx6 & R6 & M6v & MG6 & fFR & fFZ & (fMS & fKS & fR1 & fR10 & fR11 & fR20 & fR24 & FQ)).
  set (W6 := fun a => F + 976 <= a < F + 976 + 8 \/ F / 8 + 2147451012 <= a < F / 8 + 2147451012 + 4 \/ F / 8 + 2147451020 <= a < F / 8 + 2147451020 + 2 \/ F + 1120 <= a < F + 1120 + 4).
  assert (WC6 : forall a, 0 <= a < 2 ^ 64 -> W6 a -> aclientw L ar (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W6; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]]; split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia. }
  rewrite <- !app_assoc in HH'.
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx6 R' 0xa8e94 R6 0xdb064 M6v W6 K HH' AM' fMS MG6).
  { intros a Ha Hna. apply fFZ; [exact Ha|..]; intros X0; apply Hna; subst W6; cbn beta; clear - X0; lia. }
  { exact WC6. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H' M6 = M6v) in VIS6.
  rewrite !app_assoc in HH6.
  pose proof HH' as HH''. rewrite (app_assoc (PM.vs_own s') (PM.vs_own s) LB) in HH''. rewrite (app_assoc (PM.parser_own (PMSPA.parser_init qc b)) (PM.vs_own s' ++ PM.vs_own s) LB) in HH''.
  assert (BI6 : Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M6 model6 W6 BI' HH6 AM6 MRT6 MGM6 FR6).
    intros a Wa. subst W6; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]]; [right; left| right; right| right; right| right; left]; change (ff_bytes 5) with 2048;
      [clear - Wa; lia| change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| clear - Wa; lia]. }
  assert (RI6 : rinvH R R6 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R' R6 (V2 - 160) F 2147450880 PEACHP2.KS_ahnF RI' fKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS6 : PESTA.ls_okA RSEGS AD AAD EE g M6).
  { apply (PEAHK.ls_piece _ M' M6 W6 FR6); [| exact LS']. intros a Wa. subst W6; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  assert (PF6 : PEAHK2.pfoot F (V2 - 160) V2 W6) by (intros a Wa; subst W6; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (OAX6 : forall o k, F <= o -> o + k <= F + 976 -> PEAHK2.oav W6 o k).
  { intros o k H1 H2 x Hx. subst W6; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 FBD; lia. }
  pose proof BI6 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (HB6 : PEAHK2.hbase F M6 s s' sm).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 s s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX6; clear; lia| apply OAX6; clear; lia| exact HB']. }
  pose proof HB6 as (VS6 & IS6 & SZI6).
  assert (HSE6 : PEACH.hse0 L ar P F M6).
  { apply (PEAHK4.hse0_piece L ar P F FHF W6 M' M6 FR6); [apply OAX6; clear; lia| apply OAX6; clear; lia| exact HSE']. }
  assert (PA6 : parser_at M6 (F + 592) (F + 96) (PMSPA.parser_init qc b)).
  { apply (PEAHK4.parser_keep_piece L ar C HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 592) (F + 96));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX6; clear; lia| exact PAT]. }
  assert (FR6lo : forall a, 0 <= a < 2 ^ 64 -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) -> ~ (F + 976 <= a < F + 984) -> ~ (F + 1120 <= a < F + 1124) -> M6 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hr Hn1 Hn2. apply FR6; [exact Ha|]. subst W6; cbn beta. intros X. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hr. clear - Hr Hn1 Hn2 X FBD. lia. }
  assert (FAPP : forall a, F <= a < F + 2048 -> a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) by (intros a Ha; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - Ha FBIG; lia).
  assert (HSTKa6 : L5.u64_at RSEGS M6 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M' M6 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
    intros i Hi; apply FR6lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia| clear - Hi Q3 CLS; lia]. }
  assert (HSTKb6 : L5.u64_at RSEGS M6 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M' M6 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
    intros i Hi; apply FR6lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia| clear - Hi Q3 CLS; lia]. }
  assert (PAYB6 : L5.bytes_at RSEGS M6 (PM.vs_data (F + 176) s') p).
  { pose proof IS5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _). replace (F + 96 + 80) with (F + 176) in VSA by (clear; lia).
    pose proof VSA as (_ & _ & VX). destruct s' as [n0|c0 n0 q0]; cbn [PM.vs_data] in PAYB' |- *; cbn in SZ5, VX.
    - pose proof (proj1 VX) as SZB.
      apply (L5C.bytes_at_agree RSEGS M' M6 (F + 176 + 1) p); rewrite ?LENp; [| clear - FR; lia| clear - FR SZB SZ5; lia| exact PAYB'].
      intros i Hi. apply FR6lo; [clear - Hi FR SZB SZ5; lia| apply FAPP; clear - Hi SZB SZ5; lia| clear - Hi SZB SZ5; lia| clear - Hi SZB SZ5; lia].
    - pose proof VX as (_ & _ & _ & NC & CC & _).
      destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q0 c0 B1 ltac:(apply in_or_app; left; left; reflexivity)) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      pose proof (PFA (F, 5, V2 - 160 + 32) FIN5) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
      apply (L5C.bytes_at_agree RSEGS M' M6 q0 p); rewrite ?LENp; [| clear - P0; lia| clear - P47 NC SZ5; lia| exact PAYB'].
      intros i Hi. apply FR6lo; [clear - Hi P0 P47 NC SZ5; lia| clear - Hi PSH NC SZ5; lia| clear - Hi PF NC SZ5; lia| clear - Hi PF NC SZ5; lia]. }
  assert (SZP6 : shadow_zero M6 (F + 592) 49).
  { apply (PEAHK2.shz_frame M' M6 W6 (F + 592) 49 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZP'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X. rewrite E592 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (SZK6 : shadow_zero M6 (F + 432) 3).
  { apply (PEAHK2.shz_frame M' M6 W6 (F + 432) 3 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZK'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E432 : (F + 432) / 8 = F / 8 + 54) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E432 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (SZE6 : shadow_zero M6 (F + 496) 7).
  { apply (PEAHK2.shz_frame M' M6 W6 (F + 496) 7 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZE'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E496 : (F + 496) / 8 = F / 8 + 62) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E496 in X. clear - X Hj FBD FR FBIG. lia. }
  assert (AVF : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PEAHK.avis_sub H' F 2048 (F + d) k FV'); lia).
  assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H' q k)
    by (intros q k Hd1 Hd2; apply (PEAHK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 q k FSV'); unfold HeapIfaceA.SB; lia).
  assert (FDEF6 : L5.defined M6 F 2048).
  { pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M6 model6 LK' cr' Aw' BI6)
      as ((_ & _ & _ & _ & _) & _ & (VFD6 & _ & _ & _ & _) & (_ & _ & FV6 & _ & _)).
    apply (proj1 (L5A.defined_vis (ahid Aw' model6) M6 F 2048 FV6)); exact VFD6. }
  decompose [and] FQ. clear FQ.
  apply (KONT fx6 R6 M6 model6 LK' cr' Aw' qc b BI6 RI6 LS6).
  - exact fR1.
  - rewrite (fKS 18%nat) by inl. exact Y18.
  - exact fR20.
  - rewrite (fKS 22%nat) by inl. exact Y22.
  - rewrite (fKS 23%nat) by inl. exact Y23.
  - exact fR24.
  - rewrite (fKS 25%nat) by inl. exact Y25.
  - exact VS6.
  - split; [exact IS6| split; [exact SZ5| split; [exact SMG| split; [exact SMST| exact PAYB6]]]].
  - exact HSE6.
  - exact PA6.
  - apply (PEAHK.u64_vis H' M6 M6v (F + 976) _ VV6 (AVF 976 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - assert (E0 : PMSPA.scA L PmSpecs.PMSP.cr0 = PMSPA.cr0) by (unfold PMSPA.scA, PmSpecs.PMSP.cr0, PMSPA.cr0; cbn [fst snd]; rewrite Z.mul_0_r; reflexivity).
    first [exact CK' | (rewrite E0 in CK'; exact CK')].
  - apply (PEAHK.u32_vis H' M6 M6v (F + 1120) _ VV6 (AVF 1120 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PEAHK.shz_vis H' M6 M6v (F + 1120) 2 (F / 8 + 2147451020) VV6 (AVS (F / 8 + 2147451020) 2 ltac:(lia) ltac:(lia)) Q1120 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1) by (clear - Hj; lia). destruct J as [J|J]; subst j; gmem.
  - apply (L5.defined_sub M6 F 2048 (F + 1120) 16 FDEF6); clear; lia.
  - exact SZP6.
  - exact SZI6.
  - exact SZK6.
  - exact SZE6.
  - exact HSTKa6.
  - exact HSTKb6.
Qed.
End Stage.
End SCFG_1.
End PEACH4.
