(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnASrcKit_b PnAHarnessP3_b PnAHarnessP4_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA9.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
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
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

Lemma stage9 (SRCD : PMA.src_dtor_spec L ar HI) (OPD : PMA.opdel_spec L ar HI) (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (K : TSet)
      (LK10 : list fframe) (cr10 : credit) (A10 : list (Z * Z)) (s str : PM.vstr) (sm : PM.strm) (src : PM.srcst) (g : PNST.st) :
  Bv W ((PM.sr_qc src, PM.CHUNK) :: PM.vs_own str ++ PM.vs_own s) M10 model10 LK10 cr10 A10 -> rinvH R R10 V2 cls F -> K [] ->
  PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M10 ->
  getr R10 (reg 1) = Z_to_bv 64 0xa8534 -> getr R10 (reg 10) = Z_to_bv 64 (F + 480) -> getr R10 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R10 (reg 22) = Z_to_bv 64 (F + 464) -> getr R10 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R10 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M10 s str sm -> PNHAK2.hsrc F M10 src ->
  (forall (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (LK11 : list fframe) (A11 : list (Z * Z)),
      Bv W (PM.vs_own s) M11 model11 LK11 cr10 A11 -> rinvH R R11 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M11 ->
      getr R11 (reg 1) = Z_to_bv 64 0xa86bc -> getr R11 (reg 10) = Z_to_bv 64 (F + 120) -> getr R11 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R11 (reg 22) = Z_to_bv 64 1266024 -> getr R11 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R11 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hfin F M11 s (PM.sm_st sm) ->
      srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0xfef40 M11 model11) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xab344 M10 model10) K.
Proof.
  intros BI RI K0 LS R1a R10a R21 R22 R23 R26 HB0 HS0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (X := PM.vs_own str ++ PM.vs_own s) in *.
  cbn [app] in B1.
  pose proof HS0 as (SF0 & NI0). pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PMA.src_dtor_spec, PMSPA.src_dtor_spec in SRCD. cbn [pa_src_dtor PMA.AD ADDR_A] in SRCD.
  apply (SRCD fx10 R10 M10 model10 K _ FF' LK10 A10 cr10 (F + 480) (F + 96) (F + 112) (V2 - 128) 0xa8534 src B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10a. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { clear - FM8. lia. }
  { exact SF0. }
  { replace (F + 480 + 8) with (F + 488) by lia. exact NI0. }
  { left. reflexivity. }
  { exact LSB. }
  intros fx' R' M' model' LK' Aw' RP' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 2) with 16384 in HP'.
  rewrite L5ADHR.lb_remove_head in HP', HH'.
  assert (WFI : PNHAK2.wfi F [(F + 480, 296)]) by (apply PNHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PNHAK2.wfi_nil]).
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 16384 [(F + 480, 296)] M10 M' HP'); [| exact LS].
    apply PNHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PNHAK.far_nil]. }
  assert (BI' : Bv W X M' model' LK' cr10 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ X X M10 model10 LK10 cr10 A10 M' model' LK' cr10 Aw' 16384 [(F + 480, 296)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr10 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R10 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R10 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R10 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R10 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R10 R' 26 RP') by inl; exact R26).
  assert (FIN10 : In (F, 5, V2 - 128 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
  assert (HB' : PNHAK2.hbase F M' s str sm).
  { eapply PNHAK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN10 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  pose proof HB' as (VS' & IS' & VV' & VZ' & VI').
  (* [comment removed for export] *)
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q7 : 65536 + 6840320 <= F \/ F + 2048 <= 65536) by (clear - FR; lia).
  assert (Q8 : 65536 + 6840320 <= fl \/ fl + 1 <= 65536) by (clear - FLR; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP3.bhaK1_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact VSB' | exact VUAR' | exact VIC' | (unfold PNAHP3.aligned; exact V2A) ]).
  destruct P as (fx1 & R1 & M1v & MG1 & kFR & kFZ & (kMS & kKS & kR10 & kR11 & kR22 & KQ)). clear KQ.
  set (W1 := fun a => F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 1 \/ F / 8 + 2147450938 <= a < F / 8 + 2147450938 + 53).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M' model' fx' fx1 R' 0xa8534 R1 0xa8618 M1v W1 K HH' AM' kMS MG1).
  { intros a Ha Hna. apply kFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (BI1 : Bv W X M1 model1 LK' cr10 Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr10 Aw' M1 model1 W1 BI' HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst W1; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI1 : rinvH R R1 V2 cls F) by (apply (rinvH_ks R R' R1 V2 cls F PNAHP3.KS_bhaK1 RI' kKS); vm_compute; reflexivity).
  assert (LS1 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M1) by (apply (PNHAK.ls_piece _ M' M1 W1 FR1); [intros a Wa; subst W1; cbn beta in Wa; clear - Wa FR; lia| exact LS']).
  assert (PF1 : PNHAK2.pfoot F (V2 - 128) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA1 : forall o n, F + 32 <= o -> o + n <= F + 368 -> PNHAK2.oav W1 o n).
  { intros o n H1 H2 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8; lia. }
  assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (INS : incl (PM.vs_own s) (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; right; exact Hx).
  assert (INT : incl (PM.vs_own str) (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; left; exact Hx).
  assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 (F + 32) s)
    by (apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W1 M' M1 SLOW SHW FR1 PF1 (F + 32) s INS); [clear - FR; lia| clear - FR; lia| apply OA1; lia| exact VS']).
  assert (IS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 (F + 96) str sm)
    by (apply (PNHAK2.iss_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W1 M' M1 SLOW SHW FR1 PF1 (F + 96) str sm INT); [clear - FR; lia| clear - FR; lia| apply OA1; lia| exact IS']).
  assert (VI1 : shadow_zero M1 (F + 96) 34).
  { apply (PNHAK2.shz_frame M' M1 W1 (F + 96) 34 FR1); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact VI'].
    intros j Hj X0. subst W1; cbn beta in X0. unfold HeapIfaceA.S, HeapIfaceA.SB in X0. rewrite E96 in X0. clear - X0 Hj. lia. }
  (* [comment removed for export] *)
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' BI1)
    as ((VW1 & VIC1 & VSB1 & VUAR1 & VMS1) & VOWN1 & (VFD1 & VFW1 & VFSW1 & VFLC1 & VFLW1) & (FLCc1 & FLV1 & FV1 & SPV1 & FSV1)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H1' := ahid Aw' model1) in *. set (MV1 := mrestrict H1' M1) in *.
  assert (Q5b : L5.writable RSEGS MV1 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW1| clear; lia| clear - CLS; lia]).
  assert (Q6b : L5.u64_at RSEGS MV1 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC1).
  assert (ZI : L5KA.zeros_at MV1 (F / 8 + 2147450892) 34).
  { apply (proj2 (L5A.zeros_at_vis H1' M1 (F / 8 + 2147450892) 34 (PNHAK.avis_sub H1' (F / 8 + HeapIfaceA.SB) 256 (F / 8 + 2147450892) 34 FSV1 ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
    replace (F / 8 + 2147450892) with (HeapIfaceA.S (F + 96)) by (unfold HeapIfaceA.S, HeapIfaceA.SB; rewrite E96; lia). apply PNHAK2.zeros_of_shz. exact VI1. }
  assert (ZV1 : L5KA.zeros_at MV1 2147609133 1).
  { pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x135168 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as Z0.
    exact Z0. }
  assert (ZV2 : L5KA.zeros_at MV1 2147609136 1).
  { pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x135180 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as Z0.
    exact Z0. }
  assert (ZV3 : L5KA.zeros_at MV1 2147609123 1).
  { pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M1 model1 0x135118 1 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as Z0.
    exact Z0. }
  pose proof IS1 as (IH0 & ID & IC & IH16 & IH24 & IH32 & IH40 & IH48 & IH64 & IVS & IH104 & IH112 & IOS & IE1 & IE2).
  replace (F + 96 + 24) with (F + 120) in IH24 by lia. replace (F + 96 + 80) with (F + 176) in IVS by lia.
  replace (F + 96 + 120) with (F + 216) in IOS by lia. replace (F + 96 + 16) with (F + 112) in IOS by lia.
  assert (FDEF1 : L5.defined M1 F 2048) by (apply (proj1 (L5A.defined_vis H1' M1 F 2048 FV1)); exact VFD1).
  assert (AV176 : L5A.avis H1' (F + 176) 8) by (apply (PNHAK.avis_sub H1' F 2048 (F + 176) 8 FV1); lia).
  assert (AV192 : L5A.avis H1' (F + 192) 8) by (apply (PNHAK.avis_sub H1' F 2048 (F + 192) 8 FV1); lia).
  set (W2 := fun a => F + 96 <= a < F + 96 + 8 \/ F + 112 <= a < F + 112 + 8 \/ F + 216 <= a < F + 216 + 8).
  assert (WC2 : forall a, 0 <= a < 2 ^ 64 -> W2 a -> aclientw L ar (X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6905856)).
  { intros a Ha Wa. subst W2; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia. }
  assert (PF2 : PNHAK2.pfoot F (V2 - 128) V2 W2) by (intros a Wa; subst W2; cbn beta in Wa; clear - Wa; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA2 : forall o n, (F + 32 <= o /\ o + n <= F + 96) \/ (F + 120 <= o /\ o + n <= F + 216) \/ (F + 224 <= o /\ o + n <= F + 2040) -> PNHAK2.oav W2 o n).
  { intros o n H12 x Hx. subst W2; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8; lia. }
  assert (SH2 : forall x, F + 216 <= x < F + 368 -> ~ W2 (HeapIfaceA.S x)).
  { intros x Hx. subst W2; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. intros X0; clear - Hx X0 SX FBIG FR FM8; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct str as [nt | c nt p].
  - (* [comment removed for export] *)
    destruct IVS as (_ & _ & (Hnt & SB0)).
    assert (SBv : L5.u8_at RSEGS MV1 (F + 176) (2 * nt))
      by (apply (proj2 (L5A.u8_at_vis H1' M1 (F + 176) (2 * nt) (PNHAK.avis_sub H1' (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    pose proof (PMF.even_byte nt) as EVB.
    pose proof RI1 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z24 & Z25 & Z3 & Z4 & Z27).
    assert (T21 : getr R1 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (kKS 21%nat) by inl; exact Y21).
    assert (T23 : getr R1 (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (kKS 23%nat) by inl; exact Y23).
    assert (T26 : getr R1 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (kKS 26%nat) by inl; exact Y26).
    LeanFeed.pfeed P (PNAHP4.bhaK2s_conc fx1 R1 MV1 (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
                       | exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5b | exact Q6b | exact VSB1 | exact VUAR1 | exact VIC1 | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
                       | exact SBv | exact EVB | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx2 & R2 & M2v & MG2 & sFR & sFZ & (sMS & sKS & sR1 & sR10 & sR11 & sR12 & sU112 & sU216 & sU96 & sD1 & sD2 & sD3 & sD4)).
    apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M1 model1 fx1 fx2 R1 0xa8618 R2 0xfef40 M2v W2 K HH1 AM1 sMS MG2).
    { intros a Ha Hna. apply sFZ; [exact Ha|..]; intros X0; apply Hna; subst W2; cbn beta; clear - X0; lia. }
    { exact WC2. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (FDEF3 : L5.defined M3 F 2048) by (eapply L5.defined_grows; [exact MGM3| exact FDEF1]).
    apply (KONT fx2 R2 M3 model3 LK' Aw').
    + apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' M3 model3 W2 BI1 HH3 AM3 MRT3 MGM3 FR3).
      intros a Wa. subst W2; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa. lia.
    + apply (rinvH_ks R R1 R2 V2 cls F PNAHP4.KS_bhaK2s RI1 sKS); vm_compute; reflexivity.
    + apply (PNHAK.ls_piece _ M1 M3 W2 FR3); [intros a Wa; subst W2; cbn beta in Wa; clear - Wa FR; lia| exact LS1].
    + exact sR1.
    + exact sR10.
    + rewrite (sKS 21%nat) by inl. exact T21.
    + rewrite (sKS 22%nat) by inl. exact kR22.
    + rewrite (sKS 23%nat) by inl. exact T23.
    + rewrite (sKS 26%nat) by inl. exact T26.
    + split; [|split].
      * apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH1 FIN' FHF (V2 - 128) V2 W2 M1 M3 SLOW SHW FR3 PF2 (F + 32) s INS);
          [clear - FR; lia| clear - FR; lia| apply OA2; lia| exact VS1].
      * apply (PNHAK2.u64_agA M1 M3 (F + 120) 8 (F + 120) _ (PNHAK.agA_frame M1 M3 W2 (F + 120) 8 FR3 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OA2 (F + 120) 8 ltac:(lia))));
          [lia| lia| lia| lia| cbn [pa_classic_imp PMA.AD ADDR_A]; exact IH24].
      * apply (PNHAK2.iosb_revptr M1 M3 (F + 216) _ 1266008 (F + 112) (PM.sm_st sm) IOS).
        -- apply (PNHAK.u64_vis H1' M3 M2v (F + 216) _ VV3 (PNHAK.avis_sub H1' F 2048 (F + 216) 8 FV1 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact sU216.
        -- intros i Hi. apply FR3; [clear - Hi FR; lia| subst W2; cbn beta; clear - Hi; lia].
        -- intros x Hx. apply FR3; [pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply SH2; lia].
        -- apply (L5.defined_sub M3 F 2048 (F + 216) 8 FDEF3); lia.
        -- clear - FR; lia.
        -- clear - FR; lia.
  - (* [comment removed for export] *)
    destruct IVS as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    replace (F + 176 + 16) with (F + 192) in TW16 by lia.
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M1 _ _ Hc64 TW0) as SB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
    assert (SBv : L5.u8_at RSEGS MV1 (F + 176) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis H1' M1 (F + 176) _ (PNHAK.avis_sub H1' (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    assert (TW0v : L5.u64_at RSEGS MV1 (F + 176) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H1' M1 (F + 176) _ AV176 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MV1 (F + 192) p) by (apply (proj2 (L5A.u64_at_vis H1' M1 (F + 192) _ AV192 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
    assert (INP : In (p, c) (X ++ LB)) by (subst X; cbn [PM.vs_own app]; left; reflexivity).
    destruct (PNHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c HH1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
    pose proof RI1 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z24 & Z25 & Z3 & Z4 & Z27).
    assert (T21 : getr R1 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (kKS 21%nat) by inl; exact Y21).
    assert (T23 : getr R1 (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (kKS 23%nat) by inl; exact Y23).
    assert (T26 : getr R1 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (kKS 26%nat) by inl; exact Y26).
    LeanFeed.pfeed P (PNAHP4.bhaK2l_conc fx1 R1 MV1 (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
                                                      | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                       | exact F32 | exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5b | exact Q6b | exact VSB1 | exact VUAR1 | exact VIC1 | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
                       | exact SBv | exact TW0v | exact TW16v | exact ODB | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx2 & R2 & M2v & MG2 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lU112 & lU216 & lU96 & lD1 & lD2 & lD3 & lD4)).
    apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw' M1 model1 fx1 fx2 R1 0xa8618 R2 0xd39ac M2v W2 K HH1 AM1 lMS MG2).
    { intros a Ha Hna. apply lFZ; [exact Ha|..]; intros X0; apply Hna; subst W2; cbn beta; clear - X0; lia. }
    { exact WC2. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (FDEF3 : L5.defined M3 F 2048) by (eapply L5.defined_grows; [exact MGM3| exact FDEF1]).
    assert (BI3 : Bv W X M3 model3 LK' cr10 Aw').
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M1 model1 LK' cr10 Aw' M3 model3 W2 BI1 HH3 AM3 MRT3 MGM3 FR3).
      intros a Wa. subst W2; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa. lia. }
    assert (RI3 : rinvH R R2 V2 cls F) by (apply (rinvH_ks R R1 R2 V2 cls F PNAHP4.KS_bhaK2l RI1 lKS); vm_compute; reflexivity).
    assert (LS3 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M3) by (apply (PNHAK.ls_piece _ M1 M3 W2 FR3); [intros a Wa; subst W2; cbn beta in Wa; clear - Wa FR; lia| exact LS1]).
    assert (HF3 : PNHAK2.hfin F M3 s (PM.sm_st sm)).
    { split; [|split].
      * apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH1 FIN' FHF (V2 - 128) V2 W2 M1 M3 SLOW SHW FR3 PF2 (F + 32) s INS);
          [clear - FR; lia| clear - FR; lia| apply OA2; lia| exact VS1].
      * apply (PNHAK2.u64_agA M1 M3 (F + 120) 8 (F + 120) _ (PNHAK.agA_frame M1 M3 W2 (F + 120) 8 FR3 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OA2 (F + 120) 8 ltac:(lia))));
          [lia| lia| lia| lia| cbn [pa_classic_imp PMA.AD ADDR_A]; exact IH24].
      * apply (PNHAK2.iosb_revptr M1 M3 (F + 216) _ 1266008 (F + 112) (PM.sm_st sm) IOS).
        -- apply (PNHAK.u64_vis H1' M3 M2v (F + 216) _ VV3 (PNHAK.avis_sub H1' F 2048 (F + 216) 8 FV1 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). exact lU216.
        -- intros i Hi. apply FR3; [clear - Hi FR; lia| subst W2; cbn beta; clear - Hi; lia].
        -- intros x Hx. apply FR3; [pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply SH2; lia].
        -- apply (L5.defined_sub M3 F 2048 (F + 216) 8 FDEF3); lia.
        -- clear - FR; lia.
        -- clear - FR; lia. }
    (* [comment removed for export] *)
    pose proof BI3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    assert (ASX : L5CA.astk ar M3 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M3 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PNHASK.callee_stack; first [exact BI3 | eassumption | lia]).
    destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
    pose proof RI3 as (U2 & U8 & U9 & U18 & U19 & U20 & U24 & U25 & U3 & U4 & U27).
    unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
    apply (OPD fx2 R2 M3 model3 K _ FF' LK' Aw' cr10 p c (V2 - 128) 0xa86a4 C1 C2 K0 INP).
    { rewrite L5K.rl10. exact lR10. }
    { rewrite L5K.rl1. exact lR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact U2. }
    { rewrite L5K.rl4. rewrite U4. exact TP. }
    { replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M3 M3 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
        [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros fx3 R3 M4 model4 Aw4 RP4 HPo MRT4 INCA4 AM4 HHo.
    subst X. cbn [PM.vs_own app] in HPo, HHo, BI3, C1.
    rewrite L5ADHR.lb_remove_head in HPo, HHo.
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK' cr10 Aw4).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s) _ M3 model3 LK' cr10 Aw' M4 model4 LK' cr10 Aw4 4096 [] BI3 HPo HHo AM4 MRT4 INCA4 (incl_refl _)).
      - lia.
      - clear - CLS; lia.
      - intros rr a [].
      - intros a _ _ rr [].
      - intros a X0. exact X0. }
    assert (LS4 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M4) by (apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M3 M4 HPo PNHAK.far_nil LS3)).
    assert (FIN3 : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
    assert (HF4 : PNHAK2.hfin F M4 s (PM.sm_st sm)).
    { eapply PNHAK2.hfin_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HF3 | exact FHF | exact FIN3 | apply PNHAK2.wfi_nil | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx) | apply PNHAK2.wapart_nil | lia ]. }
    pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M4 model4 LK' cr10 Aw4 BI4)
      as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
    change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
    set (H4' := ahid Aw4 model4) in *. set (MV4 := mrestrict H4' M4) in *.
    assert (RI4 : rinvH R R3 V2 cls F) by exact (rinvH_pres R R2 R3 V2 cls F RI3 RP4).
    assert (S21 : getr R3 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R2 R3 21 RP4) by inl; rewrite (lKS 21%nat) by inl; exact T21).
    assert (S22 : getr R3 (reg 22) = Z_to_bv 64 1266024) by (rewrite (cs_of_preserved R2 R3 22 RP4) by inl; rewrite (lKS 22%nat) by inl; exact kR22).
    assert (S23 : getr R3 (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R2 R3 23 RP4) by inl; rewrite (lKS 23%nat) by inl; exact T23).
    assert (S26 : getr R3 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R2 R3 26 RP4) by inl; rewrite (lKS 26%nat) by inl; exact T26).
    pose proof RI4 as (V2r & V8r & V9r & V18r & V19r & V20r & V24r & V25r & V3r & V4r & V27r).
    assert (Q5c : L5.writable RSEGS MV4 (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW4| clear; lia| clear - CLS; lia]).
    assert (Q6c : L5.u64_at RSEGS MV4 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC4).
    LeanFeed.pfeed P (PNAHP4.bhaL_conc fx3 R3 MV4 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R3 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                       | exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5c | exact Q6c | exact VSB4 | exact VUAR4 | exact VIC4 | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx4 & R4 & M5v & MG5 & hFR & hFZ & (hMS & hKS & hR1 & hR10 & hU112 & hD1 & hD2)).
    set (W5 := fun a => F + 112 <= a < F + 112 + 8).
    apply (apiece L ar C HI LYa HIok _ FF' LK' cr10 Aw4 M4 model4 fx3 fx4 R3 0xa86a4 R4 0xfef40 M5v W5 K HHo AM4 hMS MG5).
    { intros a Ha Hna. apply hFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
    { intros a Ha Wa. subst W5; cbn beta in Wa. split.
      - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      - clear - Wa FR. lia. }
    intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
    assert (PF5 : PNHAK2.pfoot F (V2 - 128) V2 W5) by (intros a Wa; subst W5; cbn beta in Wa; clear - Wa; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (OA5 : forall o n, (F + 32 <= o /\ o + n <= F + 112) \/ (F + 120 <= o /\ o + n <= F + 2040) -> PNHAK2.oav W5 o n).
    { intros o n H12 x Hx. subst W5; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
      unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (KONT fx4 R4 M5 model5 LK' Aw4).
    + apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M4 model4 LK' cr10 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
      intros a Wa. subst W5; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa. lia.
    + apply (rinvH_ks R R3 R4 V2 cls F PNAHP4.KS_bhaL RI4 hKS); vm_compute; reflexivity.
    + apply (PNHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; clear - Wa FR; lia| exact LS4].
    + exact hR1.
    + exact hR10.
    + rewrite (hKS 21%nat) by inl. exact S21.
    + rewrite (hKS 22%nat) by inl. exact S22.
    + rewrite (hKS 23%nat) by inl. exact S23.
    + rewrite (hKS 26%nat) by inl. exact S26.
    + apply (PNHAK2.hfin_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HHo FIN3 FHF (V2 - 128) V2 W5 M4 M5 SLOW SHW FR5 PF5 s (PM.sm_st sm));
        [intros x Hx; apply in_or_app; left; exact Hx| apply OA5; lia| apply OA5; lia| apply OA5; lia| exact HF4].
Qed.
End Stage.
End SCFG_1.
End PNHA9.
