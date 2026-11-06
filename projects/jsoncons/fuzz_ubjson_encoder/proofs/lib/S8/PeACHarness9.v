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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCFrameA PeCSpecs PeCSpecsA PeCSpecsAa PeCDtorSpecsA PeACHarnessStmts PeACHarnessKit PeACHarnessKit2 PeACHarnessSK PeACHarnessKit3 PeACHarnessKit4 PeACHarnessP3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEACH9.
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
Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma stage9 (ESTK : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb140c) (SNK : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaa5cc)
      (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (K : TSet)
      (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z)) (s s' : PM.vstr) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (g : PMST.st) :
  Bv W ((PEC.enc_own en1 ++ PESK.sink_own k1) ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 (V2 - 160) F 2147450880 -> K [] -> PESTA.ls_okA RSEGS AD AAD EE g M9 ->
  getr R9 (reg 18) = Z_to_bv 64 (F + 520) -> getr R9 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R9 (reg 22) = Z_to_bv 64 (F + 432) -> getr R9 (reg 23) = Z_to_bv 64 18446744073709551608 -> getr R9 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R9 (reg 25) = Z_to_bv 64 (F + 592) ->
  PEAHK2.hbase F M9 s s' sm1 -> PECA.enc_atA RSEGS EE L ar M9 (F + 496) F en1 -> PESKA.sink_atA RSEGS L ar P M9 (F + 432) k1 ->
  L5.u64_at RSEGS M9 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M9 (V2 - 136) F ->
  (forall (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (LK10 : list fframe) (A10 : list (Z * Z)),
      Bv W (PM.vs_own s' ++ PM.vs_own s) M10 model10 LK10 cr9 A10 -> rinvH R R10 (V2 - 160) F 2147450880 -> PESTA.ls_okA RSEGS AD AAD EE g M10 ->
      getr R10 (reg 18) = Z_to_bv 64 (F + 520) -> getr R10 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R10 (reg 22) = Z_to_bv 64 (F + 432) -> getr R10 (reg 23) = Z_to_bv 64 18446744073709551608 -> getr R10 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R10 (reg 25) = Z_to_bv 64 (F + 592) ->
      PEAHK2.hbase F M10 s s' sm1 ->
      L5.u64_at RSEGS M10 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M10 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xa9034 M10 model10) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xa8f3c M9 model9) K.
Proof.
  intros BI RI K0 LS R18 R20 R22 R23 R24 R25 HB0 EA0 KA0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PEAHK2.hf F) by (unfold PEAHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (SPA16 : (V2 - 160) mod 16 = 0) by (clear - V2A; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  set (X := PM.vs_own s' ++ PM.vs_own s) in *. set (EO := PEC.enc_own en1) in *. set (SO := PESK.sink_own k1) in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof B1 as B1x. rewrite <- !app_assoc in B1x.
  assert (FIN9 : In (F, 5, V2 - 160 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  assert (ENB : 0 < PEC.en_k en1 -> EO = [(PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1))] /\ 0 <= PEC.en_b en1 /\ PEC.en_b en1 + PEC.ESZ * PEC.ecap (PEC.en_k en1) <= 2 ^ 64).
  { intros Hk0. assert (E : EO = [(PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1))]) by (subst EO; unfold PEC.enc_own; destruct (PEC.en_k en1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| reflexivity]).
    split; [exact E|]. destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ (PEC.en_b en1) (PEC.ESZ * PEC.ecap (PEC.en_k en1)) B1x ltac:(rewrite E; left; reflexivity)) as (Q0 & _ & _ & _ & _ & Q47 & _). clear - Q0 Q47; lia. }
  assert (SKB : 0 < PESK.sk_c k1 -> SO = [(PESK.sk_b k1, PESK.sk_c k1)] /\ 0 <= PESK.sk_b k1 /\ PESK.sk_b k1 + PESK.sk_c k1 <= 2 ^ 64).
  { intros Hk0. assert (E : SO = [(PESK.sk_b k1, PESK.sk_c k1)]) by (subst SO; unfold PESK.sink_own; destruct (PESK.sk_c k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| reflexivity]).
    split; [exact E|]. destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ (PESK.sk_b k1) (PESK.sk_c k1) B1x ltac:(apply in_or_app; right; apply in_or_app; left; rewrite E; left; reflexivity)) as (Q0 & _ & _ & _ & _ & Q47 & _). clear - Q0 Q47; lia. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK9 cr9 A9 BI)
    as ((VW9 & VIC9 & VSB9 & VUAR9 & VMS9) & VOWN9 & (VFD9 & VFW9 & VFSW9 & VFLC9 & VFLW9) & (FLCc9 & FLV9 & FV9 & SPV9 & FSV9)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H9 := ahid A9 model9) in *. set (MV9 := mrestrict H9 M9) in *.
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  assert (Q5 : L5.writable RSEGS MV9 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW9| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV9 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC9).
  pose proof (PEACHP3.ahnL_conc fx9 R9 MV9 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R9 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD9 | exact VFW9 | exact VFSW9 | exact VFLW9 | exact Q5 | exact Q6 | (unfold PEACHP3.aligned; exact V2A) ]).
  destruct PP as (fx1 & R1 & M1v & MG1 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iC & IQ)).
  set (W1 := fun a => F / 8 + 2147450954 <= a < F / 8 + 2147450954 + 49 \/ V2 - 112 <= a < V2 - 112 + 8).
  assert (WC1 : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar (EO ++ SO ++ X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|Wa]; split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply stack_client; [clear - Wa SLO V2R CLS; lia| clear - Wa; lia].
    - clear - Wa V2R. lia. }
  apply (apiece L ar C HI LYa HIok _ FF' LK9 cr9 A9 M9 model9 fx9 fx1 R9 0xa8f3c R1 0xb140c M1v W1 K B1x B2 iMS MG1).
  { intros a Ha Hna. apply iFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
  { exact WC1. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H9 M1 = M1v) in VIS1.
  rewrite !app_assoc in HH1.
  assert (BI1 : Bv W ((EO ++ SO) ++ X) M1 model1 LK9 cr9 A9).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK9 cr9 A9 M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|Wa]; [right; right| left]; change (ff_bytes 5) with 2048;
      [change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| unfold tocell; clear - Wa CLS; lia]. }
  assert (RI1 : rinvH R R1 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R9 R1 (V2 - 160) F 2147450880 PEACHP3.KS_ahnL RI iKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS1 : PESTA.ls_okA RSEGS AD AAD EE g M1).
  { apply (PEAHK.ls_piece _ M9 M1 W1 FR1); [| exact LS]. intros a Wa. subst W1; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
  assert (PF1 : PEAHK2.pfoot F (V2 - 160) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (OAX1 : forall o k2, F <= o -> o + k2 <= F + 592 -> PEAHK2.oav W1 o k2).
  { intros o k2 H1 H2 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8 FBD V2R SLO FCEIL CLS; lia. }
  pose proof BI1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  pose proof C1 as C1x. rewrite <- !app_assoc in C1x.
  assert (HB1 : PEAHK2.hbase F M1 s s' sm1).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1 FIN9 FHF (V2 - 160) V2 W1 M9 M1 SLOW SHW FR1 PF1 s s' sm1);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX1; clear; lia| apply OAX1; clear; lia| exact HB0]. }
  assert (EA1 : PECA.enc_atA RSEGS EE L ar M1 (F + 496) F en1).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar M9 M1 (F + 496) F en1); [clear - FR; lia| clear - FR; lia| apply (PEAHK.agA_frame M9 M1 W1 (F + 496) 56 FR1); [clear - FR; lia| clear - FR; lia| apply OAX1; clear; lia]| | exact EA0].
    intros Hk0. destruct (ENB Hk0) as (E & Q0 & Q47). split; [exact Q0|]. split; [exact Q47|].
    apply (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x); [rewrite E; left; reflexivity| exact FIN9| exact FHF| exact SLOW| exact SHW| exact FR1| exact PF1]. }
  assert (KA1 : PESKA.sink_atA RSEGS L ar P M1 (F + 432) k1).
  { apply (PECFA.sink_atA_agree RSEGS L ar M9 M1 P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply (PEAHK.agA_frame M9 M1 W1 (F + 432) 24 FR1); [clear - FR; lia| clear - FR; lia| apply OAX1; clear; lia]| | exact KA0].
    intros Hk0. destruct (SKB Hk0) as (E & Q0 & Q47). split; [exact Q0|]. split; [exact Q47|].
    apply (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x); [apply in_or_app; right; apply in_or_app; left; rewrite E; left; reflexivity| exact FIN9| exact FHF| exact SLOW| exact SHW| exact FR1| exact PF1]. }
  assert (FR1st : forall a, V2 - 160 <= a < V2 + cls -> ~ (V2 - 112 <= a < V2 - 104) -> M1 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha Hn. apply FR1; [clear - Ha V2R V2S CLS; lia|]. subst W1; cbn beta. intros X0. clear - Ha Hn X0 FBD V2R. lia. }
  assert (HSTKa1 : L5.u64_at RSEGS M1 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M9 M1 (V2 - 144) (F + 32)); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb1 : L5.u64_at RSEGS M1 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M9 M1 (V2 - 136) F); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M1 model1 LK9 cr9 A9 BI1)
    as ((_ & _ & _ & _ & _) & _ & (VFD1 & _ & _ & _ & _) & (_ & _ & FV1 & _ & _)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FDEF1 : L5.defined M1 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A9 model1) M1 F 2048 FV1)); exact VFD1).
  assert (OSZ1 : shadow_zero M1 (V2 - 160) 20) by (eapply PEAHSK.own_shz; first [exact BI1 | eassumption]).
  assert (TC1 : L5.u64_at RSEGS M1 (V2 - 112) (F + 520)).
  { apply (PEAHK.u64_vis H9 M1 M1v (V2 - 112) _ VV1); [| clear - V2R; lia| clear - V2R; lia| exact iC].
    intros i Hi. replace (V2 - 112 + i) with ((V2 - 160) + (48 + i)) by (clear; lia). apply SPV9. clear - Hi CLS; lia. }
  assert (ASTK1 : astk ar M1 (V2 + cls) 36864) by exact C6.
  assert (TCELL1 : PECDTA.tcell_ok RSEGS ar FF' M1 (V2 - 160) (V2 - 112) (F + 520)).
  { split; [| split; [| split; [| split; [exact TC1| clear - SHI CLS; lia]]]].
    - clear - V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - pose proof ASTK1 as (_ & _ & _ & _ & DSCR & DUP). intros i Hi. replace (V2 - 112 + i) with (V2 + cls - 36864 + (36752 - cls + i)) by (clear; lia). apply DSCR. clear - Hi CLS; lia.
    - apply (PEAHK2.acc_of_shz M1 (V2 - 160) 20 (V2 - 112) 8 OSZ1); [| clear - V2R; lia| clear; lia| clear; lia]. clear - V2A. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold PECDTA.estk_dtor_spec in ESTK.
  apply (ESTK fx1 R1 M1 model1 K _ FF' LK9 A9 cr9 (V2 - 112) (F + 496) F (V2 - 160) 0xa900c en1 C1x C2 K0).
  { eapply PEAHSK.callee_entry; first [exact BI1 | exact RI1 | exact iR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BI1 | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact iR10. }
  { replace (F + 496 + 24) with (F + 520) by (clear; lia). exact TCELL1. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
  { exact (fb_mod8 F 62 FAL). }
  { exact EA1. }
  { intros x Hx. apply in_or_app; left. exact Hx. }
  { exact (proj1 LS1). }
  intros fxv Rv Mv modv LKv Av RPv HPv MRTv INCLKv INCAv AMv HHv.
  change (PMSPA.pm_scr 1) with 14336 in HPv. replace (F + 496 + 24) with (F + 520) in HPv by (clear; lia).
  assert (ER : PECDTA.estk_rest en1 (EO ++ SO ++ X ++ LB) = SO ++ X ++ LB).
  { unfold PECDTA.estk_rest. subst EO. unfold PEC.enc_own. destruct (PEC.en_k en1 =? 0); [reflexivity|]. cbn [app]. apply L5ADHR.lb_remove_head. }
  rewrite ER in HPv, HHv.
  assert (WFIv : PEAHK2.wfi F [(F + 520, 24)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; lia| apply PEAHK2.wfi_nil]).
  assert (WAv : forall o k2, (o + k2 <= F + 520 \/ F + 544 <= o) -> PEAHK2.wapart [(F + 520, 24)] o k2) by (intros o k2 Ho r [<-|[]]; cbn [fst snd]; clear - Ho; lia).
  assert (LSv : PESTA.ls_okA RSEGS AD AAD EE g Mv).
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 [(F + 520, 24)] M1 Mv HPv); [| exact LS1]. apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BIv : Bv W (SO ++ X) Mv modv LKv cr9 Av).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (SO ++ X) (SO ++ X) M1 model1 LK9 cr9 A9 Mv modv LKv cr9 Av 14336 [(F + 520, 24)] BI1);
      [rewrite app_assoc in HPv; exact HPv| rewrite app_assoc in HHv; exact HHv| exact AMv| exact MRTv| exact INCAv| exact INCLKv| lia| clear - CLS; lia| | | intros a X0; exact X0].
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc]. }
  pose proof BIv as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  assert (RIv : rinvH R Rv (V2 - 160) F 2147450880) by exact (rinvH_pres R R1 Rv (V2 - 160) F 2147450880 RI1 RPv).
  assert (V18 : getr Rv (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R1 Rv 18 RPv) by inl; rewrite (iKS 18%nat) by inl; exact R18).
  assert (V20 : getr Rv (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 Rv 20 RPv) by inl; rewrite (iKS 20%nat) by inl; exact R20).
  assert (V22 : getr Rv (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R1 Rv 22 RPv) by inl; rewrite (iKS 22%nat) by inl; exact R22).
  assert (V23 : getr Rv (reg 23) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 Rv 23 RPv) by inl; rewrite (iKS 23%nat) by inl; exact R23).
  assert (V24 : getr Rv (reg 24) = Z_to_bv 64 (F + 1120)) by (rewrite (cs_of_preserved R1 Rv 24 RPv) by inl; rewrite (iKS 24%nat) by inl; exact R24).
  assert (V25 : getr Rv (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R1 Rv 25 RPv) by inl; rewrite (iKS 25%nat) by inl; exact R25).
  assert (FIN1 : In (F, 5, V2 - 160 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  assert (HBv : PEAHK2.hbase F Mv s s' sm1).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact C1x | exact HPv | exact HB1 | exact FHF | exact FIN1 | exact WFIv | (apply WAv; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx)
      | (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx) | lia ]. }
  assert (AGFv : forall o k2, F + 32 <= o -> o + k2 <= F + 2040 -> (o + k2 <= F + 520 \/ F + 544 <= o) -> PMFA.agA M1 Mv o k2).
  { intros o k2 H1 H2 H3. apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 14336 [(F + 520, 24)] M1 Mv (F, 5, V2 - 160 + 32) F o k2 HPv (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFIv| apply WAv; exact H3]. }
  assert (KAv : PESKA.sink_atA RSEGS L ar P Mv (F + 432) k1).
  { apply (PECFA.sink_atA_agree RSEGS L ar M1 Mv P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply AGFv; clear; lia| | exact KA1].
    intros Hk0. destruct (SKB Hk0) as (E & Q0 & Q47). split; [exact Q0|]. split; [exact Q47|].
    eapply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 14336 [(F + 520, 24)] M1 Mv C1x); [apply in_or_app; right; apply in_or_app; left; rewrite E; left; reflexivity| exact FIN1| exact FHF| exact HPv| apply in_or_app; left; rewrite E; left; reflexivity| exact WFIv]. }
  assert (AGstkv : forall a, V2 - 160 <= a < V2 + cls -> Mv (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HPv a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKav : L5.u64_at RSEGS Mv (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M1 Mv (V2 - 144) (F + 32)); [intros i Hi; apply AGstkv; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa1]. }
  assert (HSTKbv : L5.u64_at RSEGS Mv (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M1 Mv (V2 - 136) F); [intros i Hi; apply AGstkv; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb1]. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mv modv LKv cr9 Av BIv)
    as ((VWv & VICv & VSBv & VUARv & VMSv) & VOWNv & (VFDv & VFWv & VFSWv & VFLCv & VFLWv) & (FLCcv & FLVv & FVv & SPVv & FSVv)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (Hv := ahid Av modv) in *. set (MVv := mrestrict Hv Mv) in *.
  pose proof RIv as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (Q5v : L5.writable RSEGS MVv (V2 - 160) 160) by (eapply L5.writable_sub; [exact VWv| clear; lia| clear - CLS; lia]).
  assert (Q6v : L5.u64_at RSEGS MVv (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLCv).
  pose proof (PEACHP3.ahnM_conc fxv Rv MVv (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rv 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFDv | exact VFWv | exact VFSWv | exact VFLWv | exact Q5v | exact Q6v | (unfold PEACHP3.aligned; exact V2A) ]).
  destruct PP as (fx2 & R2' & M2v & MG2 & mFR & mFZ & (mMS & mKS & mR1 & mR10 & mC & MQ)).
  set (W2 := fun a => F / 8 + 2147450942 <= a < F / 8 + 2147450942 + 7 \/ V2 - 112 <= a < V2 - 112 + 8).
  assert (WC2 : forall a, 0 <= a < 2 ^ 64 -> W2 a -> aclientw L ar (SO ++ X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W2; cbn beta in Wa. destruct Wa as [Wa|Wa]; split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply stack_client; [clear - Wa SLO V2R CLS; lia| clear - Wa; lia].
    - clear - Wa V2R. lia. }
  pose proof D1 as D1x. rewrite <- !app_assoc in D1x.
  apply (apiece L ar C HI LYa HIok _ FF' LKv cr9 Av Mv modv fxv fx2 Rv 0xa900c R2' 0xaa5cc M2v W2 K D1x D2 mMS MG2).
  { intros a Ha Hna. apply mFZ; [exact Ha|..]; intros X0; apply Hna; subst W2; cbn beta; clear - X0; lia. }
  { exact WC2. }
  intros Mm modm HHm AMm MRTm HIDm VISm MGMm FRm VVm. change (mrestrict Hv Mm = M2v) in VISm.
  rewrite !app_assoc in HHm.
  assert (BIm : Bv W (SO ++ X) Mm modm LKv cr9 Av).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mv modv LKv cr9 Av Mm modm W2 BIv HHm AMm MRTm MGMm FRm).
    intros a Wa. subst W2; cbn beta in Wa. destruct Wa as [Wa|Wa]; [right; right| left]; change (ff_bytes 5) with 2048;
      [change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| unfold tocell; clear - Wa CLS; lia]. }
  assert (RIm : rinvH R R2' (V2 - 160) F 2147450880) by (apply (rinvH_ks R Rv R2' (V2 - 160) F 2147450880 PEACHP3.KS_ahnM RIv mKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LSm : PESTA.ls_okA RSEGS AD AAD EE g Mm).
  { apply (PEAHK.ls_piece _ Mv Mm W2 FRm); [| exact LSv]. intros a Wa. subst W2; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
  assert (PF2 : PEAHK2.pfoot F (V2 - 160) V2 W2) by (intros a Wa; subst W2; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (OAX2 : forall o k2, F <= o -> o + k2 <= F + 496 -> PEAHK2.oav W2 o k2).
  { intros o k2 H1 H2 x Hx. subst W2; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8 FBD V2R SLO FCEIL CLS; lia. }
  pose proof BIm as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  pose proof E1 as E1x. rewrite <- !app_assoc in E1x.
  assert (FINv : In (F, 5, V2 - 160 + 32) (FF' ++ LKv)) by (apply in_or_app; left; left; reflexivity).
  assert (HBm : PEAHK2.hbase F Mm s s' sm1).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) D1 FINv FHF (V2 - 160) V2 W2 Mv Mm SLOW SHW FRm PF2 s s' sm1);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX2; clear; lia| apply OAX2; clear; lia| exact HBv]. }
  assert (KAm : PESKA.sink_atA RSEGS L ar P Mm (F + 432) k1).
  { apply (PECFA.sink_atA_agree RSEGS L ar Mv Mm P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply (PEAHK.agA_frame Mv Mm W2 (F + 432) 24 FRm); [clear - FR; lia| clear - FR; lia| apply OAX2; clear; lia]| | exact KAv].
    intros Hk0. destruct (SKB Hk0) as (E & Q0 & Q47). split; [exact Q0|]. split; [exact Q47|].
    apply (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W2 Mv Mm D1x); [apply in_or_app; left; rewrite E; left; reflexivity| exact FINv| exact FHF| exact SLOW| exact SHW| exact FRm| exact PF2]. }
  assert (FRmst : forall a, V2 - 160 <= a < V2 + cls -> ~ (V2 - 112 <= a < V2 - 104) -> Mm (Z_to_bv 64 a) = Mv (Z_to_bv 64 a)).
  { intros a Ha Hn. apply FRm; [clear - Ha V2R V2S CLS; lia|]. subst W2; cbn beta. intros X0. clear - Ha Hn X0 FBD V2R. lia. }
  assert (HSTKam : L5.u64_at RSEGS Mm (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS Mv Mm (V2 - 144) (F + 32)); [intros i Hi; apply FRmst; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKav]. }
  assert (HSTKbm : L5.u64_at RSEGS Mm (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS Mv Mm (V2 - 136) F); [intros i Hi; apply FRmst; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKbv]. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mm modm LKv cr9 Av BIm)
    as ((_ & _ & _ & _ & _) & _ & (VFDm & _ & _ & _ & _) & (_ & _ & FVm & _ & _)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (OSZm : shadow_zero Mm (V2 - 160) 20) by (eapply PEAHSK.own_shz; first [exact BIm | eassumption]).
  assert (TCm : L5.u64_at RSEGS Mm (V2 - 112) (F + 432)).
  { apply (PEAHK.u64_vis Hv Mm M2v (V2 - 112) _ VVm); [| clear - V2R; lia| clear - V2R; lia| exact mC].
    intros i Hi. replace (V2 - 112 + i) with ((V2 - 160) + (48 + i)) by (clear; lia). apply SPVv. clear - Hi CLS; lia. }
  assert (TCELLm : PECDTA.tcell_ok RSEGS ar FF' Mm (V2 - 160) (V2 - 112) (F + 432)).
  { split; [| split; [| split; [| split; [exact TCm| clear - SHI CLS; lia]]]].
    - clear - V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - pose proof E6 as (_ & _ & _ & _ & DSCR & DUP). intros i Hi. replace (V2 - 112 + i) with (V2 + cls - 36864 + (36752 - cls + i)) by (clear; lia). apply DSCR. clear - Hi CLS; lia.
    - apply (PEAHK2.acc_of_shz Mm (V2 - 160) 20 (V2 - 112) 8 OSZm); [| clear - V2R; lia| clear; lia| clear; lia]. clear - V2A. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold PECDTA.sink_dtor_spec in SNK.
  apply (SNK fx2 R2' Mm modm K _ FF' LKv Av cr9 (V2 - 112) (F + 432) (V2 - 160) 0xa9034 k1 E1x E2 K0).
  { eapply PEAHSK.callee_entry; first [exact BIm | exact RIm | exact mR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BIm | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact mR10. }
  { exact TCELLm. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
  { exact (fb_mod8 F 54 FAL). }
  { exact KAm. }
  { intros x Hx. apply in_or_app; left. exact Hx. }
  intros fxw Rw Mw modw LKw Aw RPw HPw MRTw INCLKw INCAw AMw HHw.
  change (PMSPA.pm_scr 1) with 14336 in HPw.
  assert (SR : PECDTA.sink_rest k1 (SO ++ X ++ LB) = X ++ LB).
  { unfold PECDTA.sink_rest. subst SO. unfold PESK.sink_own. destruct (PESK.sk_c k1 =? 0); [reflexivity|]. cbn [app]. apply L5ADHR.lb_remove_head. }
  rewrite SR in HPw, HHw.
  assert (WFIw : PEAHK2.wfi F [(F + 432, 24)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; lia| apply PEAHK2.wfi_nil]).
  assert (WAw : forall o k2, (o + k2 <= F + 432 \/ F + 456 <= o) -> PEAHK2.wapart [(F + 432, 24)] o k2) by (intros o k2 Ho r [<-|[]]; cbn [fst snd]; clear - Ho; lia).
  assert (LSw : PESTA.ls_okA RSEGS AD AAD EE g Mw).
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 [(F + 432, 24)] Mm Mw HPw); [| exact LSm]. apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BIw : Bv W X Mw modw LKw cr9 Aw).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ X X Mm modm LKv cr9 Av Mw modw LKw cr9 Aw 14336 [(F + 432, 24)] BIm HPw HHw AMw MRTw INCAw INCLKw);
      [lia| clear - CLS; lia| | | intros a X0; exact X0].
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc]. }
  assert (RIw : rinvH R Rw (V2 - 160) F 2147450880) by exact (rinvH_pres R R2' Rw (V2 - 160) F 2147450880 RIm RPw).
  assert (FINm : In (F, 5, V2 - 160 + 32) (FF' ++ LKv)) by (apply in_or_app; left; left; reflexivity).
  assert (AGstkw : forall a, V2 - 160 <= a < V2 + cls -> Mw (Z_to_bv 64 a) = Mm (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HPw a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  apply (KONT fxw Rw Mw modw LKw Aw BIw RIw LSw).
  - rewrite (cs_of_preserved R2' Rw 18 RPw) by inl. rewrite (mKS 18%nat) by inl. exact V18.
  - rewrite (cs_of_preserved R2' Rw 20 RPw) by inl. rewrite (mKS 20%nat) by inl. exact V20.
  - rewrite (cs_of_preserved R2' Rw 22 RPw) by inl. rewrite (mKS 22%nat) by inl. exact V22.
  - rewrite (cs_of_preserved R2' Rw 23 RPw) by inl. rewrite (mKS 23%nat) by inl. exact V23.
  - rewrite (cs_of_preserved R2' Rw 24 RPw) by inl. rewrite (mKS 24%nat) by inl. exact V24.
  - rewrite (cs_of_preserved R2' Rw 25 RPw) by inl. rewrite (mKS 25%nat) by inl. exact V25.
  - eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact E1x | exact HPw | exact HBm | exact FHF | exact FINm | exact WFIw | (apply WAw; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx)
      | (intros x Hx; apply in_or_app; left; exact Hx) | lia ].
  - apply (L5C.u64_at_agree RSEGS Mm Mw (V2 - 144) (F + 32)); [intros i Hi; apply AGstkw; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKam].
  - apply (L5C.u64_at_agree RSEGS Mm Mw (V2 - 136) F); [intros i Hi; apply AGstkw; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKbm].
Qed.
End Stage.
End SCFG_1.
End PEACH9.
