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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCFrameA PeCSpecs PeCSpecsA PeCSpecsAa PeACHarnessStmts PeACHarnessKit PeACHarnessKit2 PeACHarnessSK PeACHarnessKit3 PeACHarnessKit4 PeACHarnessP3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEACH8.
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
Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma stage8 (VEC : PMSPA.vec_dtor_spec RSEGS AD L ar HI) (OPD : PMSPA.opdel_spec RSEGS AD L ar HI) (SRC : PMSPA.src_dtor_spec RSEGS AD L ar HI)
      (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (K : TSet)
      (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z)) (s s' : PM.vstr) (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (nn : nat) (g : PMST.st) :
  Bv W (PEC.owned s1 en1 k1 ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 (V2 - 160) F 2147450880 -> K [] -> PESTA.ls_okA RSEGS AD AAD EE g M9 ->
  getr R9 (reg 18) = Z_to_bv 64 (F + 520) -> getr R9 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R9 (reg 22) = Z_to_bv 64 (F + 432) -> getr R9 (reg 23) = Z_to_bv 64 (F + 496) -> getr R9 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R9 (reg 25) = Z_to_bv 64 (F + 592) ->
  PEAHK2.hbase F M9 s s' sm1 -> PEACH.hparsed L ar P payload F M9 s1 s' sm1 en1 k1 e1 nn -> shadow_zero M9 (F + 592) 49 ->
  L5.u64_at RSEGS M9 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M9 (V2 - 136) F ->
  (forall (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (LK10 : list fframe) (A10 : list (Z * Z)),
      Bv W ((PEC.enc_own en1 ++ PESK.sink_own k1) ++ PM.vs_own s' ++ PM.vs_own s) M10 model10 LK10 cr9 A10 -> rinvH R R10 (V2 - 160) F 2147450880 -> PESTA.ls_okA RSEGS AD AAD EE g M10 ->
      getr R10 (reg 18) = Z_to_bv 64 (F + 520) -> getr R10 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R10 (reg 22) = Z_to_bv 64 (F + 432) -> getr R10 (reg 23) = Z_to_bv 64 18446744073709551608 -> getr R10 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R10 (reg 25) = Z_to_bv 64 (F + 592) ->
      PEAHK2.hbase F M10 s s' sm1 -> PECA.enc_atA RSEGS EE L ar M10 (F + 496) F en1 -> PESKA.sink_atA RSEGS L ar P M10 (F + 432) k1 ->
      L5.u64_at RSEGS M10 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M10 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xa8f3c M10 model10) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xa8ef0 M9 model9) K.
Proof.
  intros BI RI K0 LS R18 R20 R22 R23 R24 R25 HB0 HPD SZP0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
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
  assert (E592 : (F + 592) / 8 = F / 8 + 74) by (clear - FM8; lia).
  assert (SPA16 : (V2 - 160) mod 16 = 0) by (clear - V2A; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FIN9 : In (F, 5, V2 - 160 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  pose proof HPD as (PA9 & IA9 & EA9 & KA9 & BASE9 & ERR9 & DEF9 & HALT & SINK9).
  pose proof PA9 as (_ & PDEF & _ & _ & _ & _ & _ & _ & NUL9 & SRCF9 & _ & _ & _ & TB9 & VEC9 & _).
  pose proof HB0 as (VS9 & IS9 & VI9).
  set (src := PM.p_src s1) in *. set (tb := PM.p_tb s1) in *. set (b := PM.p_b s1) in *. set (kk := PM.p_k s1) in *. set (stk := PM.p_stk s1) in *.
  set (REST := PEC.enc_own en1 ++ PESK.sink_own k1) in *. set (X := PM.vs_own s' ++ PM.vs_own s) in *.
  assert (EOWN : PEC.owned s1 en1 k1 ++ X = ([(PM.sr_qc src, PM.CHUNK)] ++ [(b, 32 * 2 ^ kk)] ++ PM.vs_own tb) ++ REST ++ X).
  { unfold PEC.owned, PM.parser_own, PM.src_own, PM.vec_own, REST. subst src tb b kk. rewrite <- !app_assoc. reflexivity. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK9 cr9 A9 BI)
    as ((VW9 & VIC9 & VSB9 & VUAR9 & VMS9) & VOWN9 & (VFD9 & VFW9 & VFSW9 & VFLC9 & VFLW9) & (FLCc9 & FLV9 & FV9 & SPV9 & FSV9)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H9 := ahid A9 model9) in *. set (MV9 := mrestrict H9 M9) in *.
  assert (FDEF9 : L5.defined M9 F 2048) by (apply (proj1 (L5A.defined_vis H9 M9 F 2048 FV9)); exact VFD9).
  assert (Q5 : L5.writable RSEGS MV9 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW9| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV9 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC9).
  pose proof (PEACHP3.ahnI_conc fx9 R9 MV9 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R9 1 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD9 | exact VFW9 | exact VFSW9 | exact VFLW9 | exact Q5 | exact Q6 | (unfold PEACHP3.aligned; exact V2A) ]).
  destruct PP as (fx1 & R1 & M1v & MG1 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR23 & iC & iV & IQ)).
  set (W1 := fun a => F / 8 + 2147451020 <= a < F / 8 + 2147451020 + 2 \/ F + 592 <= a < F + 592 + 8 \/ V2 - 112 <= a < V2 - 112 + 8).
  assert (WC1 : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar (PEC.owned s1 en1 k1 ++ X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 6914048)).
  { intros a Ha Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]]; split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR; lia.
    - apply stack_client; [clear - Wa SLO V2R CLS; lia| clear - Wa; lia].
    - clear - Wa V2R. lia. }
  pose proof B1 as B1x. rewrite <- app_assoc in B1x.
  apply (apiece L ar C HI LYa HIok _ FF' LK9 cr9 A9 M9 model9 fx9 fx1 R9 0xa8ef0 R1 0xa9ec0 M1v W1 K B1x B2 iMS MG1).
  { intros a Ha Hna. apply iFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
  { exact WC1. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H9 M1 = M1v) in VIS1.
  rewrite app_assoc in HH1.
  assert (BI1 : Bv W (PEC.owned s1 en1 k1 ++ X) M1 model1 LK9 cr9 A9).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M9 model9 LK9 cr9 A9 M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]]; [right; right| right; left| left]; change (ff_bytes 5) with 2048;
      [change (2048 / 8) with 256; unfold HeapIfaceA.SB in *; clear - Wa; lia| clear - Wa; lia| unfold tocell; clear - Wa CLS; lia]. }
  assert (RI1 : rinvH R R1 (V2 - 160) F 2147450880) by (apply (rinvH_ks R R9 R1 (V2 - 160) F 2147450880 PEACHP3.KS_ahnI RI iKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
  assert (LS1 : PESTA.ls_okA RSEGS AD AAD EE g M1).
  { apply (PEAHK.ls_piece _ M9 M1 W1 FR1); [| exact LS]. intros a Wa. subst W1; cbn beta in Wa. unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
  assert (PF1 : PEAHK2.pfoot F (V2 - 160) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (OAX1 : forall o k2, (F <= o /\ o + k2 <= F + 592) \/ (F + 600 <= o /\ o + k2 <= F + 1120) -> PEAHK2.oav W1 o k2).
  { intros o k2 H12 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8 FBD V2R SLO FCEIL CLS; lia. }
  pose proof BI1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (HB1 : PEAHK2.hbase F M1 s s' sm1).
  { apply (PEAHK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1 FIN9 FHF (V2 - 160) V2 W1 M9 M1 SLOW SHW FR1 PF1 s s' sm1);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX1; clear; lia| apply OAX1; clear; lia| exact HB0]. }
  assert (FR1lo : forall a, 0 <= a < 2 ^ 64 -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) -> ~ (F + 592 <= a < F + 600) -> ~ (V2 - 112 <= a < V2 - 104) -> M1 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha Hr Hn1 Hn2. apply FR1; [exact Ha|]. subst W1; cbn beta. intros X0. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hr. clear - Hr Hn1 Hn2 X0 FBD. lia. }
  assert (FAPP : forall a, F <= a < F + 2048 -> a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) by (intros a Ha; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - Ha FBIG; lia).
  assert (AGF1 : forall o k2, F + 600 <= o -> o + k2 <= F + 1120 -> PMFA.agA M9 M1 o k2).
  { intros o k2 H1 H2. apply (PEAHK.agA_frame M9 M1 W1 o k2 FR1); [clear - H1 FR; lia| clear - H2 FR; lia|]. apply OAX1. right. clear - H1 H2; lia. }

  assert (ENB : 0 < PEC.en_k en1 -> In (PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1)) (PEC.owned s1 en1 k1 ++ X ++ LB) /\ 0 <= PEC.en_b en1 /\ PEC.en_b en1 + PEC.ESZ * PEC.ecap (PEC.en_k en1) <= 2 ^ 64).
  { intros Hk0. assert (IN : In (PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1)) (PEC.owned s1 en1 k1 ++ X ++ LB)).
    { apply in_or_app; left. unfold PEC.owned. apply in_or_app; right. apply in_or_app; left. unfold PEC.enc_own. destruct (PEC.en_k en1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]. }
    split; [exact IN|]. destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ B1x IN) as (Q0 & _ & _ & _ & _ & Q47 & _). clear - Q0 Q47; lia. }
  assert (SKB : 0 < PESK.sk_c k1 -> In (PESK.sk_b k1, PESK.sk_c k1) (PEC.owned s1 en1 k1 ++ X ++ LB) /\ 0 <= PESK.sk_b k1 /\ PESK.sk_b k1 + PESK.sk_c k1 <= 2 ^ 64).
  { intros Hk0. assert (IN : In (PESK.sk_b k1, PESK.sk_c k1) (PEC.owned s1 en1 k1 ++ X ++ LB)).
    { apply in_or_app; left. unfold PEC.owned. apply in_or_app; right. apply in_or_app; right. unfold PESK.sink_own. destruct (PESK.sk_c k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]. }
    split; [exact IN|]. destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ B1x IN) as (Q0 & _ & _ & _ & _ & Q47 & _). clear - Q0 Q47; lia. }
  assert (EA1 : PECA.enc_atA RSEGS EE L ar M1 (F + 496) F en1).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar M9 M1 (F + 496) F en1); [clear - FR; lia| clear - FR; lia| apply (PEAHK.agA_frame M9 M1 W1 (F + 496) 56 FR1); [clear - FR; lia| clear - FR; lia| apply OAX1; left; clear; lia]| | exact EA9].
    intros Hk0. destruct (ENB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
    exact (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x IN FIN9 FHF SLOW SHW FR1 PF1). }
  assert (KA1 : PESKA.sink_atA RSEGS L ar P M1 (F + 432) k1).
  { apply (PECFA.sink_atA_agree RSEGS L ar M9 M1 P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply (PEAHK.agA_frame M9 M1 W1 (F + 432) 24 FR1); [clear - FR; lia| clear - FR; lia| apply OAX1; left; clear; lia]| | exact KA9].
    intros Hk0. destruct (SKB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
    exact (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x IN FIN9 FHF SLOW SHW FR1 PF1). }

  pose proof C1 as C1x. rewrite <- app_assoc in C1x.
  assert (INB : In (b, 32 * 2 ^ kk) (PEC.owned s1 en1 k1 ++ X ++ LB)).
  { apply in_or_app; left. unfold PEC.owned, PM.parser_own, PM.vec_own. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
  assert (INQ : In (PM.sr_qc src, PM.CHUNK) (PEC.owned s1 en1 k1 ++ X ++ LB)).
  { apply in_or_app; left. unfold PEC.owned, PM.parser_own, PM.src_own. apply in_or_app; left. apply in_or_app; left. left. reflexivity. }
  destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ B1x INB) as (B0 & _ & _ & _ & BSH & B47 & _).
  destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ B1x INQ) as (Qc0 & _ & _ & _ & QSH & Q47 & _).
  assert (VEC1 : PM.vec_at RSEGS PMSPA.accA PMSPA.annA M1 (F + 952) b kk stk).
  { apply (PMFA.vec_at_agreeA RSEGS M9 M1 (F + 952) b kk stk); [clear - FR; lia| clear - FR; lia| clear - B0; lia| clear - B47; lia| exact (proj1 (AGF1 (F + 952) 24 ltac:(clear; lia) ltac:(clear; lia)))| | replace (F + 952) with (F + 592 + 360) by (clear; lia); exact VEC9].
    exact (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x INB FIN9 FHF SLOW SHW FR1 PF1). }
  assert (SRCF1 : PM.src_fields_at RSEGS PMSPA.accA M1 (F + 616) (F + 96) (F + 96 + 16) src).
  { apply (PMFA.src_fields_at_agreeA RSEGS M9 M1 (F + 616) (F + 96) (F + 96 + 16) src); [clear - FR; lia| clear - FR; lia| clear - Qc0; lia| clear - Q47; lia| apply AGF1; clear; lia| | replace (F + 616) with (F + 592 + 24) by (clear; lia); exact SRCF9].
    exact (PEAHK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W1 M9 M1 B1x INQ FIN9 FHF SLOW SHW FR1 PF1). }
  assert (NUL1 : PM.nullis_at RSEGS AD PMSPA.accA M1 (F + 624)).
  { apply (PMFA.nullis_at_agreeA RSEGS AD M9 M1 (F + 624)); [clear - FR; lia| clear - FR; lia| apply AGF1; clear; lia| replace (F + 624) with (F + 592 + 32) by (clear; lia); exact NUL9]. }
  assert (TB1 : PM.vstr_at RSEGS PMSPA.accA M1 (F + 928) tb).
  { apply (PEAHK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1x FIN9 FHF (V2 - 160) V2 W1 M9 M1 SLOW SHW FR1 PF1 (F + 928) tb);
      [| clear - FR; lia| clear - FR; lia| apply OAX1; right; clear; lia| replace (F + 928) with (F + 592 + 336) by (clear; lia); exact TB9].
    intros x Hx. apply in_or_app; left. unfold PEC.owned, PM.parser_own. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. exact Hx. }
  assert (SZP1 : shadow_zero M1 (F + 592) 49).
  { apply (PEAHK2.shz_frame M9 M1 W1 (F + 592) 49 FR1); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZP0].
    intros j Hj X0. subst W1; cbn beta in X0. unfold HeapIfaceA.S, HeapIfaceA.SB in X0. rewrite E592 in X0. clear - X0 Hj FBD FR FBIG V2R. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia. }
  assert (HSTKa1 : L5.u64_at RSEGS M1 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M9 M1 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa].
    intros i Hi; apply FR1lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia| clear - Hi; lia]. }
  assert (HSTKb1 : L5.u64_at RSEGS M1 (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M9 M1 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb].
    intros i Hi; apply FR1lo; [clear - Hi V2R; lia| unfold BIGSHADOW_HI; clear - Hi V2R; lia| clear - Hi Q3 CLS; lia| clear - Hi; lia]. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M1 model1 LK9 cr9 A9 BI1)
    as ((_ & _ & _ & _ & _) & _ & (VFD1 & _ & _ & _ & _) & (_ & _ & FV1 & SPV1 & _)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FDEF1 : L5.defined M1 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A9 model1) M1 F 2048 FV1)); exact VFD1).
  pose proof RI1 as (Y2 & Y3 & Y4 & Y8 & Y9 & Y19 & Y21 & Y26 & Y27).
  assert (OSZ1 : shadow_zero M1 (V2 - 160) 20) by (eapply PEAHSK.own_shz; first [exact BI1 | eassumption]).
  assert (TC1 : L5.u64_at RSEGS M1 (V2 - 112) (F + 952)).
  { apply (PEAHK.u64_vis H9 M1 M1v (V2 - 112) _ VV1); [| clear - V2R; lia| clear - V2R; lia| exact iC].
    intros i Hi. replace (V2 - 112 + i) with ((V2 - 160) + (48 + i)) by (clear; lia). apply SPV9. clear - Hi CLS; lia. }
  unfold PMSPA.vec_dtor_spec in VEC. cbn [pa_vec_dtor PeCLayoutA.CADDR_A] in VEC.
  apply (VEC fx1 R1 M1 model1 K _ FF' LK9 A9 cr9 (V2 - 112) (F + 952) b kk (V2 - 160) 0xa8f18 stk C1x C2 K0).
  { eapply PEAHSK.callee_entry; first [exact BI1 | exact RI1 | exact iR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEAHSK.callee_room; first [exact BI1 | eassumption | lia]. }
  { eapply PEAHSK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact iR10. }
  { clear; lia. }
  { clear - SHI CLS; lia. }
  { clear - V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { apply (PEAHK2.acc_of_shz M1 (V2 - 160) 20 (V2 - 112) 8 OSZ1); [| clear - V2R; lia| clear; lia| clear; lia].
    clear - SPA16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { exact TC1. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
  { exact (fb_mod8 F 119 FAL). }
  { apply (L5.defined_sub M1 F 2048 (F + 952) 24 FDEF1); clear; lia. }
  { apply (PEAHK2.acc_of_shz M1 (F + 592) 49 (F + 952) 24 SZP1); [exact (fb_mod8 F 74 FAL)| clear - FR; lia| clear; lia| clear; lia]. }
  { exact VEC1. }
  { exact INB. }
  intros fxv Rv Mv modv LKv Av RPv HPv MRTv INCLKv INCAv AMv HHv.
  change (PMSPA.pm_scr 1) with 14336 in HPv.

  set (LBv := ([(PM.sr_qc src, PM.CHUNK)] ++ PM.vs_own tb) ++ REST ++ X).
  assert (ELB : lb_remove b (PEC.owned s1 en1 k1 ++ X ++ LB) = LBv ++ LB).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1x) as AW.
    assert (ND : NoDup (map fst (PEC.owned s1 en1 k1 ++ X ++ LB))) by (decompose [and] AW; assumption).
    rewrite (app_assoc (PEC.owned s1 en1 k1) X LB) in ND |- *. rewrite EOWN in ND |- *. subst LBv.
    rewrite <- !app_assoc in ND |- *. cbn [app] in ND |- *.
    change ((PM.sr_qc src, PM.CHUNK) :: (b, 32 * 2 ^ kk) :: PM.vs_own tb ++ REST ++ X ++ LB) with ([(PM.sr_qc src, PM.CHUNK)] ++ (b, 32 * 2 ^ kk) :: (PM.vs_own tb ++ REST ++ X ++ LB)) in ND |- *.
    rewrite (PEAHK3.lb_remove_mid b (32 * 2 ^ kk) [(PM.sr_qc src, PM.CHUNK)] (PM.vs_own tb ++ REST ++ X ++ LB) ND). cbn [app]. rewrite <- ?app_assoc. reflexivity. }
  rewrite ELB in HPv, HHv.
  assert (WFIv : PEAHK2.wfi F [(F + 952, 24)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; lia| apply PEAHK2.wfi_nil]).
  assert (LSv : PESTA.ls_okA RSEGS AD AAD EE g Mv).
  { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 [(F + 952, 24)] M1 Mv HPv); [| exact LS1]. apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
  assert (BIv : Bv W LBv Mv modv LKv cr9 Av).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ LBv LBv M1 model1 LK9 cr9 A9 Mv modv LKv cr9 Av 14336 [(F + 952, 24)] BI1 HPv HHv AMv MRTv INCAv INCLKv); [lia| clear - CLS; lia| | | intros a X0; exact X0].
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc]. }
  pose proof BIv as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  assert (RIv : rinvH R Rv (V2 - 160) F 2147450880) by exact (rinvH_pres R R1 Rv (V2 - 160) F 2147450880 RI1 RPv).
  assert (V18 : getr Rv (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R1 Rv 18 RPv) by inl; rewrite (iKS 18%nat) by inl; exact R18).
  assert (V20 : getr Rv (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 Rv 20 RPv) by inl; rewrite (iKS 20%nat) by inl; exact R20).
  assert (V22 : getr Rv (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R1 Rv 22 RPv) by inl; rewrite (iKS 22%nat) by inl; exact R22).
  assert (V23 : getr Rv (reg 23) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R1 Rv 23 RPv) by inl; exact iR23).
  assert (V24 : getr Rv (reg 24) = Z_to_bv 64 (F + 1120)) by (rewrite (cs_of_preserved R1 Rv 24 RPv) by inl; rewrite (iKS 24%nat) by inl; exact R24).
  assert (V25 : getr Rv (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R1 Rv 25 RPv) by inl; rewrite (iKS 25%nat) by inl; exact R25).
  assert (FIN1 : In (F, 5, V2 - 160 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  assert (WAv : forall o k2, (o + k2 <= F + 952 \/ F + 976 <= o) -> PEAHK2.wapart [(F + 952, 24)] o k2) by (intros o k2 Ho r [<-|[]]; cbn [fst snd]; clear - Ho; lia).

  assert (INown : forall x, In x REST \/ In x X -> In x (LBv ++ LB)).
  { intros x Hx. subst LBv. apply in_or_app; left. apply in_or_app; right. apply in_or_app. exact Hx. }
  assert (HBv : PEAHK2.hbase F Mv s s' sm1).
  { eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact C1x | exact HPv | exact HB1 | exact FHF | exact FIN1 | exact WFIv | (apply WAv; lia)
      | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply INown; right; exact Hx) | lia ]. }
  assert (AGFv : forall o k2, F + 32 <= o -> o + k2 <= F + 2040 -> (o + k2 <= F + 952 \/ F + 976 <= o) -> PMFA.agA M1 Mv o k2).
  { intros o k2 H1 H2 H3. apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 14336 [(F + 952, 24)] M1 Mv (F, 5, V2 - 160 + 32) F o k2 HPv (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFIv| apply WAv; exact H3]. }
  assert (EAv : PECA.enc_atA RSEGS EE L ar Mv (F + 496) F en1).
  { apply (PECFA.enc_atA_agree RSEGS EE L ar M1 Mv (F + 496) F en1); [clear - FR; lia| clear - FR; lia| apply AGFv; clear; lia| | exact EA1].
    intros Hk0. destruct (ENB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
    apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 14336 [(F + 952, 24)] M1 Mv C1x IN FIN1 FHF HPv); [| exact WFIv].
    apply INown. left. subst REST. apply in_or_app; left. unfold PEC.enc_own. destruct (PEC.en_k en1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]. }
  assert (KAv : PESKA.sink_atA RSEGS L ar P Mv (F + 432) k1).
  { apply (PECFA.sink_atA_agree RSEGS L ar M1 Mv P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply AGFv; clear; lia| | exact KA1].
    intros Hk0. destruct (SKB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
    apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 14336 [(F + 952, 24)] M1 Mv C1x IN FIN1 FHF HPv); [| exact WFIv].
    apply INown. left. subst REST. apply in_or_app; right. unfold PESK.sink_own. destruct (PESK.sk_c k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]. }
  assert (INQv : In (PM.sr_qc src, PM.CHUNK) (LBv ++ LB)) by (subst LBv; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
  assert (SRCFv : PM.src_fields_at RSEGS PMSPA.accA Mv (F + 616) (F + 96) (F + 96 + 16) src).
  { apply (PMFA.src_fields_at_agreeA RSEGS M1 Mv (F + 616) (F + 96) (F + 96 + 16) src); [clear - FR; lia| clear - FR; lia| clear - Qc0; lia| clear - Q47; lia| apply AGFv; clear; lia| | exact SRCF1].
    apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 14336 [(F + 952, 24)] M1 Mv C1x INQ FIN1 FHF HPv INQv WFIv). }
  assert (NULv : PM.nullis_at RSEGS AD PMSPA.accA Mv (F + 624)).
  { apply (PMFA.nullis_at_agreeA RSEGS AD M1 Mv (F + 624)); [clear - FR; lia| clear - FR; lia| apply AGFv; clear; lia| exact NUL1]. }
  assert (TBv : PM.vstr_at RSEGS PMSPA.accA Mv (F + 928) tb).
  { eapply PEAHK2.vstr_keep_callee; first [ exact LY | exact HIok | exact C1x | exact HPv | exact TB1 | exact FHF | exact FIN1 | exact WFIv | (apply WAv; lia)
      | (left; reflexivity) | (split; reflexivity)
      | (intros x Hx; apply in_or_app; left; unfold PEC.owned, PM.parser_own; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx)
      | (intros x Hx; subst LBv; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; exact Hx) | lia ]. }
  assert (AGstkv : forall a, V2 - 160 <= a < V2 + cls -> Mv (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HPv a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKav : L5.u64_at RSEGS Mv (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M1 Mv (V2 - 144) (F + 32)); [intros i Hi; apply AGstkv; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa1]. }
  assert (HSTKbv : L5.u64_at RSEGS Mv (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M1 Mv (V2 - 136) F); [intros i Hi; apply AGstkv; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb1]. }

  assert (TAIL : forall (fxk : FPState) Rk Mk modk LKk Ak,
    L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5 W ((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) Mk modk LKk cr9 Ak ->
    rinvH R Rk (V2 - 160) F 2147450880 -> PESTA.ls_okA RSEGS AD AAD EE g Mk ->
    getr Rk (reg 18) = Z_to_bv 64 (F + 520) -> getr Rk (reg 20) = Z_to_bv 64 18446744073709551608 ->
    getr Rk (reg 22) = Z_to_bv 64 (F + 432) -> getr Rk (reg 23) = Z_to_bv 64 18446744073709551608 -> getr Rk (reg 24) = Z_to_bv 64 (F + 1120) -> getr Rk (reg 25) = Z_to_bv 64 (F + 592) ->
    PEAHK2.hbase F Mk s s' sm1 -> PECA.enc_atA RSEGS EE L ar Mk (F + 496) F en1 -> PESKA.sink_atA RSEGS L ar P Mk (F + 432) k1 ->
    PM.src_fields_at RSEGS PMSPA.accA Mk (F + 616) (F + 96) (F + 96 + 16) src -> PM.nullis_at RSEGS AD PMSPA.accA Mk (F + 624) ->
    L5.u64_at RSEGS Mk (V2 - 144) (F + 32) -> L5.u64_at RSEGS Mk (V2 - 136) F ->
    srealizes RSEGS SCFG (@L5A.cfg fxk Rk 0xa8f34 Mk modk) K).
  { intros fxk Rk Mk modk LKk Ak BIk RIk LSk K18 K20 K22 K23 K24 K25 HBk EAk KAk SRCFk NULk HSTKak HSTKbk.
    pose proof BIk as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mk modk LKk cr9 Ak BIk)
      as ((VWk & VICk & VSBk & VUARk & VMSk) & VOWNk & (VFDk & VFWk & VFSWk & VFLCk & VFLWk) & (FLCck & FLVk & FVk & SPVk & FSVk)).
    change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
    set (Hk' := ahid Ak modk) in *. set (MVk := mrestrict Hk' Mk) in *.
    assert (Q5k : L5.writable RSEGS MVk (V2 - 160) 160) by (eapply L5.writable_sub; [exact VWk| clear; lia| clear - CLS; lia]).
    assert (Q6k : L5.u64_at RSEGS MVk (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLCk).
    pose proof (PEACHP3.ahnK_conc fxk Rk MVk (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rk 1 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                       | exact VFDk | exact VFWk | exact VFSWk | exact VFLWk | exact Q5k | exact Q6k | (unfold PEACHP3.aligned; exact V2A)
                       | (match goal with |- getr Rk (reg ?i) = _ => pose proof RIk as (Z2 & Z3 & Z4 & Z8 & Z9 & Z19 & Z21 & Z26 & Z27); asm end) ]).
    destruct PP as (fxq & Rq & Mqv & MGq & kFR & kFZ & (kMS & kKS & kR1 & kR10)).
    pose proof E1 as E1x. rewrite <- app_assoc in E1x || idtac.
    apply (apiece L ar C HI LYa HIok _ FF' LKk cr9 Ak Mk modk fxk fxq Rk 0xa8f34 Rq 0xa9c58 Mqv (fun _ => False) K E1 E2 kMS MGq).
    { intros a Ha _. apply kFZ. exact Ha. }
    { intros a _ []. }
    intros Mq modq HHq AMq MRTq HIDq VISq MGMq FRq VVq.
    assert (BIq : L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5 W ((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) Mq modq LKk cr9 Ak).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mk modk LKk cr9 Ak Mq modq (fun _ => False) BIk HHq AMq MRTq MGMq FRq). intros a []. }
    assert (RIq : rinvH R Rq (V2 - 160) F 2147450880) by (apply (rinvH_ks R Rk Rq (V2 - 160) F 2147450880 PEACHP3.KS_ahnK RIk kKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
    assert (EQq : Mq = Mk) by (apply mem_eq_of_agree; intros a Ha; apply FRq; [exact Ha| intros []]). subst Mq.
    pose proof BIq as (G1 & G2' & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    pose proof LSk as (LSBk & _).
    unfold PMSPA.src_dtor_spec in SRC. cbn [pa_src_dtor PeCLayoutA.CADDR_A] in SRC.
    apply (SRC fxq Rq Mk modq K _ FF' LKk Ak cr9 (F + 616) (F + 96) (F + 96 + 16) (V2 - 160) 0xa8f3c src G1 G2' K0).
    { eapply PEAHSK.callee_entry; first [exact BIq | exact RIq | exact kR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
    { eapply PEAHSK.callee_room; first [exact BIq | eassumption | lia]. }
    { eapply PEAHSK.callee_rs; eassumption. }
    { rewrite L5K.rl10. exact kR10. }
    { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
    { exact (fb_mod8 F 77 FAL). }
    { exact SRCFk. }
    { replace (F + 616 + 8) with (F + 624) by (clear; lia). exact NULk. }
    { left. reflexivity. }
    { exact LSBk. }
    intros fxf Rf Mf modf LKf Af RPf HPf MRTf INCLKf INCAf AMf HHf.
    change (PMSPA.pm_scr 2) with 16384 in HPf.
    cbn [app] in HPf, HHf. rewrite L5ADHR.lb_remove_head in HPf, HHf.
    assert (WFIf : PEAHK2.wfi F [(F + 616, 296)]) by (apply PEAHK2.wfi_cons; [cbn [fst snd]; left; lia| apply PEAHK2.wfi_nil]).
    assert (WAf : forall o k2, (o + k2 <= F + 616 \/ F + 912 <= o) -> PEAHK2.wapart [(F + 616, 296)] o k2) by (intros o k2 Ho r [<-|[]]; cbn [fst snd]; clear - Ho; lia).
    assert (LSf : PESTA.ls_okA RSEGS AD AAD EE g Mf).
    { apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 16384 [(F + 616, 296)] Mk Mf HPf); [| exact LSk]. apply PEAHK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PEAHK.far_nil]. }
    assert (BIf : Bv W (REST ++ X) Mf modf LKf cr9 Af).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (REST ++ X) (REST ++ X) Mk modq LKk cr9 Ak Mf modf LKf cr9 Af 16384 [(F + 616, 296)] BIq);
        [first [exact HPf| rewrite app_assoc in HPf; exact HPf]| first [exact HHf| rewrite app_assoc in HHf; exact HHf]| exact AMf| exact MRTf| exact INCAf| exact INCLKf| lia| clear - CLS; lia| | | intros a X0; exact X0].
      - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
      - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc]. }
    assert (RIf : rinvH R Rf (V2 - 160) F 2147450880) by exact (rinvH_pres R Rq Rf (V2 - 160) F 2147450880 RIq RPf).
    assert (FINk : In (F, 5, V2 - 160 + 32) (FF' ++ LKk)) by (apply in_or_app; left; left; reflexivity).
    assert (AGFf : forall o k2, F + 32 <= o -> o + k2 <= F + 2040 -> (o + k2 <= F + 616 \/ F + 912 <= o) -> PMFA.agA Mk Mf o k2).
    { intros o k2 H1 H2 H3. apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 16384 [(F + 616, 296)] Mk Mf (F, 5, V2 - 160 + 32) F o k2 HPf (or_introl eq_refl));
        cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFIf| apply WAf; exact H3]. }
    assert (INr : forall x, In x REST \/ In x X -> In x ((REST ++ X) ++ LB)) by (intros x Hx; apply in_or_app; left; apply in_or_app; exact Hx).
    assert (INk : forall x, In x REST \/ In x X -> In x (((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) ++ LB)) by (intros x Hx; right; apply in_or_app; left; apply in_or_app; exact Hx).
    apply (KONT fxf Rf Mf modf LKf Af BIf RIf LSf).
    - rewrite (cs_of_preserved Rq Rf 18 RPf) by inl. rewrite (kKS 18%nat) by inl. exact K18.
    - rewrite (cs_of_preserved Rq Rf 20 RPf) by inl. rewrite (kKS 20%nat) by inl. exact K20.
    - rewrite (cs_of_preserved Rq Rf 22 RPf) by inl. rewrite (kKS 22%nat) by inl. exact K22.
    - rewrite (cs_of_preserved Rq Rf 23 RPf) by inl. rewrite (kKS 23%nat) by inl. exact K23.
    - rewrite (cs_of_preserved Rq Rf 24 RPf) by inl. rewrite (kKS 24%nat) by inl. exact K24.
    - rewrite (cs_of_preserved Rq Rf 25 RPf) by inl. rewrite (kKS 25%nat) by inl. exact K25.
    - eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact G1 | exact HPf | exact HBk | exact FHF | exact FINk | exact WFIf | (apply WAf; lia)
        | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply INk; right; exact Hx) | (intros x Hx; apply INr; right; exact Hx) | lia ].
    - apply (PECFA.enc_atA_agree RSEGS EE L ar Mk Mf (F + 496) F en1); [clear - FR; lia| clear - FR; lia| apply AGFf; clear; lia| | exact EAk].
      intros Hk0. destruct (ENB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
      assert (INe : In (PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1)) REST) by (subst REST; apply in_or_app; left; unfold PEC.enc_own; destruct (PEC.en_k en1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]).
      apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 16384 [(F + 616, 296)] Mk Mf G1 (INk _ (or_introl INe)) FINk FHF HPf (INr _ (or_introl INe)) WFIf).
    - apply (PECFA.sink_atA_agree RSEGS L ar Mk Mf P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply AGFf; clear; lia| | exact KAk].
      intros Hk0. destruct (SKB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
      assert (INe : In (PESK.sk_b k1, PESK.sk_c k1) REST) by (subst REST; apply in_or_app; right; unfold PESK.sink_own; destruct (PESK.sk_c k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]).
      apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 16384 [(F + 616, 296)] Mk Mf G1 (INk _ (or_introl INe)) FINk FHF HPf (INr _ (or_introl INe)) WFIf).
    - apply (L5C.u64_at_agree RSEGS Mk Mf (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKak].
      intros i Hi. apply (proj1 HPf i). split; [clear - Hi V2R V2S CLS; lia| split]; [apply stack_client; [clear - Hi SLO V2S CLS; lia| clear - Hi; lia]| intros rr [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi FCEIL SLO CLS; lia].
    - apply (L5C.u64_at_agree RSEGS Mk Mf (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKbk].
      intros i Hi. apply (proj1 HPf i). split; [clear - Hi V2R V2S CLS; lia| split]; [apply stack_client; [clear - Hi SLO V2S CLS; lia| clear - Hi; lia]| intros rr [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi FCEIL SLO CLS; lia]. }

  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mv modv LKv cr9 Av BIv)
    as ((VWv & VICv & VSBv & VUARv & VMSv) & VOWNv & (VFDv & VFWv & VFSWv & VFLCv & VFLWv) & (FLCcv & FLVv & FVv & SPVv & FSVv)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (Hv := ahid Av modv) in *. set (MVv := mrestrict Hv Mv) in *.
  assert (Q5v : L5.writable RSEGS MVv (V2 - 160) 160) by (eapply L5.writable_sub; [exact VWv| clear; lia| clear - CLS; lia]).
  assert (Q6v : L5.u64_at RSEGS MVv (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLCv).
  assert (AV928 : L5A.avis Hv (F + 928) 8) by (apply (PEAHK.avis_sub Hv F 2048 (F + 928) 8 FVv); lia).
  assert (AV944 : L5A.avis Hv (F + 944) 8) by (apply (PEAHK.avis_sub Hv F 2048 (F + 944) 8 FVv); lia).
  pose proof RIv as (U2' & U3 & U4 & U8 & U9 & U19 & U21 & U26 & U27).
  destruct tb as [nt | c nt q] eqn:ETB.
  -
    destruct TBv as (_ & _ & (Hnt & SB0)).
    assert (SBv : L5.u8_at RSEGS MVv (F + 928) (2 * nt))
      by (apply (proj2 (L5A.u8_at_vis Hv Mv (F + 928) (2 * nt) (PEAHK.avis_sub Hv (F + 928) 8 (F + 928) 1 AV928 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    pose proof (PMF.even_byte nt) as EVB.
    pose proof (PEACHP3.ahnJs_conc fxv Rv MVv (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U Rv 1 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
                       | exact VFDv | exact VFWv | exact VFSWv | exact VFLWv | exact Q5v | exact Q6v | exact SBv | exact EVB | (unfold PEACHP3.aligned; exact V2A) ]).
    destruct PP as (fxs & Rs & Msv & MGs & sFR & sFZ & (sMS & sKS & sR10)).
    apply (apiece L ar C HI LYa HIok _ FF' LKv cr9 Av Mv modv fxv fxs Rv 0xa8f18 Rs 0xa8f34 Msv (fun _ => False) K D1 D2 sMS MGs).
    { intros a Ha _. apply sFZ. exact Ha. }
    { intros a _ []. }
    intros Ms mods HHs AMs MRTs HIDs VISs MGMs FRs VVs.
    assert (BIs : Bv W LBv Ms mods LKv cr9 Av).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mv modv LKv cr9 Av Ms mods (fun _ => False) BIv HHs AMs MRTs MGMs FRs). intros a []. }
    assert (RIs : rinvH R Rs (V2 - 160) F 2147450880) by (apply (rinvH_ks R Rv Rs (V2 - 160) F 2147450880 PEACHP3.KS_ahnJs RIv sKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
    assert (EQs : Ms = Mv) by (apply mem_eq_of_agree; intros a Ha; apply FRs; [exact Ha| intros []]). subst Ms.
    subst LBv. cbn [PM.vs_own app] in BIs.
    apply (TAIL fxs Rs Mv mods LKv Av); [first [exact BIs | (unfold L5AFKR.binv in BIs |- *; rewrite <- ?app_assoc in BIs |- *; exact BIs)]| exact RIs| exact LSv| | | | | | | exact HBv| exact EAv| exact KAv| exact SRCFv| exact NULv| exact HSTKav| exact HSTKbv];
      rewrite sKS by inl; assumption.
  -
    destruct TBv as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    replace (F + 928 + 16) with (F + 944) in TW16 by (clear; lia).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by (clear - Hc; lia).
    pose proof (PMF.u8_of_u64 RSEGS Mv _ _ Hc64 TW0) as SB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(clear - Hc; lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as HVB.
    assert (SBv : L5.u8_at RSEGS MVv (F + 928) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis Hv Mv (F + 928) _ (PEAHK.avis_sub Hv (F + 928) 8 (F + 928) 1 AV928 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    assert (TW0v : L5.u64_at RSEGS MVv (F + 928) (c + 1)) by (apply (proj2 (L5A.u64_at_vis Hv Mv (F + 928) _ AV928 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MVv (F + 944) q) by (apply (proj2 (L5A.u64_at_vis Hv Mv (F + 944) _ AV944 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
    assert (INP : In (q, c) (LBv ++ LB)) by (subst LBv; cbn [PM.vs_own app]; right; left; reflexivity).
    destruct (PEAHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q c D1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
    pose proof (PEACHP3.ahnJl_conc fxv Rv MVv (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => q
                                                     | 40%nat => F | 41%nat => fl | 58%nat => U Rv 1 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    feed PP ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                       | exact F32 | exact VFDv | exact VFWv | exact VFSWv | exact VFLWv | exact Q5v | exact Q6v | exact SBv | exact TW0v | exact TW16v | exact ODB | (unfold PEACHP3.aligned; exact V2A) ]).
    destruct PP as (fxl & Rl & Mlv & MGl & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11)).
    apply (apiece L ar C HI LYa HIok _ FF' LKv cr9 Av Mv modv fxv fxl Rv 0xa8f18 Rl 0xd4a60 Mlv (fun _ => False) K D1 D2 lMS MGl).
    { intros a Ha _. apply lFZ. exact Ha. }
    { intros a _ []. }
    intros Ml modl HHl AMl MRTl HIDl VISl MGMl FRl VVl.
    assert (BIl : Bv W LBv Ml modl LKv cr9 Av).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ Mv modv LKv cr9 Av Ml modl (fun _ => False) BIv HHl AMl MRTl MGMl FRl). intros a []. }
    assert (RIl : rinvH R Rl (V2 - 160) F 2147450880) by (apply (rinvH_ks R Rv Rl (V2 - 160) F 2147450880 PEACHP3.KS_ahnJl RIv lKS); unfold incl; apply L5K.incl_b; vm_compute; reflexivity).
    assert (EQl : Ml = Mv) by (apply mem_eq_of_agree; intros a Ha; apply FRl; [exact Ha| intros []]). subst Ml.

    pose proof BIl as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9' & C10').
    assert (ASX : L5CA.astk ar Mv (V2 - 160) (PMSPA.pm_scr 0) /\ shadow_zero Mv (V2 - 160 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PEAHSK.callee_stack; first [exact BIl | eassumption | lia]).
    destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
    pose proof RIl as (Ul2 & Ul3 & Ul4 & Ul8 & Ul9 & Ul19 & Ul21 & Ul26 & Ul27).
    unfold PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PeCLayoutA.CADDR_A] in OPD.
    apply (OPD fxl Rl Mv modl K _ FF' LKv Av cr9 q c (V2 - 160) 0xa8f34 C1' C2' K0 INP).
    { rewrite L5K.rl10. exact lR10. }
    { rewrite L5K.rl1. exact lR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact Ul2. }
    { rewrite L5K.rl4. rewrite Ul4. exact TP. }
    { replace (V2 - 160) with (V2 - 160 - 0) by lia. apply (L5SAR.astk_sub ar Mv Mv (V2 - 160) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
        [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| replace (V2 - 160 - 0) with (V2 - 160) by (clear; lia); exact SPA16]. }
    intros fxo Ro Mo modo Ao RPo HPo MRTo INCAo AMo HHo.
    assert (ELB2 : lb_remove q (LBv ++ LB) = ((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) ++ LB).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1') as AW. assert (ND : NoDup (map fst (LBv ++ LB))) by (decompose [and] AW; assumption).
      subst LBv. cbn [PM.vs_own app] in ND |- *.
      change ((PM.sr_qc src, PM.CHUNK) :: (q, c) :: (REST ++ X) ++ LB) with ([(PM.sr_qc src, PM.CHUNK)] ++ (q, c) :: ((REST ++ X) ++ LB)) in ND |- *.
      rewrite (PEAHK3.lb_remove_mid q c [(PM.sr_qc src, PM.CHUNK)] ((REST ++ X) ++ LB) ND). reflexivity. }
    rewrite ELB2 in HPo, HHo. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    assert (BIo : L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5 W ((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) Mo modo LKv cr9 Ao).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ _ _ Mv modl LKv cr9 Av Mo modo LKv cr9 Ao 4096 [] BIl HPo HHo AMo MRTo INCAo (incl_refl _)).
      - lia.
      - clear - CLS; lia.
      - intros rr a [].
      - intros a _ _ rr [].
      - intros a X0. exact X0. }
    assert (LSo : PESTA.ls_okA RSEGS AD AAD EE g Mo) by (apply (PEAHK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 4096 [] Mv Mo HPo PEAHK.far_nil LSv)).
    assert (RIo : rinvH R Ro (V2 - 160) F 2147450880) by exact (rinvH_pres R Rl Ro (V2 - 160) F 2147450880 RIl RPo).
    assert (AGo : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) ++ LB) FF' (V2 - 160) 4096 a -> Mo (Z_to_bv 64 a) = Mv (Z_to_bv 64 a)).
    { intros a Ha Hc0. apply (proj1 HPo a). split; [exact Ha| split; [exact Hc0| intros rr []]]. }
    assert (AGFo : forall o k2, F + 32 <= o -> o + k2 <= F + 2040 -> PMFA.agA Mv Mo o k2).
    { intros o k2 H1 H2. apply (PEAHK2.ff_callee L ar _ FF' (V2 - 160) 4096 [] Mv Mo (F, 5, V2 - 160 + 32) F o k2 HPo (or_introl eq_refl));
        cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| apply PEAHK2.wfi_nil| apply PEAHK2.wapart_nil]. }
    assert (FINv : In (F, 5, V2 - 160 + 32) (FF' ++ LKv)) by (apply in_or_app; left; left; reflexivity).
    assert (INo : forall x, In x REST \/ In x X -> In x (((PM.sr_qc src, PM.CHUNK) :: (REST ++ X)) ++ LB)) by (intros x Hx; right; apply in_or_app; left; apply in_or_app; exact Hx).
    assert (INl : forall x, In x REST \/ In x X -> In x (LBv ++ LB)) by (intros x Hx; subst LBv; apply in_or_app; left; apply in_or_app; right; apply in_or_app; exact Hx).
    apply (TAIL fxo Ro Mo modo LKv Ao BIo RIo LSo).
    + rewrite (cs_of_preserved Rl Ro 18 RPo) by inl. rewrite (lKS 18%nat) by inl. exact V18.
    + rewrite (cs_of_preserved Rl Ro 20 RPo) by inl. rewrite (lKS 20%nat) by inl. exact V20.
    + rewrite (cs_of_preserved Rl Ro 22 RPo) by inl. rewrite (lKS 22%nat) by inl. exact V22.
    + rewrite (cs_of_preserved Rl Ro 23 RPo) by inl. rewrite (lKS 23%nat) by inl. exact V23.
    + rewrite (cs_of_preserved Rl Ro 24 RPo) by inl. rewrite (lKS 24%nat) by inl. exact V24.
    + rewrite (cs_of_preserved Rl Ro 25 RPo) by inl. rewrite (lKS 25%nat) by inl. exact V25.
    + eapply PEAHK2.hbase_callee; first [ exact LY | exact HIok | exact C1' | exact HPo | exact HBv | exact FHF | exact FINv | apply PEAHK2.wfi_nil | apply PEAHK2.wapart_nil
        | (left; reflexivity) | (split; reflexivity) | (intros x Hx; apply INl; right; exact Hx) | (intros x Hx; apply INo; right; exact Hx) | lia ].
    + apply (PECFA.enc_atA_agree RSEGS EE L ar Mv Mo (F + 496) F en1); [clear - FR; lia| clear - FR; lia| apply AGFo; clear; lia| | exact EAv].
      intros Hk0. destruct (ENB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
      assert (INe : In (PEC.en_b en1, PEC.ESZ * PEC.ecap (PEC.en_k en1)) REST) by (subst REST; apply in_or_app; left; unfold PEC.enc_own; destruct (PEC.en_k en1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]).
      apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 4096 [] Mv Mo C1' (INl _ (or_introl INe)) FINv FHF HPo (INo _ (or_introl INe)) (PEAHK2.wfi_nil F)).
    + apply (PECFA.sink_atA_agree RSEGS L ar Mv Mo P (F + 432) k1); [clear - FR; lia| clear - FR; lia| apply AGFo; clear; lia| | exact KAv].
      intros Hk0. destruct (SKB Hk0) as (IN & Q0 & Q47'). split; [exact Q0|]. split; [exact Q47'|].
      assert (INe : In (PESK.sk_b k1, PESK.sk_c k1) REST) by (subst REST; apply in_or_app; right; unfold PESK.sink_own; destruct (PESK.sk_c k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity]).
      apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 4096 [] Mv Mo C1' (INl _ (or_introl INe)) FINv FHF HPo (INo _ (or_introl INe)) (PEAHK2.wfi_nil F)).
    + apply (PMFA.src_fields_at_agreeA RSEGS Mv Mo (F + 616) (F + 96) (F + 96 + 16) src); [clear - FR; lia| clear - FR; lia| clear - Qc0; lia| clear - Q47; lia| apply AGFo; clear; lia| | exact SRCFv].
      apply (PEAHK2.blk_callee L ar C SCFG HI LY HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) _ FF' (V2 - 160) 4096 [] Mv Mo C1' INQv FINv FHF HPo ltac:(left; reflexivity) (PEAHK2.wfi_nil F)).
    + apply (PMFA.nullis_at_agreeA RSEGS AD Mv Mo (F + 624)); [clear - FR; lia| clear - FR; lia| apply AGFo; clear; lia| exact NULv].
    + apply (L5C.u64_at_agree RSEGS Mv Mo (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKav].
      intros i Hi. apply AGo; [clear - Hi V2R; lia|]. apply stack_client; [clear - Hi SLO V2S CLS; lia| clear - Hi; lia].
    + apply (L5C.u64_at_agree RSEGS Mv Mo (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKbv].
      intros i Hi. apply AGo; [clear - Hi V2R; lia|]. apply stack_client; [clear - Hi SLO V2S CLS; lia| clear - Hi; lia].
Qed.
End Stage.
End SCFG_1.
End PEACH8.
