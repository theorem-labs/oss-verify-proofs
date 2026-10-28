(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u ChunkKit_u SourceDtorStretch_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SD.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.
Lemma frame_but_nil0 : forall (M M' : mem) a, L5.frame_but [(a, 0)] M M' -> M' = M.
Proof. intros M M' a H. apply FunctionalExtensionality.functional_extensionality. intros x. apply H. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. Qed.
Lemma lb_remove_in : forall A (LB : list (Z * Z)) b, In b (lb_remove A LB) -> In b LB.
Proof. intros A LB b. induction LB as [|x LB IH]; cbn [lb_remove]; [tauto|]. destruct (Z.eqb (fst x) A); intros H; [right; exact H | destruct H as [H|H]; [left; exact H | right; exact (IH H)]]. Qed.
Lemma al8_add : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a + k) mod 8 = 0.
Proof. intros a k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; apply Z.mod_divide; try lia; assumption. Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.
Hypothesis LOCDTOR : PMS.locale_dtor_spec L.
Hypothesis ISTRDTOR : TPS.istream_dtor_spec L.
Hypothesis IOSBDTOR : TPS.iosb_dtor_spec L.

Theorem source_dtor_ok : PMS.source_dtor_spec L HI.
Proof.
  intros LB cr Rr ch sp r fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & SRC & INch & RO & OP) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). destruct OP as (OP1 & OP2 & OP3).
  destruct SRC as (C264 & C272 & (st0 & IOSB) & C32 & DEFR). unfold PML.a0 in A0.
  set (SCR := 96 + PMS.OPDEL_SCR) in *. assert (HSCR : SCR = 8320) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).
  set (LBk := lb_remove ch LB) in *.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; exact (lb_remove_in _ _ _ Hb)).
  destruct (BOK _ INch) as (CH0 & _ & _ & _ & CH4). cbn [fst snd] in CH0, CH4. unfold hl_ceil in *.
  set (foot := fun a : Z => Rr <= a < Rr + 592).
  assert (FR0 : TK2.FR L LBk sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).

  apply (SDS.s_sd_entry FPM fx R M model K sp Rr ch 16384 r Hh Hl Hfp Hsp SPOK Hra Hrok A0 ltac:(lia) ltac:(lia) ltac:(lia) C264 C272 ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) OP1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H8a FRM1 KO1 AG1 MG1.
  pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 32) sp HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AG1 MG1) as HH1.
  assert (FR1 : TK2.FR L LBk sp SCR foot M M1) by (apply (TK2.FR_grows L LAY LBk sp SCR foot M M M1 _ FR0 AG1 MG1 BOKk ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; left; lia).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
  assert (STKg : forall Mx scr, TK2.FR L LBk sp SCR foot M Mx -> 0 <= scr -> 32 + scr <= SCR -> L5C.stk (hl_sptop L) Mx (sp - 32) scr).
  { intros Mx scr FRx Q1 Q2. split; [apply CK.al16; [exact S1 | reflexivity]|]. split; [lia|]. split; [lia|]. split; [exact S4|]. intros i Hi. apply (proj2 FRx). lia. }

  apply (OPDELS LB cr ch 16384 (sp - 32) SDT.R1 fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 32) _ _ H1a (ra_ok_lit SDT.R1 eq_refl) H2a TP1 (STKg M1 PMS.OPDEL_SCR FR1 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)))|].
    split; [exact H10a | exact INch]. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & -> & ->) RP2 HP2 BV2 HH2. fold LBk in HP2, HH2.
  pose proof (TK2.hpres_samem L LAY LBk (sp - 32) _ _ M1 M2 HP2 BOKk (STKg M1 PMS.OPDEL_SCR FR1 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) as AG2.
  assert (KH : forall a, sp - 32 <= a -> TK2.keepH L LBk [] (sp - 32) PMS.OPDEL_SCR a) by (intros a Ha; split; [intros w [] | left; exact Ha]).
  assert (FR2 : TK2.FR L LBk sp SCR foot M M2).
  { apply (TK2.FR_hpres L LAY LBk sp SCR foot M M1 M2 _ (sp - 32) _ _ FR1 HP2 BOKk); [intros b Hb; exact Hb | unfold hl_ceil; lia | lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | intros w a []]. }
  assert (MOK2 : PML.model_ok model2) by (split; [rewrite (L5C.halted_but_vm _ _ BV2); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV2); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV2); exact Hmat]]).
  destruct MOK2 as (Hh2 & Hl2 & Hmat2).
  assert (RO2 : PML.img_ro M2).
  { apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; split; [intros w [] | right; right; right; lia]|].
    apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; cbn beta; lia | exact RO]. }
  assert (DEF2 : L5.defined M2 Rr 320).
  { apply (TK.defined_samem _ M1 M2 _ _ AG2); [lia | lia | intros i Hi; apply KH; lia | exact (L5.defined_grows _ _ _ _ MG1 DEFR)]. }
  assert (R2sp : getr R2 2%bv = Z_to_bv 64 (sp - 32)) by (rewrite (SDS.sp_rp _ _ RP2); exact H2a).
  assert (R2s0 : getr R2 8%bv = Z_to_bv 64 Rr) by (rewrite (RP2 8%bv ltac:(ck_in)); exact H8a).

  apply (SDS.s_sd_r1 FPM fx2 R2 M2 model2 K sp Rr Hh2 Hl2 Hfp2 R2sp SPOK R2s0 ltac:(lia) RO2 ltac:(eapply L5.defined_sub; [exact DEF2 | lia | lia])).
  intros fx3 R3 M3 Hfp3 H2c H1c H10c LIVE3 KO3 AG3 MG3.
  assert (AGS3 : TK.samem (fun a => ~ (sp - 32 <= a < hl_sptop L)) M2 M3) by (apply (TK.samem_weaken _ _ _ _ AG3); intros a Ha; unfold SDS.KV; lia).
  pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M2 M3 _ (sp - 32) (hl_sptop L) HH2 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS3 MG3) as HH3.
  assert (FR3 : TK2.FR L LBk sp SCR foot M M3) by (apply (TK2.FR_grows L LAY LBk sp SCR foot M M2 M3 _ FR2 AG3 MG3 BOKk ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; right; unfold SDS.KV, foot in *; lia).
  assert (C32c : L5.u64_at RSEGS M3 (Rr + 32) PML.CLASSIC_IMP).
  { apply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; unfold SDS.KV; lia|]. apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply KH; lia|].
    apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; cbn beta; lia | exact C32]. }
  assert (IOSB3 : PML.iosb_at M3 (Rr + 88) st0 (Rr + 24)).
  { apply (TK2.iosb_at_xg _ M2 M3 AG3); [lia | intros i Hi; unfold SDS.KV; lia | exact MG3|]. apply (TK2.iosb_at_x _ M1 M2 AG2); [lia | intros i Hi; apply KH; lia|].
    apply (TK2.iosb_at_x _ M M1 AG1); [lia | intros i Hi; cbn beta; lia | exact IOSB]. }
  assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO3 4%bv ltac:(ck_in)), (RP2 4%bv ltac:(ck_in)); exact TP1).

  apply (LOCDTOR (Rr + 32) (sp - 32) SDT.R2 fx3 R3 M3 model2 K Hh2 Hl2 HK0 Hfp3).
  { split; [exact (CK.mk_entry L R3 M3 (sp - 32) _ _ H1c (ra_ok_lit SDT.R2 eq_refl) H2c TP3 (STKg M3 0 FR3 ltac:(lia) ltac:(lia)))|]. split; [exact H10c|]. split; [lia | exact C32c]. }
  intros fx4 R4 M4 Hfp4 _ RP4 FB4 _. rewrite (frame_but_nil0 M3 M4 _ FB4). clear FB4 M4.
  apply (SDS.s_sd_r2 FPM fx4 R4 M3 model2 K sp Rr Hh2 Hl2 Hfp4 ltac:(rewrite (SDS.sp_rp _ _ RP4); exact H2c) SPOK (SDS.sd_live_keep R3 R4 Rr (SDS.sv_rp _ _ RP4) LIVE3) ltac:(lia)).
  intros fx5 R5 Hfp5 H2e H1e LIVE5 KO5.
  assert (TP5 : getr R5 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO5 4%bv ltac:(ck_in)), (RP4 4%bv ltac:(ck_in)); exact TP3).

  apply (ISTRDTOR (sp - 32) SDT.R3 fx5 R5 M3 model2 K Hh2 Hl2 HK0 Hfp5).
  { exact (CK.mk_entry L R5 M3 (sp - 32) _ _ H1e (ra_ok_lit SDT.R3 eq_refl) H2e TP5 (STKg M3 0 FR3 ltac:(lia) ltac:(lia))). }
  intros fx6 R6 M6 Hfp6 _ RP6 FB6 _. rewrite (frame_but_nil0 M3 M6 _ FB6). clear FB6 M6.
  assert (FRM3 : SDS.sd_frame M3 sp r R).
  { apply (SDS.sd_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; unfold SDS.KV; lia|]. apply (SDS.sd_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; apply KH; lia | exact FRM1]. }
  apply (SDS.s_sd_r3 FPM fx6 R6 M3 model2 K sp Rr r R Hh2 Hl2 Hfp6 ltac:(rewrite (SDS.sp_rp _ _ RP6); exact H2e) SPOK (SDS.sd_live_keep R5 R6 Rr (SDS.sv_rp _ _ RP6) LIVE5) ltac:(lia) FRM3 Hrok).
  intros fx7 R7 Hfp7 H2g H1g H10g SS7 KO7.
  assert (KOall : TK.keepsR SDS.KO3 R R7).
  { exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (SDS.ko3_rp _ _ RP2)) KO3) (SDS.ko3_rp _ _ RP4)) KO5) (SDS.ko3_rp _ _ RP6)) KO7). }
  assert (RP07 : regs_preserved R R7) by (apply SDS.rp_final; [rewrite H2g, Hsp; reflexivity | exact SS7 | exact KOall]).

  apply (IOSBDTOR (Rr + 88) st0 (Rr + 24) sp r fx7 R7 M3 model2 K Hh2 Hl2 HK0 Hfp7).
  { split.
    - apply (CK.mk_entry L R7 M3 sp r _ H1g Hrok H2g ltac:(rewrite (KOall 4%bv ltac:(ck_in)); exact Htp)).
      split; [exact S1|]. split; [unfold TPS.IOSB_SCR; lia|]. split; [lia|]. split; [exact S4|]. intros i Hi. apply (proj2 FR3). unfold TPS.IOSB_SCR in *. lia.
    - split; [exact H10g|]. split; [exact IOSB3|]. split; [lia|]. split; [lia|]. apply al8_add; [exact OP3 | reflexivity]. }
  intros fx8 R8 M8 Hfp8 _ RP8 FB8 MG8. unfold TPS.IOSB_SCR in FB8. pose proof (TK2.frame_but_samem _ _ _ FB8) as AG8.
  assert (NK8 : forall a, ~ L5.outside [(sp - 64, 64); (Rr + 88, 8)] a -> (sp - 64 <= a < sp) \/ (Rr + 88 <= a < Rr + 96)).
  { intros a Ha. destruct (classic (sp - 64 <= a < sp)) as [Y|N]; [left; exact Y|]. destruct (classic (Rr + 88 <= a < Rr + 96)) as [Y2|N2]; [right; exact Y2|].
    exfalso. apply Ha. intros w [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (AGS8 : TK.samem (fun a => ~ (sp - 64 <= a < hl_sptop L)) M3 M8).
  { apply (TK.samem_weaken _ _ _ _ AG8). intros a Ha. destruct (classic (L5.outside [(sp - 64, 64); (Rr + 88, 8)] a)) as [Y|N]; [exact Y|]. destruct (NK8 a N); lia. }
  apply (Hcont fx8 R8 M8 model2 LBk cr LBk [(Rr, 592)] Hfp8).
  - repeat split; reflexivity.
  - intros q Hq. rewrite (RP8 q Hq). exact (RP07 q Hq).
  - assert (FR8 : TK2.FR L LBk sp SCR foot M M8).
    { apply (TK2.FR_grows L LAY LBk sp SCR foot M M3 M8 _ FR3 AG8 MG8 BOKk ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. destruct (NK8 a Ha); [left; lia | right; unfold foot; lia]. }
    destruct FR8 as [F1 F2]. apply L5C.hpres_intro.
    + intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros X. apply (HO (Rr, 592) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
    + intros i Hi. apply F2. lia.
    + intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [|rewrite (F1 a Ha HC N HE); exact Hd].
      apply MG8, MG3. unfold foot in Y.
      apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP2 Ha); [right; left; unfold hl_ceil; unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | apply MG1; exact Hd].
  - exact BV2.
  - exact (TK2.heap_stack_write L HI HIok LAY _ _ M3 M8 _ (sp - 64) (hl_sptop L) HH3 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS8 MG8).
Qed.
End H.
End SD.
