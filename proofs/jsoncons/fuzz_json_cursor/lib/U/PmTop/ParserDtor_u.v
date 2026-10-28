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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u ChunkKit_u ParserDtorStretch_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PD.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.
Lemma land1_odd_low : forall w, Z.testbit w 0 = true -> Z.land (w mod 256) 1 = 1.
Proof.
  intros w H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite H. reflexivity.
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.

Theorem parser_dtor_ok : PMS.parser_dtor_spec L HI.
Proof.
  intros LBo cr sp r P ps fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & PAR & RO & OP & SCAP) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). destruct OP as (OP1 & OP2 & OP3).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. unfold PML.a0 in A0.
  set (SCR := 64 + PMS.OPDEL_SCR) in *. assert (HSCR : SCR = 8288) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).

  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  assert (BOKo : TK2.blocks_ok L LBo) by (intros b Hb; apply BOK; apply in_or_app; right; exact Hb).
  pose proof (BOK _ (or_introl eq_refl)) as (BB0 & BB1 & _ & BB3 & BB4). pose proof (BOK _ (or_intror (or_introl eq_refl))) as (SB0 & SB1 & _ & SB3 & SB4). cbn [fst snd] in BB0, BB1, BB3, BB4, SB0, SB1, SB3, SB4.
  assert (NE : PML.ps_bptr ps <> PML.ps_sb ps).
  { destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & ND & _). unfold PML.ps_blocks in ND. cbn [app map fst] in ND. inversion ND as [|x1 l1 X1 X2]; subst.
    intros Y. apply X1. rewrite Y. left. }

  pose proof PAR as PAR0. unfold PML.parser_at in PAR0.
  destruct PAR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & C24 & _) & (_ & C48 & _) & (_ & C72 & _) & C96 & C128 & _ & _ & _ & _ & _ & _ & _ & _ & _ & STRB & _ & C248 & C256 & C264 & _ & SLEN & DEFP).
  cbn [length Z.of_nat Z.mul] in C24, C48, C72. destruct STRB as ((Sbit & Sw0 & _ & Sw16 & _) & _ & _). replace (P + 224 + 16) with (P + 240) in Sw16 by lia.
  unfold hl_ceil in *.

  set (foot := fun a : Z => P <= a < P + 272).
  assert (WF : forall w a, In w [(P, 272)] -> L5.in_rng w a -> foot a) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
  assert (FR0 : TK2.FR L LBo sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).
  assert (CLI : forall a LBx spc scr, foot a -> sp - SCR <= spc - scr -> spc <= sp -> client_addr L LBx spc scr a /\ ~ in_errno L a).
  { intros a LBx spc scr Hf H1 H2. unfold foot in Hf. split; [right; left; unfold hl_ceil; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia]. }

  apply (PDS.s_pd_entry FPM fx R M model K sp P (PML.ps_sb ps) (PML.ps_sb ps + PML.ps_scap ps) (Z.of_nat (length (PML.ps_stack ps))) r Hh Hl Hfp Hsp SPOK Hra Hrok A0 ltac:(lia) OP3 ltac:(lia) ltac:(lia) ltac:(lia) C248 C256 C264
           ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) DEFP OP1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H8a FRM1 KO1 AG1 MG1.
  assert (AGS1 : TK.samem (fun a => ~ (sp - 32 <= a < hl_sptop L)) M M1) by (apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; unfold PDS.KE; lia).
  pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 32) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS1 MG1) as HH1.
  assert (FR1 : TK2.FR L LBo sp SCR foot M M1) by (apply (TK2.FR_grows L LAY LBo sp SCR foot M M M1 _ FR0 AG1 MG1 BOKo ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; unfold PDS.KE, foot in *; lia).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 32) PMS.OPDEL_SCR) by (apply (CK.sub_stk _ M M1 sp SCR _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]).

  apply (OPDELS (PML.ps_blocks ps ++ LBo) cr (PML.ps_sb ps) (PML.ps_scap ps) (sp - 32) PDT.R1 fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 32) _ _ H1a (ra_ok_lit PDT.R1 eq_refl) H2a TP1 STK1)|]. split; [exact H10a|]. right. left. reflexivity. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & -> & ->) RP2 HP2 BV2 HH2.
  assert (LBE : lb_remove (PML.ps_sb ps) (PML.ps_blocks ps ++ LBo) = (PML.ps_bptr ps, PML.ps_bcap ps) :: LBo).
  { unfold PML.ps_blocks. cbn [app lb_remove fst]. rewrite (proj2 (Z.eqb_neq _ _) NE), Z.eqb_refl. reflexivity. }
  rewrite LBE in HP2, HH2.
  assert (BOK2 : TK2.blocks_ok L ((PML.ps_bptr ps, PML.ps_bcap ps) :: LBo)) by (intros b [<-|Hb]; [exact (BOK _ (or_introl eq_refl)) | exact (BOKo b Hb)]).
  pose proof (TK2.hpres_samem L LAY _ (sp - 32) _ _ M1 M2 HP2 BOK2 STK1 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) as AG2.
  assert (KH : forall LBk a, sp - 32 <= a -> TK2.keepH L LBk [] (sp - 32) PMS.OPDEL_SCR a) by (intros LBk a Ha; split; [intros w [] | left; exact Ha]).
  assert (X64 : forall LBk Ma Mb off v, TK.samem (TK2.keepH L LBk [] (sp - 32) PMS.OPDEL_SCR) Ma Mb -> 0 <= off -> off + 8 <= 272 -> PML.u64 Ma (P + off) v -> PML.u64 Mb (P + off) v).
  { intros LBk Ma Mb off v AG Ho1 Ho2 H. apply (TK2.u64_x _ Ma Mb AG); [lia | intros i Hi; apply KH; lia | exact H]. }
  assert (X8 : forall LBk Ma Mb off v, TK.samem (TK2.keepH L LBk [] (sp - 32) PMS.OPDEL_SCR) Ma Mb -> 0 <= off -> off + 1 <= 272 -> PML.u8 Ma (P + off) v -> PML.u8 Mb (P + off) v).
  { intros LBk Ma Mb off v AG Ho1 Ho2 H. apply (TK2.u8_x _ Ma Mb AG); [lia | intros i Hi; apply KH; lia | exact H]. }
  assert (Y64 : forall off v, (8 <= off /\ off + 8 <= 256) \/ (264 <= off /\ off + 8 <= 272) -> PML.u64 M (P + off) v -> PML.u64 M1 (P + off) v).
  { intros off v Ho H. apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; unfold PDS.KE; lia | exact H]. }
  assert (Y8 : forall off v, 8 <= off /\ off + 1 <= 256 -> PML.u8 M (P + off) v -> PML.u8 M1 (P + off) v).
  { intros off v Ho H. apply (TK2.u8_x _ M M1 AG1); [lia | intros i Hi; unfold PDS.KE; lia | exact H]. }
  assert (FR2 : TK2.FR L LBo sp SCR foot M M2).
  { apply (TK2.FR_hpres L LAY LBo sp SCR foot M M1 M2 _ (sp - 32) _ _ FR1 HP2 BOKo); [intros b Hb; right; exact Hb | unfold hl_ceil; lia | lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | intros w a []]. }
  assert (R2sp : getr R2 2%bv = Z_to_bv 64 (sp - 32)) by (rewrite (PDS.sp_rp _ _ RP2); exact H2a).
  assert (R2s0 : getr R2 8%bv = Z_to_bv 64 P) by (rewrite (PDS.s0_rp _ _ RP2); exact H8a).
  pose proof BV2 as BV2'. assert (MOK2 : PML.model_ok model2) by (split; [rewrite (L5C.halted_but_vm _ _ BV2); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV2); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV2); exact Hmat]]).
  destruct MOK2 as (Hh2 & Hl2 & Hmat2).

  pose proof (TK2.u64_u8_low M2 (P + 224) (PML.ps_bcap ps + 1) ltac:(lia) ltac:(lia) (X64 _ M1 M2 224 _ AG2 ltac:(lia) ltac:(lia) (Y64 224 _ ltac:(lia) Sw0))) as Sb0.
  apply (PDS.s_pd_r1 FPM fx2 R2 M2 model2 K sp P ((PML.ps_bcap ps + 1) mod 256) Hh2 Hl2 Hfp2 R2sp SPOK R2s0 ltac:(lia)
           ltac:(pose proof (Z.mod_pos_bound (PML.ps_bcap ps + 1) 256 ltac:(lia)); lia) (land1_odd_low _ Sbit) Sb0).
  intros fx3 R3 Hfp3 H2c H8c KO3.
  apply (PDS.s_pd_long2 FPM fx3 R3 M2 model2 K sp P (PML.ps_bcap ps + 1) (PML.ps_bptr ps) Hh2 Hl2 Hfp3 H2c SPOK H8c ltac:(lia) ltac:(lia) ltac:(lia)
           (X64 _ M1 M2 224 _ AG2 ltac:(lia) ltac:(lia) (Y64 224 _ ltac:(lia) Sw0)) (X64 _ M1 M2 240 _ AG2 ltac:(lia) ltac:(lia) (Y64 240 _ ltac:(lia) Sw16))).
  intros fx4 R4 Hfp4 H2d H1d H10d H8d KO4.
  assert (TP4 : getr R4 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO4 4%bv ltac:(ck_in)), (KO3 4%bv ltac:(ck_in)), (PDS.ko1_rp _ _ RP2 4%bv ltac:(ck_in)); exact TP1).
  assert (STK2 : L5C.stk (hl_sptop L) M2 (sp - 32) PMS.OPDEL_SCR).
  { destruct STK1 as (T1 & T2 & T3 & T4 & _). split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. intros i Hi. apply (proj2 FR2). unfold PMS.OPDEL_SCR, PML.HEAP_STACK in *. lia. }

  apply (OPDELS ((PML.ps_bptr ps, PML.ps_bcap ps) :: LBo) cr (PML.ps_bptr ps) (PML.ps_bcap ps) (sp - 32) PDT.R2 fx4 R4 M2 model2 K HH2 (conj Hh2 (conj Hl2 Hmat2)) HK0 Hfp4).
  { split; [exact (CK.mk_entry L R4 M2 (sp - 32) _ _ H1d (ra_ok_lit PDT.R2 eq_refl) H2d TP4 STK2)|]. split; [exact H10d|]. left. reflexivity. }
  intros fx5 R5 M5 model5 LB5 cr5 LBk5 W5 Hfp5 (-> & -> & -> & ->) RP5 HP5 BV5 HH5.
  cbn [lb_remove fst] in HP5, HH5. rewrite Z.eqb_refl in HP5, HH5.
  pose proof (TK2.hpres_samem L LAY _ (sp - 32) _ _ M2 M5 HP5 BOKo STK2 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) as AG5.
  assert (FR5 : TK2.FR L LBo sp SCR foot M M5).
  { apply (TK2.FR_hpres L LAY LBo sp SCR foot M M2 M5 _ (sp - 32) _ _ FR2 HP5 BOKo); [intros b Hb; exact Hb | unfold hl_ceil; lia | lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | intros w a []]. }
  assert (MOK5 : PML.model_ok model5) by (split; [rewrite (L5C.halted_but_vm _ _ BV5); exact Hh2 | split; [rewrite (L5C.lazy_but_vm _ _ BV5); exact Hl2 | rewrite (L5C.materialized_but_vm _ _ BV5); exact Hmat2]]).
  destruct MOK5 as (Hh5 & Hl5 & _).
  assert (RO5 : PML.img_ro M5).
  { assert (IMK : forall LBk i, 0x10000 <= i < PML.IMG_RO_HI -> TK2.keepH L LBk [] (sp - 32) PMS.OPDEL_SCR i) by (intros LBk i Hi; unfold PML.IMG_RO_HI in Hi; split; [intros w [] | right; right; right; lia]).
    apply (TK.img_clear_samem _ M2 M5 _ _ AG5); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; apply IMK; exact Hi|].
    apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; apply IMK; exact Hi|].
    apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold PDS.KE; lia | exact RO]. }

  apply (PDS.s_pd_r2 FPM fx5 R5 M5 model5 K sp P r R Hh5 Hl5 Hfp5 ltac:(rewrite (PDS.sp_rp _ _ RP5); exact H2d) SPOK ltac:(rewrite (PDS.s0_rp _ _ RP5); exact H8d) ltac:(lia)
           (X64 _ M2 M5 128 _ AG5 ltac:(lia) ltac:(lia) (X64 _ M1 M2 128 _ AG2 ltac:(lia) ltac:(lia) (Y64 128 _ ltac:(lia) C128)))
           (X64 _ M2 M5 96 _ AG5 ltac:(lia) ltac:(lia) (X64 _ M1 M2 96 _ AG2 ltac:(lia) ltac:(lia) (Y64 96 _ ltac:(lia) C96))) RO5
           (X8 _ M2 M5 72 _ AG5 ltac:(lia) ltac:(lia) (X8 _ M1 M2 72 _ AG2 ltac:(lia) ltac:(lia) (Y8 72 _ ltac:(lia) C72)))
           (X8 _ M2 M5 48 _ AG5 ltac:(lia) ltac:(lia) (X8 _ M1 M2 48 _ AG2 ltac:(lia) ltac:(lia) (Y8 48 _ ltac:(lia) C48)))
           (X8 _ M2 M5 24 _ AG5 ltac:(lia) ltac:(lia) (X8 _ M1 M2 24 _ AG2 ltac:(lia) ltac:(lia) (Y8 24 _ ltac:(lia) C24)))).
  { apply (PDS.pd_frame_x _ M2 M5 sp r R AG5); [lia | intros i Hi; apply KH; lia|]. apply (PDS.pd_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; apply KH; lia | exact FRM1]. }
  { exact Hrok. }
  intros fx6 R6 Hfp6 H2f H8f KO6.
  apply (Hcont fx6 R6 M5 model5 LBo cr LBo [(P, 272)] Hfp6).
  - repeat split; reflexivity.
  - apply PDS.rp_final; [rewrite H2f, Hsp; reflexivity | exact H8f |].
    exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (PDS.ko1_rp _ _ RP2)) KO3) KO4) (PDS.ko1_rp _ _ RP5)) KO6).
  - destruct FR5 as [F1 F2]. apply L5C.hpres_intro.
    + intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros X. apply (HO (P, 272) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
    + intros i Hi. apply F2. lia.
    + intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [|rewrite (F1 a Ha HC N HE); exact Hd].
      destruct (CLI a ((PML.ps_bptr ps, PML.ps_bcap ps) :: LBo) (sp - 32) PMS.OPDEL_SCR Y ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(lia)) as [Q1 Q2].
      destruct (CLI a LBo (sp - 32) PMS.OPDEL_SCR Y ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(lia)) as [Q3 Q4].
      apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP5 Ha Q3 Q4). apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP2 Ha Q1 Q2). apply MG1. exact Hd.
  - exact (L5C.model_but_vm_trans _ _ _ BV2 BV5).
  - exact HH5.
Qed.
End H.
End PD.
