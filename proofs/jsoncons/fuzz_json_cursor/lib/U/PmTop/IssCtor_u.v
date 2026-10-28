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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u TopSpecs2_u ReadKit_u ReadBase_u ChunkKit_u IssCtorStretch_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module IC.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.
Lemma al8_add : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a + k) mod 8 = 0.
Proof. intros a k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; apply Z.mod_divide; try lia; assumption. Qed.
Lemma foot_range : forall a, PML.in_foot11 a -> 0xd4df0 <= a < 0xf6a68.
Proof. intros a (iv & Hiv & Hr). unfold PML.ll_foot_csrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv. Qed.
Lemma islandW_foot : forall w a, In w TPS2.island_W -> L5.in_rng w a -> PML.in_foot11 a.
Proof.
  intros w a Hw Hin. unfold TPS2.island_W in Hw. apply in_map_iff in Hw as (iv & <- & Hiv). apply PML.in_prist_foot11. exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
Qed.
Lemma foot_islandW : forall a, PML.in_foot11 a -> exists w, In w (map (fun iv => (fst iv, snd iv - fst iv)) PML.ll_foot_csrc) /\ L5.in_rng w a.
Proof.
  intros a (iv & Hiv & Hr). exists (fst iv, snd iv - fst iv). split; [apply in_map_iff; exists iv; split; [reflexivity | exact Hiv] | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.

Lemma iosb_at_xg2 : forall (K : Z -> Prop) (M M' : mem) B rd rb, TK.samem K M M' -> 0 <= B < 2 ^ 61 -> TK2.cov K (B + 32) 104 -> mem_grows M M' -> PML.iosb_at M B rd rb -> PML.iosb_at M' B rd rb.
Proof.
  intros K M M' B rd rb AG HB HK MG (H32 & H36 & H40 & H48 & Hk & Hd).
  split; [apply (TK2.u32_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact H32]|].
  split; [apply (TK2.u32_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact H36]|].
  split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact H40]|].
  split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact H48]|].
  split; [intros k Hk0; apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact (Hk k Hk0)]|].
  exact (L5.defined_grows M M' _ _ MG Hd).
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis INITF : TPS2.iosb_init_first_spec L.
Hypothesis INITL : TPS2.iosb_init_later_spec L.
Hypothesis SBUF : TPS2.sbuf_ctor_spec L HI.

Theorem iss_ctor_ok : PMS.iss_ctor_spec L HI.
Proof.
  intros LB cr IS so sp r srep0 fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & A1 & A2 & STR & INB & Hn & OIS & OSO & APT & DIS & DSO & STAT & CRD) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). destruct OIS as (OI1 & OI2 & OI3). destruct OSO as (OS1 & OS2 & OS3).
  unfold PML.a0, PML.a1, PML.a2, PML.apart in *.
  set (SCR := 80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR) in *. assert (HSCR : SCR = 9344) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  unfold hl_ceil in *.
  set (B := IS + 120). set (SB := IS + 16).
  set (foot := fun a : Z => (IS <= a < IS + 272) \/ PML.in_foot11 a).
  set (KU := fun a : Z => ~ (sp - SCR <= a < sp) /\ ~ (IS <= a < IS + 272) /\ ~ PML.in_foot11 a).
  set (KU' := fun a : Z => ~ (sp - SCR <= a < sp - 80) /\ ~ (IS <= a < IS + 272) /\ ~ PML.in_foot11 a).
  assert (KUU : forall a, KU a -> KU' a) by (intros a (Z1 & Z2 & Z3); unfold KU'; split; [lia | split; assumption]).
  assert (NKU : forall a, ~ KU a -> (sp - SCR <= a < sp) \/ foot a).
  { intros a Ha. destruct (classic (sp - SCR <= a < sp)) as [Y|N]; [left; exact Y|]. right. destruct (classic (IS <= a < IS + 272)) as [Y2|N2]; [left; exact Y2|].
    right. destruct (classic (PML.in_foot11 a)) as [Y3|N3]; [exact Y3|]. exfalso. apply Ha. unfold KU. tauto. }
  assert (KUlo : forall a, 0x10000 <= a < 0xf8000 -> ~ PML.in_foot11 a -> KU a) by (intros a Ha Hf; unfold KU; split; [lia | split; [lia | exact Hf]]).
  assert (KUhi : forall a, sp <= a -> ~ (IS <= a < IS + 272) -> KU a) by (intros a Ha Hn2; unfold KU; split; [lia | split; [exact Hn2 | intros X; apply foot_range in X; lia]]).
  assert (KUblk : forall b, In b LB -> TK2.cov KU (fst b) (snd b)).
  { intros b Hb i Hi. destruct (BOK b Hb) as (Q0 & Q1 & _ & _ & Q4). rewrite ILO, IHI in Q1. unfold hl_ceil in Q4. unfold KU. split; [lia|]. split; [lia|]. intros X. apply foot_range in X. lia. }
  assert (FR0 : TK2.FR L LB sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).
  assert (RO : PML.img_ro M) by (destruct STAT as [(X & _)|(X & _)]; exact X).

  apply (ICS.s_ic_entry FPM fx R M model K sp IS so r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 A2 ltac:(lia) ltac:(lia) RO ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) DIS OI1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H11a LIVE1 FRM1 KO1 AG1 MG1.
  assert (AG1u : TK.samem KU M M1) by (apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; unfold KU, ICS.KE1 in *; lia).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
  assert (DSC1 : forall scr, 0 <= scr -> 80 + scr <= SCR -> L5C.stk (hl_sptop L) M1 (sp - 80) scr).
  { intros scr Q1 Q2. apply (CK.sub_stk _ M M1 sp SCR _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | lia | lia | exact Q1]. }
  assert (OB : PML.obj_on_stack L (sp - 80) B 152) by (unfold B; split; [lia | split; [lia | apply al8_add; [exact OI3 | reflexivity]]]).
  assert (DB1 : L5.defined M1 B 152) by (apply (L5.defined_grows _ _ _ _ MG1); unfold B; eapply L5.defined_sub; [exact DIS | lia | lia]).

  assert (AFTER : forall (fx2 : FPState) R2 M2, PML.fp_ok fx2 -> regs_preserved R1 R2 -> TK.samem KU' M1 M2 -> mem_grows M1 M2 -> PML.iosb_at M2 B 0 SB -> PMS.statics_mid M2 ->
                    srealizes RSEGS SCFG (@PML.cfg fx2 R2 ICT.R_INIT M2 model) K).
  { intros fx2 R2 M2 Hfp2 RP2 AG2 MG2 IOSB2 SM2.
    assert (AG02 : TK.samem KU M M2) by exact (CK.samem_weaken2 _ _ _ _ _ _ AG1u AG2 (fun a Ha => conj Ha (KUU a Ha))).
    assert (MG02 : mem_grows M M2) by (intros z Hz; apply MG2, MG1; exact Hz).
    apply (ICS.s_ic_r_init FPM fx2 R2 M2 model K sp IS so Hh Hl Hfp2 ltac:(rewrite (ICS.sp_rp _ _ RP2); exact H2a) SPOK (ICS.ic_live_keep R1 R2 IS so (ICS.sv_rp _ _ RP2) LIVE1) ltac:(lia) ltac:(lia)
             (L5.defined_grows _ _ _ _ MG02 DIS)).
    intros fx3 R3 M3 Hfp3 H2c H1c H10c H11c H12c KO3 CVT CVI AG3 MG3.
    assert (AG3u : TK.samem KU M2 M3) by (apply (TK.samem_weaken _ _ _ _ AG3); intros a Ha; unfold KU, ICS.KE2 in *; lia).
    assert (AG03 : TK.samem KU M M3) by exact (CK.samem_weaken2 _ _ _ _ _ _ AG02 AG3u (fun a Ha => conj Ha Ha)).
    assert (MG03 : mem_grows M M3) by (intros z Hz; apply MG3, MG02; exact Hz).
    assert (HH3 : hi_heap HI LB cr M3 (m_vmmaps model)).
    { apply (TK2.heap_pure_write L HI HIok LAY _ _ M M3 _ KU HH ltac:(lia) AG03 MG03). intros a Ha NK. destruct (NKU a NK) as [X|[X|X]]; [left; unfold hl_ceil; lia | left; unfold hl_ceil; lia | right; apply foot_range in X; lia]. }
    assert (FR3 : TK2.FR L LB sp SCR foot M M3) by exact (TK2.FR_grows L LAY LB sp SCR foot M M M3 KU FR0 AG03 MG03 BOK ltac:(unfold hl_ceil; lia) ltac:(lia) NKU).
    assert (SM3 : PMS.statics_mid M3) by (apply (TK2.statics_mid_x _ M2 M3 AG3); [apply CK.statics_cov_lo; intros a Ha; unfold ICS.KE2; lia | exact SM2]).
    assert (IOSB3 : PML.iosb_at M3 B 0 SB) by (apply (iosb_at_xg2 _ M2 M3 B 0 SB AG3); [unfold B; lia | intros i Hi; unfold ICS.KE2, B in *; lia | exact MG3 | exact IOSB2]).
    assert (STR3 : PML.str_at_w M3 so srep0).
    { apply (TK2.str_at_w_x KU M M3 AG03); [lia | | exact STR]. split; [intros i Hi; apply KUhi; lia|]. destruct srep0 as [s|cap p s]; [exact I|].
      pose proof (INB (p, cap) (or_introl eq_refl)) as Hb. destruct (BOK _ Hb) as (Q0 & _ & _ & _ & Q4). cbn [fst snd] in Q0, Q4. unfold hl_ceil in Q4. split; [lia|]. split; [lia|]. exact (KUblk _ Hb). }
    assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO3 4%bv ltac:(ck_in)), (RP2 4%bv ltac:(ck_in)); exact TP1).
    assert (STK3 : L5C.stk (hl_sptop L) M3 (sp - 80) TPS2.SBUF_SCR).
    { split; [apply CK.al16; [exact S1 | reflexivity]|]. split; [unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia|]. split; [lia|]. split; [exact S4|]. intros i Hi. apply (proj2 FR3).
      unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. lia. }
    destruct SM3 as (RO3 & LQ3 & GL3 & SG3 & EC3).

    apply (SBUF LB cr SB so (sp - 80) ICT.R_SBUF srep0 fx3 R3 M3 model K HH3 (conj Hh (conj Hl Hmat)) HK0 Hfp3).
    { split; [exact (CK.mk_entry L R3 M3 (sp - 80) _ _ H1c (ra_ok_lit ICT.R_SBUF eq_refl) H2c TP3 STK3)|]. split; [exact H10c|]. split; [exact H11c|]. split; [exact H12c|]. split; [exact STR3|].
      split; [exact INB|]. split; [exact Hn|]. split; [unfold SB; split; [lia | split; [lia | apply al8_add; [exact OI3 | reflexivity]]]|]. split; [split; [lia | split; [exact OS2 | exact OS3]]|].
      split; [unfold PML.apart, SB; lia|]. split; [apply (L5.defined_grows _ _ _ _ MG03); unfold SB; eapply L5.defined_sub; [exact DIS | lia | lia]|]. split; [exact (L5.defined_grows _ _ _ _ MG03 DSO)|]. split; [exact GL3|]. split; [exact RO3 | exact CRD]. }
    intros fx4 R4 M4 model4 LB4 cr4 LBk4 W4 Hfp4 (rep & CHR & SBA & -> & -> & FRESH & NOBLK & ->) RP4 HP4 BV4 HH4.
    pose proof (TK2.hpres_samem L LAY LB (sp - 80) _ _ M3 M4 HP4 BOK STK3 ltac:(unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia)) as AG4.
    assert (KH : forall a, sp - 80 <= a -> ~ (SB <= a < SB + 104) -> TK2.keepH L LB [(SB, 104)] (sp - 80) TPS2.SBUF_SCR a).
    { intros a Ha Hn4. split; [intros w [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia | left; exact Ha]. }
    assert (MOK4 : PML.model_ok model4) by (split; [rewrite (L5C.halted_but_vm _ _ BV4); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV4); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV4); exact Hmat]]).
    destruct MOK4 as (Hh4 & Hl4 & _).

    apply (ICS.s_ic_r_sbuf FPM fx4 R4 M4 model4 K sp r R Hh4 Hl4 Hfp4 ltac:(rewrite (ICS.sp_rp _ _ RP4); exact H2c) SPOK).
    { apply (ICS.ic_frame_x _ M3 M4 sp r R AG4); [lia | intros i Hi; apply KH; unfold SB; lia|]. apply (ICS.ic_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; unfold ICS.KE2; lia|].
      apply (ICS.ic_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; unfold KU'; split; [lia | split; [lia | intros X; apply foot_range in X; lia]] | exact FRM1]. }
    { exact Hrok. }
    intros fx5 R5 Hfp5 H2e SS5 KO5.
    apply (Hcont fx5 R5 M4 model4 (PML.srep_blocks rep ++ LB) cr4 LB ((IS, 272) :: map (fun iv => (fst iv, snd iv - fst iv)) PML.ll_foot_csrc) Hfp5).
    - exists rep. split; [exact CHR|].
      split.
      { unfold TPS2.sbuf_at in SBA. unfold SB in SBA. destruct SBA as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & CST & C88 & C96).
        replace (IS + 16 + 8) with (IS + 24) in C8 by lia. replace (IS + 16 + 16) with (IS + 32) in C16 by lia. replace (IS + 16 + 24) with (IS + 40) in C24 by lia.
        replace (IS + 16 + 32) with (IS + 48) in C32 by lia. replace (IS + 16 + 40) with (IS + 56) in C40 by lia. replace (IS + 16 + 48) with (IS + 64) in C48 by lia.
        replace (IS + 16 + 56) with (IS + 72) in C56 by lia. replace (IS + 16 + 88) with (IS + 104) in C88 by lia. replace (IS + 16 + 96) with (IS + 112) in C96 by lia.
        replace (IS + 16 + 64) with (IS + 80) in * by lia.
        unfold PML.isrc_at. cbn zeta.
        split; [apply (TK2.u64_x _ M3 M4 AG4); [lia | intros i Hi; apply KH; unfold SB; lia | exact CVT]|].
        split; [exact C0|]. split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32|].
        split; [pose proof (Zle_0_nat (length (PML.srep_chars rep))); lia|].
        split; [exact C40|]. split; [exact C48|]. split; [exact C56|]. split; [exact CST|]. split; [exact C88|]. split; [exact C96|].
        split; [apply (TK2.u64_x _ M3 M4 AG4); [lia | intros i Hi; apply KH; unfold SB; lia | exact CVI]|].
        split; [apply (TK2.iosb_at_x _ M3 M4 AG4); [unfold B; lia | intros i Hi; apply KH; unfold SB, B in *; lia | exact IOSB3]|].
        split; [left; reflexivity|].
        intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (IS + i) HP4 ltac:(lia));
          [right; left; unfold hl_ceil; unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | apply MG03; apply DIS; exact Hi]. }
      split.
      { apply (TK2.statics_mid_x _ M3 M4 AG4); [|exact (conj RO3 (conj LQ3 (conj GL3 (conj SG3 EC3))))]. apply TK2.statics_cov_keepH. intros a Ha w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold SB in Hin.
        destruct Ha as [Ha|Ha]; [apply foot_range in Ha; lia | unfold PML.IMG_RO_HI in Ha; lia]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact FRESH|]. split; [exact NOBLK | reflexivity].
    - apply ICS.rp_final; [rewrite H2e, Hsp; reflexivity | exact SS5 |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (ICS.ko8_rp _ _ RP2)) KO3) (ICS.ko8_rp _ _ RP4)) KO5).
    - assert (FR4 : TK2.FR L LB sp SCR foot M M4).
      { apply (TK2.FR_hpres L LAY LB sp SCR foot M M3 M4 LB (sp - 80) _ _ FR3 HP4 BOK (incl_refl _)); [unfold hl_ceil; lia | lia | lia | unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | lia
          | unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia |].
        intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. right. left. unfold SB in Hin. lia. }
      destruct FR4 as [F1 F2]. apply L5C.hpres_intro.
      + intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros [X|X].
        * apply (HO (IS, 272) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
        * destruct (foot_islandW a X) as (w & Hw & Hin). exact (HO w (or_intror Hw) Hin).
      + intros i Hi. apply F2. lia.
      + intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [|rewrite (F1 a Ha HC N HE); exact Hd].
        apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP4 Ha); [| exact HE | apply MG03; exact Hd].
        destruct Y as [Y|Y]; [right; left; unfold hl_ceil; unfold TPS2.SBUF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia|]. right. right. apply foot_range in Y. rewrite ILO, IHI.
        split; [lia | intros Z0; apply (PmLayout.ly_static L LAY) in Z0; lia].
    - exact BV4.
    - exact HH4. }
  destruct STAT as [LS0|SM].
  -
    apply (INITF B SB (sp - 80) ICT.R_INIT fx1 R1 M1 model K Hh Hl HK0 Hfp1).
    { split; [exact (CK.mk_entry L R1 M1 (sp - 80) _ _ H1a (ra_ok_lit ICT.R_INIT eq_refl) H2a TP1 (DSC1 (16 + PMS.ISLAND_SCR) ltac:(unfold PMS.ISLAND_SCR; lia) ltac:(unfold PMS.ISLAND_SCR; lia)))|].
      split; [exact H10a|]. split; [exact H11a|]. split; [unfold SB; lia|].
      split; [apply (TK2.ls_ok_x _ M M1 AG1); [apply CK.statics_cov_lo; intros a Ha; unfold ICS.KE1; lia | exact LS0]|]. split; [exact OB | exact DB1]. }
    intros fx2 R2 M2 Hfp2 (IOSB2 & (G1 & G2 & EG & CG & AC & D0 & D1 & LQ)) RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
    assert (OUT2 : forall a, KU' a -> L5.outside ((sp - 80 - (16 + PMS.ISLAND_SCR), 16 + PMS.ISLAND_SCR) :: (B, 136) :: TPS2.island_W) a).
    { intros a (Z1 & Z2 & Z3) w Hw Hin. destruct Hw as [<-|[<-|Hw]]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold PMS.ISLAND_SCR in Hin; lia | unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold B in Hin; lia |].
      exact (Z3 (islandW_foot w a Hw Hin)). }
    apply (AFTER fx2 R2 M2 Hfp2 RP2 (TK.samem_weaken _ _ _ _ AG2 OUT2) MG2 IOSB2).
    split.
    { apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | | apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold ICS.KE1; lia | exact RO]].
      intros i Hi. apply OUT2. apply KUU. apply KUlo; [unfold PML.IMG_RO_HI in Hi; lia | intros X; apply foot_range in X; unfold PML.IMG_RO_HI in Hi; lia]. }
    split; [exact LQ|]. split; [split; [exact G1 | exact G2]|]. split; [left; split; [exact D0 | exact D1] | exists PML.LS1; split; [discriminate|]; split; [exact EG|]; split; [exact CG | exact AC]].
  -
    pose proof SM as (_ & _ & GL & _).
    apply (INITL B SB (sp - 80) ICT.R_INIT fx1 R1 M1 model K Hh Hl HK0 Hfp1).
    { split; [exact (CK.mk_entry L R1 M1 (sp - 80) _ _ H1a (ra_ok_lit ICT.R_INIT eq_refl) H2a TP1 (DSC1 TPS2.IOSBI_SCR ltac:(unfold TPS2.IOSBI_SCR; lia) ltac:(unfold TPS2.IOSBI_SCR; lia)))|].
      split; [exact H10a|]. split; [exact H11a|]. split; [unfold SB; lia|].
      assert (SM1 : PMS.statics_mid M1) by (apply (TK2.statics_mid_x _ M M1 AG1); [apply CK.statics_cov_lo; intros a Ha; unfold ICS.KE1; lia | exact SM]).
      destruct SM1 as (RO1 & _ & GL1 & _). split; [exact GL1|]. split; [exact RO1|]. split; [exact OB | exact DB1]. }
    intros fx2 R2 M2 Hfp2 IOSB2 RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
    assert (OUT2 : forall a, KU' a -> L5.outside [(sp - 80 - TPS2.IOSBI_SCR, TPS2.IOSBI_SCR); (B, 136)] a).
    { intros a (Z1 & Z2 & Z3) w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [unfold TPS2.IOSBI_SCR in Hin; lia | unfold B in Hin; lia]. }
    apply (AFTER fx2 R2 M2 Hfp2 RP2 (TK.samem_weaken _ _ _ _ AG2 OUT2) MG2 IOSB2).
    apply (TK2.statics_mid_x _ M1 M2 AG2); [|apply (TK2.statics_mid_x _ M M1 AG1); [apply CK.statics_cov_lo; intros a Ha; unfold ICS.KE1; lia | exact SM]].
    apply CK.statics_cov_lo. intros a Ha w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [unfold TPS2.IOSBI_SCR in Hin; lia | unfold B in Hin; lia].
Qed.
End H.
End IC.
