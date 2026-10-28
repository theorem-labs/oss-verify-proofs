(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmCurSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u ChunkKit_u ChunkBase_u ChunkStretch_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CHKC.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Definition hid (P : Prop) : Prop := P.
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.

Section XferC.
Variable K : Z -> Prop.
Variables M M' : mem.
Hypothesis AG : TK.samem K M M'.
Hypothesis MG : mem_grows M M'.
Lemma rdc_upd : forall Rr IS ch bof bof' de', 0 <= Rr < 2 ^ 59 ->
  TK2.cov K Rr 256 -> TK2.cov K (Rr + 264) 16 -> TK2.cov K (Rr + 297) 23 ->
  PML.u64 M' (Rr + 280) de' -> ch <= de' <= ch + 16384 -> PML.u64 M' (Rr + 288) 0 -> PML.u8 M' (Rr + 296) (PML.b2z bof') ->
  PMCS.rdc_at M Rr IS ch bof -> PMCS.rdc_at M' Rr IS ch bof'.
Proof.
  intros Rr IS ch bof bof' de' HR HK1 HK2 _ C280 Hde C288 C296 ((A240 & A248 & A264 & A272 & _ & _ & _ & (st0 & Aio) & A32) & Adef).
  assert (X1 : forall off v, 0 <= off -> off + 8 <= 256 -> PML.u64 M (Rr + off) v -> PML.u64 M' (Rr + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact H]. }
  assert (X2 : forall off v, 264 <= off -> off + 8 <= 280 -> PML.u64 M (Rr + off) v -> PML.u64 M' (Rr + off) v).
  { intros off v H1 H2 H. apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK2 | lia | lia] | exact H]. }
  unfold PMCS.rdc_at, PMCS.src_at.
  split; [|exact (L5.defined_grows _ _ _ _ MG Adef)].
  split; [apply X1; [lia | lia | exact A240]|]. split; [apply X1; [lia | lia | exact A248]|]. split; [apply X2; [lia | lia | exact A264]|]. split; [apply X2; [lia | lia | exact A272]|].
  split; [exists de'; split; [exact C280 | exact Hde]|]. split; [exact C288|]. split; [exact C296|].
  split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK1 | lia | lia] | exact Aio]|].
  apply X1; [lia | lia | exact A32].
Qed.
End XferC.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis XSGETN : TPS.xsgetn_spec L.
Hypothesis DETECT : TPS.detect_json_spec L.
Hypothesis SETEC : PMS.set_ec_spec L.

Theorem read_chunk_c_ok : PMCS.read_chunk_c_spec L.
Proof.
  intros sp r Rr IS E ch gp rdst rep bof g fx R M model K Hh Hl HK0 Hfp
         (EN & A0 & A1 & RDR & ISRC & EC & LS & G0 & Hn & OR & OI & OE & AP1 & AP2 & AP3 & BR & DD & BLK) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  destruct OR as (OR1 & OR2 & OR3). destruct OI as (OI1 & OI2 & OI3). destruct OE as (OE1 & OE2 & OE3). pose proof BR as (B1 & B2 & B3 & B4 & B5).
  pose proof LAY as [Y1 _ _ _ _ _ Y7 Y8 _ _ _ _ _ _]. rewrite Y7, Y8 in B2. unfold PMCS.RCHUNK_SCR in *. unfold hl_ceil in *. unfold PML.apart in AP1, AP2, AP3.
  unfold PML.a0, PML.a1 in A0, A1. clear B4.
  change (hid (Rr + 592 <= E \/ E + 16 <= Rr)) in AP2. change (hid (IS + 272 <= E \/ E + 16 <= IS)) in AP3. change (hid (ch + 16384 <= 65536 \/ 1015808 <= ch)) in B2.
  pose proof RDR as ((A240 & A248 & A264 & A272 & (de & A280 & Hde) & A288 & A296 & Aio & A32) & Adef).
  pose proof ISRC as ISRC0. unfold PML.isrc_at in ISRC0. cbv zeta in ISRC0.
  destruct ISRC0 as (I0 & I16 & _ & _ & _ & _ & Ig & _ & _ & _ & Is & _ & _ & _ & (J32 & J36 & J40 & _) & Ird & Idef).
  replace (IS + 120 + 32) with (IS + 152) in J32 by lia. replace (IS + 120 + 36) with (IS + 156) in J36 by lia. replace (IS + 120 + 40) with (IS + 160) in J40 by lia.
  set (D := PML.srep_data (IS + 80) rep) in *. set (n := Z.of_nat (length (PML.srep_chars rep))) in *.
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  assert (SRC : CS.src_cells M Rr IS) by (split; [exact A240 | split; [exact A248 | split; [exact I0 | exact I16]]]).
  assert (RO : PML.img_ro M) by exact (proj1 LS).
  assert (Hde64 : 0 <= de < 2 ^ 64) by lia.

  assert (SCV : forall KX : Z -> Prop, (forall a, a < sp - 512 -> ~ (ch <= a < ch + 16384) -> ~ (0x10000 <= a < 0xf8000) -> KX a) -> (forall i, IS + 80 <= i < IS + 104 -> KX i) -> TK2.str_cov KX (IS + 80) rep).
  { intros KX HX1 HX2. split; [intros i Hi; apply HX2; lia|]. destruct rep as [s | cap p s]; [exact I|].
    destruct (BLK (p, cap) (or_introl eq_refl)) as ((P1 & P2 & P3 & P4 & P5) & AP). cbn [fst snd] in *. unfold PML.apart in AP. rewrite Y7, Y8 in P2.
    split; [lia|]. split; [lia|]. intros i Hi. apply HX1; lia. }
  assert (STC : forall KX : Z -> Prop, (forall a, 0x10000 <= a < 0xf8000 -> KX a) -> TK2.statics_cov KX) by exact CK.statics_cov_lo.

  set (KT := fun a : Z => ~ (sp - 512 <= a < sp) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 297) /\ ~ (IS + 40 <= a < IS + 48) /\ ~ (IS + 152 <= a < IS + 156) /\
                        ~ (ch <= a < ch + 16384)).
  set (W := [(Rr, 304); (IS, 272); (E, 16); (ch, 16384); (0xd4df8, 2); (0xf6848, 544)]).
  assert (KTW : forall a, L5.outside ((sp - 512, 512) :: W) a -> KT a).
  { intros a Ha. unfold KT. pose proof (Ha (sp - 512, 512) ltac:(ck_in)) as X1. pose proof (Ha (Rr, 304) ltac:(ck_in)) as X2. pose proof (Ha (IS, 272) ltac:(ck_in)) as X3.
    pose proof (Ha (ch, 16384) ltac:(ck_in)) as X4. unfold L5.in_rng in *. cbn [fst snd] in *. lia. }

  assert (FIN : forall (fx' : FPState) R' M' p k gp' rdst' bof', PML.fp_ok fx' -> regs_preserved R R' -> TK.samem KT M M' -> mem_grows M M' ->
                  getr R' 10%bv = Z_to_bv 64 p -> getr R' 11%bv = Z_to_bv 64 k -> 0 <= p -> p + k < 2 ^ 64 -> 0 <= k <= 16384 -> (0 < k -> ch <= p /\ p + k <= ch + 16384) ->
                  PMCS.rdc_at M' Rr IS ch bof' -> PML.isrc_at M' IS rep gp' rdst' -> gp <= gp' -> k <= gp' - gp -> (k = 0 -> rdst' = 2) ->
                  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model) K).
  { intros fx' R' M' p k gp' rdst' bof' Hfp' RP AG MG Q1 Q2 Q3 Q4 Q5 Q6 RDR' ISRC' Q7 Q8 Q9.
    apply (Hcont fx' R' M' Hfp'); [| exact RP | exact (CK.samem_frame_but KT _ M M' AG KTW) | exact MG].
    exists p, k, gp', rdst', 0, bof', g. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
    split; [exact RDR'|]. split; [exact ISRC'|]. split; [exact Q7|]. split; [exact Q8|]. split; [intros _; exact Q9|].
    split; [apply (TK2.ec_at_x KT M M' AG); [lia | intros i Hi; unfold KT; unfold hid in AP2, AP3; clear - Hi AP2 AP3 OE1 OE2 B5 S2 S3; lia | exact EC]|].
    split; [apply (TK2.ls_ok_x KT M M' AG); [apply STC; intros a Ha; unfold KT; unfold hid in B2; clear - Ha B2 S2 S3 S4 OR1 OI1; lia | exact LS] | left; reflexivity]. }
  apply (CS.s_rc_entry FPM fx R M model K sp Rr E IS ch rdst de (PML.b2z bof) r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 ltac:(lia) ltac:(lia) OI3 ltac:(lia) ltac:(lia) Ird Hde64
           ltac:(destruct bof; cbn; lia) SRC
           ltac:(apply RB.u32_u8_low; [lia | lia | lia | exact J32]) RO A288 A264 A272 A280 A296
           ltac:(eapply L5.defined_sub; [exact Adef | lia | lia]) ltac:(eapply L5.defined_sub; [exact Adef | lia | lia]) ltac:(eapply L5.defined_sub; [exact S5 | lia | lia])
           ltac:(lia) ltac:(lia) ltac:(lia)).
  -
    intros NE fx' R' M' Hfp' H2' H10' H11' KR C280' C288' AG MG.
    assert (RD2 : rdst = 2) by (destruct Ird as [-> | ->]; [exfalso; apply NE; reflexivity | reflexivity]). clear Ird.
    assert (AGT : TK.samem KT M M') by (apply (TK.samem_weaken _ _ _ _ AG); intros a Ha; unfold KT in Ha; lia).
    apply (FIN fx' R' M' 0 0 gp rdst bof Hfp'); try lia; try assumption.
    + apply CK.rp_of_keeps; [rewrite H2', Hsp; reflexivity | exact KR].
    + apply (rdc_upd _ M M' AG MG Rr IS ch bof bof de); [lia | intros i Hi; cbn beta; lia | intros i Hi; cbn beta; lia | intros i Hi; cbn beta; lia | exact C280' | exact Hde | |  | exact RDR].
      * exact C288'.
      * apply (TK2.u8_x _ M M' AG); [lia | intros i Hi; cbn beta; lia | exact A296].
    + apply (TK2.isrc_at_x _ M M' AG); [lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact ISRC].
  -
    intros Z0 fx1 R1 M1 Hfp1 H2a H1a H10a H11a H12a FBL FBF C280a KO1 AG1 MG1.
    assert (RD0 : rdst = 0) by (destruct Ird as [-> | ->]; [reflexivity | discriminate Z0]). clear Ird.
    assert (ISRC1 : PML.isrc_at M1 IS rep gp rdst) by (apply (TK2.isrc_at_x _ M M1 AG1); [lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact ISRC]).
    assert (RO1 : PML.img_ro M1) by (apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; cbn beta; clear - Hi S2 S3 S4 OR1; lia | exact RO]).
    assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
    apply (XSGETN (sp - 96) CKT.FB_R_XSGETN IS ch gp rdst rep fx1 R1 M1 model K Hh Hl HK0 Hfp1).
    { split; [apply (CK.mk_entry L R1 M1 (sp - 96) _ _ H1a (ra_ok_lit CKT.FB_R_XSGETN eq_refl) H2a TP1); apply (CK.sub_stk _ M M1 sp 512 _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | unfold TPS.XSGETN_SCR; lia | lia | unfold TPS.XSGETN_SCR; lia]|].
      split; [exact H10a|]. split; [exact H11a|]. split; [exact H12a|]. split; [exact ISRC1|]. split; [exact RO1|]. split; [exact Hn|].
      split; [split; [lia | split; [lia | exact OI3]]|]. split; [exact BR|]. split; [exact (L5.defined_grows _ _ _ _ MG1 DD)|]. exact BLK. }
    intros fx2 R2 M2 Hfp2 (k0 & A0b & Hk0 & ISRC2) RP2 FB2 MG2. unfold TPS.XSGETN_SCR in FB2. fold D n in Hk0. unfold PML.a0 in A0b.
    assert (K0R : 0 <= k0 <= 16384 /\ k0 <= D + n - gp) by lia. clear Hk0.
    pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
    assert (OUT2 : forall a, ~ (sp - 96 - 96 <= a < sp - 96) -> ~ (IS + 40 <= a < IS + 48) -> ~ (ch <= a < ch + 16384) -> L5.outside [(sp - 96 - 96, 96); (IS + 40, 8); (ch, 16384)] a).
    { intros a X1 X2 X3 w Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia. }
    pose proof ISRC2 as ISRC2'. unfold PML.isrc_at in ISRC2'. cbv zeta in ISRC2'.
    destruct ISRC2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (J32b & J36b & J40b & _) & _ & Idef2).
    replace (IS + 120 + 32) with (IS + 152) in J32b by lia. replace (IS + 120 + 36) with (IS + 156) in J36b by lia. replace (IS + 120 + 40) with (IS + 160) in J40b by lia. rewrite RD0 in J32b.
    assert (AG02 : TK.samem (fun a => ~ (sp - 512 <= a < sp) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 296) /\ ~ (IS + 40 <= a < IS + 48) /\ ~ (ch <= a < ch + 16384)) M M2).
    { apply (CK.samem_weaken2 _ _ _ _ _ _ AG1 AG2). intros a Ha. split; [lia | apply OUT2; lia]. }
    assert (MG02 : mem_grows M M2) by (intros x Hx; apply MG2, MG1; exact Hx).
    apply (CS.s_fb_r_xsgetn FPM fx2 R2 M2 model K sp Rr E IS ch k0 (PML.b2z bof) r R Hh Hl Hfp2).
    { rewrite (CS.sp_rp _ _ RP2). exact H2a. } { exact SPOK. } { exact A0b. } { lia. } { exact (CS.fb_live_rp _ _ _ RP2 FBL). } { lia. } { lia. } { exact OI3. } { lia. } { lia. } { destruct bof; cbn; lia. }
    { apply (CS.fb_frames_x _ M1 M2 sp r R E Rr AG2); [lia | intros i Hi; apply OUT2; lia | exact FBF]. }
    { exact Hrok. } { apply (L5.defined_grows _ _ _ _ MG02). eapply L5.defined_sub; [exact S5 | lia | lia]. }
    { apply (CS.src_cells_x _ M M2 Rr IS AG02); [lia | lia | intros i Hi; cbn beta; lia | intros i Hi; cbn beta; lia | exact SRC]. }
    { exact J32b. } { exact J36b. } { exact J40b. } { eapply L5.defined_sub; [exact Idef2 | lia | lia]. }
    { apply (TK.img_clear_samem _ M M2 _ _ AG02); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; cbn beta; unfold hid in B2; clear - Hi B2 S2 S3 S4 OR1 OI1; lia | exact RO]. }
    { apply (L5.defined_grows _ _ _ _ MG02). eapply L5.defined_sub; [exact Adef | lia | lia]. }
    { apply (TK.u64_samem _ M1 M2 _ _ AG2); [lia | intros i Hi; apply OUT2; lia | exact C280a]. }
    { apply (TK.u8_samem _ M M2 _ _ AG02); [lia | cbn beta; lia | exact A296]. }
    { apply (L5.defined_grows _ _ _ _ MG02). eapply L5.defined_sub; [exact Adef | lia | lia]. }
    { lia. } { lia. } { lia. }
    +
      intros _ fx3 R3 M3 Hfp3 H2c H10c H11c SS3 KO3 (P280 & P288 & P152 & AG3 & MG3).
      set (rdst' := if k0 <? 16384 then 2 else 0) in *.
      assert (AGT : TK.samem KT M M3) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG02 AG3); intros a Ha; unfold KT in Ha; lia).
      apply (FIN fx3 R3 M3 ch k0 (gp + k0) rdst' bof Hfp3); try lia; try assumption.
      * apply CS.rp_final; [rewrite H2c, Hsp; reflexivity | exact SS3 |].
        apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (CS.ko_rp _ _ RP2)) KO3).
      * intros x Hx. apply MG3, MG02. exact Hx.
      * apply (rdc_upd _ M M3 AGT ltac:(intros x Hx; apply MG3, MG02; exact Hx) Rr IS ch bof bof (ch + k0));
          [lia | intros i Hi; unfold KT; lia | intros i Hi; unfold KT; lia | intros i Hi; unfold KT; lia | exact P280 | lia | exact P288 | | exact RDR].
        apply (TK.u8_samem _ M2 M3 _ _ AG3); [lia | cbn beta; lia|]. apply (TK.u8_samem _ M M2 _ _ AG02); [lia | cbn beta; lia | exact A296].
      * apply (CB.isrc_at_setrd _ M2 M3 AG3 MG3 IS rep (gp + k0) rdst rdst'); [lia | intros i Hi; cbn beta; lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact P152 | | exact ISRC2].
        unfold rdst'. destruct (k0 <? 16384); [right | left]; reflexivity.
      * intros Hk. unfold rdst'. destruct (Z.ltb_spec k0 16384); [reflexivity | lia].
    +
      intros K0P BOF fx3 R3 M3 Hfp3 H2c H1c H10c H11c LIVE3 FRM3 KO3 (P280 & P288 & P152 & AG3 & MG3).
      set (rdst' := if k0 <? 16384 then 2 else 0) in *.
      assert (BT : bof = true) by (destruct bof; [reflexivity | discriminate BOF]).
      assert (AG03 : TK.samem KT M M3) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG02 AG3); intros a Ha; unfold KT in Ha; lia).
      assert (MG03 : mem_grows M M3) by (intros x Hx; apply MG3, MG02; exact Hx).
      assert (ISRC3 : PML.isrc_at M3 IS rep (gp + k0) rdst').
      { apply (CB.isrc_at_setrd _ M2 M3 AG3 MG3 IS rep (gp + k0) rdst rdst'); [lia | intros i Hi; cbn beta; lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact P152 | | exact ISRC2].
        unfold rdst'. destruct (k0 <? 16384); [right | left]; reflexivity. }
      assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP).
      { rewrite (KO3 4%bv ltac:(ck_in)). rewrite (CS.ko_rp _ _ RP2 4%bv ltac:(ck_in)). exact TP1. }
      assert (RO3 : PML.img_ro M3) by (apply (TK.img_clear_samem _ M M3 _ _ AG03); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold KT; unfold hid in B2; clear - Hi B2 S2 S3 S4 OR1 OI1; lia | exact RO]).
      apply (DETECT (sp - 48) CKT.RC_R_DETECT ch k0 fx3 R3 M3 model K Hh Hl HK0 Hfp3).
      { split; [apply (CK.mk_entry L R3 M3 (sp - 48) _ _ H1c (ra_ok_lit CKT.RC_R_DETECT eq_refl) H2c TP3); apply (CK.sub_stk _ M M3 sp 512 _ _ STK MG03); [apply CK.al16; [exact S1 | reflexivity] | unfold TPS.DETECT_SCR; lia | lia | unfold TPS.DETECT_SCR; lia]|].
        split; [exact H10c|]. split; [exact H11c|]. split; [lia|]. split; [unfold block_range, hl_ceil; rewrite Y7, Y8; unfold hid in B2; clear - B1 B2 B3 B5 K0P K0R; lia|].
        split; [apply (L5.defined_grows _ _ _ _ MG03); eapply L5.defined_sub; [exact DD | lia | lia] | exact RO3]. }
      intros fx4 R4 M4 Hfp4 (p' & A0d & Hp' & Hp4) RP4 FB4 MG4. unfold TPS.DETECT_SCR in FB4. unfold PML.a0 in A0d.
      pose proof (TK2.frame_but_samem _ _ _ FB4) as AG4.
      assert (OUT4 : forall a, ~ (sp - 48 - 64 <= a < sp - 48) -> L5.outside [(sp - 48 - 64, 64)] a).
      { intros a X1 w Hw. unfold L5.in_rng. destruct Hw as [<-|[]]; cbn [fst snd]; lia. }
      assert (AG04 : TK.samem KT M M4) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG03 AG4); intros a Ha; split; [exact Ha | apply OUT4; unfold KT in Ha; lia]).
      assert (MG04 : mem_grows M M4) by (intros x Hx; apply MG4, MG03; exact Hx).
      set (kind := bv_unsigned (getr R4 11%bv)). assert (Hkind : 0 <= kind < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R4 11%bv)) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
      assert (C296d : L5.u8_at RSEGS M4 (Rr + 296) (PML.b2z bof)).
      { apply (TK.u8_samem _ M3 M4 _ _ AG4); [lia | apply OUT4; lia|]. apply (TK.u8_samem _ M2 M3 _ _ AG3); [lia | cbn beta; lia|]. apply (TK.u8_samem _ M M2 _ _ AG02); [lia | cbn beta; lia | exact A296]. }
      apply (CS.s_rc_r_detect FPM fx4 R4 M4 model K sp Rr E k0 ch p' kind (PML.b2z bof) r R Hh Hl Hfp4).
      { rewrite (CS.sp_rp _ _ RP4). exact H2c. } { exact SPOK. } { exact A0d. } { unfold kind. symmetry. apply Z_to_bv_bv_unsigned. } { exact (CS.rc_live2_rp _ _ _ _ _ _ RP4 LIVE3). }
      { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hkind. }
      { apply (CS.rc_frame_x _ M3 M4 sp r R AG4); [lia | intros i Hi; apply OUT4; lia | exact FRM3]. }
      { exact Hrok. } { exact C296d. } { destruct bof; cbn; lia. } { apply (L5.defined_grows _ _ _ _ MG04). eapply L5.defined_sub; [exact Adef | lia | lia]. } { lia. }
      *
        intros fx5 R5 M5 Hfp5 H2e H10e H11e SS5 KO5 C296e AG5 MG5.
        assert (AGT : TK.samem KT M M5) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG04 AG5); intros a Ha; split; [exact Ha | unfold KT in Ha; lia]).
        assert (MGT : mem_grows M M5) by (intros x Hx; apply MG5, MG04; exact Hx).
        assert (AG35 : TK.samem (fun a => ~ (sp - 512 <= a < sp - 48) /\ ~ (Rr + 296 <= a < Rr + 297)) M3 M5).
        { apply (CK.samem_weaken2 _ _ _ _ _ _ AG4 AG5). intros a Ha. split; [apply OUT4; lia | lia]. }
        apply (FIN fx5 R5 M5 p' (k0 + ch - p') (gp + k0) rdst' false Hfp5); try lia; try assumption.
        -- apply CS.rp_final; [rewrite H2e, Hsp; reflexivity | exact SS5 |].
           apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (CS.ko_rp _ _ RP2)) KO3) (CS.ko_rp _ _ RP4)) KO5).
        -- apply (rdc_upd _ M M5 AGT MGT Rr IS ch bof false (ch + k0));
             [lia | intros i Hi; unfold KT; lia | intros i Hi; unfold KT; lia | intros i Hi; unfold KT; lia | | lia | | exact C296e | exact RDR].
           ++ apply (TK.u64_samem _ M3 M5 _ _ AG35); [lia | intros i Hi; cbn beta; lia | exact P280].
           ++ apply (TK.u64_samem _ M3 M5 _ _ AG35); [lia | intros i Hi; cbn beta; lia | exact P288].
        -- apply (TK2.isrc_at_x _ M3 M5 AG35); [lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact ISRC3].
        -- intros Hk. unfold rdst'. destruct (Z.ltb_spec k0 16384); [reflexivity | lia].
      *
        intros fx5 R5 M5 Hfp5 H2e H1e H10e H11e KO5 C296e AG5 MG5. clear FIN.
        assert (AG05 : TK.samem KT M M5) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG04 AG5); intros a Ha; split; [exact Ha | unfold KT in Ha; lia]).
        assert (MG05 : mem_grows M M5) by (intros x Hx; apply MG5, MG04; exact Hx).
        assert (TP5 : getr R5 4%bv = Z_to_bv 64 PML.TP).
        { rewrite (KO5 4%bv ltac:(ck_in)). rewrite (CS.ko_rp _ _ RP4 4%bv ltac:(ck_in)). exact TP3. }
        apply (SETEC E 30 (sp - 48) CKT.RC_R_SETEC g fx5 R5 M5 model K Hh Hl HK0 Hfp5).
        { split; [apply (CK.mk_entry L R5 M5 (sp - 48) _ _ H1e (ra_ok_lit CKT.RC_R_SETEC eq_refl) H2e TP5); apply (CK.sub_stk _ M M5 sp 512 _ _ STK MG05); [apply CK.al16; [exact S1 | reflexivity] | unfold PMS.SETEC_SCR; lia | lia | unfold PMS.SETEC_SCR; lia]|].
          split; [exact H10e|]. split; [exact H11e|]. split; [lia|].
          split; [apply (L5.defined_grows _ _ _ _ MG05); destruct EC as (_ & X & _); exact X|]. split; [split; [lia | split; [lia | exact OE3]]|].
          split; [apply (TK2.ls_ok_x KT M M5 AG05); [apply STC; intros a Ha; unfold KT; unfold hid in B2; clear - Ha B2 S2 S3 S4 OR1 OI1; lia | exact LS] | exact G0]. }
        intros fx6 R6 M6 Hfp6 (EC6 & LS6 & _) RP6 FB6 MG6. unfold PMS.SETEC_SCR in FB6.
        pose proof (TK2.frame_but_samem _ _ _ FB6) as AG6.
        assert (OUT6 : forall a, ~ (sp - 48 - 256 <= a < sp - 48) -> ~ (E <= a < E + 16) -> ~ (0xd4df8 <= a < 0xd4dfa) -> ~ (0xf6848 <= a < 0xf6a68) ->
                         L5.outside [(sp - 48 - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] a).
        { intros a X1 X2 X3 X4 w Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; lia. }
        set (KT6 := fun a : Z => KT a /\ ~ (E <= a < E + 16) /\ ~ (0xd4df8 <= a < 0xd4dfa) /\ ~ (0xf6848 <= a < 0xf6a68)).
        unfold hid in AP2, AP3, B2.
        assert (AGT : TK.samem KT6 M M6).
        { apply (CK.samem_weaken2 _ _ _ _ _ _ AG05 AG6). intros a [Ha Hb]. split; [exact Ha | apply OUT6; unfold KT in Ha; lia]. }
        assert (MGT : mem_grows M M6) by (intros x Hx; apply MG6, MG05; exact Hx).
        assert (AG36 : TK.samem (fun a => ~ (sp - 512 <= a < sp - 48) /\ ~ (Rr + 296 <= a < Rr + 297) /\ ~ (E <= a < E + 16) /\ ~ (0xd4df8 <= a < 0xd4dfa) /\ ~ (0xf6848 <= a < 0xf6a68)) M3 M6).
        { apply (CK.samem_weaken2 _ _ _ _ _ _ (CK.samem_weaken2 _ _ _ _ _ _ AG4 AG5 (fun a Ha => Ha)) AG6). intros a Ha. split; [split; [apply OUT4; lia | lia] | apply OUT6; lia]. }
        apply (CS.s_rc_r_setec FPM fx6 R6 M6 model K sp r R Hh Hl Hfp6).
        { rewrite (CS.sp_rp _ _ RP6). exact H2e. } { exact SPOK. }
        { apply (CS.rc_frame_x _ M3 M6 sp r R AG36); [lia | intros i Hi; cbn beta; lia | exact FRM3]. } { exact Hrok. }
        intros fx7 R7 Hfp7 H2g H10g H11g SS7 KO7.
        apply (Hcont fx7 R7 M6 Hfp7); [| | | exact MGT].
        -- exists 0, 0, (gp + k0), rdst', 30, bof, (PML.regJ g). split; [exact H10g|]. split; [exact H11g|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
           split.
           { apply (rdc_upd _ M M6 AGT MGT Rr IS ch bof bof (ch + k0));
               [lia | intros i Hi; unfold KT6, KT; lia | intros i Hi; unfold KT6, KT; lia | intros i Hi; unfold KT6, KT; lia | | lia | | | exact RDR].
             - apply (TK.u64_samem _ M3 M6 _ _ AG36); [lia | intros i Hi; cbn beta; lia | exact P280].
             - apply (TK.u64_samem _ M3 M6 _ _ AG36); [lia | intros i Hi; cbn beta; lia | exact P288].
             - apply (TK.u8_samem _ M5 M6 _ _ AG6); [lia | apply OUT6; lia | exact C296e]. }
           split; [apply (TK2.isrc_at_x _ M3 M6 AG36); [lia | intros i Hi; cbn beta; lia | apply SCV; intros; cbn beta; lia | exact ISRC3]|].
           split; [lia|]. split; [lia|]. split; [intros X; discriminate X|]. split; [exact EC6|]. split; [exact LS6|]. right. split; [reflexivity | discriminate].
        -- apply CS.rp_final; [rewrite H2g, Hsp; reflexivity | exact SS7 |].
           apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (CS.ko_rp _ _ RP2)) KO3) (CS.ko_rp _ _ RP4)) KO5) (CS.ko_rp _ _ RP6)) KO7).
        -- apply (CK.samem_frame_but KT6 _ M M6 AGT). intros a Ha. split; [apply KTW; exact Ha|].
           pose proof (Ha (E, 16) ltac:(ck_in)) as X1. pose proof (Ha (0xd4df8, 2) ltac:(ck_in)) as X2. pose proof (Ha (0xf6848, 544) ltac:(ck_in)) as X3. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
Qed.
End H.
End CHKC.

