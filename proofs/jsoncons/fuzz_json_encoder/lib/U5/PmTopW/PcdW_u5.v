(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ReadBase_u5 ChunkKit_u5 PsBase_u5 PcdStretch_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import PsKitW_u5 PcdStretchW_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PCDW.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition hid (P : Prop) : Prop := P.
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.
(* [comment removed for export] *)
Lemma u8_of_defined : forall (M : mem) a, M (Z_to_bv 64 a) <> None -> exists b, L5.u8_at RSEGS M a b /\ 0 <= b <= 255.
Proof.
  intros M a H. destruct (M (Z_to_bv 64 a)) as [b|] eqn:EM; [|contradiction]. exists (bv_unsigned b). split.
  - unfold L5.u8_at. cbn [rdn]. rewrite EM, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range _ b) as X. change (bv_modulus 8) with 256 in X. lia.
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis SETEC : PMS.set_ec_spec L.

Theorem parser_check_done_okw : PMW.parser_check_done_specw L HI STRTOD_SCR PMR.the_rm.
Proof.
  intros LBo cr sp r P V E B kx bx g ps w xaux c fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp
         (EN & (A0 & A1) & PAR & WF & WOK & BB & VIS & EC & LS & G0 & PC & OP & OV & OE & AP1 & AP2 & AP3 & WB & RMC) Hcont.
  cbn [PMW.rm_match PMR.the_rm] in RMC. unfold PMW.inp_win in Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  destruct OP as (OP1 & OP2 & OP3). destruct OE as (OE1 & OE2 & OE3). unfold PML.apart in AP2. clear AP1 AP3 OV.
  pose proof LAY as [Y1 _ _ _ _ _ Y7 Y8 _ _ _ _ _ _]. unfold hl_ceil in *. unfold PML.a0, PML.a1 in A0, A1.
  assert (SCRB : 1024 <= PMS.PF_SCR STRTOD_SCR) by (unfold PMS.PF_SCR; pose proof (Z.le_max_l PMS.OPNEW_SCR STRTOD_SCR); unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *; lia).
  set (SCR := PMS.PF_SCR STRTOD_SCR) in *.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  assert (BOKo : TK2.blocks_ok L LBo) by (intros b Hb; apply BOK; apply in_or_app; right; exact Hb).
  pose proof (BOK _ (or_introl eq_refl)) as (BB0 & BB1 & _ & _ & BB4). pose proof (BOK _ (or_intror (or_introl eq_refl))) as (SB0 & SB1 & _ & _ & SB4). cbn [fst snd] in BB0, BB1, BB4, SB0, SB1, SB4.
  rewrite Y7, Y8 in BB1, SB1. unfold hl_ceil in *.
  change (hid (PML.ps_bptr ps + PML.ps_bcap ps <= 65536 \/ 1040384 <= PML.ps_bptr ps)) in BB1. change (hid (PML.ps_sb ps + PML.ps_scap ps <= 65536 \/ 1040384 <= PML.ps_sb ps)) in SB1.
  change (hid (P + 272 <= E \/ E + 16 <= P)) in AP2.
  pose proof (RB.win_cells M P ps PAR) as (C200 & C192 & Hpe). set (p := RB.wp ps) in *. set (e := RB.we ps) in *.
  pose proof PAR as PAR0. unfold PML.parser_at in PAR0.
  destruct PAR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C96 & C128 & _ & _ & C208 & _ & _ & C211 & _ & _ & _ & _ & _ & _ & C256 & _ & _ & _ & DEFP).
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  assert (RO : PML.img_ro M) by exact (proj1 LS).
  (* [comment removed for export] *)
  assert (WIN : (0 <= p /\ e < 2 ^ 62) /\ (p = e \/ (PML.ps_win ps = Some (p, e) /\ 4096 <= p /\ e <= hl_sptop L - 8388608 /\ forall i, p <= i < e -> M (Z_to_bv 64 i) <> None))).
  { unfold p, e, RB.wp, RB.we, PML.win_ok in *. destruct (PML.ps_win ps) as [[p0 e0]|]; [|split; [lia | left; reflexivity]].
    destruct WOK as (ch & Hin & W1 & W2 & Wd). destruct (BOKo _ Hin) as (Q0 & _ & _ & _ & Q4). cbn [fst snd] in Q0, Q4. unfold hl_ceil in Q4.
    split; [lia|]. right. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros i Hi. replace i with (p0 + (i - p0)) by lia. apply Wd. lia. }
  destruct WIN as [PR WIN].
  (* [comment removed for export] *)
  set (KOK := fun a : Z => ~ (sp - 80 <= a < sp) /\ ~ (P + 200 <= a < P + 208) /\ ~ (P + 211 <= a < P + 212)).
  set (KT := fun a : Z => ~ (sp - 336 <= a < sp) /\ ~ (P + 200 <= a < P + 208) /\ ~ (P + 211 <= a < P + 212) /\ ~ (E <= a < E + 16) /\ ~ (0xdb5c0 <= a < 0xdb5c2) /\ ~ (0xfd058 <= a < 0xfd278)).
  assert (KOKT : forall a, KT a -> KOK a) by (intros a Ha; unfold KT, KOK in *; lia).
  assert (KTW : forall a, L5.outside (PML.W_par P E) a -> ~ (sp - SCR <= a < sp) -> KT a).
  { intros a Ha Hs. unfold KT. pose proof (Ha (P, 272) ltac:(ck_in)) as X1. pose proof (Ha (E, 16) ltac:(ck_in)) as X2. pose proof (Ha (0xdb5c0, 2) ltac:(ck_in)) as X3.
    pose proof (Ha (0xfd058, 544) ltac:(ck_in)) as X4. unfold L5.in_rng in *. cbn [fst snd] in *. lia. }
  (* [comment removed for export] *)
  assert (FIN : forall (fx' : FPState) R' M' q mo' code g', PML.fp_ok fx' -> regs_preserved R R' -> TK.samem KT M M' -> mem_grows M M' ->
                  PML.ps_win ps = Some (p, e) -> p <= q <= e -> L5.u64_at RSEGS M' (P + 200) q -> L5.u8_at RSEGS M' (P + 211) (PML.b2z mo') ->
                  PML.ec_at M' E code -> PML.ls_ok g' M' -> (g' = g \/ (g' = PML.LS2 /\ code <> 0)) ->
                  ((code = 0 /\ q = e /\ mo' = PML.ps_more ps) \/ (code = 4 /\ mo' = false)) ->
                  forallb PMR.is_ws w = (code =? 0) (* [comment removed for export] *) ->
                  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model) K).
  { intros fx' R' M' q mo' code g' Hfp' RP AG MG HWIN Hq C200' C211' EC' LS' GG' CASE SCAN.
    set (ps' := PSB.ps_upd ps (PML.ps_st ps) mo' (PML.ps_stack ps) (Some (q, e))).
    assert (X64 : forall off v, (0 <= off /\ off + 8 <= 200) \/ (212 <= off /\ off + 8 <= 272) -> PML.u64 M (P + off) v -> PML.u64 M' (P + off) v).
    { intros off v Ho H. apply (TK2.u64_x KT M M' AG); [lia | intros i Hi; unfold KT; unfold hid in AP2; clear - Hi Ho AP2 OP1 OP2 S2 S3 S4 SCRB; lia | exact H]. }
    assert (PAR' : PML.parser_at M' P ps').
    { apply (PSB.parser_at_upd KT M M' P ps (PML.ps_st ps) mo' (PML.ps_stack ps) (Some (q, e)) [] PAR AG MG ltac:(lia)).
      - split; [lia|]. split; [lia|]. intros i Hi. unfold KT. unfold hid in BB1. clear - Hi BB0 BB1 BB4 S2 S3 S4 OP1 OE1 SCRB. lia.
      - split; [lia|]. split; [lia|]. intros i Hi. unfold KT. unfold hid in SB1. clear - Hi SB0 SB1 SB4 S2 S3 S4 OP1 OE1 SCRB. lia.
      - intros i Hi. unfold KT. unfold hid in AP2. clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB. lia. - intros i Hi. unfold KT. unfold hid in AP2. clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB. lia.
      - intros i Hi. unfold KT. unfold hid in AP2. clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB. lia. - intros i Hi. unfold KT. unfold hid in AP2. clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB. lia.
      - split; [exact C200'|]. split; [apply (X64 192 e); [lia | exact C192] | lia].
      - apply (TK2.u8_x KT M M' AG); [lia | intros i Hi; unfold KT; unfold hid in AP2; clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB; lia | exact C208].
      - exact C211'.
      - apply (X64 256); [lia | exact C256].
      - rewrite app_nil_r. reflexivity. }
    apply (Hcont fx' R' M' model (PML.ps_blocks ps' ++ LBo) cr LBo (PML.W_par P E) Hfp').
    - exists ps', code, g'. split; [exact PAR'|].
      split; [destruct CASE as [(_ & _ & ->)|(_ & ->)]; [unfold ps'; rewrite PSB.ps_upd_win; apply PSB.wf_upd_win; exact WF | apply PSB.wf_more_false; exact WF]|].
      split.
      { assert (WOK' : PML.win_ok M' LBo ps).
        { apply (RB.win_ok_x KT M M' AG LBo ps); [|exact WOK]. intros b Hb. destruct (BOKo b Hb) as (Q0 & Q1 & _ & _ & Q4). unfold hl_ceil in Q4. rewrite Y7, Y8 in Q1.
          split; [lia|]. split; [lia|]. intros i Hi. unfold KT. clear - Hi Q0 Q1 Q4 S2 S3 S4 OP1 OE1 SCRB. lia. }
        exact (PSB.win_ok_sub M' LBo ps _ _ _ p e q HWIN Hq WOK'). }
      split.
      { apply PSB.buf_bound_upd; [exact BB | | destruct CASE as [(_ & _ & ->)|(_ & ->)]; [right; split; reflexivity | left; reflexivity]].
        unfold PML.winlen, ps'. rewrite HWIN. destruct ps. cbn [PSB.ps_upd PML.ps_win]. lia. }
      split; [exact EC'|].
      split; [intros NZ; destruct CASE as [(Z0 & _)|(_ & ->)]; [contradiction | destruct ps; reflexivity]|].
      split; [exact LS'|]. split; [exact GG'|]. split; [destruct ps; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply PSB.pcredit_upd; exact PC|].
      split.
      { destruct CASE as [(Z0 & Qe & ->)|(Z4 & _)]; [left | right; exact Z4].
        split; [exact Z0|]. split; [unfold PMS.win_exhausted, ps'; destruct ps; cbn [PSB.ps_upd PML.ps_win]; lia|]. destruct ps; repeat split; reflexivity. }
      (* [comment removed for export] *)
      pose proof (PKW.win_bytes_len M ps p e w WB HWIN) as LW.
      assert (WKT : forall a, p <= a < e -> KT a).
      { intros a Ha. unfold KT. unfold PML.win_ok in WOK. rewrite HWIN in WOK. destruct WOK as (ch & Hin & X1 & X2 & _).
        destruct (BOKo _ Hin) as (Q0 & Q1 & _ & Q3 & Q4). cbn [fst snd] in Q0, Q1, Q3, Q4. rewrite Y7, Y8 in Q1. unfold hl_ceil in Q4. unfold hid in AP2.
        clear - Ha X1 X2 Q0 Q1 Q3 Q4 S2 S3 S4 OP1 OE1 SCRB AP2. lia. }
      destruct CASE as [(-> & -> & ->)|(-> & ->)].
      + rewrite Z.eqb_refl in SCAN. rewrite (PKW.pcd_ok c w SCAN). rewrite PKW.w_after_CR. cbn [PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.rm_match PMR.the_rm].
        split; [reflexivity|]. split; [reflexivity|]. intros _. split; [|split].
        * unfold ps'. apply (PKW.rm_match_xfer KT c M M' P ps); [exact RMC | exact AG | lia | | reflexivity | reflexivity | reflexivity].
          intros a Ha. unfold PKW.tokc in Ha. unfold KT. unfold hid in AP2. clear - Ha AP2 OP1 OP2 S2 S3 S4 SCRB. lia.
        * unfold PML.winlen, ps'. rewrite HWIN. destruct ps. cbn [PSB.ps_upd PML.ps_win]. lia.
        * replace (Z.to_nat (Z.of_nat (length w))) with (Z.to_nat (e - p)) by lia.
          unfold ps'. apply (PKW.win_bytes_move M M' ps p e w e KT); [exact WB | exact HWIN | exact AG | exact WKT | lia | lia | lia].
      + change (4 =? 0) with false in SCAN. rewrite (PKW.pcd_err c w SCAN). cbn [PMW.r_code PMW.r_evs]. split; [reflexivity|]. split; [reflexivity|]. intros X. discriminate X.
    - exact RP.
    - apply (CK.hpres_of_samem L LBo sp SCR (PML.W_par P E) KT M M' AG MG STK Y8 BOKo KTW).
    - apply L5C.model_but_vm_refl.
    - assert (HH' : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M' (m_vmmaps model)).
      { apply (TK2.heap_pure_write L HI HIok LAY _ _ M M' _ KT HH ltac:(lia) AG MG). intros a Ha NK. unfold KT in NK. unfold hl_ceil. lia. }
      destruct ps; exact HH'. }
  apply (PS.s_pcd_entry FPM fx R M model K sp P E p e r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) C192 C200 ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) OP1).
  - (* [comment removed for export] *)
    intros EQ fx1 R1 M1 Hfp1 H2a KR1 AG1 MG1.
    apply (Hcont fx1 R1 M1 model (PML.ps_blocks ps ++ LBo) cr LBo (PML.W_par P E) Hfp1).
    + assert (AGK : TK.samem KOK M M1) by (apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; unfold KOK in Ha; lia).
      assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> 0 <= fst b /\ fst b + snd b <= 2 ^ 62 /\ TK2.cov KOK (fst b) (snd b)).
      { intros b Hb. destruct (BOK b Hb) as (Q0 & _ & _ & _ & Q4). unfold hl_ceil in Q4. split; [lia|]. split; [lia|]. intros i Hi. unfold KOK. lia. }
      exists ps, 0, g. split.
      { apply (TK2.parser_at_x _ M M1 AG1); [lia | intros i Hi; cbn beta; lia | | exact PAR].
        split; [lia|]. split; [lia|]. split; [intros i Hi; cbn beta; lia|]. split; [lia|]. split; [lia|]. intros i Hi. cbn beta. lia. }
      split; [exact WF|].
      split; [apply (RB.win_ok_x KOK M M1 AGK LBo ps); [intros b Hb; apply CB; apply in_or_app; right; exact Hb | exact WOK]|].
      split; [exact BB|].
      split; [apply (TK2.ec_at_x _ M M1 AG1); [lia | intros i Hi; cbn beta; lia | exact EC]|].
      split; [intros X; contradiction|].
      split; [apply (TK2.ls_ok_x _ M M1 AG1); [apply TK2.statics_cov_lo; intros a Ha; cbn beta; lia | exact LS]|].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact PC|].
      split; [left; split; [reflexivity|]; split; [apply RB.exhausted_iff; exact EQ|]; repeat split; reflexivity|].
      (* [comment removed for export] *)
      assert (W0 : w = []).
      { unfold PMW.win_bytes in WB. unfold p, e, RB.wp, RB.we in EQ. destruct (PML.ps_win ps) as [[p0 e0]|]; [|exact WB]. destruct WB as (_ & LW & _). destruct w; [reflexivity | cbn in LW; lia]. }
      subst w. rewrite (PKW.pcd_ok c [] eq_refl). rewrite PKW.w_after_CR. cbn [PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.rm_match PMR.the_rm length skipn Z.to_nat].
      split; [reflexivity|]. split; [reflexivity|]. intros _. split; [|split; [change (Z.of_nat 0) with 0; unfold PML.winlen; unfold p, e, RB.wp, RB.we in EQ; destruct (PML.ps_win ps) as [[p0 e0]|]; lia|]].
      * rewrite <- (PSB.ps_upd_same ps). apply (PKW.rm_match_xfer (fun a => ~ (sp - 80 <= a < sp)) c M M1 P ps); [exact RMC | exact AG1 | lia | | reflexivity | reflexivity | reflexivity].
        intros a Ha. unfold PKW.tokc in Ha. cbn beta. clear - Ha OP1 OP2. lia.
      * rewrite skipn_nil. unfold PMW.win_bytes in WB |- *. destruct (PML.ps_win ps) as [[p0 e0]|]; [|reflexivity]. destruct WB as (_ & LW & _). split; [intros i Hi; exfalso; cbn in Hi; lia | split; [exact LW | apply Forall_nil]].
    + apply CK.rp_of_keeps; [rewrite H2a, Hsp; reflexivity | exact KR1].
    + apply (CK.hpres_of_samem L LBo sp SCR (PML.W_par P E) _ M M1 AG1 MG1 STK Y8 BOKo). intros a _ Hs. lia.
    + apply L5C.model_but_vm_refl.
    + apply (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 80) sp HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AG1 MG1).
  - (* [comment removed for export] *)
    intros NE fx1 R1 M1 Hfp1 H2a LIVE1 CUR1 FRM1 KO1 AG1 MG1.
    destruct WIN as [W|(HWIN & W1 & W2 & WD)]; [contradiction|].
    assert (LOOP : forall (n : nat) (fx2 : FPState) R2 M2 q, e - q <= Z.of_nat n -> p <= q < e -> PML.fp_ok fx2 -> getr R2 2%bv = Z_to_bv 64 (sp - 80) ->
                     PS.pcd_live R2 P E -> PS.pcd_cur R2 q e -> PS.pcd_frame M2 sp r R -> TK.keepsR PS.KO4 R R2 -> TK.samem KOK M M2 -> mem_grows M M2 ->
                     L5.u64_at RSEGS M2 (P + 200) q -> L5.u8_at RSEGS M2 (P + 211) (PML.b2z (PML.ps_more ps)) ->
                     forallb PMR.is_ws (firstn (Z.to_nat (q - p)) w) = true (* [comment removed for export] *) ->
                     srealizes RSEGS SCFG (@PML.cfg fx2 R2 PT.LOOP M2 model) K).
    { pose proof (PKW.win_bytes_len M ps p e w WB HWIN) as LW.
      assert (WKOK : forall a, p <= a < e -> KOK a).
      { intros a Ha. unfold KOK. unfold PML.win_ok in WOK. rewrite HWIN in WOK. destruct WOK as (ch & Hin & X1 & X2 & _).
        destruct (BOKo _ Hin) as (Q0 & Q1 & _ & Q3 & Q4). cbn [fst snd] in Q0, Q1, Q3, Q4. rewrite Y7, Y8 in Q1. unfold hl_ceil in Q4.
        clear - Ha X1 X2 Q0 Q1 Q3 Q4 S2 S3 S4 OP1 OE1 SCRB. lia. }
      induction n as [|n IH]; intros fx2 R2 M2 q Hn Hq Hfp2 H2b LIVE2 CUR2 FRM2 KO2 AG2 MG2 C200b C211b PFX; [lia|].
      assert (DB : M2 (Z_to_bv 64 q) <> None) by (apply MG2; apply WD; lia).
      destruct (u8_of_defined M2 q DB) as (b & Cb & Hb).
      pose proof (PKW.win_byte M M2 ps p e w q b KOK WB HWIN AG2 WKOK ltac:(lia) ltac:(lia) Hq Cb ltac:(lia)) as BW.
      assert (X64 : forall off v, (0 <= off /\ off + 8 <= 200) \/ (212 <= off /\ off + 8 <= 272) -> PML.u64 M (P + off) v -> PML.u64 M2 (P + off) v).
      { intros off v Ho H. apply (TK2.u64_x KOK M M2 AG2); [lia | intros i Hi; unfold KOK; lia | exact H]. }
      assert (RO2 : PML.img_ro M2) by (apply (TK.img_clear_samem KOK M M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold KOK; lia | exact RO]).
      apply (PSW.s_pcd_loopw FPM fx2 R2 M2 model K sp P E q e b (PML.b2z (PML.ps_more ps)) Hh Hl Hfp2 H2b SPOK LIVE2 CUR2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb
               ltac:(destruct (PML.ps_more ps); cbn; lia) Cb (X64 128 _ ltac:(lia) C128) (X64 96 _ ltac:(lia) C96) RO2 C211b
               ltac:(apply (L5.defined_grows _ _ _ _ MG2); eapply L5.defined_sub; [exact DEFP | lia | lia])
               ltac:(apply (L5.defined_grows _ _ _ _ MG2); eapply L5.defined_sub; [exact S5 | lia | lia]) OP1 ltac:(lia) OP3).
      - (* [comment removed for export] *)
        intros WSB fx3 R3 M3 Hfp3 H2c LIVE3 CUR3 KO3 C211c AG3 MG3.
        assert (PFX1 : forallb PMR.is_ws (firstn (Z.to_nat (q + 1 - p)) w) = true).
        { replace (Z.to_nat (q + 1 - p)) with (S (Z.to_nat (q - p))) by lia. rewrite PKW.forallb_firstn_S by lia. rewrite PFX, <- BW, WSB. reflexivity. }
        assert (AG03 : TK.samem KOK M M3) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG2 AG3); intros a Ha; split; [exact Ha | unfold KOK in Ha; lia]).
        assert (MG03 : mem_grows M M3) by (intros x Hx; apply MG3, MG2; exact Hx).
        assert (FRM3 : PS.pcd_frame M3 sp r R) by (apply (PS.pcd_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; cbn beta; lia | exact FRM2]).
        apply (PS.s_pcd_inc FPM fx3 R3 M3 model K sp P E q e q r R Hh Hl Hfp3 H2c SPOK LIVE3 CUR3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(apply (TK.u64_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; cbn beta; lia | exact C200b])
                 ltac:(apply (L5.defined_grows _ _ _ _ MG03); eapply L5.defined_sub; [exact DEFP | lia | lia])
                 ltac:(apply (TK.u64_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; cbn beta; lia | exact (X64 192 e ltac:(lia) C192)]) FRM3 Hrok OP1).
        + (* [comment removed for export] *)
          intros QE fx4 R4 M4 Hfp4 H2d SS4 KO4' C200d AG4 MG4.
          assert (AGK : TK.samem KOK M M4) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG03 AG4); intros a Ha; split; [exact Ha | unfold KOK in Ha; lia]).
          assert (AGT : TK.samem KT M M4) by (apply (TK.samem_weaken KOK); [exact AGK | exact KOKT]).
          apply (FIN fx4 R4 M4 (q + 1) (PML.ps_more ps) 0 g Hfp4); try assumption; try lia.
          * apply PS.rp_final; [rewrite H2d, Hsp; reflexivity | exact SS4 |]. exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO2 KO3) KO4').
          * intros x Hx. apply MG4, MG03. exact Hx.
          * apply (TK.u8_samem _ M3 M4 _ _ AG4); [lia | cbn beta; lia | exact C211c].
          * apply (TK2.ec_at_x KOK M M4 AGK); [lia | intros i Hi; unfold KOK; unfold hid in AP2; clear - Hi AP2 OE1 OE2 OP1 S2 S3 S4 SCRB; lia | exact EC].
          * apply (TK2.ls_ok_x KOK M M4 AGK); [apply TK2.statics_cov_lo; intros a Ha; unfold KOK; clear - Ha OP1 S2 S3 S4 SCRB; lia | exact LS].
          * left; reflexivity.
          * left. split; [reflexivity|]. split; [lia | reflexivity].
          * cbn [Z.eqb]. rewrite <- (firstn_all w). replace (length w) with (Z.to_nat (q + 1 - p)) by lia. exact PFX1.
        + (* [comment removed for export] *)
          intros QN fx4 R4 M4 Hfp4 H2d LIVE4 CUR4 KO4' C200d AG4 MG4.
          apply (IH fx4 R4 M4 (q + 1)); try assumption; try lia.
          * apply (PS.pcd_frame_x _ M3 M4 sp r R AG4); [lia | intros i Hi; cbn beta; lia | exact FRM3].
          * exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO2 KO3) KO4').
          * apply (CK.samem_weaken2 _ _ _ _ _ _ AG03 AG4). intros a Ha. split; [exact Ha | unfold KOK in Ha; lia].
          * intros x Hx. apply MG4, MG03. exact Hx.
          * apply (TK.u8_samem _ M3 M4 _ _ AG4); [lia | cbn beta; lia | exact C211c].
      - (* [comment removed for export] *)
        intros NWS fx3 R3 M3 Hfp3 H2c H1c H10c H11c KO3 C211c AG3 MG3.
        assert (AG03 : TK.samem KOK M M3) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG2 AG3); intros a Ha; split; [exact Ha | unfold KOK in Ha; lia]).
        assert (MG03 : mem_grows M M3) by (intros x Hx; apply MG3, MG2; exact Hx).
        assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO3 4%bv ltac:(ck_in)), (KO2 4%bv ltac:(ck_in)); exact Htp).
        apply (SETEC E 4 (sp - 80) PT.R_SETEC g fx3 R3 M3 model K Hh Hl HK0 Hfp3).
        { split; [apply (CK.mk_entry L R3 M3 (sp - 80) _ _ H1c (ra_ok_lit PT.R_SETEC eq_refl) H2c TP3); apply (CK.sub_stk _ M M3 sp SCR _ _ STK MG03); [apply CK.al16; [exact S1 | reflexivity] | unfold PMS.SETEC_SCR; lia | lia | unfold PMS.SETEC_SCR; lia]|].
          split; [exact H10c|]. split; [exact H11c|]. split; [lia|].
          split; [apply (L5.defined_grows _ _ _ _ MG03); destruct EC as (_ & X & _); exact X|]. split; [split; [lia | split; [lia | exact OE3]]|].
          split; [apply (TK2.ls_ok_x KOK M M3 AG03); [apply TK2.statics_cov_lo; intros a Ha; unfold KOK; lia | exact LS] | exact G0]. }
        intros fx4 R4 M4 Hfp4 (EC4 & LS4 & _) RP4 FB4 MG4. unfold PMS.SETEC_SCR in FB4.
        pose proof (TK2.frame_but_samem _ _ _ FB4) as AG4.
        assert (OUT4 : forall a, ~ (sp - 80 - 256 <= a < sp - 80) -> ~ (E <= a < E + 16) -> ~ (0xdb5c0 <= a < 0xdb5c2) -> ~ (0xfd058 <= a < 0xfd278) ->
                         L5.outside [(sp - 80 - 256, 256); (E, 16); (0xdb5c0, 2); (0xfd058, 544)] a).
        { intros a X1 X2 X3 X4 w0 Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; lia. }
        assert (AGT : TK.samem KT M M4) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG03 AG4); intros a Ha; split; [exact (KOKT a Ha) | apply OUT4; unfold KT in Ha; lia]).
        apply (PS.s_pcd_r_setec FPM fx4 R4 M4 model K sp r R Hh Hl Hfp4 ltac:(rewrite (PS.sp_rp _ _ RP4); exact H2c) SPOK).
        { apply (PS.pcd_frame_x _ M3 M4 sp r R AG4); [lia | intros i Hi; apply OUT4; lia|]. apply (PS.pcd_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; cbn beta; lia | exact FRM2]. }
        { exact Hrok. }
        intros fx5 R5 Hfp5 H2e SS5 KO5.
        apply (FIN fx5 R5 M4 q false 4 PML.LS2 Hfp5); try assumption; try lia.
        + apply PS.rp_final; [rewrite H2e, Hsp; reflexivity | exact SS5 |].
          exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO2 KO3) (PS.ko4_rp _ _ RP4)) KO5).
        + intros x Hx. apply MG4, MG03. exact Hx.
        + apply (TK.u64_samem _ M3 M4 _ _ AG4); [lia | intros i Hi; apply OUT4; unfold hid in AP2; clear - Hi AP2 OP1 OP2 S2 S3 S4 SCRB; lia|]. apply (TK.u64_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; cbn beta; lia | exact C200b].
        + apply (TK.u8_samem _ M3 M4 _ _ AG4); [lia | apply OUT4; unfold hid in AP2; clear - AP2 OP1 OP2 S2 S3 S4 SCRB; lia | exact C211c].
        + right. split; [reflexivity | discriminate].
        + cbn [Z.eqb]. apply (PKW.forallb_fail_at PMR.is_ws (Z.to_nat (q - p))); [lia | rewrite <- BW; exact NWS]. }
    apply (LOOP (Z.to_nat (e - p)) fx1 R1 M1 p); try assumption; try lia.
    + apply (TK.samem_weaken _ _ _ _ AG1). intros a Ha. unfold KOK in Ha. lia.
    + apply (TK.u64_samem _ M M1 _ _ AG1); [lia | intros i Hi; cbn beta; lia | exact C200].
    + apply (TK.u8_samem _ M M1 _ _ AG1); [lia | cbn beta; lia | exact C211].
    + rewrite Z.sub_diag. reflexivity.
Qed.
End H.
End PCDW.
