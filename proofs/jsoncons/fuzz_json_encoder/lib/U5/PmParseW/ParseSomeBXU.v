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
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseBridgesX_u5 ParseSomeAt_u5 ParseSomeSem_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeAU ParseSomeBU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKnX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallPtX_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import VisitBridgeX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSBXU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section BX.
Context {SCFG_P : ScfgP}.
Variable I : PSIU.inst.
(* [comment removed for export] *)
Variables (eg : PMES.eghost) (M0c : mem).
Local Abbreviation L := (PSIU.iL I).      Local Abbreviation HI := (PSIU.iHI I).    Local Abbreviation LBo := (PSIU.iLBo I).  Local Abbreviation cr := (PSIU.icr I).
Local Abbreviation sp := (PSIU.isp I).    Local Abbreviation r := (PSIU.ir I).      Local Abbreviation P := (PSIU.iP I).      Local Abbreviation V := (PSIU.iV I).      Local Abbreviation E := (PSIU.iE I).
Local Abbreviation B := (PSIU.iB I).      Local Abbreviation kx := (PSIU.kxe I eg).    Local Abbreviation bx := (PSIU.ibx I).    Local Abbreviation g := (PSIU.ig I).      Local Abbreviation ps := (PSIU.ips I).
Local Abbreviation fx := (PSIU.ifx I).    Local Abbreviation R := (PSIU.iR I).      Local Abbreviation M := (PSIU.iM I).      Local Abbreviation model := (PSIU.imodel I).  Local Abbreviation K := (PSIU.iK I).
Local Abbreviation HIok := (PSIU.iHIok I).  Local Abbreviation LAY := (PSIU.iLAY I).
Local Abbreviation E0 := (PSIU.E0 I).     Local Abbreviation W := (PSIU.W I).       Local Abbreviation Cred := (PSIU.Cred I eg). Local Abbreviation XI := (PSIU.XI I eg).
Local Abbreviation XIv := (PSIU.XIv I eg).  Local Abbreviation LBr := (PSIU.LBr I eg).  Local Abbreviation S2 := (PSIU.iS2 I).
Local Abbreviation seg := (PSIU.seg I).   Local Abbreviation wend := (PSIU.wend I). Local Abbreviation wlen := (PSIU.wlen I). Local Abbreviation st0 := (PSIU.st0 I).  Local Abbreviation more0 := (PSIU.more0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred XIv).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis OKV : CH2V.okV L M LBo sp G.HDECL W M0c.

(* [comment removed for export] *)
Definition wc_okx (Wc : list L5.range) : Prop :=
  forall w, In w Wc -> (fst w + snd w <= V \/ V + PMES.ENC_SIZE <= fst w) /\ (fst w + snd w <= S2 \/ S2 + 24 <= fst w) /\
                      (sp <= fst w \/ (hl_img_lo L <= fst w /\ fst w + snd w <= hl_img_hi L /\ (fst w + snd w <= PML.LIT_LO \/ PML.LIT_HI <= fst w))).
(* [comment removed for export] *)
Lemma gblocks_amb : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> forall b, In b (PMES.g_lbv eg) -> block_range L (fst b) (snd b).
Proof.
  intros i E1 M1 model1 (_ & _ & _ & (cr1 & HH & _) & _ & _) b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
  apply (Hwf b). unfold CH2.cur, PSIU.LBr. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xinv_keep : forall (M1 M2 : mem), (forall b, In b (PMES.g_lbv eg) -> block_range L (fst b) (snd b)) ->
  (forall a, (V <= a < V + PMES.ENC_SIZE \/ S2 <= a < S2 + 24 \/ in_block (PMES.g_lbv eg) a \/ PML.LIT_LO <= a < PML.LIT_HI) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PSIU.xinv I M1 eg -> PSIU.xinv I M2 eg.
Proof.
  intros M1 M2 HB HAG [HINV HLIT]. pose proof (PSIU.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSIU.OBJRX I) as (X1 & X2 & X3 & X4 & _). pose proof (PSIU.SPF I) as (_ & _ & _ & S4 & _).
  pose proof (PSBU.CEIL I) as CL. split.
  - apply (SPTX.enc_inv_keep L M1 M2 V S2 eg ltac:(clear -CL O1 O2 O3; unfold hl_ceil in *; lia) ltac:(clear -X1 O1; lia) ltac:(clear -X2 S4; unfold PMES.ENC_SIZE; lia) ltac:(clear -X3 O1; lia) ltac:(clear -X4 S4; lia) HB); [|exact HINV].
    intros a Ha. apply HAG. clear -Ha. destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha].
  - apply (PML.lits_ok_agree M1 M2); [|exact HLIT]. intros a Ha. apply HAG. right. right. right. exact Ha.
Qed.
(* [comment removed for export] *)
Lemma xinv_hpres : forall i E1 (Mx M1 M2 : mem) model1 LBc spc scr (Wc : list L5.range), HAMB i E1 Mx model1 ->
  L5C.hpres L LBc spc scr Wc M1 M2 -> incl (PMES.g_lbv eg) LBc -> spc <= sp -> hl_ceil L + scr <= spc -> wc_okx Wc -> PSIU.xinv I M1 eg -> PSIU.xinv I M2 eg.
Proof.
  intros i E1 Mx M1 M2 model1 LBc spc scr Wc HA (HK & _ & _) Hincl Hspc Hscr HW HX. pose proof (gblocks_amb i E1 Mx model1 HA) as HB.
  pose proof (PSIU.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSIU.OBJRX I) as (X1 & X2 & X3 & X4 & _). pose proof (PSIU.SPF I) as (_ & _ & _ & S4 & _). pose proof (PSBU.CEIL I) as CL.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LER.
  apply (xinv_keep M1 M2 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha. apply HK.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha X1 X2 O1 S4; lia | clear -Ha X3 X4 O1 S4; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 CL O1 O2 O3. unfold hl_ceil in *. lia. }
  split; [exact Ra|]. split; [|split].
  - destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    + right. left. clear -Ha X1 Hspc CL O1 Ra. unfold hl_ceil in *. lia.
    + right. left. clear -Ha X3 Hspc CL O1 Ra. unfold hl_ceil in *. lia.
    + left. exists b. split; [exact (Hincl b Hb) | exact Hr].
    + right. right. rewrite ILO, IHI. split; [clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia|]. intros X. pose proof (PmLayout.ly_static L LAY a X). clear -Ha H. unfold PML.LIT_LO, PML.LIT_HI in Ha. lia.
  - unfold in_errno. rewrite LER. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha X1 O1; lia | clear -Ha X3 O1; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). rewrite ILO, IHI in B1. clear -Hr B1 B3. lia.
  - intros w Hw. destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 S4 O1 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B1 B3 B4 W3 CL O1. unfold hl_ceil in *. lia.
Qed.
(* [comment removed for export] *)
Lemma xinv_frame_but : forall i E1 (Mx M1 M2 : mem) model1 spc scr (Wc : list L5.range), HAMB i E1 Mx model1 ->
  L5.frame_but ((spc - scr, scr) :: Wc) M1 M2 -> spc <= sp -> hl_ceil L + scr <= spc -> wc_okx Wc -> PSIU.xinv I M1 eg -> PSIU.xinv I M2 eg.
Proof.
  intros i E1 Mx M1 M2 model1 spc scr Wc HA HFB Hspc Hscr HW HX. pose proof (gblocks_amb i E1 Mx model1 HA) as HB.
  pose proof (PSIU.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSIU.OBJRX I) as (X1 & X2 & X3 & X4 & _). pose proof (PSIU.SPF I) as (_ & _ & _ & S4 & _). pose proof (PSBU.CEIL I) as CL.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (xinv_keep M1 M2 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha X1 X2 O1 S4; lia | clear -Ha X3 X4 O1 S4; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 CL O1 O2 O3. unfold hl_ceil in *. lia. }
  apply HFB. intros w Hw. rewrite (L5.unsigned_lit a) by exact Ra. destruct Hw as [<-|Hw].
  - unfold L5.in_rng. cbn [fst snd]. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha X1 Hspc; lia | clear -Ha X3 Hspc; lia | | clear -Ha Hscr S4 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 Hscr. lia.
  - destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 S4 O1 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B1 B3 B4 W3 CL O1. unfold hl_ceil in *. lia.
Qed.
End BX.
End PSBXU.
