(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallPtX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module XIK.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section K.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Variables sp P V E S2 SCR : Z.
Hypothesis OBJS : PMX.objs_x L sp P V E S2.
Hypothesis STKX : hl_ceil L + SCR <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ 0 <= SCR.
Set Default Proof Using "LAY OBJS STKX".      (* [comment removed for export] *)

Definition xinv (M1 : mem) (g1 : PMES.eghost) : Prop := PMES.enc_inv M1 V S2 g1 /\ PML.lits_ok M1.
Definition gblocks (g1 : PMES.eghost) : Prop := forall b, In b (PMES.g_lbv g1) -> block_range L (fst b) (snd b).

Lemma gblocks_of_hi_heap : forall HI own LBo' g1 cr1 (M1 : mem) vm, heap_iface_ok L SCFG HI -> hi_heap HI (own ++ LBo' ++ PMES.g_lbv g1) cr1 M1 vm -> gblocks g1.
Proof.
  intros HI own LBo' g1 cr1 M1 vm HIok HH1 b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
  apply (Hwf b). apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

Lemma GEOMX : (sp <= V /\ V + 408 <= hl_sptop L /\ V mod 8 = 0) /\ (sp <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0) /\ (sp <= P /\ P + 272 <= hl_sptop L) /\ (sp <= E /\ E + 16 <= hl_sptop L) /\
  0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ hl_sptop L - 2 ^ 23 + SCR <= sp <= hl_sptop L /\ 0 <= SCR /\
  PML.apart P 272 V 408 /\ PML.apart P 272 S2 24 /\ PML.apart V 408 S2 24 /\ PML.apart V 408 E 16 /\ PML.apart S2 24 E 16.
Proof.
  pose proof OBJS as ((OP1 & OP2 & OP3) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & (OE1 & OE2 & OE3) & AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
  destruct STKX as (T1 & T2 & T3 & T4). unfold PMES.ENC_SIZE, hl_ceil in *. repeat split; try assumption; lia.
Qed.

Lemma xinv_keep : forall (M1 M2 : mem) g1, gblocks g1 ->
  (forall a, (V <= a < V + PMES.ENC_SIZE \/ S2 <= a < S2 + 24 \/ in_block (PMES.g_lbv g1) a \/ PML.LIT_LO <= a < PML.LIT_HI) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 HB HAG [HINV HLIT]. pose proof GEOMX as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & _ & G4 & G5 & G6 & _). split.
  - apply (SPTX.enc_inv_keep L M1 M2 V S2 g1 ltac:(clear -G4; unfold hl_ceil; lia) ltac:(clear -OV1 G5 G4 G6; lia) ltac:(clear -OV2 G4; unfold PMES.ENC_SIZE; lia) ltac:(clear -OS1 G5 G4 G6; lia) ltac:(clear -OS2 G4; lia) HB); [|exact HINV].
    intros a Ha. apply HAG. clear -Ha. unfold PMES.ENC_SIZE in *. destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha].
  - apply (PML.lits_ok_agree M1 M2); [|exact HLIT]. intros a Ha. apply HAG. right. right. right. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma inv_stretch : forall (F : list SGP.region) (Pb : expr) E' (M1 M' : mem) g1,
  (forall r, In r F -> r = (EVar 2, - SCR, ELit SCR) \/ r = (Pb, 0, ELit 272)) -> uv E' (EVar 2) = sp -> uv E' Pb = P ->
  (forall a : word, SGP.outside E' F a -> M' a = M1 a) -> gblocks g1 -> xinv M1 g1 -> xinv M' g1.
Proof.
  intros F Pb E' M1 M' g1 HF U2 UP HFR HB HX. unfold uv, PB.uv in U2, UP. cbn [edenot] in U2.
  pose proof GEOMX as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & (OP1 & OP2) & _ & G4 & G5 & G6 & AP1 & AP2 & _). unfold PML.apart in AP1, AP2.
  apply (xinv_keep M1 M' g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G5 G6; lia | clear -Ha OS1 OS2 G4 G5 G6; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  apply HFR. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin. rewrite (L5.unsigned_lit a) by exact Ra.
  destruct (HF _ Hin) as [X|X]; injection X as -> -> ->; unfold estart, elenZ; cbn [a_base a_off edenot].
  - rewrite U2. rewrite u64_of_Z by (clear -G4 G5 G6; lia).
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 G6; lia | clear -Ha OS1 G6; lia | | clear -Ha G4 G5 G6; unfold PML.LIT_LO, PML.LIT_HI in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 G5. unfold hl_ceil in B4. lia.
  - rewrite UP. rewrite u64_of_Z by (clear; lia).
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha AP1; lia | clear -Ha AP2; lia | | clear -Ha OP1 G4 G5 G6; unfold PML.LIT_LO, PML.LIT_HI in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 G5 G6 OP1. unfold hl_ceil in B4. lia.
Qed.

(* [comment removed for export] *)
Definition wc_ok2 (Wc : list L5.range) : Prop :=
  forall w, In w Wc -> (fst w + snd w <= V \/ V + PMES.ENC_SIZE <= fst w) /\ (fst w + snd w <= S2 \/ S2 + 24 <= fst w) /\
                      (hl_ceil L <= fst w \/ (hl_img_lo L <= fst w /\ fst w + snd w <= hl_img_hi L /\ (fst w + snd w <= PML.LIT_LO \/ PML.LIT_HI <= fst w))).

(* [comment removed for export] *)
Lemma inv_frame_but2 : forall (M1 M2 : mem) g1 spc scr (Wc : list L5.range),
  L5.frame_but ((spc - scr, scr) :: Wc) M1 M2 -> spc <= sp -> hl_ceil L + scr <= spc -> wc_ok2 Wc -> gblocks g1 -> xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 spc scr Wc HFB Hspc Hscr HW HB HX.
  pose proof GEOMX as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & _ & G4 & G5 & G6 & _).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (xinv_keep M1 M2 g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G5 G6; lia | clear -Ha OS1 OS2 G4 G5 G6; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  apply HFB. intros w Hw. rewrite (L5.unsigned_lit a) by exact Ra. destruct Hw as [<-|Hw].
  - unfold L5.in_rng. cbn [fst snd]. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 Hspc; lia | clear -Ha OS1 Hspc; lia | | clear -Ha Hscr G4 G5; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 Hscr. lia.
  - destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 G4 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B1 B4 W3 ILO IHI. unfold hl_ceil in *. lia.
Qed.

(* [comment removed for export] *)
Lemma inv_hpres : forall (M1 M2 : mem) g1 LBc spc scr (Wc : list L5.range),
  L5C.hpres L LBc spc scr Wc M1 M2 -> incl (PMES.g_lbv g1) LBc -> spc <= sp -> hl_ceil L + scr <= spc -> wc_ok2 Wc -> gblocks g1 -> xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 LBc spc scr Wc (HK & _ & _) Hincl Hspc Hscr HW HB HX.
  pose proof GEOMX as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & _ & G4 & G5 & G6 & _).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LER.
  apply (xinv_keep M1 M2 g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha. apply HK.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G5 G6; lia | clear -Ha OS1 OS2 G4 G5 G6; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  split; [exact Ra|]. split; [|split].
  - destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    + right. left. clear -Ha OV1 Hspc G5 G6 Ra. unfold hl_ceil in *. lia.
    + right. left. clear -Ha OS1 Hspc G5 G6 Ra. unfold hl_ceil in *. lia.
    + left. exists b. split; [exact (Hincl b Hb) | exact Hr].
    + right. right. rewrite ILO, IHI. split; [clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia|]. intros X. pose proof (PmLayout.ly_static L LAY a X). clear -Ha H. unfold PML.LIT_LO, PML.LIT_HI in Ha. lia.
  - unfold in_errno. rewrite LER. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 G5 G4 G6; lia | clear -Ha OS1 G5 G4 G6; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). rewrite ILO, IHI in B1. clear -Hr B1 B3. lia.
  - intros w Hw. destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 G4 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B1 B4 W3 ILO IHI. unfold hl_ceil in *. lia.
Qed.
End K.
End XIK.
