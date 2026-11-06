(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCB PsoSemA PsoSemCA PsoKnCB PsoBaseCB ParseSomeChkCB PsoXiCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOLK.
Section K.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation P := (PSOI.iP I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation ps := (PSOI.ips I).

Lemma pview_in : forall cells v, PSO.pview cells = Some v ->
  In (KWord (SA PE 144) 4 (PSO.v_level v)) cells /\ In (KWord (SA PE 192) 8 (PSO.v_wend v)) cells /\ In (KWord (SA PE 200) 8 (PSO.v_wptr v)) cells /\
  In (KWord (SA PE 208) 1 (PSO.v_st v)) cells /\ In (KWord (SA PE 209) 1 (PSO.v_sst v)) cells /\ In (KWord (SA PE 210) 1 (PSO.v_nst v)) cells /\
  In (KWord (SA PE 211) 1 (PSO.v_more v)) cells /\ In (KWord (SA PE 212) 1 (PSO.v_done v)) cells /\
  In (KWord (SA PE 224) 8 (PSO.v_cap1 v)) cells /\ In (KWord (SA PE 232) 8 (PSO.v_size v)) cells /\ In (KWord (SA PE 240) 8 (PSO.v_bptr v)) cells /\
  In (KWord (SA PE 248) 8 (PSO.v_sb v)) cells /\ In (KWord (SA PE 256) 8 (PSO.v_send v)) cells /\ In (KWord (SA PE 264) 8 (PSO.v_scend v)) cells /\
  (forall e, PSO.v_ec v = Some e -> In (KWord (SA EE 0) 4 e) cells).
Proof.
  intros cells v H. unfold PSO.pview, PSO.cellP in H.
  destruct (CAX.cell_at cells PE 144 4) as [a|] eqn:Ha; [|discriminate]. destruct (CAX.cell_at cells PE 192 8) as [b|] eqn:Hb; [|discriminate].
  destruct (CAX.cell_at cells PE 200 8) as [c|] eqn:Hc; [|discriminate]. destruct (CAX.cell_at cells PE 208 1) as [d|] eqn:Hd; [|discriminate].
  destruct (CAX.cell_at cells PE 209 1) as [e|] eqn:He; [|discriminate]. destruct (CAX.cell_at cells PE 210 1) as [f|] eqn:Hf; [|discriminate].
  destruct (CAX.cell_at cells PE 211 1) as [g|] eqn:Hg; [|discriminate]. destruct (CAX.cell_at cells PE 212 1) as [h|] eqn:Hh; [|discriminate].
  destruct (CAX.cell_at cells PE 224 8) as [k|] eqn:Hk; [|discriminate]. destruct (CAX.cell_at cells PE 232 8) as [l|] eqn:Hl; [|discriminate].
  destruct (CAX.cell_at cells PE 240 8) as [m|] eqn:Hm; [|discriminate]. destruct (CAX.cell_at cells PE 248 8) as [n|] eqn:Hn; [|discriminate].
  destruct (CAX.cell_at cells PE 256 8) as [o|] eqn:Ho; [|discriminate]. destruct (CAX.cell_at cells PE 264 8) as [p|] eqn:Hp; [|discriminate].
  injection H as <-. cbn [PSO.v_level PSO.v_wend PSO.v_wptr PSO.v_st PSO.v_sst PSO.v_nst PSO.v_more PSO.v_done PSO.v_cap1 PSO.v_size PSO.v_bptr PSO.v_sb PSO.v_send PSO.v_scend PSO.v_ec].
  repeat (split; [apply cell_at_has; assumption|]). intros x Hx. apply cell_at_has. exact Hx.
Qed.

Record VRD (Ex : env) (Mx : mem) (v : PSO.pv) : Prop := MKVRD {
  vr_wptr : L5.u64_at (hl_segs L) Mx (P + 200) (CL5A.uv Ex (PSO.v_wptr v));
  vr_st : L5.u8_at (hl_segs L) Mx (P + 208) (CL5A.uv Ex (PSO.v_st v));
  vr_sst : L5.u8_at (hl_segs L) Mx (P + 209) (CL5A.uv Ex (PSO.v_sst v));
  vr_nst : L5.u8_at (hl_segs L) Mx (P + 210) (CL5A.uv Ex (PSO.v_nst v));
  vr_more : L5.u8_at (hl_segs L) Mx (P + 211) (CL5A.uv Ex (PSO.v_more v));
  vr_done : L5.u8_at (hl_segs L) Mx (P + 212) (CL5A.uv Ex (PSO.v_done v));
  vr_size : L5.u64_at (hl_segs L) Mx (P + 232) (CL5A.uv Ex (PSO.v_size v));
  vr_wend : L5.u64_at (hl_segs L) Mx (P + 192) (CL5A.uv Ex (PSO.v_wend v));
  vr_cap1 : L5.u64_at (hl_segs L) Mx (P + 224) (CL5A.uv Ex (PSO.v_cap1 v));
  vr_bptr : L5.u64_at (hl_segs L) Mx (P + 240) (CL5A.uv Ex (PSO.v_bptr v));
  vr_sb : L5.u64_at (hl_segs L) Mx (P + 248) (CL5A.uv Ex (PSO.v_sb v));
  vr_send : L5.u64_at (hl_segs L) Mx (P + 256) (CL5A.uv Ex (PSO.v_send v));
  vr_scend : L5.u64_at (hl_segs L) Mx (P + 264) (CL5A.uv Ex (PSO.v_scend v)) }.
Lemma VIEW_RD : forall Ex A1 m1 (Mx : mem) cells v,
  H_off_segments (hl_segs L) (ahid A1 m1) -> bv_unsigned (ev Ex 10) = P ->
  (forall X, In X cells -> kentry_ok (hl_segs L) Ex (CCA.vis A1 m1 Mx) X) -> PSO.pview cells = Some v -> VRD Ex Mx v.
Proof.
  intros Ex A1 m1 Mx cells v Hoff W10 HK Hv.
  destruct (pview_in cells v Hv) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & _).
  constructor.
  - exact (RD64 I Ex A1 m1 Mx 200 _ Hoff W10 (HK _ I3)).
  - exact (RD8 I Ex A1 m1 Mx 208 _ Hoff W10 (HK _ I4)).
  - exact (RD8 I Ex A1 m1 Mx 209 _ Hoff W10 (HK _ I5)).
  - exact (RD8 I Ex A1 m1 Mx 210 _ Hoff W10 (HK _ I6)).
  - exact (RD8 I Ex A1 m1 Mx 211 _ Hoff W10 (HK _ I7)).
  - exact (RD8 I Ex A1 m1 Mx 212 _ Hoff W10 (HK _ I8)).
  - exact (RD64 I Ex A1 m1 Mx 232 _ Hoff W10 (HK _ I10)).
  - exact (RD64 I Ex A1 m1 Mx 192 _ Hoff W10 (HK _ I2)).
  - exact (RD64 I Ex A1 m1 Mx 224 _ Hoff W10 (HK _ I9)).
  - exact (RD64 I Ex A1 m1 Mx 240 _ Hoff W10 (HK _ I11)).
  - exact (RD64 I Ex A1 m1 Mx 248 _ Hoff W10 (HK _ I12)).
  - exact (RD64 I Ex A1 m1 Mx 256 _ Hoff W10 (HK _ I13)).
  - exact (RD64 I Ex A1 m1 Mx 264 _ Hoff W10 (HK _ I14)).
Qed.

Lemma U8INJ : forall (Mx : mem) a v1 v2, L5.u8_at (hl_segs L) Mx a v1 -> L5.u8_at (hl_segs L) Mx a v2 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> v1 = v2.
Proof.
  intros Mx a v1 v2 H1 H2 R1 R2. unfold L5.u8_at in *. rewrite H1 in H2. injection H2 as H.
  assert (H' : bv_unsigned (Z_to_bv 8 v1) = bv_unsigned (Z_to_bv 8 v2)) by first [exact H | rewrite H; reflexivity].
  rewrite !Z_to_bv_unsigned in H'. unfold bv_wrap in H'. change (bv_modulus 8) with 256 in H'.
  rewrite !Z.mod_small in H' by lia. exact H'.
Qed.

Lemma PA_cells : forall (Mx : mem) psx mw, PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win psx mw) ->
  L5.u8_at (hl_segs L) Mx (P + 208) (PML.ps_st psx) /\ L5.u8_at (hl_segs L) Mx (P + 209) (PML.ps_sst psx) /\ L5.u8_at (hl_segs L) Mx (P + 210) (PML.ps_nst psx) /\
  L5.u8_at (hl_segs L) Mx (P + 211) (PML.b2z (PML.ps_more psx)) /\ L5.u8_at (hl_segs L) Mx (P + 212) (PML.b2z (PML.ps_done psx)) /\
  L5.u64_at (hl_segs L) Mx (P + 200) (PSOI.wlo mw) /\ L5.u64_at (hl_segs L) Mx (P + 192) (PSOI.whi mw) /\
  L5.u64_at (hl_segs L) Mx (P + 232) (Z.of_nat (length (PML.ps_buf psx))) /\ L5.u64_at (hl_segs L) Mx (P + 224) (PML.ps_bcap psx + 1) /\
  L5.u64_at (hl_segs L) Mx (P + 240) (PML.ps_bptr psx) /\ L5.u64_at (hl_segs L) Mx (P + 248) (PML.ps_sb psx) /\
  L5.u64_at (hl_segs L) Mx (P + 256) (PML.ps_sb psx + Z.of_nat (length (PML.ps_stack psx))) /\ L5.u64_at (hl_segs L) Mx (P + 264) (PML.ps_sb psx + PML.ps_scap psx).
Proof.
  intros Mx psx mw H. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in H. destruct psx; cbn in H |- *.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & Hst & Hsst & Hnst & Hmore & Hdone & _ & _ & Hstr & _ & Hsb & Hsend & Hscend & _).
  destruct Hstr as ((_ & Hcap & Hsz & Hbp & _) & _ & _).
  assert (W : L5.u64_at (hl_segs L) Mx (P + 200) (PSOI.wlo mw) /\ L5.u64_at (hl_segs L) Mx (P + 192) (PSOI.whi mw)).
  { destruct mw as [[p e]|]; cbn [PSOI.wlo PSOI.whi]; [destruct Hw as (W1 & W2 & _); split; [exact W1 | exact W2] | destruct Hw as (W1 & W2); split; [exact W2 | exact W1]]. }
  destruct W as [W1 W2]. replace (P + 224 + 8) with (P + 232) in Hsz by lia. replace (P + 224 + 16) with (P + 240) in Hbp by lia.
  repeat split; try assumption.
Qed.

Lemma LINK : forall Ex (Mx : mem) v psx mw,
  VRD Ex Mx v -> PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win psx mw) ->
  0 <= PML.ps_st psx < 256 -> 0 <= PML.ps_sst psx < 256 -> 0 <= PML.ps_nst psx < 256 ->
  0 <= CL5A.uv Ex (PSO.v_st v) < 256 -> 0 <= CL5A.uv Ex (PSO.v_sst v) < 256 -> 0 <= CL5A.uv Ex (PSO.v_nst v) < 256 ->
  0 <= CL5A.uv Ex (PSO.v_more v) < 256 -> 0 <= CL5A.uv Ex (PSO.v_done v) < 256 ->
  0 <= PSOI.wlo mw < 2 ^ 64 -> 0 <= PSOI.whi mw < 2 ^ 64 -> Z.of_nat (length (PML.ps_buf psx)) < 2 ^ 64 ->
  0 <= PML.ps_bptr psx < 2 ^ 64 -> 0 <= PML.ps_sb psx -> PML.ps_sb psx + PML.ps_scap psx < 2 ^ 64 -> 0 <= PML.ps_scap psx -> 0 <= PML.ps_bcap psx -> PML.ps_bcap psx + 1 < 2 ^ 64 ->
  Z.of_nat (length (PML.ps_stack psx)) <= PML.ps_scap psx ->
  CL5A.uv Ex (PSO.v_st v) = PML.ps_st psx /\ CL5A.uv Ex (PSO.v_sst v) = PML.ps_sst psx /\ CL5A.uv Ex (PSO.v_nst v) = PML.ps_nst psx /\
  CL5A.uv Ex (PSO.v_more v) = PML.b2z (PML.ps_more psx) /\ CL5A.uv Ex (PSO.v_done v) = PML.b2z (PML.ps_done psx) /\
  CL5A.uv Ex (PSO.v_wptr v) = PSOI.wlo mw /\ CL5A.uv Ex (PSO.v_wend v) = PSOI.whi mw /\ CL5A.uv Ex (PSO.v_size v) = Z.of_nat (length (PML.ps_buf psx)) /\
  CL5A.uv Ex (PSO.v_cap1 v) = PML.ps_bcap psx + 1 /\ CL5A.uv Ex (PSO.v_bptr v) = PML.ps_bptr psx /\ CL5A.uv Ex (PSO.v_sb v) = PML.ps_sb psx /\
  CL5A.uv Ex (PSO.v_send v) = PML.ps_sb psx + Z.of_nat (length (PML.ps_stack psx)) /\ CL5A.uv Ex (PSO.v_scend v) = PML.ps_sb psx + PML.ps_scap psx.
Proof.
  intros Ex Mx v psx mw VR PA Rst Rsst Rnst Ust Usst Unst Umore Udone Rlo Rhi Rsz Rbp Rsb Rsc Rscap Rbc Rbc1 Rstk.
  destruct VR as [Vwptr Vst Vsst Vnst Vmore Vdone Vsize Vwend Vcap1 Vbptr Vsb Vsend Vscend].
  destruct (PA_cells Mx psx mw PA) as (Ast & Asst & Anst & Amore & Adone & Awlo & Awhi & Asz & Acap & Abp & Asb & Asend & Ascend).
  pose proof UVR as UV.
  assert (B2 : forall b, 0 <= PML.b2z b < 256) by (intros [|]; cbn; lia).
  split; [exact (U8INJ Mx _ _ _ Vst Ast Ust Rst)|]. split; [exact (U8INJ Mx _ _ _ Vsst Asst Usst Rsst)|]. split; [exact (U8INJ Mx _ _ _ Vnst Anst Unst Rnst)|].
  split; [exact (U8INJ Mx _ _ _ Vmore Amore Umore (B2 _))|]. split; [exact (U8INJ Mx _ _ _ Vdone Adone Udone (B2 _))|].
  split; [exact (U64INJ I Mx _ _ _ Vwptr Awlo (UV _ _) Rlo)|]. split; [exact (U64INJ I Mx _ _ _ Vwend Awhi (UV _ _) Rhi)|].
  split; [exact (U64INJ I Mx _ _ _ Vsize Asz (UV _ _) ltac:(lia))|]. split; [exact (U64INJ I Mx _ _ _ Vcap1 Acap (UV _ _) ltac:(lia))|].
  split; [exact (U64INJ I Mx _ _ _ Vbptr Abp (UV _ _) Rbp)|]. split; [exact (U64INJ I Mx _ _ _ Vsb Asb (UV _ _) ltac:(lia))|].
  split; [exact (U64INJ I Mx _ _ _ Vsend Asend (UV _ _) ltac:(lia)) | exact (U64INJ I Mx _ _ _ Vscend Ascend (UV _ _) ltac:(lia))].
Qed.

Lemma PA_UPD : forall (M M' : mem) (Sg : Z -> Prop), (forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall psx mw w2 st2 sst2 nst2 (more2 done2 : bool) buf2,
  PTA.out Sg P 148 -> PTA.out Sg (P + 192) 8 -> PTA.out Sg (P + 216) 4 -> PTA.out Sg (P + 224) 8 -> PTA.out Sg (P + 240) 32 -> PTA.out Sg (PML.ps_sb psx) (PML.ps_scap psx) ->
  PMLA.parser_at (hl_segs L) IC M P (PML.ps_set_win psx mw) ->
  PSOI.whi w2 = PSOI.whi mw -> match w2 with Some (p, e) => p <= e | None => mw = None end ->
  L5.u64_at (hl_segs L) M' (P + 200) (PSOI.wlo w2) ->
  L5.u8_at (hl_segs L) M' (P + 208) st2 -> L5.u8_at (hl_segs L) M' (P + 209) sst2 -> L5.u8_at (hl_segs L) M' (P + 210) nst2 ->
  L5.u8_at (hl_segs L) M' (P + 211) (PML.b2z more2) -> L5.u8_at (hl_segs L) M' (P + 212) (PML.b2z done2) -> L5.u8_at (hl_segs L) M' (P + 213) 1 ->
  L5.u64_at (hl_segs L) M' (P + 232) (Z.of_nat (length buf2)) -> L5.bytes_at (hl_segs L) M' (PML.ps_bptr psx) buf2 ->
  L5.u8_at (hl_segs L) M' (PML.ps_bptr psx + Z.of_nat (length buf2)) 0 -> Z.of_nat (length buf2) < PML.ps_bcap psx ->
  (forall i, 0 <= i < 272 -> M' (Z_to_bv 64 (P + i)) <> None) ->
  PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win (PML.PS st2 sst2 nst2 more2 done2 (PML.ps_level psx) (PML.ps_stack psx) (PML.ps_sb psx) (PML.ps_scap psx)
                                                      (PML.ps_bcap psx) (PML.ps_bptr psx) buf2 (PML.ps_win psx)) w2).
Proof.
  intros M M' Sg AG psx mw w2 st2 sst2 nst2 more2 done2 buf2 O0 O1 O2 O3 O4 OS H Hwhi Hw2 H200 H208 H209 H210 H211 H212 H213 H232 HBY HTERM HLT HDEF.
  unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in *. destruct psx; cbn in H, OS, HBY, HTERM, HLT |- *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  pose proof (PTA.u64_ag (hl_segs L) M M' Sg AG) as U64. pose proof (PTA.u32_ag (hl_segs L) M M' Sg AG) as U32. pose proof (PTA.u8_ag (hl_segs L) M M' Sg AG) as U8.
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A0]|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A1]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A2]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A3]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A4]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A5]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A6]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A7]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A8]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M M' Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A9]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M M' Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A10]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M M' Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A11]|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A12]|]. split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A13]|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A14]|].
  split.
  { destruct w2 as [[p2 e2]|]; cbn [PSOI.wlo PSOI.whi] in *.
    - destruct mw as [[pm em]|]; cbn [PSOI.whi] in Hwhi; [destruct A15 as (_ & Y & _) | destruct A15 as (Y & _)]; subst;
        (split; [exact H200 | split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact Y] | exact Hw2]]).
    - subst mw. destruct A15 as (Y & _). split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact Y] | exact H200]. }
  split; [exact H208|]. split; [exact H209|]. split; [exact H210|]. split; [exact H211|]. split; [exact H212|]. split; [exact H213|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O2); lia | exact A22]|].
  destruct A23 as ((T0 & C1 & _ & C3 & _ & _) & C8 & _). replace (P + 224 + 16) with (P + 240) in C3 by lia.
  split.
  { split; [|split; [exact C8 | exact HLT]]. unfold L5.lstr_long. replace (P + 224 + 8) with (P + 232) by lia. replace (P + 224 + 16) with (P + 240) by lia.
    split; [exact T0|]. split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O3); lia | exact C1]|]. split; [exact H232|].
    split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O4); lia | exact C3]|]. split; [exact HBY | exact HTERM]. }
  split; [exact A24|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O4); lia | exact A25]|]. split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O4); lia | exact A26]|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O4); lia | exact A27]|].
  split; [apply (PTA.bytes_ag (hl_segs L) M M' Sg AG); [apply (PTA.out_sub _ _ _ _ _ OS); lia | exact A28]|]. split; [exact A29|].
  intros i Hi. exact (HDEF i Hi).
Qed.
End K.
End PSOLK.
