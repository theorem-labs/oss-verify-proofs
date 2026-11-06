(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A2 (LK -> LR / CX, the key path; code B
   0x83b1c..0x83c88 and 0x83d6c): exvl_A2, CUT_LK from CUT_CX and CUT_LR (ExvB_Loop_Stmt.v). An array item (c = '[')
   has no name: B 0x83b20 jumps to LR at once. An object member (c = '{'): ExvB_Loop_A2_w.v a2_obj.
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 91, 123 (WORD: ASCII the code compares), 2, 3, 4, 8, 9, 18 .. 27 (WORD: register numbers), 8, 24, 32, 40,
   56 (LENGTH: struct ex / node fields), 4096, 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: address-space bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW YGcallMx YC88 YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_exw ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_sh ExvB_Open_kt ExvB_Loop_kitL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
  ExvB_Loop_A2_ss ExvB_Loop_A2_call ExvB_Loop_A2_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Lemma a2_arr_tag : forall t, PjTree.tag t = 5 -> exists its, t = PjTree.JArr its.
Proof. intros [] H; cbn in H; try discriminate; eexists; reflexivity. Qed.

(* a value read through aview is kept when every byte is *)
Lemma a2_vm_kept : forall H m m' a n v,
  (forall z, 0 <= z < 2 ^ 64 -> aview rsegs H m' z = aview rsegs H m z) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HK Ha Hn Hv. apply (exw_val_kept rsegs H m m'); [|exact Hv]. intros z Hz. apply HK. lia.
Qed.

Ltac a2_zn := try change (Z.of_nat 8) with 8; try change (Z.of_nat 4) with 4; try change (Z.of_nat 1) with 1.

(* ---- the piece ---- *)
Section f. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KCH : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Hypothesis KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Hypothesis KWD : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK.
Hypothesis KOFS : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.
Hypothesis PLS : PURE_L_STEP.
Hypothesis PSUF : PURE_SUFFIX.

Lemma exvl_A2 : forall n m, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_LR (fx := fx) B ARx SK n m) -> forall fx : YK11.FPState, CUT_LK (fx := fx) B ARx SK n m.
Proof using ci HYP KCALL KRUN KCH KROD KWD KOFS PLS PSUF.
intros n m HX HLR fx. unfold CUT_LK.
intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv dlc kid fl tk.
cbv zeta.
intros Hn HP HBs Hi1 Hc Hc2 Hdep Hacc HCUR Hip Hdl Hii Hm HV Hfl Hdif H20 H24 H27 H22 H23 HSP.
pose proof asan_consts as (C1 & _).
pose proof HBs as (regs0 & HB0 & _).
pose proof (a2_geom (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB0)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & (G8a & G8b) & G9 & G10 & G11 & G12 & G13 & _).
destruct Hc2 as [-> | ->].
- (* an array item: no name, LR at once *)
  change (91 =? 123) with false in *.
  apply (a2_run0 (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD E lyc Sc Hpc Wc regs memc mdc k pos _ HP HBs H27).
  intros regs' mem' md' HJ' HPM' KEPT HG HRR.
  assert (HBs' : EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs' mem' md' k pos).
  { apply (KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos regs' mem' md' HP HBs HJ').
    - intros a Ha _ _ _. apply KEPT. exact Ha.
    - exact HG.
    - exact HPM'.
    - intros r Hr _. apply HRR. unfold exv_bregs in Hr. cbn [In] in Hr |- *. tauto. }
  assert (HCUR' : prhex_cur Wc mem' (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc).
  { destruct HCUR as (Vp & Ve & Vd & Vs & Vl).
    repeat split; (eapply a2_vm_kept; [exact KEPT | | | eassumption]); a2_zn; lia. }
  assert (HSP' : exv_spills E Wc mem' lyc pos 91 vv i).
  { destruct HSP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 &
      S18 & S19).
    unfold exv_spills, exv_spill in *. cbv zeta.
    repeat split; (eapply a2_vm_kept; [exact KEPT | | | eassumption]); a2_zn; lia. }
  assert (HCH : kid = 0 \/ exv_child E Wc mem' i kid tk).
  { destruct Hfl as [(Hk0 & _) | (_ & _ & _ & (Hv0 & Hic & Htk & kids & Vk & Hkr & Hkd))]; [left; exact Hk0|].
    right. split; [exact Hv0|]. split; [exact Hic|]. split; [exact Htk|]. exists kids.
    destruct (exvl_kit_node B ARx SK HYP fx E lyc Sc Hpc Wc regs memc mdc k pos HP HBs Hv0)
      as (kids' & _ & _ & _ & _ & N4 & N5 & _).
    split; [|split; [exact Hkr | exact Hkd]].
    eapply a2_vm_kept; [exact KEPT | | | exact Vk]; a2_zn; lia. }
  pose proof (HLR fx E lyc Sc Hpc Wc regs' mem' md' k pos 91 i cap acc ip ip vv dlc kid tk []) as HL.
  cbv zeta in HL. change (91 =? 123) with false in HL.
  apply (HL Hn HP HBs' Hi1 Hc (or_introl eq_refl) Hdep Hacc HCUR' ltac:(lia) ltac:(lia) Hdl Hii ltac:(lia) HV
    eq_refl HCH).
  + intros u dl' Hd Hiff. apply Hdif; [exact Hd|]. rewrite Hiff.
    destruct Hfl as [(Hk0 & _) | (Hf0 & Hvv & Htag & (Hv0 & Hic & Htk & _))].
    * rewrite Hk0.
      split; intros [H | (H & _)]; [left; exact H | exfalso; exact (H eq_refl) | left; exact H |
        exfalso; exact (H eq_refl)].
    * destruct (a2_arr_tag _ Htag) as (its & Et). rewrite Et in Htk |- *. cbn [exv_same exv_kidt] in Htk |- *.
      rewrite <- Htk. tauto.
  + rewrite HRR by (cbn [In]; repeat (first [left; reflexivity | right])). exact H20.
  + rewrite HRR by (cbn [In]; repeat (first [left; reflexivity | right])). exact H27.
  + rewrite HRR by (cbn [In]; repeat (first [left; reflexivity | right])). exact H22.
  + rewrite HRR by (cbn [In]; repeat (first [left; reflexivity | right])). exact H23.
  + exact HSP'.
- (* an object member: the key path *)
  change (123 =? 123) with true in *.
  destruct Hfl as [(Hk0 & Hf1) | (Hf0 & Hvv & Htag & Hch)].
  + refine (a2_obj B ARx SK HYP KCALL KRUN KCH KROD KWD KOFS PLS PSUF n m E i cap acc ip vv dlc kid fl 0 tk (HX fx)
      (HLR fx) Hn HP Hi1 Hc Hdep Hacc Hip Hii Hm HV (or_introl (conj Hk0 Hf1)) Hdif lyc Sc Hpc Wc regs memc mdc k pos
      _ H24).
    unfold a2_st. split; [exact HBs|]. split; [exact H27|]. split; [exact H22|]. split; [exact H23|].
    split; [exact H20|]. split; [exact HSP|]. split; [exact HCUR|]. split; [exact Hip|]. split; [exact Hdl|].
    intros H0. lia.
  + destruct Hch as (Hv0 & Hic & Htk & kids & Vk & Hkr & Hkd).
    destruct (exvl_kit_node B ARx SK HYP fx E lyc Sc Hpc Wc regs memc mdc k pos HP HBs Hv0)
      as (kids' & _ & Vk' & _ & _ & _ & _ & Hkc).
    destruct (Hkc ltac:(lia)) as (K1 & K2).
    assert (Hkk : kids' = kids) by (apply (exvl_val8_det _ _ _ _ Vk' Vk); lia).
    subst kids'.
    assert (Hkn0 : kid <> 0) by lia.
    refine (a2_obj B ARx SK HYP KCALL KRUN KCH KROD KWD KOFS PLS PSUF n m E i cap acc ip vv dlc kid fl kids tk (HX fx)
      (HLR fx) Hn HP Hi1 Hc Hdep Hacc Hip Hii Hm HV
      (or_intror (conj Hf0 (conj Hvv (conj Htag (conj Hv0 (conj Hic (conj Htk (conj Hkr (conj Hkd Hkn0)))))))))
      Hdif lyc Sc Hpc Wc regs memc mdc k pos _ H24).
    unfold a2_st. split; [exact HBs|]. split; [exact H27|]. split; [exact H22|]. split; [exact H23|].
    split; [exact H20|]. split; [exact HSP|]. split; [exact HCUR|]. split; [exact Hip|]. split; [exact Hdl|].
    intros _. exact Vk.
Qed.
End f.

Print Assumptions exvl_A2.
