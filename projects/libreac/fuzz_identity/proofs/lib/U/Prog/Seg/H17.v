From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H17.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma IRb_mk : forall g nm tk dp regs mem R' m',
  H17b g nm tk dp regs mem -> KM [] mem m' -> OUTS g nm tk dp m' ->
  getr R' 9 = getr regs 9 -> getr R' 20 = getr regs 20 -> getr R' 21 = getr regs 21 ->
  getr R' 22 = getr regs 22 -> getr R' 23 = getr regs 23 -> getr R' 24 = getr regs 24 ->
  getr R' 25 = Z_to_bv 64 (n_r (g_in g)) -> getr R' 19 = getr regs 19 ->
  IRb g nm tk dp R' m'.
Proof.
  intros g nm tk dp regs mem R' m' ((HNB & _ & _ & _ & HNM) & _ & HDP) KMm HO F9 F20 F21 F22 F23 F24 F25 F19.
  destruct HNB as (HID & _ & E9 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HQ56 & HQ48 & _).
  unfold IRb. split; [apply KMm; [exact I | exact HID]|].
  split; [rewrite F9; exact E9|].
  rewrite F20, F21, F22, F23, F24, F19, F25.
  split; [apply KMm; [exact I | exact HQ56]|]. split; [apply KMm; [exact I | exact HQ48]|].
  do 7 (split; [first [assumption | reflexivity]|]). split; [exact HO|].
  intros _. split; apply KMm; (exact I || assumption).
Qed.

Ltac fin17 :=
  lazymatch goal with
  | HSTK0 : Frame.stk rsegs (normalize rsegs ?mem) _ _, E2 : getr ?regs 2 = _,
    HRO : ro_agree rsegs ?mem, H17 : H17b ?g ?nm ?tk ?dp ?regs ?mem,
    HFR : FR _ _ _ _ ?g _ _ ?L ?A ?regs ?mem ?md, HPM : Permutation (blocks ?L ?A) _,
    HOU : OUTS ?g ?nm ?tk ?dp ?mem, Hr : n_r _ = _ |- _ =>
    apply fin_nomem; [exact HSTK0 | rewrite E2; reflexivity | reflexivity | reflexivity |];
    let R' := fresh "R'" in let m' := fresh "m'" in let HG := fresh "HG" in let HREL := fresh "HREL" in
    intros R' m' HG HREL;
    apply (IRb_mk g nm tk dp regs mem R' m' H17
      (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL)
      (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
        (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HOU));
    first [kr HG | rewrite HG; greg2; rewrite Hr; reflexivity]
  end.

Lemma H17_d58 : Hcut B APIf ra (Inv_U13d84 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d58 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13d84. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H17 & HCN & HD1 & HD0).
  pose proof H17 as ((HNB & E8 & E26 & E18 & HNM) & E27 & HDP).
  pose proof HNB as (HID & HW & E9 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HQ56 & HQ48 & HOU).
  pose proof (n_ln_le (g_in g) HW) as HLN.
  assert (HA0 : PropExec.v_sltu (Z_to_bv 64 0) (getr regs 10) =
    Z_to_bv 64 (if has_dash (n_EXP_NM (g_in g)) then 1 else 0)).
  { destruct (has_dash (n_EXP_NM (g_in g))) eqn:Ed.
    - apply sltu0_nz. apply HD1. reflexivity.
    - rewrite (HD0 eq_refl). reflexivity. }
  assert (HLT : n_lt (g_in g) = n_ln (g_in g) - (if has_dash (n_EXP_NM (g_in g)) then 1 else 0)) by reflexivity.
  assert (HLT0 : n_ln (g_in g) - 1 <= n_lt (g_in g) <= n_ln (g_in g))
    by (rewrite HLT; destruct (has_dash (n_EXP_NM (g_in g))); lia).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold rmk, Frame.mkR. rewrite E2, E8, E23, E27, E19, E25.
  step. rewrite HA0.
  step. rewrite sub_wrap. rewrite <- HLT.
  step.
  rewrite bv_ltu_lit by lia.
  destruct (Z.ltb_spec (n_lt (g_in g)) (t_cap_tok (g_in g))) as [HLTC|HLTC]; br_if.
  - step. rewrite sltu_lit by lia.
    step.
    destruct (nr_cases (g_in g)) as [Hr|Hr]; rewrite Hr.
    + destruct (nr0_fits (g_in g) Hr) as (_ & _ & _ & HLD).
      rewrite (proj2 (Z.ltb_lt _ _) HLD).
      br_if.
      step. step. eqb_off. step. eqb_off. fin17.
    + eqb_off. step. rewrite bv_ltu_lit by lia.
      destruct (Z.ltb_spec (n_ld (g_in g)) (t_cap_disp (g_in g))) as [HLD|HLD].
      { exfalso. pose proof (fits_nr (g_in g) HW HCN HLTC HLD). lia. }
      br_if. step. step. eqb_on. fin17.
  - assert (Hr : n_r (g_in g) = -1).
    { destruct (nr_cases (g_in g)) as [H0|H0]; [|exact H0].
      destruct (nr0_fits (g_in g) H0) as (_ & _ & H1 & _). lia. }
    rewrite Hr. step. step. step. eqb_on. fin17.
Qed.

Lemma H17_d74 : Hcut B APIf ra (Inv_U13d84 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d74 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13d84. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H17 & HCN).
  pose proof H17 as ((HNB & E8 & E26 & E18 & HNM) & E27 & HDP).
  pose proof HNB as (HID & HW & E9 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HQ56 & HQ48 & HOU).
  assert (Hr : n_r (g_in g) = -1).
  { destruct (nr_cases (g_in g)) as [H0|H0]; [|exact H0].
    destruct (nr0_fits (g_in g) H0) as (_ & H1 & _). lia. }
  unfold rmk, Frame.mkR. rewrite E2, E25, Hr.
  step. step. step. eqb_on. fin17.
Qed.

Lemma seg_H17 : Hcut B APIf ra (Inv_U13d84 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13d58 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13d74 B APIf ra empty).
Proof. intros HX. split; [exact (H17_d58 HX) | exact (H17_d74 HX)]. Qed.

End H17.
