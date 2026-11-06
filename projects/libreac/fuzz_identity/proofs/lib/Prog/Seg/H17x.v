From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H17x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma IRb_mk : forall g nm tk dp regs mem R' m',
  NC g nm tk dp regs mem -> KM [] mem m' -> OUTS g nm tk dp m' -> cstr mem (spk g 48) (n_EXP_DP (g_in g)) ->
  YK11.getr regs 18 = Z_to_bv 64 (t_out (g_in g)) ->
  YK11.getr R' 9 = Z_to_bv 64 (t_in (g_in g)) -> YK11.getr R' 18 = YK11.getr regs 18 ->
  YK11.getr R' 19 = Z_to_bv 64 (t_row (g_in g)) ->
  YK11.getr R' 20 = YK11.getr regs 20 -> YK11.getr R' 21 = YK11.getr regs 21 ->
  YK11.getr R' 22 = YK11.getr regs 22 -> YK11.getr R' 23 = YK11.getr regs 23 ->
  YK11.getr R' 24 = YK11.getr regs 24 -> YK11.getr R' 25 = Z_to_bv 64 (n_r (g_in g)) ->
  YK11.getr R' 27 = Z_to_bv 64 (t_cap_disp (g_in g)) ->
  IRb g nm tk dp R' m'.
Proof.
  intros g nm tk dp regs mem R' m' HNC KMm HO HDP E18 F9 F18 F19 F20 F21 F22 F23 F24 F25 F27.
  destruct HNC as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E26 & E19 & HROW & HNM).
  unfold IRb. split; [apply KMm; [exact I | exact HID]|].
  split; [exact F9|]. split; [rewrite F18; exact E18|]. split; [exact F19|].
  split; [rewrite F20; exact E20|]. split; [rewrite F21; exact E21|]. split; [rewrite F22; exact E22|].
  split; [rewrite F23; exact E23|]. split; [rewrite F24; exact E24|]. split; [exact F25|].
  split; [exact F27|]. split; [exact HO|].
  intros _. split; apply KMm; (exact I || assumption).
Qed.

Ltac fin17 :=
  lazymatch goal with
  | HSTK0 : Frame.stk rsegs (normalize rsegs ?mem) _ _, E2 : YK11.getr ?regs 2 = _,
    HRO : ro_agree rsegs ?mem, HNC : NC ?g ?nm ?tk ?dp ?regs ?mem,
    HFR : FR _ _ _ _ ?g _ _ ?L ?A ?regs ?mem ?md, HPM : Permutation (blocks ?L ?A) _,
    HOU : OUTS ?g ?nm ?tk ?dp ?mem, HDP : cstr ?mem _ (n_EXP_DP _), E18 : YK11.getr ?regs 18 = _,
    E23 : YK11.getr ?regs 23 = _, Hr : n_r _ = _ |- _ =>
    apply fin_nomem; [exact HSTK0 | rewrite E2; reflexivity | reflexivity | reflexivity |];
    let R' := fresh "R'" in let m' := fresh "m'" in let HG := fresh "HG" in let HREL := fresh "HREL" in
    intros R' m' HG HREL;
    apply (IRb_mk g nm tk dp regs mem R' m' HNC
      (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL)
      (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
        (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HOU) HDP E18);
    rewrite HG; try rewrite Hr; first [reflexivity | rewrite E23; reflexivity]
  end.

Lemma seg_H17_ac8 : Hcut B APIf ra (Inv_K13b18 B APIf ra empty) -> Hcut B APIf ra (Inv_K13ac8 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13b18. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H17 & HCN & HD1 & HD0).
  pose proof H17 as (HNC & E9 & E18 & E8 & E27 & HDP).
  pose proof HNC as (HNB & E26 & E19 & HROW & HNM).
  pose proof HNB as (HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU).
  pose proof (n_ln_le (g_in g) HW) as HLN.
  assert (HA0 : PropExec.v_sltu (Z_to_bv 64 0) (YK11.getr regs 10) =
    Z_to_bv 64 (if has_dash (n_EXP_NM (g_in g)) then 1 else 0)).
  { destruct (has_dash (n_EXP_NM (g_in g))) eqn:Ed.
    - apply sltu0_nz. apply HD1. reflexivity.
    - rewrite (HD0 eq_refl). reflexivity. }
  assert (HLT : n_lt (g_in g) = n_ln (g_in g) - (if has_dash (n_EXP_NM (g_in g)) then 1 else 0)) by reflexivity.
  assert (HLT0 : n_ln (g_in g) - 1 <= n_lt (g_in g) <= n_ln (g_in g))
    by (rewrite HLT; destruct (has_dash (n_EXP_NM (g_in g))); lia).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HROW)) as RROW.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HCD)) as RCD.
  unfold spk, fsp, SLOT_FRAME in RROW, RCD.
  unfold rmk, Frame.mkR. rewrite E2, E19, E25, E26, E23, E8, E27.
  step. rewrite HA0.
  step. rewrite sub_wrap. rewrite <- HLT.
  step. step.
  rewrite bv_ltu_lit by lia.
  destruct (Z.ltb_spec (n_lt (g_in g)) (t_cap_tok (g_in g))) as [HLTC|HLTC]; cbn [negb].
  - step. rewrite (sub_lit_neg _ 5) by lia. replace (ld2 (g_in g) + 5) with (n_ld (g_in g)) by lia.
    step. step. rewrite sltu_lit by lia. step. step.
    destruct (nr_cases (g_in g)) as [Hr|Hr]; rewrite Hr.
    + if_true. destruct (nr0_fits (g_in g) Hr) as (_ & _ & _ & HLD).
      rewrite (proj2 (Z.ltb_lt _ _) HLD).
      step. step. if_false. step. if_false. fin17.
    + if_false. step. rewrite bv_ltu_lit by lia.
      destruct (Z.ltb_spec (n_ld (g_in g)) (t_cap_disp (g_in g))) as [HLD|HLD].
      { exfalso. pose proof (fits_nr (g_in g) HW HCN HLTC HLD). lia. }
      cbn [negb]. step. step. if_true. fin17.
  - assert (Hr : n_r (g_in g) = -1).
    { destruct (nr_cases (g_in g)) as [H0|H0]; [|exact H0].
      destruct (nr0_fits (g_in g) H0) as (_ & _ & H1 & _). lia. }
    rewrite Hr. step. step. step. step. step. if_true. fin17.
Qed.

End H17x.
