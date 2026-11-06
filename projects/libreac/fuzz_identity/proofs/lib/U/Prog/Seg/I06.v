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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU check_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I06.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis CS : check_str_contract.

Lemma seg_I06 : Hcut B APIf ra (Inv_U13dd0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13dc0 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13dd0. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM ((HI & R0) & E10).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & P2 & _ & _ & HMR & _).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold SLOT_K, SLOT_STACK in P2.
  destruct (HO R0) as (C1 & C2 & C3). destruct (Tac_si.n_r0 _ R0) as [Wk Ft].
  destruct (Tac_si.fits_unfold _ Ft) as (F1 & F2 & F3).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  destruct (slack_ok B APIf ra empty FF L A mem md dp _ (n_EXP_DP (g_in g)) HMR N3 C3) as (sl & SB & SW & SE).
  { unfold bsz, n_ld in *. lia. }
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N3) as [BN1 BN2].
  pose proof (n_ld_le _ Wk) as LD. assert (LD0 : 0 <= n_ld (g_in g)) by (unfold n_ld; lia).
  pose proof (Tac_si.caps_range (g_in g)) as CR.
  unfold rmk, Frame.mkR. rewrite E2, E10, E22, E19.
  step. rewrite Tac_si.sextw_small by lia.
  step. step. step.
  eapply (check_str_call CS) with (r := n_ld (g_in g)) (o := dp) (c := t_cap_disp (g_in g))
    (lo := g_S g - 65536) (str := n_EXP_DP (g_in g)) (slack := sl);
    [ apply ro_agree_inv; exact HMI0 | lia | reflexivity | lia | reflexivity | lia | reflexivity | |
      rewrite MState.unsigned_lit by lia;
      exact (proj1 (Frame.stk_split rsegs _ (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0 ltac:(lia))) |
      rewrite MState.unsigned_lit by lia; unfold CHECK_STR_FRAME; lia | | ].
  - intros _. unfold check_str_ok. rewrite MState.unsigned_lit by lia.
    split; [exact F3|]. split; [reflexivity|]. split; [exact (bytes_at_normalize rsegs mem _ _ HRO SB)|].
    split; [apply Tac_si.nzb_notin, Tac_si.nzb_EXP_DP, Wk|].
    split; [exact SW|]. left. unfold CHECK_STR_FRAME, n_ld in *. lia.
  - intros a Ha. rewrite MState.unsigned_lit in Ha by lia. apply noseg_ro. lia.
  - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO'.
    rewrite MState.unsigned_lit in MU by lia. unfold CHECK_STR_FRAME in MU.
    rewrite (MState.ret_pc_even 0x13dd0) by (lia || reflexivity).
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) [(g_S g - 384 - 16, g_S g - 384)])
      by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
    pose proof (stk_after _ _ _ _ _ HSTK0 MU WM ltac:(lia) ltac:(lia)) as STK1.
    apply (fin_mem g mem regs 0x13dd0 _ _ m' (munch_SWIN g _ _ _ MU FW) WM STK1);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM _ mem m'') by exact (KM_of _ mem m' m'' HRO MU HREL).
    assert (HO' : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM
        (munch_SWIN g _ _ _ MU FW) HREL HO).
    split; [|exact R0].
    apply (IRb_keep g nm tk dp regs mem R' m'' _ HI KMm HO'); try (cbn; unfold spk, fsp, SLOT_FRAME; lia); kr HG.
Qed.

End I06.
