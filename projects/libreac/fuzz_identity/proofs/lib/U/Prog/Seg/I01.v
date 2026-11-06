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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU strlen_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis SL : strlen_contract.

Lemma seg_I01 : Hcut B APIf ra (Inv_U13d90 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f34 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13d84 B APIf ra empty).
Proof.
  intros H90 H34 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H90 | exact H34 | | | exact HC | ].
  { intros c' HC'. unfold Inv_U13d90. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13f34. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HI.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  destruct (Tac_si.n_r_cases (g_in g)) as [R0 | R1].
  - destruct (HO R0) as (C1 & C2 & C3). destruct (Tac_si.n_r0 _ R0) as [Wk Ft].
    destruct (Tac_si.fits_unfold _ Ft) as (F1 & F2 & F3).
    destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
    destruct (slack_ok B APIf ra empty FF L A mem md nm _ (n_EXP_NM (g_in g)) HMR N1 C1) as (sl & SB & SW & SE).
    { unfold bsz, n_ln in *. lia. }
    pose proof (blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
    unfold rmk, Frame.mkR. rewrite E2, E25, E20.
    step. eqb_on. step. step.
    eapply (strlen_call SL) with (str := n_EXP_NM (g_in g)) (slack := sl);
      [apply ro_agree_inv; exact HMI0 |
       rewrite MState.unsigned_lit by lia; exact (bytes_at_normalize rsegs mem _ _ HRO SB) |
       apply Tac_si.nzb_notin, Tac_si.nzb_EXP_NM, Wk | rewrite MState.unsigned_lit by lia; exact SW |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO'.
    rewrite (MState.ret_pc_even 0x13d90) by (lia || reflexivity).
    assert (STK1 : Frame.stk rsegs m' (g_S g - 65536) (g_S g))
      by (apply (Frame.stk_transport rsegs [] _ m' _ _ HSTK0 MU WM); intros x _; left; exact I).
    apply (fin_l g mem regs _ _ _ _ _ m' (munch_SWIN g [] _ _ MU (Forall_nil _)) WM STK1);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM [] mem m'') by exact (KM_of [] mem m' m'' HRO MU HREL).
    assert (HO' : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM
        (munch_SWIN g [] _ _ MU (Forall_nil _)) HREL HO).
    split; [split; [|exact R0]|].
    + apply (IRb_keep g nm tk dp regs mem R' m'' [] HI KMm HO' I I I I I); kr HG.
    + rewrite HG. greg2. unfold n_ln. reflexivity.
  - unfold rmk, Frame.mkR. rewrite E2, E25.
    step. eqb_off.
    apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    split; [|split]; kr HG.
Qed.

End I01.
