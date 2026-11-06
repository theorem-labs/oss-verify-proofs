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

Section I05.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis SL : strlen_contract.

Lemma seg_I05 : Hcut B APIf ra (Inv_U13dc0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13db8 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13dc0. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM (HI & R0).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  destruct (HO R0) as (C1 & C2 & C3). destruct (Tac_si.n_r0 _ R0) as [Wk Ft].
  destruct (Tac_si.fits_unfold _ Ft) as (F1 & F2 & F3).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  pose proof (Tac_si.tk_len (g_in g)) as TL.
  destruct (slack_ok B APIf ra empty FF L A mem md dp _ (n_EXP_DP (g_in g)) HMR N3 C3) as (sl & SB & SW & SE).
  { unfold bsz, n_ld in *. lia. }
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N3) as [BN1 BN2].
  unfold rmk, Frame.mkR. rewrite E2, E22.
  step. step.
  eapply (strlen_call SL) with (str := n_EXP_DP (g_in g)) (slack := sl);
    [apply ro_agree_inv; exact HMI0 |
     rewrite MState.unsigned_lit by lia; exact (bytes_at_normalize rsegs mem _ _ HRO SB) |
     apply Tac_si.nzb_notin, Tac_si.nzb_EXP_DP, Wk |
     rewrite MState.unsigned_lit by lia; exact SW |].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO'.
  rewrite (MState.ret_pc_even 0x13dc0) by (lia || reflexivity).
  assert (STK1 : Frame.stk rsegs m' (g_S g - 65536) (g_S g))
    by (apply (Frame.stk_transport rsegs [] _ m' _ _ HSTK0 MU WM); intros x _; left; exact I).
  apply (fin_mem g mem regs 0x13dc0 _ _ m' (munch_SWIN g [] _ _ MU (Forall_nil _)) WM STK1);
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m'' HG HREL. cbv beta.
  assert (KMm : KM [] mem m'') by exact (KM_of [] mem m' m'' HRO MU HREL).
  assert (HO' : OUTS g nm tk dp m'')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM
      (munch_SWIN g [] _ _ MU (Forall_nil _)) HREL HO).
  split; [split; [|exact R0]|].
  - apply (IRb_keep g nm tk dp regs mem R' m'' [] HI KMm HO' I I I I I); kr HG.
  - rewrite HG. greg2. unfold n_ld. reflexivity.
Qed.

End I05.
