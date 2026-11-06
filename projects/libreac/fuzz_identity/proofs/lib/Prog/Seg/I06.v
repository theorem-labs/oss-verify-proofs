From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import check_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_si.
Import ListNotations.
Open Scope Z_scope.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CS : check_str_contract.

Lemma seg_I06 : Hcut B APIf ra (Inv_K13b64 B APIf ra empty) -> Hcut B APIf ra (Inv_K13b54 B APIf ra empty).
Proof.
  intros H1 g c (nm & tk & dp & L & A & regs & mem & md & -> & HFR & HP & [[HI R0] R10]).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (P1 & P2 & P3 & P4 & HMR & HRO & HSTK & HSW).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold SLOT_K, SLOT_STACK in *.
  destruct (HO R0) as (C1 & C2 & C3). destruct (n_r0 _ R0) as [Wk Ft].
  destruct (fits_unfold _ Ft) as (F1 & F2 & F3).
  destruct (nmb_in _ _ _ _ _ _ HP) as (N1 & N2 & N3).
  pose proof (tk_len (g_in g)) as TL.
  destruct (slack_ok B APIf ra empty FF L A mem md dp _ (n_EXP_DP (g_in g)) HMR N3 C3) as (sl & SB & SW & SE).
  { unfold bsz, n_ln, n_ld in *. lia. }
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N3) as [BN1 BN2].
  pose proof (n_ln_le _ Wk) as LN. pose proof (n_ld_le _ Wk) as LD.
  assert (LT : n_lt (g_in g) <= n_ln (g_in g)) by (unfold n_lt; destruct (has_dash _); lia).
  assert (ST : stk rsegs mem (g_S g - 65536) (fsp g)).
  { destruct (stk_split rsegs mem (g_S g - 65536) (fsp g) (g_S g) HSTK) as [S1 _];
      [unfold fsp, SLOT_FRAME; lia | exact S1]. }
  eapply (run_close B APIf ra empty FF g _ _ L A regs mem md 0x13b54
    (KQ regs mem 0x13b64 [(fsp g - 16, fsp g)] (fun _ _ => True))); [exact HFR | |].
  - unfold rmk. rewrite P4, R10, R22, R27.
    step. step. step. step.
    eapply (check_str_call CS) with (r := n_ld (g_in g)) (o := dp) (c := t_cap_disp (g_in g))
      (lo := g_S g - 65536) (str := n_EXP_DP (g_in g)) (slack := sl);
      [ exact HRO | unfold zlen, n_ld in *; lia | apply sextw_small; unfold zlen, n_ld in *; lia | lia | reflexivity |
        pose proof (caps_range (g_in g)); lia | reflexivity | |
        rewrite unsigned_lit by (unfold fsp, SLOT_FRAME; lia); exact ST |
        rewrite unsigned_lit by (unfold fsp, SLOT_FRAME; lia); unfold CHECK_STR_FRAME, fsp, SLOT_FRAME; lia | | ].
    + intros _. unfold check_str_ok. rewrite unsigned_lit by (unfold fsp, SLOT_FRAME; lia).
      split; [unfold zlen, n_ld in *; lia|]. split; [reflexivity|]. split; [exact SB|].
      split; [apply nzb_notin; apply nzb_EXP_DP, Wk|].
      split; [exact SW|]. left. unfold CHECK_STR_FRAME, fsp, SLOT_FRAME, n_ln, n_ld, zlen in *. lia.
    + intros a Ha. rewrite unsigned_lit in Ha by (unfold fsp, SLOT_FRAME; lia).
      apply (ro_addr_high B APIf ra empty FF). unfold fsp, SLOT_FRAME in Ha. lia.
    + intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO'.
      rewrite unsigned_lit in MU by (unfold fsp, SLOT_FRAME; lia). unfold CHECK_STR_FRAME in MU.
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [apply ret_lit; lia|]. split; [solve_keep|]. split; [exact MU|]. split; [exact WM|].
      split; [exact RO' | exact I].
  - intros R pc' mem' regs' (-> & HK & MU & WM & RO & _) ER.
    apply H1. eapply (close_IR B APIf ra empty FF) with (lo := fsp g - 16) (hi := fsp g);
      [ | exact HFR | exact HP | exact HI | unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia | left; lia |
        exact MU | exact WM | exact RO | eapply SKEEP_trans; [exact HK | exact ER] | ].
    + intros c Hc. exists nm, tk, dp. exact Hc.
    + intros HI'. split; [exact HI' | exact R0].
Qed.

End Seg.
