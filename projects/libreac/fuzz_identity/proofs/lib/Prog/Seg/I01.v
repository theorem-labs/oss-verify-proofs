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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import strlen_c.
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
Hypothesis SL : strlen_contract.

Lemma seg_I01 : Hcut B APIf ra (Inv_K13b24 B APIf ra empty) -> Hcut B APIf ra (Inv_K13c98 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b18 B APIf ra empty).
Proof.
  intros H1 H2 g c (nm & tk & dp & L & A & regs & mem & md & -> & HFR & HP & HI).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (P1 & P2 & P3 & P4 & HMR & HRO & HSTK & HSW).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold SLOT_K, SLOT_STACK in *.
  destruct (n_r_cases (g_in g)) as [R0 | R1].
  - destruct (HO R0) as (C1 & C2 & C3). destruct (n_r0 _ R0) as [Wk Ft].
    destruct (fits_unfold _ Ft) as (F1 & F2 & F3).
    destruct (nmb_in _ _ _ _ _ _ HP) as (N1 & N2 & N3).
    destruct (slack_ok B APIf ra empty FF L A mem md nm _ (n_EXP_NM (g_in g)) HMR N1 C1) as (sl & SB & SW & SE).
    { unfold bsz, n_ln in *. lia. }
    pose proof (blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
    rewrite R0 in R25.
    eapply (run_close B APIf ra empty FF g _ _ L A regs mem md 0x13b18
      (KQ regs mem 0x13b24 [] (fun R m' => YK11.getr R 10 = Z_to_bv 64 (n_ln (g_in g))))); [exact HFR | |].
    + unfold rmk. rewrite R25, R20.
      step. if_false. step. step.
      eapply (strlen_call SL) with (str := n_EXP_NM (g_in g)) (slack := sl);
        [exact HRO | rewrite unsigned_lit by lia; exact SB | apply nzb_notin, nzb_EXP_NM, Wk |
         rewrite unsigned_lit by lia; exact SW |].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO'.
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [apply ret_lit; lia|]. split; [solve_keep|]. split; [exact MU|]. split; [exact WM|].
      split; [exact RO'|]. reflexivity.
    + intros R pc' mem' regs' (-> & HK & MU & WM & RO & H10) ER.
      apply H1. eapply (close_IR B APIf ra empty FF) with (lo := fsp g) (hi := fsp g);
        [ | exact HFR | exact HP | exact HI | unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia | left; lia |
          apply munch_nil_any; exact MU | exact WM | exact RO | eapply SKEEP_trans; [exact HK | exact ER] | ].
      * intros c Hc. exists nm, tk, dp. exact Hc.
      * intros HI'. split; [split; [exact HI' | exact R0] | rewrite ER; exact H10].
  - rewrite R1 in R25.
    eapply (run_close B APIf ra empty FF g _ _ L A regs mem md 0x13b18
      (KQ regs mem 0x13c98 [] (fun _ _ => True))); [exact HFR | |].
    + unfold rmk. rewrite R25.
      step. if_true.
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [solve_keep|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [exact HRO | exact I].
    + intros R pc' mem' regs' (-> & HK & MU & WM & RO & _) ER.
      apply H2. eapply (close_IR B APIf ra empty FF) with (lo := fsp g) (hi := fsp g);
        [ | exact HFR | exact HP | exact HI | unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia | left; lia |
          apply munch_nil_any; exact MU | exact WM | exact RO | eapply SKEEP_trans; [exact HK | exact ER] | ].
      * intros c Hc. exists nm, tk, dp. exact Hc.
      * intros (_ & _ & _ & _ & Q20 & Q21 & Q22 & _). auto.
Qed.

End Seg.
