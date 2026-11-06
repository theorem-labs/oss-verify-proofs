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

Lemma seg_I09 : Hcut B APIf ra (Inv_K13b9c B APIf ra empty) -> Hcut B APIf ra (Inv_K13be0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b80 B APIf ra empty).
Proof.
  intros H1 H2 g c (nm & tk & dp & L & A & regs & mem & md & -> & HFR & HP & [[HI R0] R10]).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (P1 & P2 & P3 & P4 & HMR & HRO & HSTK & HSW).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold SLOT_K, SLOT_STACK in *.
  destruct (HO R0) as (C1 & C2 & C3). destruct (n_r0 _ R0) as [Wk Ft].
  destruct (nmb_in _ _ _ _ _ _ HP) as (N1 & N2 & N3).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
  unfold bsz in *.
  pose proof (n_ln_le _ Wk) as LN. unfold n_ln in LN.
  assert (NZ0 : bz (nthb (n_EXP_NM (g_in g)) 0) <> 0) by (apply nzb_nth; [apply nzb_EXP_NM, Wk | lia]).
  assert (RD : ov_read_bytes rsegs mem (wa (nm + Z.of_nat 0)) 1 = Some [nthb (n_EXP_NM (g_in g) ++ [z8]) 0])
    by (apply cstr_byte; [exact C1 | lia]).
  rewrite nthb_snoc_lt in RD by lia. cbv [Z.of_nat] in RD. rewrite Z.add_0_r in RD.
  pose proof (bz_range (nthb (n_EXP_NM (g_in g)) 0)) as BR.
  eapply (run_close B APIf ra empty FF g _ _ L A regs mem md 0x13b80
    (KQ regs mem 0x13b9c [] (fun R m' =>
       YK11.getr R 13 = Z_to_bv 64 45 /\
       YK11.getr R 14 = Z_to_bv 64 (bz (nthb (n_EXP_NM (g_in g)) 0)) /\
       YK11.getr R 11 = Z_to_bv 64 (nm + 1) /\
       YK11.getr R 12 = Z_to_bv 64 0 /\
       YK11.getr R 10 = Z_to_bv 64 0))); [exact HFR | |].
  - unfold rmk. rewrite R10, R20.
    step. if_false.
    step. rewrite zxb_bz.
    step.
    rewrite bv_eqb_lit by lia. if_false.
    step. step. step. step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [solve_keep|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [exact HRO|].
    repeat split; reflexivity.
  - intros R pc' mem' regs' (-> & HK & MU & WM & RO & H13 & H14 & H11 & H12 & H10) ER.
    apply H1. exists 0%nat.
    eapply (close_IR B APIf ra empty FF (fun g c => Inv_K13b9c_at B APIf ra empty g 0 c)) with (lo := fsp g) (hi := fsp g);
      [ | exact HFR | exact HP | exact HI | unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia | left; lia |
        apply munch_nil_any; exact MU | exact WM | exact RO | eapply SKEEP_trans; [exact HK | exact ER] | ].
    + intros c Hc. exists nm, tk, dp. exact Hc.
    + intros HI'. split; [split; [exact HI' | exact R0]|].
      rewrite !ER. split; [lia|]. split; [exact H13|]. split; [exact H14|].
      split; [rewrite H11; f_equal; lia|]. split; [exact H12 | exact H10].
Qed.

End Seg.
