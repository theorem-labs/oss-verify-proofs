From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sj.
Import ListNotations.
Open Scope Z_scope.

Lemma kJ04 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x10 (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c94) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13c5c) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Section J04.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_J04 : Hcut B APIf ra (Inv_K13c94 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c5c B APIf ra empty) /\ Hcut B APIf ra (Inv_K13c60 B APIf ra empty).
Proof.
  intros H94. split.
  - intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP ((HIRb & Hr) & H176 & HA0).
    eapply (run_to B APIf ra empty FF); [exact HF | apply kJ04 | intros regs' HG].
    apply H94. exists nm, tk, dp.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A).
    + apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rg HG | rg HG | rg HG].
    + exact HP.
    + destruct HIRb as (HID & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H27 & HOUT & HNM).
      destruct (HNM Hr) as [HN1 HN2].
      split.
      * split; [exact HID|]. split; [rg HG|]. split; [rg HG|]. split; [rg HG|]. split; [rg HG|].
        split; [rg HG|]. split; [rg HG|]. split; [rg HG|]. split; [exact HOUT|]. split; [exact Hr|].
        split; [exact HN1 | exact HN2].
      * right. split; [exact H176|]. split; [rg HG | rg HG].
  - intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (_ & E1 & E2).
    exfalso. rewrite E1 in E2. apply sj_bv_inj in E2; unfold CAT in *; lia.
Qed.

End J04.
