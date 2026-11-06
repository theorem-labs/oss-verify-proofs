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

Lemma kJ07 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13cb0) x2 x3 x4 x5 x6 x7 x8 x9 x20 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x15440) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ca8) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Section J07.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_J07 : Hcut B APIf ra (Inv_K13cb0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13ca8 B APIf ra empty).
Proof.
  intros H0 g c (nm & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP H20.
  assert (Hin : In (nm, bsz (t_cap_name (g_in g))) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (sj_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (run_to B APIf ra empty FF); [exact HF | apply kJ07 | intros regs_c HG].
  apply (sj_free_call B APIf ra empty FF g (2 * NR g + 5) [] [] L A regs mem md regs_c p (bsz (t_cap_name (g_in g)))).
  - rewrite Ep. exact HF.
  - rewrite Ep. exact HP.
  - exact Hp.
  - unfold bsz. lia.
  - rg HG.
  - rg HG.
  - rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG, Ep. exact H20.
  - intros L' A' regs' mem' md' HF' HP' RP'.
    replace (getr regs_c 1) with (Z_to_bv 64 0x13cb0) by (rewrite HG; reflexivity).
    apply H0. apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF' | exact HP' | exact I].
Qed.

End J07.
