(* Segment W01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x14048, 0x14060], row_of_block's cat and count
   tests. U14048 -> U14064 (i = 0 in s3, cat = row = T' in s10, s9); the exits to U140c4 (cat = 0 at 0x1404c,
   count = 0 at 0x14058) are not taken (C11 C1.2: cat = T'; C1.3: count = 11). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac w01_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac w01_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; w01_cond); cbv iota
  end.

Lemma w01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> a0 = Z_to_bv 64 0x1fcc8 ->
    ov_read_bytes rsegs m (wa (spv + 1824)) 8 = Some (le8 (Z_to_bv 64 11)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7
                              s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 (Z_to_bv 64 0x1fcc8) (Z_to_bv 64 0x1fcc8) s11
                              t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14064) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14048) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv -> Hs0 Hs1 -> HL.
  step. step. w01_if false.
  step. step. step. w01_if false.
  step. step.
  apply evt_done. reflexivity.
Qed.

Section W01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_W01 : forall j : nat, Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j 0%nat ->
  Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U14048_at B APIf ra empty) j.
Proof.
  intros j H1 _ g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HCC & Hsel & H10 & Hq)).
  pose proof (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u8_run_to B APIf ra empty FF g _ L A regs mem md);
    [exact HFR | unfold rmk; eapply w01_evt with (spv := g_S g - 1936); [exact Hsp | lia | lia | exact H10 |] |].
  { replace (g_S g - 1936 + 1824) with (spk g 1824) by (unfold spk, fsp, SLOT_FRAME; lia).
    exact (u8_ld8 mem _ _ Hq). }
  intros regs' HG.
  apply (H1 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | rewrite HG; reflexivity ..].
  - exact HP.
  - destruct HCC as (HC7 & _ & _).
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [split; [exact (u8_CC7_keep g j phi regs regs' mem mem [] HC7 HK (munch_refl [] mem) I I I)
                   | exact Hsel]|].
    split; [lia|].
    split; [unfold rg; rewrite HG; reflexivity|].
    split; [unfold rg; rewrite HG; reflexivity|].
    split; [unfold rg; rewrite HG; reflexivity|].
    split; [exact Hq|].
    intros i' Hi'. lia.
Qed.

End W01.
