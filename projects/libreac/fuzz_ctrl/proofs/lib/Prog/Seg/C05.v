(* Segment C05 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d8c, 0x13d94], P6a's check (#93: the catalogue
   match equals row_of_block, C4.12) and free of the frame copy. K13d8c -> K13d98.
   libreac v1.9.0 (table 5a S_C05: IDENTICAL, OLD 0x13d5c .. 0x13d64): pcs, free at 0x1635c (frame_facts' ms_free),
   return address 0x13d98; cuts K13d5c -> K13d8c, K13d68 -> K13d98 (SlotInv.v's renames), so seg_C05 is stated on
   the renamed cuts. K13d98's FC now holds left - h in s11 and the body pointer in the spill [sp+32] (above sp, so
   free keeps it), and IFS holds nb in s3 (callee-saved). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma kC05 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x10 = x23 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d98) x2 x3 x4 x5 x6 x7 x8 x9 x21 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1635c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d8c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro E. subst x10. step.
  if_cases HC; [exfalso; unfold bv_eqb in HC; rewrite Z.eqb_refl in HC; discriminate HC|].
  step. step. apply evt_done. reflexivity.
Qed.

Section C05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract B (APIf rc).

Lemma seg_C05 : forall j : nat, Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j.
Proof.
  intros j H1 g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HC7 & H23 & H10).
  pose proof HC7 as ((Hj & H26 & (H27 & H32 & H20) & H21 & _ & HOUR & HM7) & _ & _ & HIFS).
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  assert (E1023 : getr regs 10 = getr regs 23) by (unfold rg in *; rewrite H10, H23, b8_want_eq; reflexivity).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kC05; exact E1023 | intros regs_c HG].
  unfold hb1 in HF, HP. rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF FREE g L A regs mem md regs_c p (t_len (g_in g) j)).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 21); [reflexivity|]. rewrite Ep. exact H21.
  - intros L' A' regs' mem' md' HF' HP' RP' HKEEP.
    replace (getr regs_c 1) with (Z_to_bv 64 0x13d98) by (rewrite HG; reflexivity).
    rewrite (b8_segs B APIf ra empty FF) in HKEEP.
    assert (HK : forall x, spk g 0 <= x < 2 ^ 64 -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx; apply HKEEP; unfold spk, fsp, SLOT_FRAME in Hx; lia).
    apply H1. apply (b8_cut_close B APIf ra empty _ _ _ _ L' A'); [exact HF' | exact HP' |].
    split; [exact Hj|].
    split; [unfold rg; etransitivity; [exact (RP' 26 ltac:(unfold callee_saved; lia))|]; rewrite HG; exact H26|].
    split; [split; [|split]|].
    + unfold rg; etransitivity; [exact (RP' 27 ltac:(unfold callee_saved; lia))|]; rewrite HG; exact H27.
    + exact (b8_ba_above mem mem' (spk g 0) _ _ H32 ltac:(unfold spk; lia) HK).
    + unfold rg; etransitivity; [exact (RP' 20 ltac:(unfold callee_saved; lia))|]; rewrite HG; exact H20.
    + split; [exact (b8_OURb_above g mem mem' HOUR HK)|].
      split; [exact (b8_M7_above g mem mem' HM7 HK)|].
      apply (b8_IFS_regs g (S j) regs regs' mem'); [exact (b8_IFS_above g (S j) regs mem mem' HIFS HK)|].
      etransitivity; [exact (RP' 19 ltac:(unfold callee_saved; lia))|]. rewrite HG. reflexivity.
Qed.

End C05.
