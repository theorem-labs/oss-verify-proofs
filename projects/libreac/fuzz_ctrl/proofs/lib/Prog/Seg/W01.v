(* Segment W01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d38, 0x13d48], row_of_block's cat and count tests.
   K13d38 -> K13d4c (i = 0); the exits to K13d80 (cat = 0, count = 0) are not taken (C11 C1.2, C1.3).
   libreac v1.9.0 (table 5a S_W01: IDENTICAL-RENUMBER, OLD 0x13d08 .. 0x13d18): pcs, the count 1808 -> 1824, frame
   1920 -> 1936; a0 = CAT (SlotModel.v, = reac_box_catalogue_c's BOX_CATALOGUE) by name; cuts K13d08 -> K13d38,
   K13d1c -> K13d4c, K13d50 -> K13d80 (SlotInv.v's renames), so seg_W01 is stated on the renamed cuts. *)
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

Lemma kW01 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 -> x10 = Z_to_bv 64 CAT ->
  ov_read_bytes rsegs m (wa (sp0 + 1824)) 8 = Some (le8 (Z_to_bv 64 11)) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 11) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                           x22 x10 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d4c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d38) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 E2 H0 H1 E10 R.
  subst x2. step. step.
  first [if_cases HC; [exfalso; rewrite E10 in HC; vm_compute in HC; discriminate HC|] | idtac].
  step. step.
  first [if_cases HC2; [exfalso; vm_compute in HC2; discriminate HC2|] | idtac].
  step. apply evt_done. reflexivity.
Qed.

Section W01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_W01 : forall j : nat, Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j 0%nat ->
  Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d38_at B APIf ra empty) j.
Proof.
  intros j H1 _ g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HCC & Hsel & H10 & Hq).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; eapply kW01 with (sp0 := g_S g - 1936);
    [exact Hsp | lia | lia | exact H10 |] | intros regs' HG].
  { replace (g_S g - 1936 + 1824) with (spk g 1824) by (unfold spk, fsp, SLOT_FRAME; lia).
    apply b8_bytes_le8. exact Hq. }
  apply H1. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
  - exact HP.
  - destruct HCC as [HC7 _]. split; [split; [|exact Hsel]|].
    { apply (b8_CC7_regs _ _ _ regs); [exact HC7 | b8rg HG ..]. }
    split; [lia|].
    split; [unfold rg; rewrite HG; transitivity (getr regs 10); [reflexivity|]; rewrite H10; f_equal;
            unfold CAT, CAT_ROW; lia|].
    split; [unfold rg; rewrite HG; transitivity (Z_to_bv 64 11); [reflexivity | f_equal; lia]|].
    intros i' Hi'. lia.
Qed.

End W01.
