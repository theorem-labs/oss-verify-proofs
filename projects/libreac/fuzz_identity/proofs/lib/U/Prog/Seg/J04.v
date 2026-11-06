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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i UTac_uhj_j.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma kJ04 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x10 (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f30) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13ef8) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Section J04.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_J04 : Hcut B APIf ra (Inv_U13f30 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13ef8 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13efc B APIf ra empty).
Proof.
  intros H30. split.
  - intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP ((HIRb & Hr) & H192 & HA0).
    eapply (run_to B APIf ra empty FF); [exact HF | apply kJ04 | intros regs' HG].
    apply H30. exists nm, tk, dp.
    apply (cut_close B APIf ra empty _ _ _ _ _ L A).
    + apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rgj HG | rgj HG | rgj HG].
    + exact HP.
    + destruct HIRb as (HID & H9 & H56 & H48 & H20 & H21 & H22 & H23 & H24 & H25 & H19 & HOUT & HNM).
      destruct (HNM Hr) as [HN1 HN2].
      split.
      * split; [exact HID|]. split; [exact H56|]. split; [exact H48|].
        split; [rgj HG|]. split; [rgj HG|]. split; [rgj HG|]. split; [rgj HG|]. split; [rgj HG|].
        split; [exact HOUT|]. split; [exact Hr|]. split; [exact HN1 | exact HN2].
      * right. split; [exact H192|]. split; [rgj HG | rgj HG].
  - intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (_ & E1 & E2).
    exfalso. rewrite E1 in E2. apply sj_bv_inj in E2; unfold CAT in *; lia.
Qed.

End J04.
