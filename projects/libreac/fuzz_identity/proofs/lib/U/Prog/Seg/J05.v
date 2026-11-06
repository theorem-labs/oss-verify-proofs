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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i UTac_uhj_j.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Lemma kJ05a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13f3c) x2 x3 x4 x5 x6 x7 x8 x9 x22 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x15974) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f34) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma kJ05b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x8 = x9 -> Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f34) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f30) fc None m ro).
Proof.
  intros. subst x9. step. if_cases HC; [exfalso; unfold bv_eqb in HC; rewrite Z.eqb_refl in HC; discriminate HC|].
  apply evt_done. reflexivity.
Qed.

Lemma kJ05c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (w : Z),
  x9 = Z_to_bv 64 w -> 0 <= w <= 1 ->
  Exec.evt rsegs
    (fun ms' => exists y10, ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (w + (if bv_eqb x10 (Z_to_bv 64 0) then 0 else 2))) y10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x13f30) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f24) fc None m ro).
Proof.
  intros. step. step. step. rewrite (sj_sltu_or x9 x10 w) by assumption. apply evt_done. eexists. reflexivity.
Qed.

Section J05.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_J05 : Hcut B APIf ra (Inv_U13f3c B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13f24 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13f30 B APIf ra empty) /\
  Hcut B APIf ra (Inv_U13f34 B APIf ra empty).
Proof.
  intros H0.
  assert (H98 : Hcut B APIf ra (Inv_U13f34 B APIf ra empty)).
  { intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (H20 & H21 & H22).
    assert (Hin : In (dp, bsz (t_cap_disp (g_in g))) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); right; right; left; reflexivity).
    destruct (sj_in_blocks L A _ _ Hin) as (p & Hp & Ep).
    eapply (run_to B APIf ra empty FF); [exact HF | apply kJ05a | intros regs_c HG].
    apply (sj_free_call B APIf ra empty FF g (2 * NR g + 5)
      [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))] [] L A regs mem md regs_c p
      (bsz (t_cap_disp (g_in g)))).
    - rewrite Ep. exact HF.
    - rewrite Ep. exact HP.
    - exact Hp.
    - unfold bsz. lia.
    - rgj HG.
    - rgj HG.
    - rgj HG.
    - rewrite HG. apply ret_ok_even. reflexivity.
    - rewrite HG, Ep. exact H22.
    - intros L' A' regs' mem' md' HF' HP' RP'.
      replace (getr regs_c 1) with (Z_to_bv 64 0x13f3c) by (rewrite HG; reflexivity).
      apply H0. exists nm, tk. apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF' | exact HP' |].
      split.
      + etransitivity; [exact (RP' 20 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H20.
      + etransitivity; [exact (RP' 21 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H21. }
  assert (H94 : Hcut B APIf ra (Inv_U13f30 B APIf ra empty)).
  { intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HIR & HM).
    pose proof HIR as (_ & _ & _ & H20 & H21 & H22 & _).
    assert (Hin : In (dp, bsz (t_cap_disp (g_in g))) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); right; right; left; reflexivity).
    destruct (sj_block_pos B APIf ra empty g _ _ L A regs mem md _ _ HF Hin) as [Hd1 Hd2].
    assert (E89 : getr regs 8 = getr regs 9).
    { destruct HM as [(I & O & P & sP & HCE & E8 & E9) | (_ & E8 & E9)].
      - rewrite E8, E9. rewrite sj_mask_eq by lia. reflexivity.
      - rewrite E8, E9. reflexivity. }
    eapply (run_to B APIf ra empty FF); [exact HF | apply kJ05b; exact E89 | intros regs' HG].
    apply H98. exists nm, tk, dp. apply (cut_close B APIf ra empty _ _ _ _ _ L A).
    + apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rgj HG | rgj HG | rgj HG].
    + exact HP.
    + split; [rgj HG|]. split; [rgj HG | rgj HG]. }
  assert (H88 : Hcut B APIf ra (Inv_U13f24 B APIf ra empty)).
  { intros g c (nm & tk & dp & HC).
    eapply (cut_open B APIf ra empty); [exact HC|].
    intros L A regs mem md HF HP (HIR & I & O & P & sP & HCE & HP0 & H19 & H8 & H9 & H10).
    set (w := if (I =? t_in (g_in g)) && (O =? t_out (g_in g)) then 0 else 1) in *.
    assert (Hw : 0 <= w <= 1) by (unfold w; destruct ((I =? t_in (g_in g)) && (O =? t_out (g_in g))); lia).
    eapply (run_ex B APIf ra empty FF); [exact HF | apply kJ05c with (w := w); [exact H9 | exact Hw] | intros y regs' HG].
    assert (E9 : getr regs' 9 = Z_to_bv 64 (w + (if bv_eqb (getr regs 10) (Z_to_bv 64 0) then 0 else 2)))
      by (rewrite HG; reflexivity).
    apply H94. exists nm, tk, dp. apply (cut_close B APIf ra empty _ _ _ _ _ L A).
    + apply (FR_regs B APIf ra empty _ _ _ _ _ regs); [exact HF | rgj HG | rgj HG | rgj HG].
    + exact HP.
    + destruct HIR as (HID & HQ56 & HQ48 & H20 & H21 & H22 & H24 & H25 & HOUT & Hr & HN1 & HN2).
      split.
      * split; [exact HID|]. split; [exact HQ56|]. split; [exact HQ48|]. split; [rgj HG|]. split; [rgj HG|].
        split; [rgj HG|]. split; [rgj HG|]. split; [rgj HG|]. split; [exact HOUT|]. split; [exact Hr|].
        split; [exact HN1 | exact HN2].
      * left. exists I, O, P, sP. split; [exact HCE|]. split; [rgj HG|].
        rewrite E9. unfold exp_mask. fold w. replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; exact HP0).
        f_equal. destruct (bytes_eqb sP (n_EXP_DP (g_in g))) eqn:EB.
        -- apply bytes_eqb_eq in EB. apply H10 in EB. rewrite EB. rewrite (sj_bv_eqb 0 0) by lia. cbn. lia.
        -- destruct (bv_eqb (getr regs 10) (Z_to_bv 64 0)) eqn:E0; [|lia].
           exfalso. unfold bv_eqb in E0. apply Z.eqb_eq in E0. assert (E1 : getr regs 10 = Z_to_bv 64 0).
           { apply bv_eq. exact E0. }
           apply H10 in E1. rewrite E1, sj_beqb_refl in EB. discriminate. }
  split; [exact H88|]. split; [exact H94 | exact H98].
Qed.

End J05.
