From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotInv write_uint_c reac_identity_fw_str_c
  reac_identity_reac_ver_str_c put_dec_c reac_box_family_of_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(bsz, z8, zlen, fw_res, fw_out, id_VER, ver_res,
  ver_out, HWT_ADDR).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L, reac_identity_fw_str_c3,
  reac_identity_fw_str_c3_len, reac_identity_fw_str_c3_nz, reac_identity_fw_str_dec_h, reac_identity_fw_str_dec_f).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_reac_ver_str_c(reac_ver_str_VER,
  reac_ver_str_LV, reac_ver_str_DEC2).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_ucg.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma C02_x0 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  x8 = Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x10 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31 /\ pc' = Z_to_bv 64 0x13700 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136b0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m E8. subst x8.
  step. step.
  rewrite (uf_eqb 0 0) by lia. change (0 =? 0) with true. cbv iota.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma C02_x1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp : Z),
  x8 = Z_to_bv 64 1 -> x2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 384 <= 2 ^ 64 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists a0, R = mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 3) x10 a0 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 0x105ac) (Z_to_bv 64 (sp + 132)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) /\
       pc' = Z_to_bv 64 0x136c8 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136b0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp E8 E2 Hsp Hsp2. subst x8 x2.
  step. step.
  rewrite (uf_eqb 1 0) by lia. change (1 =? 0) with false. cbv iota.
  step. step. step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [|split; reflexivity].
  eexists. f_equal; apply bv_eq; vm_compute; reflexivity.
Qed.

End KA.

Section C02.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_C02 : Hcut B APIf ra (Inv_U13700 B APIf ra empty) -> Hcut B APIf ra (Inv_U136c8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U136b0 B APIf ra empty).
Proof.
  intros H700 H6c8 g c (L & A & regs & mem & md & -> & HF & HP & HCB & H8 & H10).
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HCB as (HNR & HNRb & HG24 & HHW & HCUR & HID).
  assert (Hhv : haveT (g_in g) = 0 \/ haveT (g_in g) = 1) by (unfold haveT, rec_have; destruct (rec_hw _ _); auto).
  destruct Hhv as [H0|H1].
  - eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136b0) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of. apply C02_x0. rewrite <- (uf_getr_reg regs 8) by reflexivity. rewrite H8, H0. reflexivity. }
    intros R pc' m' regs1 (-> & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
    assert (G9 : getr regs1 9 = Z_to_bv 64 (FAM (idT (g_in g)))).
    { rewrite (uf_getr_x _ _ 9 XR) by reflexivity. rewrite <- H10. rewrite (uf_getr_reg regs 10) by reflexivity.
      reflexivity. }
    apply H700. exists L, A, regs1, mem, md. split; [reflexivity|].
    split.
    { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
      - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
      - intros x _ _. reflexivity.
      - apply uf_wmono_eq. intros w. reflexivity. }
    split; [exact HP|].
    split.
    { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
    split; [split; assumption|]. split; [exact G9|].
    unfold fam_hw. rewrite H0. reflexivity.
  - eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136b0) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of. apply (C02_x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g)).
      - rewrite <- (uf_getr_reg regs 8) by reflexivity. rewrite H8, H1. reflexivity.
      - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
      - lia.
      - lia. }
    intros R pc' m' regs1 ((a0 & ->) & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
    assert (G9 : getr regs1 9 = Z_to_bv 64 (FAM (idT (g_in g)))).
    { rewrite (uf_getr_x _ _ 9 XR) by reflexivity. rewrite <- H10. rewrite (uf_getr_reg regs 10) by reflexivity.
      reflexivity. }
    apply H6c8. exists 0%nat, L, A, regs1, mem, md. split; [reflexivity|].
    split.
    { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
      - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
      - intros x _ _. reflexivity.
      - apply uf_wmono_eq. intros w. reflexivity. }
    split; [exact HP|].
    split.
    { rewrite <- H1. split; [exact HNR|]. split; [exact HNRb|]. split; [exact HG24|]. split; [exact HHW|].
      split; [|exact HID].
      destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
    split; [exact H1|]. split; [exact G9|].
    split; [rewrite (uf_getr_x _ _ 19 XR) by reflexivity; reflexivity|].
    split; [rewrite (uf_getr_x _ _ 8 XR) by reflexivity; reflexivity|].
    split; [rewrite (uf_getr_x _ _ 18 XR) by reflexivity; reflexivity|].
    split; [lia|]. intros j' Hj'. lia.
Qed.

End C02.
