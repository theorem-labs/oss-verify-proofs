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

Lemma E06_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (pc0 pc1 : Z) (xa : word),
  (pc0 = 0x137d4 /\ pc1 = 0x137dc /\ xa = x23 \/ pc0 = 0x13810 /\ pc1 = 0x13818 /\ xa = x20) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR (Z_to_bv 64 pc1) x2 x3 x4 x5 x6 x7 x8 x9 xa x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x15974 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 pc0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m pc0 pc1 xa PCS.
  destruct PCS as [(-> & -> & ->)|(-> & -> & ->)].
  - step. step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - step. step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End KA.

Section E06.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_E06 : Hcut B APIf ra (Inv_U137dc B APIf ra empty) -> Hcut B APIf ra (Inv_U137d4 B APIf ra empty).
Proof.
  intros HX g c (s & L & A & regs & mem & md & -> & HF & HP & HE & H23 & HO).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H20 & H21 & H22).
  assert (Hcap : 0 <= t_cap_fw (g_in g) < 16) by (unfold t_cap_fw; apply Z.mod_pos_bound; lia).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x137d4) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply E06_x. left. split; [reflexivity|]. split; reflexivity. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  pose proof (uf_KP_CSeq regs regs1 KP1) as CS1.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x137dc) by (rewrite (uf_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 s).
  { transitivity (getr regs 23); [|exact H23].
    rewrite (uf_getr_x _ _ 10 XR) by reflexivity. rewrite (uf_getr_reg regs 23) by reflexivity. reflexivity. }
  assert (HF1 : FR B APIf ra empty g (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))] L A regs1 mem md).
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  rewrite <- (uf_free_pc B APIf ra empty FF).
  apply (uf_free_step B APIf ra empty FF g (2 * NR g + 1) [] s (bsz (t_cap_fw (g_in g))) [] L A regs1 mem md _
    HF1 HP).
  - unfold bsz, MMAP_THRESHOLD. lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 HF2 HP2 RP2 FRM2.
    rewrite G1. apply HX. exists L', A', regs2, mem2, md2. split; [reflexivity|].
    split; [exact HF2|]. split; [exact HP2|].
    assert (CS : CSeq regs regs2) by (apply (uf_CSeq_trans _ regs1); [exact CS1 | exact RP2]).
    assert (FRe : FReq g mem mem2) by (intros x Hx; rewrite <- SEG; exact (FRM2 x Hx)).
    split; [exact (uf_TID_tr g mem mem2 FRe HTID)|].
    split; [exact (uf_TL_tr g regs regs2 mem mem2 CS FRe HTL)|].
    split; [uf_cs CS 21; exact H21 | uf_cs CS 22; exact H22].
Qed.

End E06.
