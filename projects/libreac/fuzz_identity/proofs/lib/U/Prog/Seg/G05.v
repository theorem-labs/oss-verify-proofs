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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require buf_of_c.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma G05_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR (Z_to_bv 64 0x13948) x2 x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15 x16
             x17 x18 x19 x20 x10 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x140f0 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x1393c) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m.
  step. step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End KA.

Section G05.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_G05 : Hcut B APIf ra (Inv_U13948 B APIf ra empty) -> Hcut B APIf ra (Inv_U1393c B APIf ra empty).
Proof.
  intros HX g c (nm & tk & L & A & regs & mem & md & -> & HF & HP & HG & H20 & H10).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HG as (HTID & H9 & H56 & H48 & H19 & H18 & H24 & H23 & H25 & H26).
  assert (Cn : 0 <= t_cap_name (g_in g) < 40) by (unfold t_cap_name; apply Z.mod_pos_bound; lia).
  assert (Ct : 0 <= t_cap_tok (g_in g) < 40) by (unfold t_cap_tok; apply Z.mod_pos_bound; lia).
  assert (Cd : 0 <= t_cap_disp (g_in g) < 64) by (unfold t_cap_disp; apply Z.mod_pos_bound; lia).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x1393c) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply G05_x. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x13948) by (rewrite (uf_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (t_cap_disp (g_in g))).
  { rewrite (uf_getr_x _ _ 10 XR) by reflexivity. rewrite <- H19. rewrite (uf_getr_reg regs 19) by reflexivity.
    reflexivity. }
  assert (G21 : getr regs1 21 = Z_to_bv 64 tk).
  { rewrite (uf_getr_x _ _ 21 XR) by reflexivity. rewrite <- H10. rewrite (uf_getr_reg regs 10) by reflexivity.
    reflexivity. }
  assert (HF1 : FR B APIf ra empty g (2 * NR g + 4)
                  [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))] L A regs1 mem md).
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  change (Z_to_bv 64 0x140f0) with (Z_to_bv 64 U.Prog.buf_of_c.BUF_OF).
  apply (uf_bufof_step B APIf ra empty FF g (2 * NR g + 4)
           [(nm, bsz (t_cap_name (g_in g))); (tk, bsz (t_cap_tok (g_in g)))] L A regs1 mem md
           (t_cap_disp (g_in g)) _ HF1 HP).
  - cbn [Datatypes.length]. lia.
  - unfold hb_bytes. cbn [map fold_right snd]. unfold bsz. lia.
  - lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 _.
    rewrite G1.
    replace (2 * NR g + 4 + 1) with (2 * NR g + 5) in HF2 by lia.
    apply HX. exists nm, tk, res, L', A', regs2, mem2, md2. split; [reflexivity|].
    split; [exact HF2|]. split; [exact HP2|].
    assert (FRe : FReq g mem mem2) by (intros x Hx; rewrite <- SEG; exact (FRM2 x Hx)).
    split; [|split; [uf_cs RP2 20; uf_k KP1 20; exact H20 | split; [uf_cs RP2 21; exact G21 | exact R10]]].
    split; [exact (uf_TID_tr g mem mem2 FRe HTID)|].
    split; [uf_cs RP2 9; uf_k KP1 9; exact H9|].
    split; [exact (uf_q64_tr g mem mem2 56 _ FRe ltac:(unfold SLOT_FRAME; lia) H56)|].
    split; [exact (uf_q64_tr g mem mem2 48 _ FRe ltac:(unfold SLOT_FRAME; lia) H48)|].
    split; [uf_cs RP2 19; uf_k KP1 19; exact H19|].
    split; [uf_cs RP2 18; uf_k KP1 18; exact H18|].
    split; [uf_cs RP2 24; uf_k KP1 24; exact H24|].
    split; [uf_cs RP2 23; uf_k KP1 23; exact H23|].
    split; [uf_cs RP2 25; uf_k KP1 25; exact H25|].
    uf_cs RP2 26; uf_k KP1 26; exact H26.
Qed.

End G05.
