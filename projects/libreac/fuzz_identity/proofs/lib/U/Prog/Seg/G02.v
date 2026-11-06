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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_stem_c reac_box_name_c.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma G02_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (f fr : Z) (pc0 : Z),
  U.Prog.reac_box_family_stem_c.reac_box_family_stem_contract -> 0 <= f < 128 ->
  (pc0 = 0x138f4 /\ x10 = Z_to_bv 64 f \/ pc0 = 0x138fc /\ x24 = Z_to_bv 64 fr /\ 0 <= fr < 256 /\ f = Z.land fr 127) ->
  bytes_at rsegs m U.Prog.reac_box_family_stem_c.STEM_T
    (le8 (Z_to_bv 64 0x102d0) ++ le8 (Z_to_bv 64 0x103a4) ++ le8 (Z_to_bv 64 0x104e9)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists a1, R = mkR (Z_to_bv 64 0x13908) x2 x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 (U.Prog.reac_box_family_stem_c.STEM_Addr f)) a1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 (Z_to_bv 64 f) x27 x28 x29 x30 x31) /\
       pc' = Z_to_bv 64 0x13908 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 pc0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m f fr pc0 SC Hf PCS HT.
  destruct PCS as [(-> & E10)|(-> & E24 & Hfr & Ef)].
  - subst x10. step. step. step. step.
    eapply evt_cut.
    { eapply SC with (f := f); [lia | reflexivity | exact HT]. }
    intros ms' (a1' & -> & _).
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [eexists; reflexivity|]. split; reflexivity.
  - subst x24. step.
    rewrite (unsigned_lit fr) by lia. rewrite <- Ef.
    step. step.
    eapply evt_cut.
    { eapply SC with (f := f); [lia | reflexivity | exact HT]. }
    intros ms' (a1' & -> & _).
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [eexists; reflexivity|]. split; reflexivity.
Qed.

End KA.

Section G02.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis STEMC : U.Prog.reac_box_family_stem_c.reac_box_family_stem_contract.

Lemma g02_core : forall g c regs mem md L A pc0,
  Hcut B APIf ra (Inv_U13908 B APIf ra empty) ->
  c = mkCfg (mkst regs (Z_to_bv 64 pc0) mem (seg_rom (ms_segs B))) md ->
  FR B APIf ra empty g (2 * NR g + 2) [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) -> TID g mem -> TL g regs mem ->
  (pc0 = 0x138f4 /\ getr regs 10 = Z_to_bv 64 (n_fam (g_in g)) \/
   pc0 = 0x138fc /\ 128 <= t_fam_raw (g_in g)) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g c regs mem md L A pc0 HX -> HF HP HTID HTL PCS.
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HTL as (H24 & _).
  pose proof (uf_nfam_range (g_in g)) as Hnf.
  pose proof (inb_range (g_in g) (cT (g_in g) + 0)) as Hfr.
  change (inb (g_in g) (cT (g_in g) + 0)) with (t_fam_raw (g_in g)) in Hfr.
  pose proof (uf_bn_ts B APIf ra empty FF mem Hrel) as HT.
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 pc0) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (G02_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (n_fam (g_in g))
             (t_fam_raw (g_in g)) pc0 STEMC); [lia | |exact HT].
    destruct PCS as [(-> & E10)|(-> & Ge)].
    - left. split; [reflexivity|]. rewrite <- (uf_getr_reg regs 10) by reflexivity. exact E10.
    - right. split; [reflexivity|]. split; [rewrite <- (uf_getr_reg regs 24) by reflexivity; exact H24|].
      split; [lia|]. unfold n_fam. destruct (Z.leb_spec 128 (t_fam_raw (g_in g))); [reflexivity | lia]. }
  intros R pc' m' regs1 ((a1 & ->) & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27] regs regs1) by uf_kp XR regs.
  apply HX. exists L, A, regs1, mem, md. split; [reflexivity|].
  split.
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  split; [exact HP|].
  split; [exact HTID|].
  split; [exact (uf_TL_kp g regs regs1 mem mem (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto))
                   ltac:(apply uf_FReq_eq; reflexivity) HTL)|].
  split; [rewrite (uf_getr_x _ _ 26 XR) by reflexivity; reflexivity|].
  rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity.
Qed.

Lemma seg_G02 : Hcut B APIf ra (Inv_U13908 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U138f4 B APIf ra empty) /\ Hcut B APIf ra (Inv_U138fc B APIf ra empty).
Proof.
  intros HX. split.
  - intros g c (L & A & regs & mem & md & Ec & HF & HP & HTID & HTL & Lt & H10).
    apply (g02_core g c regs mem md L A 0x138f4 HX Ec HF HP HTID HTL). left. split; [reflexivity|].
    rewrite H10. unfold n_fam. destruct (Z.leb_spec 128 (t_fam_raw (g_in g))); [lia | reflexivity].
  - intros g c (L & A & regs & mem & md & Ec & HF & HP & HTID & HTL & Ge).
    apply (g02_core g c regs mem md L A 0x138fc HX Ec HF HP HTID HTL). right. split; [reflexivity | exact Ge].
Qed.

End G02.
