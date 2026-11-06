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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_of_c.

Lemma g01_slli : forall x, 0 <= x < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  intros x Hx. rewrite ZBridge.bv_lts_zero_r, MState.unsigned_lit_wrap, (MState.unsigned_lit x) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  destruct (Z.leb_spec (2 ^ 63) (x * 2 ^ 56)); destruct (Z.leb_spec 128 x); reflexivity || lia.
Qed.

Lemma g01_fam : forall a idb, a <> 0 -> lib.Prog.reac_box_family_of_c.FAMOF_FAM a idb = FAM idb.
Proof.
  intros a idb H. unfold FAM, lib.Prog.reac_box_family_of_c.FAMOF_FAM.
  destruct (Z.eqb_spec a 0); [lia|]. reflexivity.
Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma G01_x1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp fr lo : Z) (idb : list byte),
  U.Prog.reac_box_family_of_c.reac_box_family_of_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 0 -> x24 = Z_to_bv 64 fr -> 0 <= fr < 128 ->
  0 <= sp -> sp + 384 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> lo + 32 <= sp -> IMG_HI <= lo ->
  bytes_at rsegs m (sp + 146) idb -> length idb = 38%nat ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x138f4) x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 (FAM idb))
                a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x138f4 /\ munch [(sp - 32, sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x138e0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp fr lo idb FO HRO E2 E10 E24 Hfr Hsp Hsp2 Hal ST HL HI BID Hlid.
  subst x2 x10 x24. unfold IMG_HI in HI.
  step. if_false. step. step.
  rewrite (g01_slli fr) by lia. replace (128 <=? fr) with false by (symmetry; apply Z.leb_gt; lia).
  cbv iota. step. step.
  eapply (uf_famof_call FO) with (lo := lo) (a := sp + 146) (idb := idb).
  - exact HRO.
  - reflexivity.
  - lia.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. lia.
  - unfold IMG_HI. lia.
  - right. split; [exact BID|]. split; [exact Hlid|]. split; [Z.div_mod_to_equations; lia|].
    right. rewrite unsigned_lit by lia. lia.
  - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO.
    rewrite (g01_fam (sp + 146) idb) by lia.
    rewrite unsigned_lit in MU by lia.
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 14 eexists; reflexivity|].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact RO].
Qed.

Lemma G01_x2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (fr : Z),
  x10 = Z_to_bv 64 0 -> x24 = Z_to_bv 64 fr -> 128 <= fr < 256 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists a0, R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31) /\
       pc' = Z_to_bv 64 0x138fc /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x138e0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m fr E10 E24 Hfr.
  subst x10 x24.
  step. if_false. step. step.
  rewrite (g01_slli fr) by lia. replace (128 <=? fr) with true by (symmetry; apply Z.leb_le; lia).
  cbv iota.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [eexists; reflexivity|]. split; reflexivity.
Qed.

End KA.

Section G01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FO : U.Prog.reac_box_family_of_c.reac_box_family_of_contract.

Lemma seg_G01 : Hcut B APIf ra (Inv_U138f4 B APIf ra empty) -> Hcut B APIf ra (Inv_U138fc B APIf ra empty) ->
  Hcut B APIf ra (Inv_U138e0 B APIf ra empty).
Proof.
  intros H8f4 H8fc g c (L & A & regs & mem & md & -> & HF & HP & ((HE & H18 & HC64 & HC242) & H10)).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H22).
  pose proof HTL as (H24 & _).
  pose proof (inb_range (g_in g) (cT (g_in g) + 0)) as Hfr.
  change (inb (g_in g) (cT (g_in g) + 0)) with (t_fam_raw (g_in g)) in Hfr.
  destruct (Z_lt_ge_dec (t_fam_raw (g_in g)) 128) as [Lt|Ge].
  - pose proof HTID as (HG24 & HID).
    eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x138e0) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of.
      apply (G01_x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (t_fam_raw (g_in g))
               (g_S g - SLOT_K) (idT (g_in g)) FO).
      - rewrite <- SEG. exact HMI.
      - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
      - rewrite <- (uf_getr_reg regs 10) by reflexivity. exact H10.
      - rewrite <- (uf_getr_reg regs 24) by reflexivity. exact H24.
      - lia.
      - lia.
      - lia.
      - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
      - exact ST.
      - lia.
      - exact HI.
      - exact HID.
      - apply rec_id_length. }
    intros R pc' m' regs1 (Hreg & -> & MU & WM & RO) XR.
    destruct Hreg as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
    assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
    assert (G10 : getr regs1 10 = Z_to_bv 64 (FAM (idT (g_in g))))
      by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
    assert (OUT : FRout g [(fsp g - 32, fsp g)]).
    { intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. unfold spk. lia. }
    apply H8f4. exists L, A, regs1, m', md. split; [reflexivity|].
    split.
    { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
               (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
      intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
    split; [exact HP|].
    split; [exact (uf_TID_munch g _ mem m' MU OUT HTID)|].
    split; [exact (uf_TL_munch g _ regs regs1 mem m'
                     (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) MU OUT HTL)|].
    split; [exact Lt | exact G10].
  - eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x138e0) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of.
      apply (G01_x2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (t_fam_raw (g_in g))).
      - rewrite <- (uf_getr_reg regs 10) by reflexivity. exact H10.
      - rewrite <- (uf_getr_reg regs 24) by reflexivity. exact H24.
      - lia. }
    intros R pc' m' regs1 ((a0 & ->) & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
    apply H8fc. exists L, A, regs1, mem, md. split; [reflexivity|].
    split.
    { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
      - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
      - intros x _ _. reflexivity.
      - apply uf_wmono_eq. intros w. reflexivity. }
    split; [exact HP|].
    split; [exact HTID|].
    split; [exact (uf_TL_kp g regs regs1 mem mem (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto))
                     ltac:(apply uf_FReq_eq; reflexivity) HTL)|].
    lia.
Qed.

End G01.
