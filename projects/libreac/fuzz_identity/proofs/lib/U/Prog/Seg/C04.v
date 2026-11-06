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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_of_c.

Lemma c04_nil : forall inp, nlen inp = 0 -> inp = [].
Proof. intros [|b inp] H; [reflexivity|]. unfold nlen in H. cbn [length] in H. lia. Qed.

Lemma c04_nrecn0 : forall inp, nrec inp = 0 -> nrecn inp = 0%nat.
Proof. intros inp H. unfold nrecn. rewrite H. reflexivity. Qed.

Lemma c04_fam : forall a idb, a <> 0 -> lib.Prog.reac_box_family_of_c.FAMOF_FAM a idb = FAM idb.
Proof.
  intros a idb H. unfold FAM, lib.Prog.reac_box_family_of_c.FAMOF_FAM.
  destruct (Z.eqb_spec a 0); [lia|]. reflexivity.
Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma C04_e : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             (Z_to_bv 64 0) x18 x27 x28 x29 x30 x31 /\ pc' = Z_to_bv 64 0x136f4 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136ec) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m.
  step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma C04_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp lo : Z) (idb : list byte),
  U.Prog.reac_box_family_of_c.reac_box_family_of_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 384 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> lo + 32 <= sp -> IMG_HI <= lo ->
  bytes_at rsegs m (sp + 146) idb -> length idb = 38%nat ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x136fc) x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 (FAM idb))
                a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x136fc /\ munch [(sp - 32, sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136f4) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp lo idb FO HRO E2 Hsp Hsp2 Hal ST HL HI BID Hlid.
  subst x2. unfold IMG_HI in HI.
  step. step.
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
    rewrite (c04_fam (sp + 146) idb) by lia.
    rewrite unsigned_lit in MU by lia.
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 14 eexists; reflexivity|].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact RO].
Qed.

End KA.

Section C04.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FO : U.Prog.reac_box_family_of_c.reac_box_family_of_contract.

Lemma c04_f4 : Hcut B APIf ra (Inv_U136fc B APIf ra empty) -> Hcut B APIf ra (Inv_U136f4 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HNR & HCUR & HG24 & HID).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof (c04_nrecn0 (g_in g) HNR) as HNRn.
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136f4) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (C04_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (g_S g - SLOT_K)
             (rec_id (g_in g) 0) FO).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
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
  assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
  assert (G10 : getr regs1 10 = Z_to_bv 64 (FAM (rec_id (g_in g) 0)))
    by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  assert (KEEP : forall a bs, bytes_at rsegs mem a bs -> fsp g <= a -> bytes_at rsegs m' a bs).
  { intros a bs H Ha. apply (uf_bytes_munch1 _ _ mem m' a bs MU); [right; lia | exact H]. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
    intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  split; [exact HP|].
  split; [exact HNR|].
  split.
  { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
  split; [unfold G24, q64, spk in *; apply KEEP; [exact HG24 | lia]|].
  split; [unfold IDb, spk in *; apply KEEP; [exact HID | lia]|].
  rewrite G10. unfold idT. rewrite HNRn. reflexivity.
Qed.

Lemma seg_C04 : Hcut B APIf ra (Inv_U136fc B APIf ra empty) ->
  Hcut B APIf ra (Inv_U136ec B APIf ra empty) /\ Hcut B APIf ra (Inv_U136f4 B APIf ra empty).
Proof.
  intros HX. pose proof (c04_f4 HX) as Hf4. split; [|exact Hf4].
  intros g c (L & A & regs & mem & md & -> & HF & HP & Hn0 & H9 & H18 & HG24 & HID).
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof (c04_nil (g_in g) Hn0) as Hnil.
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136ec) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply C04_e. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4] regs regs1) by uf_kp XR regs.
  apply Hf4. exists L, A, regs1, mem, md. split; [reflexivity|].
  split.
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - exact KP1.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  split; [exact HP|].
  split; [unfold NR; rewrite Hnil; reflexivity|].
  split; [|split; [exact HG24 | exact HID]].
  assert (EcT : cT (g_in g) = 0) by (rewrite Hnil; reflexivity).
  unfold CUR. rewrite EcT, Hn0.
  split; [lia|].
  split.
  - rewrite (uf_getr_x _ _ 26 XR) by reflexivity. rewrite <- (uf_getr_reg regs 18) by reflexivity. rewrite H18.
    f_equal. lia.
  - rewrite (uf_getr_x _ _ 25 XR) by reflexivity. reflexivity.
Qed.

End C04.
