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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_stem_c buf_of_c.

Lemma g3_stem_ne0 : forall f,
  bv_eqb (Z_to_bv 64 (U.Prog.reac_box_family_stem_c.STEM_Addr f)) (Z_to_bv 64 0) = false.
Proof.
  intros f. unfold U.Prog.reac_box_family_stem_c.STEM_Addr.
  destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma g3_firstn1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [RcIdentModel.nthb l k].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH by lia. reflexivity.
Qed.

Lemma g3_land255 : forall c, 0 <= c < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 c)) 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. rewrite MState.unsigned_lit by lia. f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma G03_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp f cn ct : Z) (b : byte),
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 (U.Prog.reac_box_family_stem_c.STEM_Addr f) ->
  x25 = Z_to_bv 64 cn -> x27 = Z_to_bv 64 ct -> 0 <= cn < 256 -> 0 <= ct < 256 ->
  0 <= sp -> sp + 384 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp + 166)) 1 = Some [b] ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists a1, R = mkR (Z_to_bv 64 0x13930) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 cn) a1 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 (bv_unsigned b)) x19 x20 x21 x22 (Z_to_bv 64 ct) (Z_to_bv 64 cn)
             (Z_to_bv 64 (if bv_unsigned b =? 0 then 0 else sp + 149)) x26 x27 x28 x29 x30 x31) /\
       pc' = Z_to_bv 64 0x140f0 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13908) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp f cn ct b E2 E10 E25 E27 Hcn Hct Hsp Hsp2 HRD.
  subst x2 x10 x25 x27.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  step. if_false_by (g3_stem_ne0 f).
  step. step. step. step. step. step. step. step. step.
  rewrite !g3_land255 by lia.
  unfold zxb.
  rewrite (uf_said (bv_unsigned b) (sp + 149)) by (cbn in Hb; lia).
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [eexists; reflexivity|]. split; reflexivity.
Qed.

End KA.

Section G03.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_G03 : Hcut B APIf ra (Inv_U13930 B APIf ra empty) -> Hcut B APIf ra (Inv_U13908 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HTID & HTL & H26 & H10).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HTL as (H24 & H9 & H56 & H48 & H25 & H27 & H19).
  pose proof HTID as (HG24 & HID).
  assert (Cn : 0 <= t_cap_name (g_in g) < 40) by (unfold t_cap_name; apply Z.mod_pos_bound; lia).
  assert (Ct : 0 <= t_cap_tok (g_in g) < 40) by (unfold t_cap_tok; apply Z.mod_pos_bound; lia).
  assert (HRO : ro_agree rsegs mem) by (rewrite <- SEG; exact HMI).
  set (idb := idT (g_in g)) in *.
  assert (Lid : length idb = RcIdentModel.ID_SIZE) by apply rec_id_length.
  assert (HRD : ov_read_bytes rsegs mem (wa (fsp g + 166)) 1 = Some [RcIdentModel.nthb idb 20]).
  { unfold IDb, spk in HID. change (rec_id (g_in g) (NRn g)) with idb in HID.
    replace (fsp g + 166) with (fsp g + 146 + 20) by lia.
    rewrite (bytes_at_read rsegs _ _ _ 20 1 HID) by (try rewrite Lid; unfold RcIdentModel.ID_SIZE; lia).
    change (Z.to_nat 20) with 20%nat. change (Z.to_nat 1) with 1%nat. rewrite g3_firstn1; [reflexivity|].
    rewrite Lid. unfold RcIdentModel.ID_SIZE. lia. }
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13908) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (G03_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (n_fam (g_in g))
             (t_cap_name (g_in g)) (t_cap_tok (g_in g)) (RcIdentModel.nthb idb 20)).
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (uf_getr_reg regs 25) by reflexivity. exact H25.
    - rewrite <- (uf_getr_reg regs 27) by reflexivity. exact H27.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HRD. }
  intros R pc' m' regs1 ((a1 & ->) & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 19; 20; 21; 22; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x13930) by (rewrite (uf_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (t_cap_name (g_in g)))
    by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  assert (G18 : getr regs1 18 = Z_to_bv 64 (RcIdentModel.has_model_name idb))
    by (rewrite (uf_getr_x _ _ 18 XR) by reflexivity; reflexivity).
  assert (G23 : getr regs1 23 = Z_to_bv 64 (t_cap_tok (g_in g)))
    by (rewrite (uf_getr_x _ _ 23 XR) by reflexivity; reflexivity).
  assert (G24 : getr regs1 24 = Z_to_bv 64 (t_cap_name (g_in g)))
    by (rewrite (uf_getr_x _ _ 24 XR) by reflexivity; reflexivity).
  assert (G25 : getr regs1 25 = Z_to_bv 64 (said_v g)).
  { rewrite (uf_getr_x _ _ 25 XR) by reflexivity. unfold said_v, n_said, spk.
    change (bv_unsigned (RcIdentModel.nthb idb 20)) with (RcIdentModel.has_model_name idb).
    change (idT (g_in g)) with idb.
    destruct (RcIdentModel.has_model_name idb =? 0); reflexivity. }
  assert (HF1 : FR B APIf ra empty g (2 * NR g + 2) [] L A regs1 mem md).
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  change (Z_to_bv 64 0x140f0) with (Z_to_bv 64 U.Prog.buf_of_c.BUF_OF).
  apply (uf_bufof_step B APIf ra empty FF g (2 * NR g + 2) [] L A regs1 mem md (t_cap_name (g_in g)) _ HF1 HP).
  - cbn [Datatypes.length]. lia.
  - unfold hb_bytes. cbn. lia.
  - lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 _.
    rewrite G1.
    replace (2 * NR g + 2 + 1) with (2 * NR g + 3) in HF2 by lia.
    apply HX. exists res, L', A', regs2, mem2, md2. split; [reflexivity|].
    split; [exact HF2|]. split; [exact HP2|].
    assert (FRe : FReq g mem mem2) by (intros x Hx; rewrite <- SEG; exact (FRM2 x Hx)).
    split; [|exact R10].
    split; [exact (uf_TID_tr g mem mem2 FRe HTID)|].
    split; [uf_cs RP2 9; uf_k KP1 9; exact H9|].
    split; [exact (uf_q64_tr g mem mem2 56 _ FRe ltac:(unfold SLOT_FRAME; lia) H56)|].
    split; [exact (uf_q64_tr g mem mem2 48 _ FRe ltac:(unfold SLOT_FRAME; lia) H48)|].
    split; [uf_cs RP2 19; uf_k KP1 19; exact H19|].
    split; [uf_cs RP2 18; exact G18|].
    split; [uf_cs RP2 24; exact G24|].
    split; [uf_cs RP2 23; exact G23|].
    split; [uf_cs RP2 25; exact G25|].
    uf_cs RP2 26; uf_k KP1 26; exact H26.
Qed.

End G03.
