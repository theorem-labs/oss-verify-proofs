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

Lemma c05_fam_row : forall hw j, (j < 3)%nat -> map bv_unsigned hw = HWT j -> fam_cmp hw = Z.of_nat j + 1.
Proof.
  intros hw j Hj H. unfold fam_cmp. cbv zeta. rewrite H.
  destruct j as [|[|[|j]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

Lemma c05_rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma c05_row_chk : forall j, (j < 3)%nat ->
  uf_ro_chk (HWT_ADDR - 4 + 12 * Z.of_nat j) [Z_to_bv 8 (Z.of_nat j + 1); Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] = true.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [vm_compute; reflexivity .. | lia]. Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma C05_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  x10 = Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x10 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31 /\ pc' = Z_to_bv 64 0x13704 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136fc) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m E10. subst x10.
  step. step.
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let b := eval vm_compute in c in replace c with b by (vm_compute; reflexivity); cbv iota
  end.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma C05_b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  x9 = Z_to_bv 64 0 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31 /\ pc' = Z_to_bv 64 0x13704 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13700) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m E9. subst x9.
  step.
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let b := eval vm_compute in c in replace c with b by (vm_compute; reflexivity); cbv iota
  end.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma C05_c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (j : nat),
  (j < 3)%nat -> x9 = Z_to_bv 64 (Z.of_nat j + 1) -> x18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) ->
  ov_read_bytes rsegs m (wa (HWT_ADDR - 4 + 12 * Z.of_nat j)) 4 =
    Some [Z_to_bv 8 (Z.of_nat j + 1); Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists a0, R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31) /\ pc' = Z_to_bv 64 0x13704 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13f04) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m j Hj E9 E18 RD. subst x9 x18.
  destruct j as [|[|[|j]]]; [| | | lia]; cbn [Z.of_nat Z.mul Z.add] in *; unfold HWT_ADDR in *; cbn [Z.add Z.sub] in RD;
  step; step;
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let b := eval vm_compute in c in replace c with b by (vm_compute; reflexivity); cbv iota
  end;
  apply evt_done; do 3 eexists; (split; [reflexivity|]); (split; [eexists; reflexivity|]); split; reflexivity.
Qed.

End KA.

Section C05.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma c05_exit : forall g L A regs mem md regs1,
  Hcut B APIf ra (Inv_U13704 B APIf ra empty) ->
  forall km, km = 2 * NR g -> FR B APIf ra empty g km [] L A regs mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  CUR g (cT (g_in g)) regs -> TID g mem -> KP [2; 3; 4; 25; 26] regs regs1 ->
  Rz (ms_segs B) (mkCfg (mkst regs1 (Z_to_bv 64 0x13704) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g L A regs mem md regs1 HX km Ekm HF HP HCUR HTID KP1. subst km.
  apply HX. exists L, A, regs1, mem, md. split; [reflexivity|].
  split.
  { apply (uf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply uf_wmono_eq. intros w. reflexivity. }
  split; [exact HP|].
  split.
  { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
  split; [exact HTID|]. exact (rec_P7 (g_in g) (nrecn (g_in g))).
Qed.

Lemma seg_C05 : Hcut B APIf ra (Inv_U13704 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U136fc B APIf ra empty) /\ Hcut B APIf ra (Inv_U13700 B APIf ra empty) /\
  Hcut B APIf ra (Inv_U13f04 B APIf ra empty).
Proof.
  intros HX. split; [|split].
  - intros g c (L & A & regs & mem & md & -> & HF & HP & HNR & HCUR & HG24 & HID & H10).
    pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
    destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
    assert (HNRn : nrecn (g_in g) = 0%nat) by (unfold nrecn; unfold NR in HNR; rewrite HNR; reflexivity).
    assert (E0 : FAM (idT (g_in g)) = 0).
    { unfold idT. rewrite rec_P7. unfold rec_have. rewrite HNRn. reflexivity. }
    eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136fc) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of. apply C05_a. rewrite <- (uf_getr_reg regs 10) by reflexivity. rewrite H10, E0. reflexivity. }
    intros R pc' m' regs1 (-> & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
    apply (c05_exit g L A regs mem md regs1 HX 0 ltac:(lia) HF HP HCUR); [|exact KP1].
    split; [exact HG24|]. unfold IDb, NRn. rewrite HNRn. exact HID.
  - intros g c (L & A & regs & mem & md & -> & HF & HP & HCUR & HTID & H9 & Hfh).
    pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
    destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
    assert (E0 : FAM (idT (g_in g)) = 0).
    { pose proof (rec_P7 (g_in g) (nrecn (g_in g))) as P7. exact (eq_trans P7 Hfh). }
    eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13700) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of. apply C05_b. rewrite <- (uf_getr_reg regs 9) by reflexivity. rewrite H9, E0. reflexivity. }
    intros R pc' m' regs1 (-> & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
    exact (c05_exit g L A regs mem md regs1 HX _ eq_refl HF HP HCUR HTID KP1).
  - intros g c [j (L & A & regs & mem & md & -> & HF & HP & HCB & Hhv & H9 & H18 & Hj & Hrow & Hmiss)].
    pose proof (uf_segs B APIf ra empty FF) as SEG.
    pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
    destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
    pose proof HCB as (_ & _ & HG24 & _ & HCUR & HID).
    assert (HRO : ro_agree rsegs mem) by (rewrite <- SEG; exact HMI).
    assert (EF : FAM (idT (g_in g)) = Z.of_nat j + 1).
    { pose proof (rec_P7 (g_in g) (nrecn (g_in g))) as P7. refine (eq_trans P7 _).
      change (rec_have (g_in g) (nrecn (g_in g))) with (haveT (g_in g)).
      rewrite Hhv. unfold fam_hw. cbn [Z.eqb]. apply c05_fam_row; assumption. }
    assert (RD : ov_read_bytes rsegs mem (wa (HWT_ADDR - 4 + 12 * Z.of_nat j)) 4 =
                 Some [Z_to_bv 8 (Z.of_nat j + 1); Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
    { apply (c05_rd_all mem _ [_; _; _; _]).
      apply (uf_ro_chk_bytes _ _ _ HRO (c05_row_chk j Hj)); unfold HWT_ADDR; cbn [Datatypes.length]; lia. }
    eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13f04) mem md); [exact Hh | exact Hl | |].
    { unfold mkR_of. apply (C05_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem j Hj).
      - rewrite <- (uf_getr_reg regs 9) by reflexivity. rewrite H9, EF. reflexivity.
      - rewrite <- (uf_getr_reg regs 18) by reflexivity. exact H18.
      - exact RD. }
    intros R pc' m' regs1 ((a0 & ->) & -> & ->) XR.
    assert (KP1 : KP [2; 3; 4; 25; 26] regs regs1) by uf_kp XR regs.
    exact (c05_exit g L A regs mem md regs1 HX _ eq_refl HF HP HCUR (conj HG24 HID) KP1).
Qed.

End C05.
