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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require bcmp_c reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require StrFun.

Lemma c03_hwb_len : forall inp i, length (rec_hwb inp i) = 8%nat.
Proof.
  intros inp i. unfold rec_hwb. induction i as [|i IH]; cbn [rec_hw]; [reflexivity|].
  destruct ((rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? rec_k inp i)) eqn:E; [|exact IH].
  apply andb_prop in E as [_ E]. apply Z.leb_le in E.
  rewrite length_firstn, rec_pl_length. lia.
Qed.

Lemma c03_none : forall hw, map bv_unsigned hw <> HWT 0 -> map bv_unsigned hw <> HWT 1 ->
  map bv_unsigned hw <> HWT 2 -> fam_cmp hw = 0.
Proof.
  intros hw H0 H1 H2. unfold fam_cmp. cbv zeta. cbn [HWT nth] in H0, H1, H2.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) lib.Prog.reac_box_family_of_c.FAMOF_HW1); [contradiction|].
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) lib.Prog.reac_box_family_of_c.FAMOF_HW2); [contradiction|].
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) lib.Prog.reac_box_family_of_c.FAMOF_HW3); [contradiction|].
  reflexivity.
Qed.

Lemma c03_tab : forall j, (j < 3)%nat ->
  uf_ro_chk (HWT_ADDR + 12 * Z.of_nat j) (map (Z_to_bv 8) (HWT j)) = true.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [vm_compute; reflexivity .. | lia]. Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma C03_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp : Z) (j : nat) (l r : list byte) (v : Z),
  U.Prog.bcmp_c.bcmp_contract -> mem_inv rsegs m ->
  x8 = Z_to_bv 64 (3 - Z.of_nat j) -> x18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat j) ->
  x19 = Z_to_bv 64 (sp + 132) -> (j < 3)%nat -> 0 <= sp -> sp + 384 <= 2 ^ 64 ->
  bytes_at rsegs m (sp + 132) l -> bytes_at rsegs m (HWT_ADDR + 12 * Z.of_nat j) r ->
  U.Spec.StrFun.memcmp_model l r 8 = Some v -> -256 < v < 256 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ munch [] m m' /\
       exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
         (v = 0 /\ pc' = Z_to_bv 64 0x13f04 /\
          R = mkR ra' x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                t3 t4 t5 t6) \/
         (v <> 0 /\ (S j < 3)%nat /\ pc' = Z_to_bv 64 0x136c8 /\
          R = mkR ra' x2 x3 x4 t0 t1 t2 (Z_to_bv 64 (3 - Z.of_nat (S j))) x9 a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat (S j))) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) \/
         (v <> 0 /\ j = 2%nat /\ pc' = Z_to_bv 64 0x13700 /\
          R = mkR ra' x2 x3 x4 t0 t1 t2 (Z_to_bv 64 0) x9 a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (HWT_ADDR + 36)) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136c8) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp j l r v BC MI E8 E18 E19 Hj Hsp Hsp2 BL BR Hv Hvr.
  subst x8 x18 x19.
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := l) (rs := r) (v := v).
    - rewrite unsigned_lit by lia. exact BL.
    - rewrite unsigned_lit by (unfold HWT_ADDR; lia). exact BR.
    - change (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) with 8%nat. exact Hv.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & _).
  rewrite uf_ret_pc_lit by lia.
  step.
  destruct (Z.eq_dec v 0) as [->|Hv0].
  - rewrite (uf_eqb 0 0) by lia. change (0 =? 0) with true. cbv iota.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|].
    do 16 eexists. left. split; [reflexivity|]. split; reflexivity.
  - rewrite (uf_bveq_nz v) by lia. cbv iota.
    step. step. step.
    destruct j as [|[|[|j]]]; [| | | lia]; cbn [Z.of_nat Z.mul Z.add] in *;
    lazymatch goal with
    | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let b := eval vm_compute in c in replace c with b by (vm_compute; reflexivity); cbv iota
    end.
    + step. apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|].
      do 16 eexists. right; left. split; [exact Hv0|]. split; [lia|]. split; [reflexivity|].
      f_equal; apply bv_eq; vm_compute; reflexivity.
    + step. apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|].
      do 16 eexists. right; left. split; [exact Hv0|]. split; [lia|]. split; [reflexivity|].
      f_equal; apply bv_eq; vm_compute; reflexivity.
    + apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|].
      do 16 eexists. right; right. split; [exact Hv0|]. split; [reflexivity|]. split; [reflexivity|].
      f_equal; apply bv_eq; vm_compute; reflexivity.
Qed.

End KA.

Section C03.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis BC : U.Prog.bcmp_c.bcmp_contract.

Lemma c03_step : forall g j,
  Hcut B APIf ra (Inv_U13f04 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13700 B APIf ra empty) ->
  (forall c', Inv_U136c8_at B APIf ra empty g (S j) c' -> Rz (ms_segs B) c' (Post B APIf ra g)) ->
  forall c, Inv_U136c8_at B APIf ra empty g j c -> Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g j Hf04 H700 IH c (L & A & regs & mem & md & -> & HF & HP & HCB & Hhv & H9 & H19 & H8 & H18 & Hj & Hmiss).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HCB as (HNR & HNRb & HG24 & (W1 & W2 & W3) & HCUR & HID).
  assert (HRO : ro_agree rsegs mem) by (rewrite <- SEG; exact HMI).
  assert (Hlen : length (hwbT (g_in g)) = 8%nat) by apply c03_hwb_len.
  assert (BR : bytes_at rsegs (normalize rsegs mem) (HWT_ADDR + 12 * Z.of_nat j) (map (Z_to_bv 8) (HWT j))).
  { apply (uf_ro_chk_bytes _ _ _ (uf_ro_agree_norm mem) (c03_tab j Hj)); [unfold HWT_ADDR; lia|].
    destruct j as [|[|[|j]]]; [cbn; unfold HWT_ADDR; lia .. | lia]. }
  assert (Hlr : length (map (Z_to_bv 8) (HWT j)) = 8%nat) by (destruct j as [|[|[|j]]]; [reflexivity .. | lia]).
  destruct (U.Spec.StrFun.memcmp_model_total (hwbT (g_in g)) (map (Z_to_bv 8) (HWT j)) 8 ltac:(lia) ltac:(lia))
    as [v Hv].
  destruct (U.Prog.reac_box_family_of.famof_memcmp 8 (hwbT (g_in g)) (map (Z_to_bv 8) (HWT j)) v Hlen Hlr Hv)
    as [Rv Iv].
  assert (EM : map bv_unsigned (map (Z_to_bv 8) (HWT j)) = HWT j)
    by (destruct j as [|[|[|j]]]; [vm_compute; reflexivity .. | lia]).
  rewrite EM in Iv.
  eapply (uf_kA_run B APIf ra empty FF regs (Z_to_bv 64 0x136c8) mem md); [exact Hh | exact Hl | exact HMI | |].
  { unfold mkR_of.
    apply (C03_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs mem) (fsp g) j
             (hwbT (g_in g)) (map (Z_to_bv 8) (HWT j)) v BC).
    - apply mem_inv_normalize.
    - rewrite <- (uf_getr_reg regs 8) by reflexivity. exact H8.
    - rewrite <- (uf_getr_reg regs 18) by reflexivity. exact H18.
    - rewrite <- (uf_getr_reg regs 19) by reflexivity. exact H19.
    - exact Hj.
    - lia.
    - lia.
    - apply bytes_at_normalize; [exact HRO | exact W3].
    - exact BR.
    - exact Hv.
    - exact Rv. }
  intros R pc' m' regs1 mem1 (MU & ra' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & BR3)
    XR Hmr Hsame.
  pose proof (uf_nowrite0 mem mem1 m' Hmr Hsame MU) as EQM.
  assert (FRe : FReq g mem mem1) by (apply uf_FReq_eq; exact EQM).
  assert (BS : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs mem1 a bs).
  { intros a bs HB. apply (uf_bytes_same rsegs mem mem1 a bs); [|exact HB]. intros i _. apply EQM. }
  destruct BR3 as [(V0 & -> & ->) | [(V0 & Hj' & -> & ->) | (V0 & Ej & -> & ->)]].
  - assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
    apply Hf04. exists j, L, A, regs1, mem1, md. split; [reflexivity|].
    split.
    { apply (uf_FR_kA B APIf ra empty FF g _ _ L A regs mem md regs1 mem1 HF HP
               (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in))).
      - intros x _ _. apply EQM.
      - apply uf_wmono_eq. exact EQM. }
    split; [exact HP|].
    split.
    { split; [exact HNR|]. split; [apply BS; exact HNRb|]. split; [apply BS; exact HG24|].
      split; [split; [apply BS; exact W1 | split; apply BS; assumption]|].
      split; [|apply BS; exact HID].
      destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
    split; [exact Hhv|]. split; [uf_k KP1 9; exact H9|]. split; [uf_k KP1 18; exact H18|].
    split; [exact Hj|]. split; [apply Iv; exact V0 | exact Hmiss].
  - assert (KP1 : KP [2; 3; 4; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
    apply IH. exists L, A, regs1, mem1, md. split; [reflexivity|].
    split.
    { apply (uf_FR_kA B APIf ra empty FF g _ _ L A regs mem md regs1 mem1 HF HP
               (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in))).
      - intros x _ _. apply EQM.
      - apply uf_wmono_eq. exact EQM. }
    split; [exact HP|].
    split.
    { split; [exact HNR|]. split; [apply BS; exact HNRb|]. split; [apply BS; exact HG24|].
      split; [split; [apply BS; exact W1 | split; apply BS; assumption]|].
      split; [|apply BS; exact HID].
      destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
    split; [exact Hhv|]. split; [uf_k KP1 9; exact H9|]. split; [uf_k KP1 19; exact H19|].
    split; [rewrite (uf_getr_x _ _ 8 XR) by reflexivity; reflexivity|].
    split; [rewrite (uf_getr_x _ _ 18 XR) by reflexivity; reflexivity|].
    split; [exact Hj'|].
    intros j' Hj''. destruct (Nat.eq_dec j' j) as [->|Hne]; [|apply Hmiss; lia].
    intros X. apply V0. apply Iv. exact X.
  - assert (KP1 : KP [2; 3; 4; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
    apply H700. exists L, A, regs1, mem1, md. split; [reflexivity|].
    split.
    { apply (uf_FR_kA B APIf ra empty FF g _ _ L A regs mem md regs1 mem1 HF HP
               (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in))).
      - intros x _ _. apply EQM.
      - apply uf_wmono_eq. exact EQM. }
    split; [exact HP|].
    split.
    { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
    split; [split; apply BS; assumption|].
    split; [uf_k KP1 9; exact H9|].
    subst j. rewrite Hhv. unfold fam_hw. cbn [Z.eqb].
    apply c03_none; [apply Hmiss; lia | apply Hmiss; lia |].
    intros X. apply V0. apply Iv. exact X.
Qed.

Lemma seg_C03 : Hcut B APIf ra (Inv_U13f04 B APIf ra empty) -> Hcut B APIf ra (Inv_U13700 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U136c8 B APIf ra empty).
Proof.
  intros Hf04 H700 g c [j Hc].
  assert (Hind : forall k j' c', (3 - j' = k)%nat -> Inv_U136c8_at B APIf ra empty g j' c' ->
                   Rz (ms_segs B) c' (Post B APIf ra g)).
  { induction k as [|k IHk]; intros j' c' Hk Hc'.
    - destruct Hc' as (L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _). lia.
    - apply (c03_step g j' Hf04 H700); [|exact Hc'].
      intros c'' Hc''. apply (IHk (S j') c''); [lia | exact Hc'']. }
  exact (Hind (3 - j)%nat j c eq_refl Hc).
Qed.

End C03.
