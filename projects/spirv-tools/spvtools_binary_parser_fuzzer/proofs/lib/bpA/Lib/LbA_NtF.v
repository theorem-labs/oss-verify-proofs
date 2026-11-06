(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HFpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs LibIface LbA_Bridge LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_HEmpF.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_f36ac : bv 32 := 0x0006a787.
Lemma F_f36ac : fetch_word asegs (Z_to_bv 64 0xf36bc) = Some W_f36ac. Proof. vm_refl. Qed.
Lemma D_f36ac : decode_any W_f36ac = Some (FLoad FMT_S 15 13 0, 4%Z). Proof. vm_refl. Qed.
Definition W_f36b4 : bv 32 := 0xd0357753.
Lemma F_f36b4 : fetch_word asegs (Z_to_bv 64 0xf36c4) = Some W_f36b4. Proof. vm_refl. Qed.
Lemma D_f36b4 : decode_any W_f36b4 = Some (Fcvt FC_S FC_LU 14 10 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f36b8 : bv 32 := 0xd03bf6d3.
Lemma F_f36b8 : fetch_word asegs (Z_to_bv 64 0xf36c8) = Some W_f36b8. Proof. vm_refl. Qed.
Lemma D_f36b8 : decode_any W_f36b8 = Some (Fcvt FC_S FC_LU 13 23 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f36bc : bv 32 := 0x10d7f6d3.
Lemma F_f36bc : fetch_word asegs (Z_to_bv 64 0xf36cc) = Some W_f36bc. Proof. vm_refl. Qed.
Lemma D_f36bc : decode_any W_f36bc = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f36c0 : bv 32 := 0xa0e69553.
Lemma F_f36c0 : fetch_word asegs (Z_to_bv 64 0xf36d0) = Some W_f36c0. Proof. vm_refl. Qed.
Lemma D_f36c0 : decode_any W_f36c0 = Some (Fcmp F_LT FMT_S 10 13 14, 4%Z). Proof. vm_refl. Qed.

Lemma lf_fpN : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (obj sz bc : Z),
  0 <= sz -> sz + 1 < 2 ^ 24 -> 0 <= bc < 2 ^ 24 -> (bc = 0 -> sz = 0) ->
  0 <= obj -> obj + 40 <= 2 ^ 47 ->
  PropExec.rdn asegs m (Z_to_bv 64 (obj + 32)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x3f800000)) ->
  frm_zero fc ->
  evt asegs (fun x => exists F' fc', x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (if bc <? sz + 1 then 1 else 0)) x11 x12 (Z_to_bv 64 (obj + 32)) x14 x15 x16 x17
                                             x18 x19 x20 x21 x22 (Z_to_bv 64 bc) x24 x25 x26 x27 x28 x29 x30 x31)
                                          F' (Z_to_bv 64 0xf36d4) fc' None m rom
               /\ frm_zero fc' /\ fholds (PropExec.mkFP F' fc') 15 one32 /\ fholds (PropExec.mkFP F' fc') 14 (ieee (sz + 1)))
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 sz) x11 x12 (Z_to_bv 64 (obj + 32)) x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 bc) x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xf36bc) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m rom obj sz bc
    Hsz Hsz1 Hbc Hbc0 Ho0 Ho1 RD FZ.
  set (R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 sz) x11 x12 (Z_to_bv 64 (obj + 32)) x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 bc) x24 x25 x26 x27 x28 x29 x30 x31).

  eapply evt_step.
  { split; [reflexivity|].
    eapply (fp_step_flw (PropExec.mkFP F fc) asegs R (Z_to_bv 64 0xf36bc) m rom W_f36ac 15%bv 13%bv 0%bv (Z_to_bv 64 (obj + 32)) _
              F_f36ac eq_refl D_f36ac); [change (PropExec.getr R 13) with (Z_to_bv 64 (obj + 32)); change (bv_signed 0%bv) with 0;
                                          rewrite v_addi_Z by lia; f_equal; lia | exact RD]. }
  cbn [PropExec.fp_regs PropExec.fp_csr]. rewrite flw_nan_box by lia. rewrite mkst_MS. rewrite v_addi_Z by lia.
  change (Z_to_bv 64 (0xf36bc + 4)) with (Z_to_bv 64 0xf36c0). subst R.

  step.
  lazymatch goal with |- evt _ _ (MS ?T ?FF _ _ _ _ _) => set (R1 := T); set (F1 := FF) end.
  assert (A1 : PropExec.getr R1 10 = Z_to_bv 64 (sz + 1)) by reflexivity.
  assert (A24 : PropExec.getr R1 23 = Z_to_bv 64 bc) by reflexivity.

  destruct (hp_step_fcvt_s_lu (PropExec.mkFP F1 fc) asegs R1 (Z_to_bv 64 0xf36c4) m rom W_f36b4 14%bv 10%bv 7%bv
              F_f36b4 eq_refl D_f36b4 FZ ltac:(right; reflexivity)) as [md1 S1].
  cbv zeta in S1. rewrite A1, u64_of_Z, of_int_val in S1 by lia. cbn [fst snd] in S1.
  eapply evt_step; [split; [reflexivity | exact S1] |].
  rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (997060 + 4)) with (Z_to_bv 64 0xf36c8). cbn [PropExec.fp_regs PropExec.fp_csr].
  set (F2 := bvmap_set 14 _ F1). set (fc2 := accrue_csr fc no_flags).
  assert (FZ2 : frm_zero fc2) by (apply frm_zero_accrue_csr; exact FZ).

  destruct (hp_step_fcvt_s_lu (PropExec.mkFP F2 fc2) asegs R1 (Z_to_bv 64 0xf36c8) m rom W_f36b8 13%bv 23%bv 7%bv
              F_f36b8 eq_refl D_f36b8 FZ2 ltac:(right; reflexivity)) as [md2 S2].
  cbv zeta in S2. rewrite A24, u64_of_Z in S2 by lia.
  pose proof (ieee_range (sz + 1) ltac:(lia)) as IE1.
  assert (H15 : fholds (PropExec.mkFP F2 fc2) 15 one32)
    by (apply fholds_set_other; [intros X; discriminate X | unfold fholds; cbn [PropExec.fp_regs]; subst F1; unfold reg_get; rewrite bvmap_get_set_same; reflexivity]).
  assert (H14 : fholds (PropExec.mkFP F2 fc2) 14 (ieee (sz + 1))) by (apply fholds_set_same; lia).
  destruct (Z.eq_dec bc 0) as [Hb0 | Hb1].
  -
    pose proof (Hbc0 Hb0) as Hsz0. subst bc. subst sz.
    rewrite of_int_zero in S2. cbn [fst snd] in S2.
    eapply evt_step; [split; [reflexivity | exact S2] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36c8 + 4)) with (Z_to_bv 64 0xf36cc). cbn [PropExec.fp_regs PropExec.fp_csr].
    set (F3 := bvmap_set 13 _ F2). set (fc3 := accrue_csr fc2 no_flags).
    assert (FZ3 : frm_zero fc3) by (apply frm_zero_accrue_csr; exact FZ2).
    assert (G15 : fholds (PropExec.mkFP F3 fc3) 15 one32) by (apply fholds_set_other; [intros X; discriminate X | exact H15]).
    assert (G14 : fholds (PropExec.mkFP F3 fc3) 14 (ieee (0 + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact H14]).
    assert (G13 : fholds (PropExec.mkFP F3 fc3) 13 0) by (apply fholds_set_same; lia).

    destruct (hp_step_fari_s (PropExec.mkFP F3 fc3) asegs R1 (Z_to_bv 64 0xf36cc) m rom W_f36bc F_MUL 13%bv 15%bv 13%bv 7%bv one32 0
                F_f36bc eq_refl D_f36bc FZ3 ltac:(right; reflexivity) G15 G13 ltac:(unfold one32; lia) ltac:(lia)) as [md3 S3].
    cbv zeta in S3. cbn [fari_op] in S3. rewrite mul_one_zero in S3. cbn [fst snd] in S3.
    eapply evt_step; [split; [reflexivity | exact S3] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36cc + 4)) with (Z_to_bv 64 0xf36d0). cbn [PropExec.fp_regs PropExec.fp_csr].
    set (F4 := bvmap_set 13 _ F3). set (fc4 := accrue_csr fc3 no_flags).
    assert (FZ4 : frm_zero fc4) by (apply frm_zero_accrue_csr; exact FZ3).
    assert (K15 : fholds (PropExec.mkFP F4 fc4) 15 one32) by (apply fholds_set_other; [intros X; discriminate X | exact G15]).
    assert (K14 : fholds (PropExec.mkFP F4 fc4) 14 (ieee (0 + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact G14]).
    assert (K13 : fholds (PropExec.mkFP F4 fc4) 13 0) by (apply fholds_set_same; lia).

    pose proof (hp_step_fcmp_s (PropExec.mkFP F4 fc4) asegs R1 (Z_to_bv 64 0xf36d0) m rom W_f36c0 F_LT 10%bv 13%bv 14%bv 0 (ieee (0 + 1))
                F_f36c0 eq_refl D_f36c0 K13 K14 ltac:(lia) ltac:(change (0 + 1) with 1 in *; lia)) as S4.
    cbv zeta in S4. cbn [fcmp_op] in S4. change (0 + 1) with 1 in S4. rewrite lt_zero_one in S4. cbn [fst snd] in S4.
    eapply evt_step; [split; [reflexivity | exact S4] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36d0 + 4)) with (Z_to_bv 64 0xf36d4). cbn [PropExec.fp_regs PropExec.fp_csr].
    apply evt_done. exists F4, (accrue_csr fc4 no_flags). split; [reflexivity|].
    split; [apply frm_zero_accrue_csr; exact FZ4|]. split; [exact K15 | exact K14].
  -
    rewrite of_int_val in S2 by lia. cbn [fst snd] in S2.
    pose proof (ieee_range bc ltac:(lia)) as IE2.
    eapply evt_step; [split; [reflexivity | exact S2] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36c8 + 4)) with (Z_to_bv 64 0xf36cc). cbn [PropExec.fp_regs PropExec.fp_csr].
    set (F3 := bvmap_set 13 _ F2). set (fc3 := accrue_csr fc2 no_flags).
    assert (FZ3 : frm_zero fc3) by (apply frm_zero_accrue_csr; exact FZ2).
    assert (G15 : fholds (PropExec.mkFP F3 fc3) 15 one32) by (apply fholds_set_other; [intros X; discriminate X | exact H15]).
    assert (G14 : fholds (PropExec.mkFP F3 fc3) 14 (ieee (sz + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact H14]).
    assert (G13 : fholds (PropExec.mkFP F3 fc3) 13 (ieee bc)) by (apply fholds_set_same; lia).

    destruct (hp_step_fari_s (PropExec.mkFP F3 fc3) asegs R1 (Z_to_bv 64 0xf36cc) m rom W_f36bc F_MUL 13%bv 15%bv 13%bv 7%bv one32 (ieee bc)
                F_f36bc eq_refl D_f36bc FZ3 ltac:(right; reflexivity) G15 G13 ltac:(unfold one32; lia) ltac:(lia)) as [md3 S3].
    cbv zeta in S3. cbn [fari_op] in S3. rewrite mul_one_val in S3 by lia. cbn [fst snd] in S3.
    eapply evt_step; [split; [reflexivity | exact S3] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36cc + 4)) with (Z_to_bv 64 0xf36d0). cbn [PropExec.fp_regs PropExec.fp_csr].
    set (F4 := bvmap_set 13 _ F3). set (fc4 := accrue_csr fc3 no_flags).
    assert (FZ4 : frm_zero fc4) by (apply frm_zero_accrue_csr; exact FZ3).
    assert (K15 : fholds (PropExec.mkFP F4 fc4) 15 one32) by (apply fholds_set_other; [intros X; discriminate X | exact G15]).
    assert (K14 : fholds (PropExec.mkFP F4 fc4) 14 (ieee (sz + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact G14]).
    assert (K13 : fholds (PropExec.mkFP F4 fc4) 13 (ieee bc)) by (apply fholds_set_same; lia).

    pose proof (hp_step_fcmp_s (PropExec.mkFP F4 fc4) asegs R1 (Z_to_bv 64 0xf36d0) m rom W_f36c0 F_LT 10%bv 13%bv 14%bv (ieee bc) (ieee (sz + 1))
                F_f36c0 eq_refl D_f36c0 K13 K14 ltac:(lia) ltac:(lia)) as S4.
    cbv zeta in S4. cbn [fcmp_op] in S4. rewrite lt_val in S4 by lia. cbn [fst snd] in S4.
    eapply evt_step; [split; [reflexivity | exact S4] |].
    rewrite mkst_MS, v_addi_Z by lia. change (Z_to_bv 64 (0xf36d0 + 4)) with (Z_to_bv 64 0xf36d4). cbn [PropExec.fp_regs PropExec.fp_csr].
    apply evt_done. exists F4, (accrue_csr fc4 no_flags). split; [reflexivity|].
    split; [apply frm_zero_accrue_csr; exact FZ4|]. split; [exact K15 | exact K14].
Qed.

Definition W_fcvlu10 : bv 32 := 0xc037b553.
Lemma F_f3704 : fetch_word asegs (Z_to_bv 64 0xf3714) = Some W_fdiv. Proof. vm_refl. Qed.
Lemma F_f3708 : fetch_word asegs (Z_to_bv 64 0xf3718) = Some W_fcvlu10. Proof. vm_refl. Qed.
Lemma D_fcvlu10 : decode_any W_fcvlu10 = Some (Fcvt (if false then FC_L else FC_LU) FC_S 10 15 3, 4%Z). Proof. vm_refl. Qed.

Lemma gr_fpN : forall (pc : Z) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (sz : Z),
  fetch_word asegs (Z_to_bv 64 pc) = Some W_fdiv -> fetch_word asegs (Z_to_bv 64 (pc + 4)) = Some W_fcvlu10 ->
  0 <= pc -> pc + 8 < 2 ^ 64 ->
  0 <= sz -> sz + 1 < 2 ^ 24 -> frm_zero fc ->
  fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee (sz + 1)) ->
  evt asegs (fun x => exists F' fc', x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sz + 1)) x11 x12 x13 x14 x15 x16 x17
                                             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                          F' (Z_to_bv 64 (pc + 8)) fc' None m rom /\ frm_zero fc')
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m rom sz FD FC P0 P1 Hsz Hsz1 FZ H15 H14.
  set (R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  pose proof (ieee_range (sz + 1) ltac:(lia)) as IE1.

  destruct (hp_step_fari_s (PropExec.mkFP F fc) asegs R (Z_to_bv 64 pc) m rom W_fdiv F_DIV 15%bv 14%bv 15%bv 7%bv (ieee (sz + 1)) one32
              FD eq_refl D_fdiv FZ ltac:(right; reflexivity) H14 H15 ltac:(lia) ltac:(unfold one32; lia)) as [md1 S1].
  cbv zeta in S1. cbn [fari_op] in S1. rewrite div_one_val in S1 by lia. cbn [fst snd] in S1.
  eapply evt_step; [split; [reflexivity | exact S1] |].
  rewrite mkst_MS, v_addi_Z by lia. cbn [PropExec.fp_regs PropExec.fp_csr].
  set (F1 := bvmap_set 15 _ F). set (fc1 := accrue_csr fc no_flags).
  assert (FZ1 : frm_zero fc1) by (apply frm_zero_accrue_csr; exact FZ).
  assert (G15 : fholds (PropExec.mkFP F1 fc1) 15 (ieee (sz + 1))) by (apply fholds_set_same; lia).

  destruct (hp_step_fcvt_l_s (PropExec.mkFP F1 fc1) asegs R (Z_to_bv 64 (pc + 4)) m rom W_fcvlu10 false 10%bv 15%bv 3%bv (ieee (sz + 1))
              FC eq_refl D_fcvlu10 FZ1 ltac:(left; vm_compute; intros X; discriminate X) G15 ltac:(lia)) as (md2 & Hmd2 & S2).
  cbv zeta in S2. rewrite to_lu_val in S2 by lia. cbn [fst snd] in S2.
  eapply evt_step; [split; [reflexivity | exact S2] |].
  rewrite mkst_MS, v_addi_Z by lia. cbn [PropExec.fp_regs PropExec.fp_csr].
  apply evt_done. exists F1, (accrue_csr fc1 no_flags). split; [|apply frm_zero_accrue_csr; exact FZ1].
  replace (pc + 4 + 4) with (pc + 8) by lia. reflexivity.
Qed.
