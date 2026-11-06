(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY07.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymPlanSoundA.
From LinuxProcessSemantics.LinuxProcessSem Require Monad Specs.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require CatSim SeqExec StoreOk SimInv ExitSim Nodes MmapSim AllocSim FileSim AgentLib ShapeLaws SpecConsts LibWritev RefNodes UbExitBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require StepTac WalkTac LibAtomic Ub_code_1735c_17f20 Ub_code_186e0_18f94.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbLibCas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_186e0_18f94.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Lemma lw_bytes : forall old, (0 <= old < 2 ^ 32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 old)) = bv_unsigned (Z_to_bv 64 old).
Proof.
  intros old Hold. rewrite bytes_le_N. rewrite (u_Z2bv old) by lia.
  apply Z.mod_small. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite (u_Z2bv z) by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma sextw_lw : forall v : word, v_addiw (v_lw v) 0 = v_lw v.
Proof.
  intros v. unfold v_addiw, v_lw. f_equal. rewrite Z.add_0_r, Z_to_bv_unsigned.
  rewrite <- (bv_swrap_wrap 32 (bv_wrap 64 _)).
  rewrite (bv_wrap_bv_wrap 32 64) by (compute; discriminate || lia).
  rewrite bv_swrap_wrap. apply bv_swrap_small. apply bv_swrap_in_range. discriminate.
Qed.

(* [comment removed for export] *)
Lemma w2b4_low32 : forall x y : word,
  (bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32)%Z -> word_to_le_bytes 4 x = word_to_le_bytes 4 y.
Proof.
  intros x y H. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned x)) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned y)) by (cbn; lia).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite H. reflexivity.
Qed.

Lemma u_v_lw_mod32 : forall v : word, (bv_unsigned (v_lw v) mod 2 ^ 32 = bv_unsigned v mod 2 ^ 32)%Z.
Proof.
  intros v. unfold v_lw. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_swrap 32 (bv_unsigned v)) mod 2 ^ 32)%Z with (bv_wrap 32 (bv_wrap 64 (bv_swrap 32 (bv_unsigned v)))).
  rewrite (bv_wrap_bv_wrap 32 64) by (compute; discriminate || lia).
  unfold bv_swrap. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned v + bv_half_modulus 32 - bv_half_modulus 32)%Z with (bv_unsigned v) by lia.
  reflexivity.
Qed.

Lemma lor_mod32 : forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.lor a b mod 2 ^ 32 = Z.lor (a mod 2 ^ 32) (b mod 2 ^ 32) mod 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.lor_spec. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma land_mod32 : forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.land a b mod 2 ^ 32 = Z.land (a mod 2 ^ 32) (b mod 2 ^ 32) mod 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.land_spec. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_lt32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (0 <= Z.lor a b < 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec. rewrite (Z_testbit_high 32 a k) by lia. rewrite (Z_testbit_high 32 b k) by lia. reflexivity.
Qed.

Lemma land_lt32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b)%Z -> (0 <= Z.land a b < 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec. rewrite (Z_testbit_high 32 a k) by lia. reflexivity.
Qed.

Lemma u_v_or : forall x y : word, bv_unsigned (v_or x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. pose proof (Z_lor_range _ _ (u64_range x) (u64_range y)). unfold v_or. apply u_Z2bv; lia.
Qed.

Lemma u_v_and : forall x y : word, bv_unsigned (v_and x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. pose proof (u64_range y). pose proof (Z_land_range _ (bv_unsigned y) (u64_range x) ltac:(lia)). unfold v_and. apply u_Z2bv; lia.
Qed.

Lemma w2b4_or_sext : forall (v bits : word),
  word_to_le_bytes 4 (v_or (v_lw v) bits) = word_to_le_bytes 4 (v_or v bits).
Proof.
  intros v bits. apply w2b4_low32. rewrite !u_v_or.
  pose proof (u64_range (v_lw v)). pose proof (u64_range v). pose proof (u64_range bits).
  rewrite (lor_mod32 (bv_unsigned (v_lw v))) by lia. rewrite (lor_mod32 (bv_unsigned v)) by lia.
  rewrite u_v_lw_mod32. reflexivity.
Qed.

Lemma w2b4_and_sext : forall (v mask : word),
  word_to_le_bytes 4 (v_and (v_lw v) mask) = word_to_le_bytes 4 (v_and v mask).
Proof.
  intros v mask. apply w2b4_low32. rewrite !u_v_and.
  pose proof (u64_range (v_lw v)). pose proof (u64_range v). pose proof (u64_range mask).
  rewrite (land_mod32 (bv_unsigned (v_lw v))) by lia. rewrite (land_mod32 (bv_unsigned v)) by lia.
  rewrite u_v_lw_mod32. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell32_or : forall old (bits : word), (0 <= old < 2 ^ 32)%Z ->
  word_to_le_bytes 4 (v_or (Z_to_bv 64 old) bits)
  = word_to_le_bytes 4 (Z_to_bv 64 (Z.lor old (bv_unsigned bits mod 2 ^ 32))).
Proof.
  intros old bits Hold. pose proof (u64_range bits).
  pose proof (Z.mod_pos_bound (bv_unsigned bits) (2 ^ 32) ltac:(lia)).
  pose proof (lor_lt32 old (bv_unsigned bits mod 2 ^ 32) Hold ltac:(lia)) as R.
  apply w2b4_low32. rewrite u_v_or. rewrite !u_Z2bv by lia.
  rewrite (lor_mod32 old) by lia. rewrite (Z.mod_small old) by lia.
  rewrite (Z.mod_small (Z.lor old _)) by lia. reflexivity.
Qed.

Lemma cell32_and : forall old (mask : word), (0 <= old < 2 ^ 32)%Z ->
  word_to_le_bytes 4 (v_and (Z_to_bv 64 old) mask)
  = word_to_le_bytes 4 (Z_to_bv 64 (Z.land old (bv_unsigned mask))).
Proof.
  intros old mask Hold. pose proof (u64_range mask).
  pose proof (land_lt32 old (bv_unsigned mask) Hold ltac:(lia)) as R.
  apply w2b4_low32. rewrite u_v_and. rewrite !u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cas_or_17b50 : forall regs mem rom (a bits : word) (old : Z),
  getr regs 14 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 11 = bits ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x17f00 : word) mem rom)
                 (mkst regs' (0x17f20 : word) (wbytes mem a (word_to_le_bytes 4 (v_or (Z_to_bv 64 old) bits))) rom)
    /\ getr regs' 10 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 12 = v_or (v_lw (Z_to_bv 64 old)) bits
    /\ getr regs' 13 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 13 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom a bits old Ha Hal Hrd Hold Hbits Hok.
  eexists. split.
  - (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_17f00 | reflexivity | exact D_17f00
        | gres; imm_norm; rewrite v_addi_0, Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepn F_17f04 D_17f04. rewrite Hbits.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_17f08 | reflexivity | exact D_17f08
        | gres; rewrite Ha; exact Hal
        | gres; rewrite Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17f0c | reflexivity | exact D_17f0c | gres; apply c_eq_refl ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17f10 | reflexivity | exact D_17f10
        | gres; rewrite Ha; exact Hal | gres; rewrite Ha; reflexivity | gres; rewrite Ha; exact Hok ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_17f14 D_17f14 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepiwv F_17f18 D_17f18 (v_lw (Z_to_bv 64 old)) ltac:(gres; imm_norm; apply sextw_lw).
    (* [comment removed for export] *)
    stepb_ft F_17f1c D_17f1c ltac:(apply c_eq_refl).
    rewrite Ha, w2b4_or_sext.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
    intros r H10 H12 H13 H15. rewrite !getr_other by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cas_and_18330 : forall regs mem rom (a mask : word) (old : Z),
  getr regs 12 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 13 = mask ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x186e0 : word) mem rom)
                 (mkst regs' (0x18700 : word) (wbytes mem a (word_to_le_bytes 4 (v_and (Z_to_bv 64 old) mask))) rom)
    /\ getr regs' 14 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = v_and (v_lw (Z_to_bv 64 old)) mask
    /\ getr regs' 16 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom a mask old Ha Hal Hrd Hold Hmask Hok.
  eexists. split.
  - (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_186e0 | reflexivity | exact D_186e0
        | gres; imm_norm; rewrite v_addi_0, Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepn F_186e4 D_186e4. rewrite Hmask.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_186e8 | reflexivity | exact D_186e8
        | gres; rewrite Ha; exact Hal
        | gres; rewrite Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_186ec | reflexivity | exact D_186ec | gres; apply c_eq_refl ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_186f0 | reflexivity | exact D_186f0
        | gres; rewrite Ha; exact Hal | gres; rewrite Ha; reflexivity | gres; rewrite Ha; exact Hok ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_186f4 D_186f4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepiwv F_186f8 D_186f8 (v_lw (Z_to_bv 64 old)) ltac:(gres; imm_norm; apply sextw_lw).
    (* [comment removed for export] *)
    stepb_ft F_186fc D_186fc ltac:(apply c_eq_refl).
    rewrite Ha, w2b4_and_sext.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
    intros r H14 H15 H16 H17. rewrite !getr_other by assumption. reflexivity.
Qed.
End WithFP1.

End UbLibCas.

Module UbLibCas2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic UbLibCas OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Theorem cas_lock_17308 : forall regs mem rom (a newv : word) (old : Z),
  getr regs 13 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 11 = v_lw (Z_to_bv 64 old) ->
  getr regs 12 = newv ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1757c : word) mem rom)
                 (mkst regs' (0x1758c : word) (wbytes mem a (word_to_le_bytes 4 newv)) rom)
    /\ getr regs' 14 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom a newv old Ha Hal Hrd Hold Ha1 Ha2 Hok.
  eexists. split.
  - (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_1757c | reflexivity | exact D_1757c
        | gres; rewrite Ha; exact Hal
        | gres; rewrite Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17580 | reflexivity | exact D_17580
        | gres; rewrite Ha1; apply c_eq_refl ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17584 | reflexivity | exact D_17584
        | gres; rewrite Ha; exact Hal | gres; rewrite Ha; reflexivity | gres; rewrite Ha; exact Hok ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_17588 D_17588 ltac:(cond_compute).
    rewrite Ha, Ha2.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
    intros r H14 H15. rewrite !getr_other by assumption. reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbLibCas2.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Hoare Frame RefMemcpyLib UbMemcpyBase UbMemcpy MallocDefs UbEnframeBase RefEnframeArith UbEnframe UbGetMeta UbFreePro UbStdioDefs.

Module UbSymPlanSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase UbLibCas UbLibCas2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbFreePro OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPS.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Export SPSA.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section NX0.
Variable nx0 : nat.
(* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound RSEGS IT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

Lemma kentry_keep_sem : forall E M M' K lo n,
  kentry_ok RSEGS E M K -> kfoot_apart E K lo n ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  kentry_ok RSEGS E M' K.
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn RSEGS M' a k = rdn RSEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2]; cbn [kentry_ok] in *;
    try exact HK.
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (A & B & C). split; [exact A|]. split; [exact B|]. intros i Hi.
    rewrite Hout; [apply C; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview RSEGS M x).
    eapply (store_ok_all RSEGS M (S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Lemma kentry_apart_b_sem : forall E M allkn K ub uk un,
  know_ok RSEGS E M allkn -> kentry_apart_b allkn ub uk un K = true ->
  kfoot_apart E K (estart E (SA ub uk)) (elenZ E un).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound RSEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

Lemma kentry_apart_keep : forall E M M' allkn K (ub : expr) uk un,
  know_ok RSEGS E M allkn -> kentry_ok RSEGS E M K ->
  kentry_apart_b allkn ub uk un K = true ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  kentry_ok RSEGS E M' K.
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

Lemma know_ok_filter_apart : forall E M M' k (f : kentry -> bool) (ub : expr) uk un,
  know_ok RSEGS E M k ->
  (forall K, In K k -> f K = true -> kentry_apart_b k ub uk un K = true \/ kentry_ok RSEGS E M' K) ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  know_ok RSEGS E M' (List.filter f k).
Proof.
  intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin Hfk].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
  eapply kentry_apart_keep; eassumption.
Qed.

(* [comment removed for export] *)
Lemma kentry_apart_bp_eq : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_unfill : forall E M k ub un,
  know_ok RSEGS E M k -> flat E (SA ub 0) (elenZ E un) ->
  know_ok RSEGS E (unfill (edenot E ub) (edenot E un) M) (kn_unfill k ub 0 un).
Proof.
  intros E M k ub un HK Hfl. rewrite kn_unfill_eq. (* [comment removed for export] *) unfold kn_unfill_ref.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  cbv zeta. eapply know_ok_filter_apart; [exact HK | |].
  - intros K Hin Hf. cbv beta in Hf. rewrite kentry_apart_bp_eq in Hf.   (* [comment removed for export] *)
    apply orb_prop in Hf as [Himg|Ha]; [|left; exact Ha].
    right. destruct K; try discriminate. cbn [kentry_ok].
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as (A & B & C). split; [exact A|]. split; [exact B|].
    intros i Hi. unfold unfill. rewrite (C i Hi). destruct (_ && _)%bool; reflexivity.
  - intros x Hx. apply unfill_out. fold (elenZ E un).
    unfold estart in Hx. cbn [a_base a_off] in Hx. unfold estart in Hu. cbn [a_base a_off] in Hu.
    unfold adenot, v_addi in Hu. cbn [a_base a_off] in Hu. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hu. lia.
Qed.

(* [comment removed for export] *)

Lemma seps_In2 : forall l p q, seps l -> In p l -> In q l -> p = q \/ iv_disjoint p q.
Proof.
  intros l p q Hs. induction Hs as [|r l Hf Hs IH]; intros Hp Hq; [destruct Hp|].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - left; reflexivity.
  - right. exact (proj1 (Forall_forall _ _) Hf q Hq).
  - right. pose proof (proj1 (Forall_forall _ _) Hf p Hp) as H. unfold iv_disjoint in *. lia.
  - exact (IH Hp Hq).
Qed.

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l Hs. induction Hs as [|p l Hf Hs IH]; cbn [List.filter]; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma Forall_filter : forall {A} (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma map_remove_filter : forall l (a : word), map_remove l a = List.filter (fun p => negb (bv_eqb (fst p) a)) l.
Proof. reflexivity. Qed.

Lemma In_map_remove : forall l (a b n : word), In (b, n) l -> b <> a -> In (b, n) (map_remove l a).
Proof.
  intros l a b n Hin Hne. rewrite map_remove_filter. apply filter_In. split; [exact Hin|].
  cbn [fst]. unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned b) (bv_unsigned a)) as [Heq|Hneq]; [|reflexivity].
  exfalso. apply Hne. apply bv_eq. exact Heq.
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof.
  intros l a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
  cbn [fst snd]. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma munmap_len_sound : forall E cs R M model n nhi,
  cs_ok E cs R M model -> munmap_len cs = Some (n, nhi) ->
  exists len, getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ (0 < len)%Z
              /\ page_round_up_Z len = elenZ E n /\ (elenZ E n <= nhi)%Z.
Proof.
  intros E cs R M model n nhi HC H. unfold munmap_len in H.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit cs 11) as [len|] eqn:H11.
  - destruct (Z.ltb 0 len && Z.leb (page_up len) (2 ^ 40))%bool eqn:Hl; [|discriminate].
    apply andb_prop in Hl as [Hl Hpb]. apply Z.ltb_lt in Hl. apply Z.leb_le in Hpb. injection H as <- <-.
    destruct (reg_lit_sound E cs R M model 11 len HC ltac:(lia) H11) as [R11 Hlenr].
    exists len. split; [exact R11|]. split; [exact Hl|].
    assert (Hpu : page_round_up_Z len = page_up len) by (symmetry; apply page_up_eq).
    assert (Hb : (0 <= page_up len < 2 ^ 64)%Z).
    { split; [|lia]. unfold page_up. assert (0 <= (len + 4095) / 4096)%Z by (apply Z.div_pos; lia). lia. }
    rewrite elenZ_lit by exact Hb. split; [exact Hpu | lia].
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    destruct (Z.ltb 0 lo && Z.leb 12 (ealign (kn cs) (reg cs 11)))%bool eqn:Hc; [|discriminate].
    injection H as <- <-. apply andb_prop in Hc as [Hlo Hal]. apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal.
    pose proof (xlo_sound RSEGS E M (kn cs) _ lo HKN Hxl) as A.
    pose proof (xhi_sound RSEGS E M (kn cs) _ hi HKN Hxh) as B.
    exists (bv_unsigned (edenot E (reg cs 11))).
    split; [rewrite Z_to_bv_bv_unsigned; apply (reg_sound E cs R M model 11 HC ltac:(lia))|].
    split; [lia|]. unfold elenZ. split; [|lia].
    destruct (ealign_sound RSEGS E M (kn cs) (reg cs 11) HKN) as [Hea [q Hq]].
    assert (Hd : (2 ^ 12 | 2 ^ ealign (kn cs) (reg cs 11))%Z) by (apply pow2_divide_le; lia).
    destruct Hd as [r Hr]. rewrite Hr in Hq.
    unfold page_round_up_Z, page_size. rewrite Hq.
    replace (q * (r * 2 ^ 12) + 4096 - 1)%Z with (q * r * 4096 + 4095)%Z by (change (2^12)%Z with 4096%Z; ring).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Z.div_add_l by lia. change (4095 / 4096)%Z with 0%Z. change (2 ^ 12)%Z with 4096%Z. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma len_eqb_sound : forall E M k n m,
  know_ok RSEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros E M k n m HK H. rewrite len_eqb_eq in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound RSEGS E M k _ _ HK H1) as A. pose proof (lin_ge0_sound RSEGS E M k _ _ HK H2) as B.
    cbn [xt_den] in A, B. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma below_band_x_sound : forall E M k b o n shi nhi,
  know_ok RSEGS E M k ->
  (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)))%Z ->
  (0 < elenZ E n <= nhi)%Z ->
  (bv_unsigned (edenot E b) + o <= shi)%Z ->
  below_band_x k b o n shi nhi = true ->
  (bv_unsigned (edenot E b) + o + elenZ E n <= bv_unsigned (edenot E (EVar 0)) - 8388608)%Z.
Proof.
  intros E M k b o n shi nhi HK Hsp Hn Hhi H. unfold below_band_x in H.
  apply andb_prop in H as [Hkd Hfar]. apply Z.leb_le in Hfar.
  pose proof (kdisj_apart_x_sound RSEGS E M k k _ _ _ _ _ _ HK HK Hkd) as Hd.
  unfold estart in Hd; cbn [a_base a_off] in Hd.
  rewrite (elenZ_lit E 0x800000000000) in Hd by lia.
  unfold SPBAND_LO in Hfar. lia.
Qed.

Lemma node_munmap_sound {FP : FPState} : forall cs cs' E R M model T,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_munmap cs = Some cs' ->
  (forall R' M' model', cs_ok E cs' R' M' model' -> m_fs model' = m_fs model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model') T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hec Hn HK.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_munmap in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (munmap_len cs) as [[n nhi]|] eqn:HML.
  2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hno : no = 215).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; reflexivity. }
  subst no.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hn with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. subst cs'. clear Hn.
  apply andb_prop in Hcond as [Hcond Hhi]. apply andb_prop in Hcond as [Hcond Hoth].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hn30 Hfind].
  apply Z.leb_le in Hn30. apply Z.leb_le in Hal.
  set (b := reg cs 10) in *.
  destruct (ehi (kn cs) b) as [hi|] eqn:Hehi; [|discriminate].
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit_sound E cs R M model 17 215 HC ltac:(lia) H17) as [R17 _].
  destruct (munmap_len_sound E cs R M model n nhi HC HML) as (len & R11 & Hlen0 & Hpr & HNhi).
  set (N := elenZ E n) in *.
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10. fold b in R10.
  (* [comment removed for export] *)
  assert (Hbhi : (bv_unsigned (edenot E b) <= hi)%Z).
  { unfold ehi in Hehi. destruct b; try (destruct (erange (kn cs) _) as [[lo' hi']|] eqn:Her; [|discriminate];
      injection Hehi as <-; exact (proj2 (erange_sound RSEGS E M (kn cs) _ lo' hi' HKN Her))).
    injection Hehi as <-. cbn [edenot]. rewrite u_lit64. lia. }
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) b HKN) as [Hea [q Hq]].
  assert (Hmod : (bv_unsigned (edenot E b) mod page_size = 0)%Z).
  { unfold page_size. rewrite Hq.
    assert (Hd : (2 ^ 12 | 2 ^ ealign (kn cs) b)%Z) by (apply pow2_divide_le; lia).
    destruct Hd as [r Hr]. rewrite Hr. replace (q * (r * 2 ^ 12))%Z with ((q * r) * 4096)%Z by (change (2^12)%Z with 4096%Z; ring).
    apply Z.mod_mul. lia. }
  pose proof (u64_range (edenot E b)) as Hbr.
  assert (Hnpos : (0 < N)%Z).
  { rewrite <- Hpr. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  assert (HNw : Z_to_bv 64 N = edenot E n) by (subst N; unfold elenZ; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (Hhi47 : (bv_unsigned (edenot E b) + N <= 0x800000000000)%Z).
  { apply orb_prop in Hhi as [Hhi|Hhi].
    - apply Z.leb_le in Hhi. lia.
    - assert (Hsp0 : (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)) <= 0x800000000000)%Z).
      { pose proof (co_vm _ _ _ _ _ HC) as HV. rewrite <- (vo_sp _ _ _ _ _ HV). exact (vo_sprange _ _ _ _ _ HV). }
      pose proof (below_band_x_sound E M (kn cs) b 0 n hi nhi HKN ltac:(lia) ltac:(fold N; lia) ltac:(lia) Hhi) as D.
      fold N in D. lia. }
  clear Hhi.
  (* [comment removed for export] *)
  pose proof (co_vm _ _ _ _ _ HC) as HV.
  assert (MATCH : forall m, smap_match (kn cs) b n m = true ->
                    sm_exact m = true /\ sm_base m = b /\ edenot E (sm_len m) = Z_to_bv 64 N).
  { intros [mb ml mx] Hm. unfold smap_match in Hm. cbn [sm_exact sm_base sm_len] in *.
    apply andb_prop in Hm as [Hm Hl]. apply andb_prop in Hm as [Hx Hb].
    apply expr_eqb_eq in Hb. subst. rewrite HNw. split; [reflexivity|]. split; [reflexivity|].
    symmetry. eapply len_eqb_sound; [exact HKN | exact Hl]. }
  assert (Hin : In (edenot E b, Z_to_bv 64 N) (vm_maps (m_vmmaps model))).
  { apply existsb_exists in Hfind as (m & Hm_in & Hm).
    destruct (MATCH m Hm) as (Hx & Hb & Hl).
    pose proof (proj1 (Forall_forall _ _) (vo_maps _ _ _ _ _ HV) m Hm_in) as Hok.
    unfold smap_ok in Hok. rewrite Hx, Hb, Hl in Hok. destruct Hok as (_ & _ & Hok). exact Hok. }
  unfold cfg_of.
  eapply (rz_munmap RSEGS R (Z_to_bv 64 (pc cs)) M model w (edenot E b) len T Hf He
            (co_halt _ _ _ _ _ HC) (co_lazy _ _ _ _ _ HC) R17 R10 Hmod R11 Hlen0).
  { rewrite Hpr. unfold TASK_SIZE. lia. }
  { rewrite Hpr. apply map_has_In. exact Hin. }
  rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite Hpr.
  rewrite (munmap_model_simple _ _ model (co_lazy _ _ _ _ _ HC) (co_mat _ _ _ _ _ HC)).
  apply HK; [|reflexivity].
  (* [comment removed for export] *)
  destruct HC as [HR HK0 HL Hh Hlz Hmt Hfd HV0 HS0].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - replace (sr_upd (s_regs (c_ss cs)) 10 (ELit 0)) with (sr_upd (s_regs (c_ss cs)) (ridx (10%bv : bv 5)) (ELit 0)) by reflexivity.
    apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate | reflexivity].
  - rewrite HNw. apply know_ok_unfill; [exact HK0|]. fold N. unfold flat, estart. cbn [a_base a_off]. lia.
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    destruct HV0 as [Vres Vmaps Vlen Vlive Vsmall Vnw Vseps Vlim Vsp Vspr].
    rewrite m_vmmaps_with_vmmaps. constructor; cbn [vm_reserved vm_maps vm_limit vm_live_bytes].
    + exact Vres.
    + (* [comment removed for export] *)
      apply Forall_forall. intros m Hm. unfold remove_exact in Hm. apply filter_In in Hm as [Hm_in Hnm].
      pose proof (proj1 (Forall_forall _ _) Vmaps m Hm_in) as Hok.
      rewrite others_apart_eq in Hoth. pose proof (proj1 (forallb_forall _ _) Hoth m Hm_in) as Hap.
      cbv beta in Hap. apply negb_true_iff in Hnm.
      apply orb_prop in Hap as [Hap|Hap]; [rewrite Hap in Hnm; discriminate|].
      pose proof (ranges_apart_x_sound RSEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as Hd.
      unfold estart in Hd. cbn [a_base a_off] in Hd. rewrite !Z.add_0_r in Hd. fold N in Hd.
      unfold smap_ok in Hok |- *. destruct Hok as (Hl0 & Hnw & Hok). split; [exact Hl0|]. split; [exact Hnw|].
      unfold elenZ in Hd.
      destruct (sm_exact m).
      * apply In_map_remove; [exact Hok|]. intros Heq. apply (f_equal bv_unsigned) in Heq. lia.
      * destruct Hok as (lo & sz & Hinl & Hlo & Hsz). exists lo, sz. split; [|split; [exact Hlo | exact Hsz]].
        apply In_map_remove; [exact Hinl|]. intros Heq.
        destruct (seps_In2 _ _ _ Vseps Hinl Hin) as [Hsame | Hdisj].
        -- injection Hsame as Hlo' Hsz'. rewrite Hsz' in Hsz. rewrite Hlo' in Hlo, Hsz.
           rewrite u64_lit in Hsz by (unfold two64 in *; lia). lia.
        -- unfold iv_disjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite u64_lit in Hdisj by (unfold two64 in *; lia).
           apply (f_equal bv_unsigned) in Heq. pose proof (u64_range sz). lia.
    + pose proof (map_remove_length (vm_maps (m_vmmaps model)) (edenot E b)). lia.
    + unfold vm_live_bytes in Vlive |- *. cbn [vm_maps].
      pose proof (live_bytes_map_remove_le (vm_maps (m_vmmaps model)) (edenot E b)). lia.
    + rewrite map_remove_filter. apply Forall_filter. exact Vsmall.
    + rewrite map_remove_filter. apply Forall_filter. exact Vnw.
    + rewrite map_remove_filter. apply seps_filter. exact Vseps.
    + exact Vlim.
    + exact Vsp.
    + exact Vspr.
  - (* [comment removed for export] *) rewrite HNw. eapply slots_unfill_sound; [exact HK0 | exact HS0 |].
    fold N. unfold flat, estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)

Lemma lin_inside_sound : forall E M kn b1 k1 n1 b2 k2 n2,
  know_ok RSEGS E M kn -> lin_inside kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z /\ (estart E (SA b1 k1) + n1 <= estart E (SA b2 k2) + n2)%Z.
Proof.
  intros E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold lin_inside in H.
  apply andb_prop in H as [H Hm]. apply andb_prop in H as [Hw1 Hw2].
  pose proof (lin_nowrapR_sound RSEGS E M kn b1 Hkn Hw1) as E1.
  pose proof (lin_nowrapR_sound RSEGS E M kn b2 Hkn Hw2) as E2.
  destruct (lin_of b1) as [c1 ts1] eqn:Hl1. destruct (lin_of b2) as [c2 ts2] eqn:Hl2. cbn [fst snd] in *.
  apply (lin_test_sound RSEGS E M kn) in Hm as (lo & hi & Hm & Hb); [|exact Hkn].
  rewrite lsub_e_sound in Hb. unfold estart. cbn [a_base a_off]. rewrite E1, E2.
  apply andb_prop in Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.leb_le in Hm2. lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_val : segments_reserved RSEGS =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x12000, Z_to_bv 64 0x00e000);
   (Z_to_bv 64 0x20000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x21000, Z_to_bv 64 0x31000)].
Proof. vm_compute. reflexivity. Qed.

Lemma region_free_image : forall maps (a : word) (n : Z),
  (0 < n < 2 ^ 64)%Z ->
  region_free (segments_reserved RSEGS ++ maps) a (Z_to_bv 64 n) = true ->
  (bv_unsigned a + n <= 0x10000 \/ 0x52000 <= bv_unsigned a)%Z
  /\ (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z.
Proof.
  intros maps a n Hn H. rewrite region_free_app in H. apply andb_prop in H as [Hr Hm].
  split.
  - rewrite reserved_val in Hr.
    pose proof (fun b s Hin => region_free_In _ a (Z_to_bv 64 n) b s Hr Hin) as X.
    rewrite u64_lit in X by lia.
    pose proof (X _ _ (or_introl eq_refl)) as X1.
    pose proof (X _ _ (or_intror (or_introl eq_refl))) as X2.
    pose proof (X _ _ (or_intror (or_intror (or_introl eq_refl)))) as X3.
    pose proof (X _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as X4.
    rewrite !u64_lit in X1, X2, X3, X4 by lia. lia.
  - intros b s Hin. pose proof (region_free_In _ a (Z_to_bv 64 n) b s Hm Hin) as X. rewrite u64_lit in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma grant_keep_b_sem : forall E M k ms maps K (a : word) n,
  know_ok RSEGS E M k -> Forall (smap_ok E maps) ms ->
  (0x1000 <= bv_unsigned a)%Z -> (bv_unsigned a + n <= bv_unsigned (edenot E (EVar 0)) - 8388608)%Z -> (0 < n)%Z ->
  (bv_unsigned a + n <= 0x10000 \/ 0x52000 <= bv_unsigned a)%Z ->
  (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z ->
  grant_keep_b INFOUB k ms K = true -> kfoot_apart E K (bv_unsigned a) n.
Proof.
  intros E M k ms maps K a n HK Hms Ha Hc Hn Himg Hmaps Hb.
  assert (SR : forall b off len, safe_range INFOUB k ms b off len = true ->
            (estart E (SA b off) + elenZ E len <= bv_unsigned a \/ bv_unsigned a + n <= estart E (SA b off))%Z).
  { clear Hb. intros b off len H. unfold safe_range in H. change (d_img_hi INFOUB) with 0x52000%Z in H.
    pose proof (u64_range (edenot E len)) as Hlr. unfold elenZ.
    apply orb_prop in H as [H|H].
    - destruct (xhi k len) as [lh|] eqn:Hxh; [|discriminate].
      pose proof (xhi_sound RSEGS E M k len lh HK Hxh) as Hlh.
      destruct (erange k b) as [[lo hi]|] eqn:Hr; [|discriminate].
      pose proof (erange_sound RSEGS E M k b lo hi HK Hr) as Hbr. unfold estart. cbn [a_base a_off].
      apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
      + (* [comment removed for export] *)
        apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2. unfold stack_based in H1.
        destruct b as [| [|[|]] | | | | | |]; try discriminate H1.
        apply Z.leb_le in H1. unfold two64 in *. lia.
      + apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; unfold two64 in *; lia.
      + apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; unfold two64 in *; lia.
    - induction ms as [|m rest IH]; [discriminate|]. cbn [inside_maps] in H.
      apply Forall_cons_iff in Hms as [Hm Hrest].
      apply orb_prop in H as [H|H]; [|exact (IH Hrest H)].
      assert (I12 : (estart E (SA (sm_base m) 0) <= estart E (SA b off))%Z
                    /\ (estart E (SA b off) + bv_unsigned (edenot E len) <= estart E (SA (sm_base m) 0) + elenZ E (sm_len m))%Z).
      { assert (XI : xinside k b off len (sm_base m) 0 (sm_len m) = true ->
                     (estart E (SA (sm_base m) 0) <= estart E (SA b off))%Z
                     /\ (estart E (SA b off) + bv_unsigned (edenot E len) <= estart E (SA (sm_base m) 0) + elenZ E (sm_len m))%Z)
          by (intros HX; exact (xinside_sound RSEGS E M k b off len (sm_base m) 0 (sm_len m) HK HX)).
        destruct len as [l| | | | | | |]; try (apply XI; exact H).
        destruct (sm_len m) as [ml| | | | | | |] eqn:Hml; try (apply XI; exact H).
        destruct (lin_inside_sound E M k b off _ (sm_base m) 0 _ HK H) as [I1 I2].
        unfold elenZ. cbn [edenot]. rewrite !u_lit64. split; [exact I1 | exact I2]. }
      destruct I12 as [I1 I2].
      unfold estart in I1, I2 |- *. unfold elenZ in I2. cbn [a_base a_off] in *.
      unfold smap_ok in Hm. destruct Hm as (Hml & Hmnw & Hm).
      destruct (sm_exact m).
      + pose proof (Hmaps _ _ Hm) as D. lia.
      + destruct Hm as (lo & sz & Hin & Hlo & Hsz). pose proof (Hmaps _ _ Hin) as D. lia. }
  unfold kfoot_apart, kfoot.
  destruct K as [[b kk] w v|[b kk] nn|[b kk] nn kb|ilo ihi|e m|e rlo rhi|[b kk] nn|a1 n1 a2 n2]; cbn [grant_keep_b] in Hb;
    change (d_img_hi INFOUB) with 0x52000%Z in Hb;
    try exact I; try discriminate.
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (SR _ _ _ Hb) as X. rewrite elenZ_lit in X by lia. lia.
  - exact (SR _ _ _ Hb).
  - exact (SR _ _ _ Hb).
  - apply orb_prop in Hb as [Hb|Hb]; apply andb_prop in Hb as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
  - exact (SR _ _ _ Hb).
Qed.

(* [comment removed for export] *)
Lemma safe_range_sem : forall E M k ms maps (a : word) n b off len,
  know_ok RSEGS E M k -> Forall (smap_ok E maps) ms ->
  (0x1000 <= bv_unsigned a)%Z -> (bv_unsigned a + n <= bv_unsigned (edenot E (EVar 0)) - 8388608)%Z -> (0 < n)%Z ->
  (bv_unsigned a + n <= 0x10000 \/ 0x52000 <= bv_unsigned a)%Z ->
  (forall b s, In (b, s) maps -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z ->
  safe_range INFOUB k ms b off len = true ->
  (estart E (SA b off) + elenZ E len <= bv_unsigned a \/ bv_unsigned a + n <= estart E (SA b off))%Z.
Proof.
  intros E M k ms maps a n b off len HK Hms Ha Hc Hn Himg Hmaps H.
  pose proof (grant_keep_b_sem E M k ms maps (KZero (SA b off) len) a n HK Hms Ha Hc Hn Himg Hmaps) as G.
  cbn [grant_keep_b] in G. specialize (G H). unfold kfoot_apart, kfoot in G. exact G.
Qed.

Lemma grant_ok_facts : forall hint model (a : word) n,
  vm_reserved (m_vmmaps model) = segments_reserved RSEGS -> (0 < n < 2 ^ 64)%Z ->
  grant_ok hint model a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0x1000 <= bv_unsigned a)%Z /\ (bv_unsigned a + n <= alloc_top (m_vmmaps model))%Z
  /\ (bv_unsigned a + n <= 0x10000 \/ 0x52000 <= bv_unsigned a)%Z
  /\ (forall b s, In (b, s) (vm_maps (m_vmmaps model)) ->
        bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a)%Z
  /\ (vm_backing_used model + n <= vm_limit (m_vmmaps model))%Z.
Proof.
  intros hint model a n Hres Hn Hg. unfold grant_ok in Hg.
  apply andb_prop in Hg as [Hg Hl]. apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Hc].
  apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hc. apply Z.leb_le in Hl.
  rewrite Hres in Hrf. destruct (region_free_image _ a n Hn Hrf) as [Himg Hmaps].
  repeat split; try assumption.
  unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). nia.
Qed.

Lemma regs_ok_ext : forall b E E' sr R, env_agree b E E' -> SP.sr_vars_lt b sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof.
  intros b E E' sr R Hag Hv HR.
  eapply regs_ok_agree; [exact Hag | | exact HR].
  clear -Hv. induction sr as [|e r IH]; cbn [SP.sr_vars_lt SymRun3.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in Hv as [H1 H2]. rewrite <- expr_vars_lt_eq, H1. cbn [andb]. exact (IH H2).
Qed.

Lemma kentry_vars_lt_eq : forall b K, SP.kentry_vars_lt b K = SymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [a w v|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2];
    cbn [SP.kentry_vars_lt SymRun3.kentry_vars_lt]; unfold SP.saddr_vars_lt, SymRun3.saddr_vars_lt;
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.

Lemma kn_vars_lt_eq : forall b kn, SP.kn_vars_lt b kn = SymRun3.kn_vars_lt b kn.
Proof.
  intros b kn. induction kn as [|K r IH]; cbn [SP.kn_vars_lt SymRun3.kn_vars_lt]; [reflexivity|].
  rewrite IH, kentry_vars_lt_eq. reflexivity.
Qed.

Lemma know_ok_ext : forall b E E' M kn, env_agree b E E' -> SP.kn_vars_lt b kn = true -> know_ok RSEGS E M kn -> know_ok RSEGS E' M kn.
Proof.
  intros b E E' M kn Hag Hv HK. eapply know_ok_agree; [exact Hag | rewrite <- kn_vars_lt_eq; exact Hv | exact HK].
Qed.

Lemma kn_vars_lt_filter : forall b f kn, SP.kn_vars_lt b kn = true -> SP.kn_vars_lt b (List.filter f kn) = true.
Proof.
  intros b f kn. induction kn as [|K r IH]; cbn [SP.kn_vars_lt List.filter]; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (f K); cbn [SP.kn_vars_lt]; [rewrite H1, (IH H2); reflexivity | exact (IH H2)].
Qed.

Lemma smaps_ok_ext : forall b E E' maps ms,
  env_agree b E E' -> maps_vars_lt b ms = true -> Forall (smap_ok E maps) ms -> Forall (smap_ok E' maps) ms.
Proof.
  intros b E E' maps ms Hag Hv H. apply Forall_forall. intros m Hm.
  pose proof (proj1 (Forall_forall _ _) H m Hm) as Hok.
  unfold maps_vars_lt in Hv. pose proof (proj1 (forallb_forall _ _) Hv m Hm) as Hvm.
  apply andb_prop in Hvm as [Hvb Hvl].
  unfold smap_ok in *. rewrite <- (edenot_agree b E E' (sm_base m) Hag) by (rewrite <- expr_vars_lt_eq; exact Hvb).
  rewrite <- (edenot_agree b E E' (sm_len m) Hag) by (rewrite <- expr_vars_lt_eq; exact Hvl). exact Hok.
Qed.

Lemma page_round_up_Z_mono : forall a b, (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

Lemma page_up_e_denot : forall E e,
  (bv_unsigned (edenot E e) + 4095 < 2 ^ 64)%Z ->
  edenot E (page_up_e e) = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E e))).
Proof.
  intros E e Hb. unfold page_up_e. rewrite !mkAlu_denot. cbn [edenot].
  pose proof (u64_range (edenot E e)) as Hr.
  rewrite alu_add.
  rewrite alu_srl, (alu_sll_amt _ (Z_to_bv 64 12) 12) by (rewrite u64_lit by lia; reflexivity).
  unfold v_srl, v_add. rewrite (u64_lit 12) by lia. change (12 mod 64)%Z with 12%Z.
  rewrite (u64_lit 4095) by lia. rewrite (u64_lit (bv_unsigned (edenot E e) + 4095)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : (0 <= (bv_unsigned (edenot E e) + 4095) / 2 ^ 12 < 2 ^ 64)%Z).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite u64_lit by lia. unfold page_round_up_Z, page_size. f_equal. change (2 ^ 12)%Z with 4096%Z. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_len_sound : forall E cs R M model ne lo nhi,
  cs_ok E cs R M model -> mmap_len cs = Some (ne, lo, nhi) ->
  exists len, getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len
    /\ (lo <= len)%Z /\ (0 <= len < 2 ^ 64)%Z /\ (page_round_up_Z len <= nhi)%Z
    /\ SP.expr_vars_lt (s_next (c_ss cs)) ne = true
    /\ forall E', env_agree (s_next (c_ss cs)) E E' -> edenot E' ne = Z_to_bv 64 (page_round_up_Z len).
Proof.
  intros E cs R M model ne lo nhi HC H. unfold mmap_len in H.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct (reg_lit cs 11) as [len|] eqn:H11.
  - injection H as <- <- <-.
    destruct (reg_lit_sound E cs R M model 11 len HC ltac:(lia) H11) as [R11 Hlenr]. unfold two64 in Hlenr.
    exists len. split; [exact R11|]. split; [lia|]. split; [lia|].
    rewrite page_up_eq. split; [lia|]. split; [reflexivity|].
    intros E' _. cbn [edenot]. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo'|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [lhi|] eqn:Hxh; [|discriminate].
    set (ne1 := match foldK (kn cs) (page_up_e (reg cs 11)) with ELit z => ELit z | _ => page_up_e (reg cs 11) end) in H.
    assert (FK1 : edenot E ne1 = edenot E (page_up_e (reg cs 11))).
    { subst ne1. pose proof (foldK_denot RSEGS E M (kn cs) (page_up_e (reg cs 11)) HKN) as FK.
      destruct (foldK (kn cs) (page_up_e (reg cs 11))); first [exact FK | reflexivity]. }
    clearbody ne1.
    destruct (xhi (kn cs) ne1) as [nhi'|] eqn:Hxn; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hb Hv]. apply Z.leb_le in Hb.
    assert (ne = ne1 /\ lo' = lo /\ nhi' = nhi) as (-> & <- & <-) by (injection H; auto). clear H.
    pose proof (xlo_sound RSEGS E M (kn cs) _ lo' HKN Hxl) as A.
    pose proof (xhi_sound RSEGS E M (kn cs) _ lhi HKN Hxh) as B.
    pose proof (xhi_sound RSEGS E M (kn cs) _ nhi' HKN Hxn) as C.
    pose proof (u64_range (edenot E (reg cs 11))) as Hr.
    assert (PD : edenot E (page_up_e (reg cs 11)) = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
      by (apply page_up_e_denot; lia).
    assert (PD1 : edenot E ne1 = Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) by (rewrite FK1; exact PD).
    exists (bv_unsigned (edenot E (reg cs 11))).
    split; [rewrite Z_to_bv_bv_unsigned; apply (reg_sound E cs R M model 11 HC ltac:(lia))|].
    split; [lia|]. split; [lia|].
    split.
    { rewrite PD1 in C. rewrite u64_lit in C; [exact C|].
      pose proof (page_round_up_Z_bounds (bv_unsigned (edenot E (reg cs 11))) ltac:(lia)) as PB. unfold page_size in PB. lia. }
    split; [exact Hv|].
    intros E' Hag. rewrite <- (edenot_agree _ E E' _ Hag) by (rewrite <- expr_vars_lt_eq; exact Hv). exact PD1.
Qed.

Lemma node_mmap_sound {FP : FPState} : forall cs csf css E R M model TB,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_mmap INFOUB nx0 cs = Some (csf, css) ->
  (forall a R' M' model', cs_ok (ext1 E (s_next (c_ss cs)) a) css R' M' model' -> m_fs model' = m_fs model ->
      realizes RSEGS (cfg_of R' (pc css) M' model') TB) ->
  realizes RSEGS (cfg_of R (pc cs) M model) TB.
Proof.
  (* [comment removed for export] *)
  intros cs csf css E R M model TB HC Hec Hn HKB.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_mmap in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [z10|] eqn:H10. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (mmap_len cs) as [[[ne lo] nhi]|] eqn:HML. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 12) as [z12|] eqn:H12. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 13) as [z13|] eqn:H13. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 14) as [m1|] eqn:H14. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 15) as [z15|] eqn:H15. 2:{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hlits : no = 222 /\ z10 = 0 /\ z12 = 3 /\ z13 = 34 /\ z15 = 0).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. repeat split; reflexivity. }
  destruct Hlits as (-> & -> & -> & -> & ->).
  match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hn with Some (?x, ?y) = Some (?x', ?y') =>
    assert (Ef : x' = x) by congruence; assert (Es : y' = y) by congruence end.
  subst csf css. clear Hn.
  apply andb_prop in Hcond as [Hcond Hv0]. apply Nat.ltb_lt in Hv0.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hlive].
  apply andb_prop in Hcond as [Hcond Hcnt]. apply andb_prop in Hcond as [Hcond Hm1].
  apply andb_prop in Hcond as [Hlo0 Hn30].
  apply Z.ltb_lt in Hlo0. apply Z.leb_le in Hn30. apply Z.eqb_eq in Hm1. apply Z.leb_le in Hcnt. apply Z.leb_le in Hlive.
  set (v := s_next (c_ss cs)) in *.
  destruct (mmap_len_sound E cs R M model ne lo nhi HC HML) as (len & R11 & Hlolen & Hlenr & Hnhi & Hnev & Hne).
  fold v in Hnev, Hne.
  set (n := page_round_up_Z len) in *.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hnb. fold n in Hnb. unfold page_size in Hnb.
  assert (Hnpos : (0 < n)%Z) by lia.
  assert (Hnlo : (page_up lo <= n)%Z).
  { rewrite page_up_eq. subst n. apply page_round_up_Z_mono. lia. }
  assert (Hplo : (0 < page_up lo)%Z).
  { unfold page_up. assert (1 <= (lo + 4095) / 4096)%Z by (apply Z.div_le_lower_bound; lia). lia. }
  destruct (reg_lit_sound E cs R M model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 12 3 HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound E cs R M model 13 34 HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound E cs R M model 14 m1 HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound E cs R M model 15 0 HC ltac:(lia) H15) as [R15 _].
  pose proof (co_vm _ _ _ _ _ HC) as HV. destruct HV as [Vres Vmaps Vlen Vlive Vsmall Vnw Vseps Vlim Vsp Vspr].
  unfold cfg_of.
  eapply (rz_mmap_anon RSEGS R (Z_to_bv 64 (pc cs)) M model w len TB Hf He (co_halt _ _ _ _ _ HC) (co_lazy _ _ _ _ _ HC) R17 R11);
    [lia | exact R12 | exact R13 | | exact R15 | |].
  { etransitivity; [exact R14|]. rewrite Hm1. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity. }
  { (* [comment removed for export] *)
    fold n. apply (grant_exists_gen _ model (2 ^ 30) n 1004); try lia.
    - reflexivity.
    - rewrite Vres, reserved_val. repeat apply Forall_cons; try (cbn [snd]; rewrite u64_lit by lia; lia).
      apply Forall_forall. intros [b sz] Hin. cbn [snd]. exact (proj2 (proj1 (Forall_forall _ _) Vsmall _ Hin)).
    - rewrite length_app, Vres, reserved_val. cbn [length]. lia.
    - rewrite cand_base_val. rewrite alloc_top_val. lia.
    - apply grant_budget_intro; [exact (co_lazy _ _ _ _ _ HC) | exact (co_mat _ _ _ _ _ HC) | lia]. }
  (* [comment removed for export] *)
  fold n. intros a Hg.
  destruct (grant_ok_facts _ model a n Vres ltac:(lia) Hg) as (Gal & Glo & Gceil & Gimg & Gmaps & Glive).
  rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  apply (HKB a); [|reflexivity].
  (* [comment removed for export] *)
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv].
  apply andb_prop in Hfresh as [Hsv Hkv]. fold v in Hsv, Hkv, Hmv, Hslv, Hnx0.
  set (E' := ext1 E v a).
  pose proof (ext1_agree E v a) as Hag. fold E' in Hag.
  assert (HneE' : edenot E' ne = Z_to_bv 64 n) by (apply Hne; exact Hag).
  assert (HelE' : elenZ E' ne = n) by (unfold elenZ; rewrite HneE'; apply u64_lit; lia).
  rewrite alloc_top_val, Vsp in Gceil.
  assert (Hsp0 : edenot E' (EVar 0) = edenot E (EVar 0)).
  { cbn [edenot]. symmetry. apply Hag. lia. }
  assert (Gsp : (bv_unsigned a + n <= bv_unsigned (edenot E' (EVar 0)) - 8388608)%Z) by (rewrite Hsp0; exact Gceil).
  rewrite Vsp in Vspr.
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd _ HSL].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots pc s_pc].
  - (* [comment removed for export] *)
    replace (sr_upd (s_regs (c_ss cs)) 10 (EVar v)) with (sr_upd (s_regs (c_ss cs)) (ridx (10%bv : bv 5)) (EVar v)) by reflexivity.
    apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate | apply ext1_at].
    eapply regs_ok_ext; [exact Hag | exact Hsv | exact HR].
  - (* [comment removed for export] *)
    apply Forall_app. split.
    + (* [comment removed for export] *)
      rewrite kn_grant_filter_eq. (* [comment removed for export] *) apply Forall_forall. intros K Hin. apply filter_In in Hin as [Hin Hkeep].
      assert (HK' : know_ok RSEGS E' M (s_know (c_ss cs))) by (eapply know_ok_ext; [exact Hag | exact Hkv | exact HK]).
      pose proof (proj1 (Forall_forall _ _) HK' K Hin) as HKK.
      eapply kentry_keep_sem; [exact HKK | |].
      * eapply (grant_keep_b_sem E' M (s_know (c_ss cs)) (c_maps cs) (vm_maps (m_vmmaps model)) K a n HK');
          [eapply smaps_ok_ext; [exact Hag | exact Hmv | exact Vmaps] | exact Glo | exact Gsp | exact Hnpos | exact Gimg | exact Gmaps | exact Hkeep].
      * intros x Hx. apply zfill_out. rewrite u64_lit by lia. lia.
    + (* [comment removed for export] *)
      assert (Hv : edenot E' (EVar v) = a) by apply ext1_at.
      assert (Hv' : ev E' v = a) by apply ext1_at.
      unfold kn_mmap. change (IMG_SZ INFOUB) with 0x042000%Z. apply Forall_app. split.
      * repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; rewrite ?Hv, ?Hv', ?HelE'.
        -- unfold CEIL in *. lia.
        -- split; [lia|]. unfold page_size in Gal. exact Gal.
        -- split; [unfold flat, estart; cbn [a_base a_off]; rewrite ?Hv, ?Hv'; lia|].
           intros d m Hd Hdm. unfold estart. cbn [a_base a_off]. rewrite ?Hv, ?Hv'.
           unfold zfill. apply store_ok_zmem; rewrite ?u64_lit; try lia.
        -- unfold flat, estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv'.
           split; [lia|].
           intros i Hi. unfold zfill, zmem. rewrite Z.add_0_r.
           rewrite u64_lit by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite u64_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
        -- unfold estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv'. rewrite elenZ_lit by lia. rewrite u64_lit by lia. lia.
        -- unfold estart. cbn [a_base a_off]. rewrite ?Hv, ?Hv'. rewrite elenZ_lit by lia.
           right. lia.
      * apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (m & <- & Hm).
        cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite ?Hv, ?Hv', ?HelE'.
        pose proof (proj1 (Forall_forall _ _) (smaps_ok_ext v E E' _ _ Hag Hmv Vmaps) m Hm) as Hok.
        unfold smap_ok in Hok. destruct Hok as (Hl0 & Hnw & Hok). unfold elenZ.
        destruct (sm_exact m).
        -- pose proof (Gmaps _ _ Hok) as D. lia.
        -- destruct Hok as (lo1 & sz & Hin & Hlo & Hsz). pose proof (Gmaps _ _ Hin) as D. lia.
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    unfold mmap_model. rewrite m_vmmaps_with_vmmaps. constructor; cbn [vm_reserved vm_maps vm_limit vm_live_bytes].
    + exact Vres.
    + apply Forall_cons.
      * unfold smap_ok. cbn [sm_base sm_len sm_exact]. assert (Hv : edenot E' (EVar v) = a) by apply ext1_at.
        rewrite Hv, HneE'. rewrite u64_lit by lia. split; [lia|]. split; [lia|]. left. reflexivity.
      * apply Forall_forall. intros m Hm.
        pose proof (proj1 (Forall_forall _ _) (smaps_ok_ext v E E' _ _ Hag Hmv Vmaps) m Hm) as Hok.
        unfold smap_ok in *. destruct Hok as (Hl0 & Hnw & Hok). split; [exact Hl0|]. split; [exact Hnw|].
        destruct (sm_exact m); [right; exact Hok|].
        destruct Hok as (lo1 & sz & Hin & Hlo & Hsz). exists lo1, sz. split; [right; exact Hin|]. auto.
    + cbn [length]. lia.
    + unfold vm_live_bytes in *. cbn [vm_maps]. rewrite live_bytes_cons, u64_lit by lia. lia.
    + apply Forall_cons; [|exact Vsmall]. cbn [snd]. rewrite u64_lit by lia. lia.
    + apply Forall_cons; [|exact Vnw]. cbn [fst snd]. rewrite u64_lit by lia. lia.
    + constructor; [|exact Vseps]. apply Forall_forall. intros [b sz] Hin. unfold iv_disjoint. cbn [fst snd].
      rewrite u64_lit by lia. pose proof (Gmaps _ _ Hin). lia.
    + exact Vlim.
    + cbn [vm_init_sp]. rewrite Hsp0. exact Vsp.
    + cbn [vm_init_sp]. rewrite Vsp. exact Vspr.
  - (* [comment removed for export] *)
    assert (HSL' : slots_ok E' M (c_slots cs)) by (eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL]).
    assert (HK' : know_ok RSEGS E' M (s_know (c_ss cs))) by (eapply know_ok_ext; [exact Hag | exact Hkv | exact HK]).
    rewrite slots_grant_filter_eq. (* [comment removed for export] *) unfold slots_ok. apply Forall_forall. intros sl Hin. apply filter_In in Hin as [Hin Hkeep].
    pose proof (proj1 (Forall_forall _ _) HSL' sl Hin) as HS1.
    destruct (split_lit (sl_start sl)) as [hb hk] eqn:Hsp.
    pose proof (safe_range_sem E' M (s_know (c_ss cs)) (c_maps cs) (vm_maps (m_vmmaps model)) a n hb (hk - 4) (sl_stride sl) HK'
                  ltac:(eapply smaps_ok_ext; [exact Hag | exact Hmv | exact Vmaps]) Glo Gsp Hnpos Gimg Gmaps Hkeep) as D.
    eapply slot_ok_agree; [exact HS1|].
    pose proof HS1 as (_ & _ & Hhull & _). rewrite Hsp in Hhull.
    intros x Hx _. apply zfill_out. rewrite u64_lit by lia.
    unfold estart, elenZ in D. cbn [a_base a_off] in D. unfold uE in *. lia.
Qed.

Lemma fd_lookup_std1 : forall model, m_fds model = fds_std ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros model H. rewrite H. reflexivity. Qed.
Lemma fd_lookup_std2 : forall model, m_fds model = fds_std ->
  fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros model H. rewrite H. reflexivity. Qed.

Lemma node_ioctl_sound {FP : FPState} : forall cs cs' E R M model T,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_ioctl cs = Some cs' ->
  (forall R' M', cs_ok E cs' R' M' model -> realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hec Hn HK.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_ioctl in Hn.
  destruct (reg_lit cs 17) as [no|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [fd|] eqn:H10; [|destruct no; try discriminate; repeat (destruct p; try discriminate)].
  destruct (reg_lit cs 11) as [rq|] eqn:H11.
  all: repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; try discriminate.
  injection Hn as <-.
  destruct (reg_lit_sound E cs R M model 17 29 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 1 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 11 0x5413 HC ltac:(lia) H11) as [R11 _].
  unfold cfg_of.
  eapply (rz_ioctl_winsz RSEGS R (Z_to_bv 64 (pc cs)) M model w (Z_to_bv 64 1));
    [exact Hf | exact He | exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact R17 | exact R10 | rewrite u64_lit; lia
    | apply fd_lookup_std1; exact (co_fds _ _ _ _ _ HC) | exact R11 |].
  rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  specialize (HK (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOTTY)) M).
  rewrite pc_set_pc in HK. apply HK.
  apply cs_ok_set_reg_pc; [exact HC | lia |].
  cbn [edenot]. unfold errno_ret, ENOTTY. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma flat_b_sound : forall E M k b off n,
  know_ok RSEGS E M k -> flat_b k b off n = true -> flat E (SA b off) n.
Proof.
  intros E M k b off n HK H. unfold flat_b in H. rewrite base_range_fk in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound RSEGS E M k b lo hi HK Hb) as Hr.
  unfold flat, estart. cbn [a_base a_off]. lia.
Qed.

Lemma kreadZ_kread : forall k b off n z,
  kreadZ RSEGS k b off n = Some z -> exists z0, kread RSEGS k b off n = Some (ELit z0) /\ z = (z0 mod two64)%Z.
Proof.
  intros k b off n z H. unfold kreadZ in H. unfold kread.
  destruct (know_lookup RSEGS k b off n false [] []) as [v scs hs|scs hs|]; try discriminate.
  destruct v; try discriminate. destruct scs; [|discriminate]. injection H as <-. eexists. split; reflexivity.
Qed.

Lemma kreadZ_rdn : forall E M k b off n z,
  know_ok RSEGS E M k -> kreadZ RSEGS k b off n = Some z -> (1 <= n <= 8)%nat ->
  flat E (SA b off) (Z.of_nat n) ->
  rdn RSEGS M (adenot E (SA b off)) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) /\ (0 <= z < two64)%Z.
Proof.
  intros E M k b off n z HK H Hn Hfl.
  destruct (kreadZ_kread k b off n z H) as (z0 & Hr & ->).
  pose proof (kread_rdn RSEGS E M k b off n (ELit z0) HK Hr ltac:(lia) ltac:(lia) Hfl) as Hrd.
  cbn [edenot] in Hrd. split; [| unfold two64; apply Z.mod_pos_bound; lia].
  rewrite Hrd. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (bv_unsigned (edenot E b) + off).
Proof. intros. unfold adenot, v_addi. reflexivity. Qed.

Lemma w2lb1 : forall z, word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with (2^8)%Z. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.

Lemma kread_bytes_rdn : forall E M k len b off zs,
  know_ok RSEGS E M k -> kread_bytes RSEGS len k b off = Some zs ->
  (0 <= bv_unsigned (edenot E b) + off)%Z -> (bv_unsigned (edenot E b) + off + Z.of_nat len <= 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; reflexivity.
  - cbn [kread_bytes] in H.
    destruct (kreadZ RSEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes RSEGS len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat, estart; cbn [a_base a_off]; lia).
    destruct (kreadZ_rdn E M k b off 1 z HK Hz ltac:(lia) Hfl) as [Hrd Hzr].
    rewrite adenot_SA in Hrd.
    destruct (IH b (off + 1)%Z rest HK Hrest ltac:(lia) ltac:(lia)) as [Hrd2 Hlen].
    split; [| cbn; lia].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app.
    + rewrite Hrd. rewrite w2lb1. reflexivity.
    + replace (Z_to_bv 64 (bv_unsigned (edenot E b) + off) + nat_to_word 1)%bv
        with (Z_to_bv 64 (bv_unsigned (edenot E b) + (off + 1))); [exact Hrd2|].
      apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
      change (Z.of_nat 1) with 1%Z. rewrite (Z.mod_small 1) by lia.
      rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma Wz_map : forall fd zs, Wz fd zs = map (WriteEv (Z_to_bv 64 fd)) (map (fun z => Z_to_bv 8 z) zs).
Proof. intros fd zs. unfold Wz. rewrite map_map. reflexivity. Qed.

Lemma node_exit_sound {FP : FPState} : forall cs code E R M model,
  cs_ok E cs R M model -> is_ecall_at RSEGS cs = true -> node_exit cs = Some code ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros cs code E R M model HC Hec Hn.
  destruct (is_ecall_at_sound cs Hec) as (w & Hf & He & _ & _).
  unfold node_exit in Hn.
  assert (H : exists no c, reg_lit cs 17 = Some no /\ (no = 94 \/ no = 93) /\ reg_lit cs 10 = Some c /\ code = Z.land c 255).
  { destruct (reg_lit cs 17) as [no|]; [|discriminate].
    destruct (reg_lit cs 10) as [c|] eqn:H10;
    repeat match type of Hn with context [match ?no with _ => _ end] => destruct no; try discriminate end;
    try discriminate; injection Hn as <-; eexists _, c; (split; [reflexivity|]); split; auto. }
  destruct H as (no & c & H17 & Hno & H10 & ->).
  destruct (reg_lit_sound E cs R M model 17 no HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound E cs R M model 10 c HC ltac:(lia) H10) as [R10 Hc].
  unfold cfg_of.
  assert (Hcode : Z_to_bv 64 (Z.land c 255) = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)).
  { apply bv_eq. rewrite !bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    assert (Hl : (0 <= Z.land c 255 < 256)%Z).
    { split; [apply Z.land_nonneg; lia|]. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound c (2^8) ltac:(lia)). lia. }
    rewrite !Z.mod_small; unfold two64 in Hc; try lia. }
  rewrite Hcode.
  eapply (rz_exit_at RSEGS R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) model w);
    [exact Hf | exact He | exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | | exact R10].
  destruct Hno as [-> | ->]; [left | right]; exact R17.
Qed.

(* [comment removed for export] *)

Lemma kwritable_sound : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable allkn k b off n = true -> (0 <= n)%Z ->
  store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true.
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest H).
  cbn [kentry_ok] in HKK.
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  2: { lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
       apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
       apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
       destruct (xinside_sound RSEGS E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
       unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
       destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
       unfold elenZ, estart in *. cbn [a_base a_off] in *.
       replace (bv_unsigned (edenot E b) + off)%Z
         with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk)))%Z by lia.
       apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  clear H. rename Hc0 into H.
  destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
  apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
  destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in H. rename H into H2.
  pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hx) as Hwl.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. unfold elenZ in Hs.
  unfold estart in Hs. cbn [a_base a_off] in Hs.
  replace (bv_unsigned (edenot E b) + off)%Z with (bv_unsigned (edenot E b) + wk + (off - wk))%Z by lia.
  apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable_x allkn k b off n = true ->
  (forall m, (Z.of_nat m <= elenZ E n)%Z ->
     store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
  /\ (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64)%Z.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable_x] in H.
  destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest H).
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4. cbn [a_base a_off] in Hs, F1, F2, F4.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : (bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off)%Z ->
                 (bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn)%Z ->
                 (forall m, (Z.of_nat m <= elenZ E n)%Z -> store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64)%Z).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off)%Z with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk)))%Z by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H. rename H into H2.
    pose proof (xhi_sound RSEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound RSEGS E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma ridx_val : forall r : bv 5, Z.of_nat (ridx r) = bv_unsigned r.
Proof. intros r. unfold ridx. pose proof (bv_unsigned_in_range 5 r). rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. apply bv_eq. rewrite <- H, ridx_val. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 5 r). unfold bv_wrap. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma v_lw_of_extz : forall old, (0 <= old < 2 ^ 32)%Z -> Z_to_bv 64 (extz true 4 old) = v_lw (Z_to_bv 64 old).
Proof.
  intros old Hold. unfold extz, v_lw. cbn [N.of_nat N.mul]. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma node_cas_sound {FP : FPState} : forall c cs cs' E R M model T,
  cs_ok E cs R M model -> node_cas RSEGS INFOUB c cs = Some cs' ->
  (forall R' M', cs_ok E cs' R' M' model -> realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros c cs cs' E R M model T HC Hn HK.
  (* [comment removed for export] *)
  assert (CORE : forall ra compute setregs pc',
    cas_core RSEGS cs ra compute setregs pc' = Some cs' -> (0 < ra < 32)%nat ->
    exists b k ve new kn' (old : Z) hs,
      split_lit (reg cs ra) = (b, k)
      /\ compute (extK (kn cs) ve) = Some new
      /\ carry [SE (SA b k) 4 new] (kn cs) [] = (kn', [], hs)
      /\ cs' = CS (SS pc' (setregs (extK (kn cs) ve) new (s_regs (c_ss cs))) [] kn' (s_next (c_ss cs))) (c_maps cs) (c_nmaps cs) (c_live cs)
                  (slots_carry kn' [SE (SA b k) 4 new] (c_slots cs))
      /\ getr R (Z_to_bv 5 (Z.of_nat ra)) = adenot E (SA b k)
      /\ (bv_unsigned (adenot E (SA b k)) mod 4 = 0)%Z
      /\ rdn RSEGS M (adenot E (SA b k)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 old))
      /\ (0 <= old < 2 ^ 32)%Z
      /\ edenot E (extK (kn cs) ve) = v_lw (Z_to_bv 64 old)
      /\ store_ok RSEGS M (adenot E (SA b k)) 4 = true
      /\ flat E (SA b k) 4).
  { intros ra compute setregs pc' H Hra. unfold cas_core in H.
    destruct (split_lit (reg cs ra)) as [b k] eqn:Hs.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hkw]. apply andb_prop in Hcond as [Hal Hfl].
    apply Z.leb_le in Hal.
    pose proof (co_know _ _ _ _ _ HC) as HKN.
    destruct (know_lookup RSEGS (kn cs) b k 4 true [] []) as [ve scs hs0|scs hs0|] eqn:Hlk; try discriminate.
    destruct scs; [|discriminate].
    destruct (compute (extK (kn cs) ve)) as [new|] eqn:Hcomp; [|discriminate].
    destruct (carry [SE (SA b k) 4 new] (kn cs) []) as [[kn' scs2] hs] eqn:Hcar.
    destruct scs2; [|discriminate].
    lazymatch type of H with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. clear H.
    pose proof (flat_b_sound E M (kn cs) b k 4 HKN Hfl) as HF.
    pose proof (know_lookup_sound RSEGS E M (kn cs) b k 4 true [] [] HKN ltac:(lia) ltac:(lia)) as HL.
    rewrite Hlk in HL. destruct (HL ltac:(constructor) HF) as (bs & Hrd & Hlen & Hval).
    pose proof (bytes_le_to_Z_bound bs) as Hbb. rewrite Hlen in Hbb. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in Hbb.
    exists b, k, ve, new, kn', (bytes_le_to_Z bs), hs.
    pose proof (split_lit_denot E (reg cs ra) b k Hs) as Hden.
    assert (Hadr : adenot E (SA b k) = edenot E (reg cs ra)) by (rewrite Hden; reflexivity).
    repeat split; try assumption.
    - rewrite (reg_sound E cs R M model ra HC Hra). symmetry. exact Hadr.
    - destruct (ealign_sound RSEGS E M (kn cs) (reg cs ra) HKN) as [Hr [q Hq]]. rewrite Hadr, Hq.
      assert (Hd : (2 ^ 2 | 2 ^ ealign (kn cs) (reg cs ra))%Z) by (apply pow2_divide_le; lia).
      destruct Hd as [r' Hr']. rewrite Hr'. replace (q * (r' * 2 ^ 2))%Z with ((q * r') * 4)%Z by (change (2^2)%Z with 4%Z; ring).
      apply Z.mod_mul. lia.
    - rewrite Hrd. f_equal. symmetry. apply word_to_le_bytes_of_lez; [exact Hlen | lia].
    - lia.
    - lia.
    - rewrite (extK_denot RSEGS E M (kn cs) ve HKN). rewrite <- Hval. apply v_lw_of_extz. lia.
    - rewrite Hadr, Hden. replace 4%nat with (Z.to_nat 4) by reflexivity.
      eapply kwritable_sound; [exact HKN | exact HKN | exact Hkw | lia].
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia.
    - destruct HF as (F1 & F2 & F3 & F4); lia. }
  (* [comment removed for export] *)
  assert (REGS : forall (sr' : list expr) (R' : bvmap 5 word) (mods : list nat),
    (forall r : bv 5, (forall m, In m mods -> ridx r <> m) -> getr R' r = getr R r /\ nth (ridx r) sr' (ELit 0) = nth (ridx r) (s_regs (c_ss cs)) (ELit 0)) ->
    (forall r : bv 5, In (ridx r) mods -> getr R' r = edenot E (nth (ridx r) sr' (ELit 0))) ->
    regs_ok E sr' R').
  { intros sr' R' mods Hoth Hmod. apply regs_ok_pointwise. intros r Hr0.
    destruct (in_dec Nat.eq_dec (ridx r) mods) as [Hin|Hnin]; [exact (Hmod r Hin)|].
    destruct (Hoth r ltac:(intros m Hm X; apply Hnin; rewrite X; exact Hm)) as [-> ->].
    pose proof (co_regs _ _ _ _ _ HC r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [|exact X].
    exfalso. apply Hr0. apply bv_eq. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. exact Hb. }
  destruct c; unfold node_cas in Hn;
    (lazymatch type of Hn with (if ?x then _ else _) = _ => destruct x eqn:Hpc; [apply Z.eqb_eq in Hpc|discriminate] end).
  - (* [comment removed for export] *)
    unfold cas_or in Hn.
    destruct (CORE 14%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl).
    assert (Hnew : mkAluK (kn cs) ALU_OR (extK (kn cs) ve) (reg cs 11) = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    destruct (cas_or_17b50 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 11)) old Ra Hal Hrd Hold R11 Hst)
      as (R' & Hms & G10 & G12 & G13 & G15 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_or INFOUB)) with (0x17f00%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_or_k INFOUB)) with (0x17f20%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (v_or (Z_to_bv 64 old) (edenot E (reg cs 11)))))
      with (mem_denot E M [SE (SA b k) 4 new]).
    2:{ cbn [mem_denot]. f_equal. rewrite <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ (co_know _ _ _ _ _ HC)), Hve, alu_or.
        apply w2b4_or_sext. }
    apply HK. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [15; 13; 12; 10]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 10%nat) | apply (Hm 12%nat) | apply (Hm 13%nat) | apply (Hm 15%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[H|[H|[]]]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G13, Hve. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
           rewrite G12, <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ HKN), Hve, alu_or. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10, Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
  - (* [comment removed for export] *)
    unfold cas_and in Hn.
    destruct (CORE 12%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl).
    assert (Hnew : mkAluK (kn cs) ALU_AND (extK (kn cs) ve) (reg cs 13) = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 13 HC ltac:(lia)) as R13.
    destruct (cas_and_18330 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 13)) old Ra Hal Hrd Hold R13 Hst)
      as (R' & Hms & G14 & G15 & G16 & G17 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_and INFOUB)) with (0x186e0%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_and_k INFOUB)) with (0x18700%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (v_and (Z_to_bv 64 old) (edenot E (reg cs 13)))))
      with (mem_denot E M [SE (SA b k) 4 new]).
    2:{ cbn [mem_denot]. f_equal. rewrite <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ (co_know _ _ _ _ _ HC)), Hve, alu_and.
        apply w2b4_and_sext. }
    apply HK. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [17; 16; 15; 14]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 14%nat) | apply (Hm 15%nat) | apply (Hm 16%nat) | apply (Hm 17%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[H|[H|[]]]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 17)) with (17%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G17. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 16)) with (16%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G16, Hve. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
           rewrite G15, <- Hnew, (mkAluK_denot RSEGS E M _ _ _ _ HKN), Hve, alu_and. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
  - (* [comment removed for export] *)
    unfold cas_lock in Hn.
    destruct (CORE 13%nat _ _ _ Hn ltac:(lia)) as (b & k & ve & new & kn' & old & hs & Hs & Hcomp & Hcar & -> & Ra & Hal & Hrd & Hold & Hve & Hst & Hfl).
    destruct (expr_eqb (extK (kn cs) ve) (ELit 0) && expr_eqb (reg cs 11) (ELit 0))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hold0 H11z]. apply expr_eqb_eq in Hold0. apply expr_eqb_eq in H11z.
    assert (Hnew : reg cs 12 = new) by congruence. clear Hcomp.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12.
    rewrite Hold0 in Hve. cbn [edenot] in Hve.
    assert (R11' : getr R (Z_to_bv 5 (Z.of_nat 11)) = v_lw (Z_to_bv 64 old)) by (rewrite R11, H11z; exact Hve).
    destruct (cas_lock_17308 R M (seg_rom RSEGS) (adenot E (SA b k)) (edenot E (reg cs 12)) old Ra Hal Hrd Hold R11' R12 Hst)
      as (R' & Hms & G14 & G15 & Goth).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_cas_lock INFOUB)) with (0x1757c%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    specialize (HK R' (mem_denot E M [SE (SA b k) 4 new])). cbn [pc c_ss s_pc] in HK. unfold cfg_of in HK.
    replace (Z_to_bv 64 (t_cas_lock_k INFOUB)) with (0x1758c%bv : word) in HK by (apply bv_eq; reflexivity).
    replace (wbytes M (adenot E (SA b k)) (word_to_le_bytes 4 (edenot E (reg cs 12))))
      with (mem_denot E M [SE (SA b k) 4 new]) by (cbn [mem_denot]; rewrite <- Hnew; reflexivity).
    apply HK. destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL].
    constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
    + apply (REGS _ R' [15; 14]%nat).
      * intros r Hm. split.
        -- apply Goth; intros X; subst r; cbn [ridx] in Hm;
             [apply (Hm 14%nat) | apply (Hm 15%nat)]; cbn; auto; reflexivity.
        -- rewrite !nth_sr_upd.
           repeat (lazymatch goal with |- context [Nat.eqb (ridx r) ?m] =>
             destruct (Nat.eqb_spec (ridx r) m) as [Xe|]; [exfalso; apply (Hm m); [cbn; auto 10 | exact Xe]|] end).
           reflexivity.
      * intros r Hin. cbn [In] in Hin.
        destruct Hin as [H|[H|[]]]; pose proof (reg_of_ridx r _ (eq_sym H)) as Xr; subst r;
          (rewrite ridx_lit by lia); rewrite !nth_sr_upd; cbn [Nat.eqb].
        -- replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15. reflexivity.
        -- replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, <- Hve. reflexivity.
    + eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
      cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
    + eapply slots_carry_sound; [| | exact HSL].
      * eapply (carry_sound RSEGS E M); [exact Hcar | | exact HKN | constructor].
        cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
      * cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> SP.sr_vars_lt nx sr = true ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r) ->
  match rv with Some e => SP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq. clear -Hsv. revert i. induction sr as [|e t IH]; intros i; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; exact H2]. }
  assert (BASE : regs_ok (ext_call E nx R') (sr_fresh sr caller_saved nx) (match rv with Some e => regupd R' (Z_to_bv 5 10) (getr R (Z_to_bv 5 10)) | None => R' end)
          \/ True) by (right; exact I). clear BASE.
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  destruct rv as [e|].
  - destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
    destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10].
    + rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
      rewrite Ha0. apply (edenot_agree nx); [exact Hag | rewrite <- expr_vars_lt_eq; exact Hev].
    + destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
      * destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
        rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
        cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
      * rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
        rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
        destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
        exact X.
  - destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    * destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    * rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X.
Qed.

(* [comment removed for export] *)
Lemma know_ok_havoc : forall E M M' k b o n,
  know_ok RSEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_havoc k b o n).
Proof.
  intros E M M' k b o n HK Hout Hg. rewrite kn_havoc_eq. (* [comment removed for export] *) unfold kn_havoc_ref, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.   (* [comment removed for export] *)
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn|]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | |]; try constructor.
    eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

Lemma wview_off_image : forall M (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x52000 <= bv_unsigned x)%Z -> M x = None -> wview RSEGS M x = None.
Proof.
  intros M x Hx HM. unfold wview. rewrite HM. pose proof (u64_range x) as Hr.
  cbn -[Z.leb Z.add Z.of_N bv_unsigned andb].
  change (Z.of_N 0x10000%N) with 0x10000%Z. change (Z.of_N 0x12000%N) with 0x12000%Z.
  change (Z.of_N 0x20000%N) with 0x20000%Z. change (Z.of_N 0x21000%N) with 0x21000%Z.
  change (Z.of_N 0x2000%N) with 0x2000%Z. change (Z.of_N 0x00d000%N) with 0x00d000%Z.
  change (Z.of_N 0x1000%N) with 0x1000%Z.
  repeat (match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); cbn [andb] end); try reflexivity; exfalso; lia.
Qed.

Lemma kwritable_flat : forall E M allkn k b off n,
  know_ok RSEGS E M allkn ->
  know_ok RSEGS E M k -> kwritable allkn k b off n = true ->
  (0 <= bv_unsigned (edenot E b) + off)%Z /\ (bv_unsigned (edenot E b) + off + n <= 2 ^ 64)%Z.
Proof.
  intros E M allkn k b off n Hall HK Hw. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  cbn [kwritable] in Hw. destruct K as [| | | | | |[wb wk] wn|]; try exact (IH Hrest Hw).
  cbn [kentry_ok] in HKK.
  lazymatch type of Hw with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  2: { lazymatch type of Hw with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest Hw)] end.
       apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
       apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
       destruct (xinside_sound RSEGS E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
       unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
       destruct HKK as [Hfl Hs]. destruct Hfl as (F1 & F2 & F3 & F4).
       unfold elenZ, estart in *. cbn [a_base a_off] in *. lia. }
  clear Hw. rename Hc0 into Hw.
  destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
  apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
  destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hw. rename Hw into H2.
  pose proof (xlo_sound RSEGS E M allkn wn wl Hall Hx) as Hwl.
  destruct HKK as [(F1 & F2 & F3 & F4) _]. unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_ok_sound : forall E M k e n,
  know_ok RSEGS E M k -> rw_ok INFOUB k e n = true -> (0 < n)%Z ->
  let a := bv_unsigned (edenot E e) in
  store_ok RSEGS M (edenot E e) (Z.to_nat n) = true
  /\ (forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + n <= 0x10000 \/ 0x52000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + n <= 2 ^ 64)%Z
  /\ (let (b, o) := split_lit e in bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
Proof.
  intros E M k e n HK H Hn. rewrite rw_ok_eq in H. destruct (split_lit e) as [b o] eqn:Hs.
  apply andb_prop in H as [Hw Hoff].
  pose proof (split_lit_denot E e b o Hs) as Hd. cbv zeta.
  pose proof (kwritable_flat E M k k b o n HK HK Hw) as FL.
  assert (Ha : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
  { rewrite Hd, u64_lit by lia. reflexivity. }
  rewrite Ha.
  pose proof (kwritable_sound E M k k b o n HK HK Hw ltac:(lia)) as Hst.
  rewrite off_image_eq in Hoff. change (IMG_SZ INFOUB) with 0x042000%Z in Hoff. pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite u64_lit in Himg by lia.
  split; [rewrite Hd; exact Hst|]. split; [|split; [lia | split; [lia | split; [lia | reflexivity]]]].
  intros i Hi.
  pose proof (store_ok_all RSEGS M (Z.to_nat n) (Z_to_bv 64 (bv_unsigned (edenot E b) + o))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst
                (Z_to_bv 64 (bv_unsigned (edenot E b) + o + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

Lemma know_ok_havoc_e : forall E M M' k e n m,
  know_ok RSEGS E M k -> rw_ok INFOUB k e m = true -> (0 < m)%Z -> (0 <= n < 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned x < bv_unsigned (edenot E e) \/ bv_unsigned (edenot E e) + n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (havoc_e k e n).
Proof.
  intros E M M' k e n m HK Hrw Hm Hn Hout Hg. unfold havoc_e.
  destruct (rw_ok_sound E M k e m HK Hrw Hm) as (_ & _ & _ & _ & _ & Hsplit).
  destruct (split_lit e) as [b o] eqn:Hs.
  apply (know_ok_havoc E M); [exact HK | | exact Hg].
  intros x Hx. apply Hout. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite elenZ_lit in Hx by lia.
  rewrite Hsplit. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma rw_ok_x_sound : forall E M k e n,
  know_ok RSEGS E M k -> rw_ok_x INFOUB k e n = true ->
  let a := bv_unsigned (edenot E e) in
  let N := elenZ E n in
  (forall m, (Z.of_nat m <= N)%Z -> store_ok RSEGS M (edenot E e) m = true)
  /\ (forall i, (0 <= i < N)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + N <= 0x10000 \/ 0x52000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + N <= 2 ^ 64)%Z
  /\ (let (b, o) := split_lit e in bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z)
  /\ (0 < N)%Z.
Proof.
  intros E M k e n HK H. rewrite rw_ok_x_eq in H. destruct (split_lit e) as [b o] eqn:Hs.
  apply andb_prop in H as [Hw Hoff]. apply andb_prop in Hw as [Hlo Hw].
  destruct (xlo k n) as [l|] eqn:Hxl; [|discriminate]. apply Z.ltb_lt in Hlo.
  pose proof (xlo_sound RSEGS E M k n l HK Hxl) as Hl.
  pose proof (split_lit_denot E e b o Hs) as Hd. cbv zeta.
  destruct (kwritable_x_sound E M k k b o n HK HK Hw) as (Hst & F1 & F2).
  assert (Ha : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o)%Z).
  { rewrite Hd, u64_lit by (unfold elenZ in F2; lia). reflexivity. }
  rewrite Ha.
  rewrite off_image_x_eq in Hoff. change (IMG_SZ INFOUB) with 0x042000%Z in Hoff. pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite elenZ_lit in Himg by lia. rewrite u64_lit in Himg by lia.
  pose proof (u64_range (edenot E n)) as Hnr. unfold elenZ in *.
  split; [intros m Hm; rewrite Hd; apply Hst; exact Hm|].
  split; [|split; [lia | split; [lia | split; [lia | split; [reflexivity | lia]]]]].
  intros i Hi.
  pose proof (Hst (Z.to_nat (bv_unsigned (edenot E n))) ltac:(rewrite Z2Nat.id by lia; lia)) as Hst'.
  pose proof (store_ok_all RSEGS M (Z.to_nat (bv_unsigned (edenot E n))) (Z_to_bv 64 (bv_unsigned (edenot E b) + o))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst'
                (Z_to_bv 64 (bv_unsigned (edenot E b) + o + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

Lemma know_ok_havoc_x : forall E M M' k e n,
  know_ok RSEGS E M k -> rw_ok_x INFOUB k e n = true ->
  (forall x : word, (bv_unsigned x < bv_unsigned (edenot E e) \/ bv_unsigned (edenot E e) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (havoc_x k e n).
Proof.
  intros E M M' k e n HK Hrw Hout Hg. unfold havoc_x.
  destruct (rw_ok_x_sound E M k e n HK Hrw) as (_ & _ & _ & _ & _ & Hsplit & _).
  destruct (split_lit e) as [b o] eqn:Hs.
  apply (know_ok_havoc E M); [exact HK | | exact Hg].
  intros x Hx. apply Hout. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite Hsplit. exact Hx.
Qed.

Lemma apart_x_sound : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_x k e1 n1 e2 n2 = true ->
  rw_ok_x INFOUB k e1 n1 = true -> rw_ok_x INFOUB k e2 n2 = true ->
  (bv_unsigned (edenot E e1) + elenZ E n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H R1 R2. rewrite apart_x_eq in H.
  destruct (rw_ok_x_sound E M k e1 n1 HK R1) as (_ & _ & _ & _ & _ & S1 & _).
  destruct (rw_ok_x_sound E M k e2 n2 HK R2) as (_ & _ & _ & _ & _ & S2 & _).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite S1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma store_ok_prefix : forall M (a : word) n k, (k <= n)%nat -> store_ok RSEGS M a n = true -> store_ok RSEGS M a k = true.
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a k Hk H.
  - assert (k = 0)%nat by lia. subst k. reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [store_ok] in *.
    destruct (wview RSEGS M a); [|discriminate]. apply IH; [lia | exact H].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined : forall M (a : Z) k,
  (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat k)%Z -> M (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn RSEGS M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros M a k. revert a. induction k as [|k IH]; intros a Ha Hnw Hdef.
  - exists []. split; reflexivity.
  - cbn [rdn]. destruct (M (Z_to_bv 64 a)) as [b|] eqn:HM.
    2:{ exfalso. apply (Hdef 0%Z ltac:(lia)). rewrite Z.add_0_r. exact HM. }
    destruct (IH (a + 1)%Z ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 1 + i)%Z with (a + (1 + i))%Z by lia; apply Hdef; lia))
      as (bs & Hbs & Hlen).
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1%Z.
        rewrite Z.add_mod_idemp_l by lia. reflexivity. }
    rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma ehi_sound : forall E M k e hi, know_ok RSEGS E M k -> ehi k e = Some hi -> (bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M k e hi HK H. unfold ehi in H. destruct e;
    try (destruct (erange k _) as [[lo' hi']|] eqn:Her; [|discriminate]; injection H as <-; exact (proj2 (erange_sound RSEGS E M k _ lo' hi' HK Her))).
  injection H as <-. cbn [edenot]. rewrite u_lit64. lia.
Qed.

Lemma elo_sound : forall E M k e lo, know_ok RSEGS E M k -> elo k e = Some lo -> (lo <= bv_unsigned (edenot E e))%Z.
Proof.
  intros E M k e lo HK H. unfold elo in H. destruct e;
    try (destruct (erange k _) as [[lo' hi']|] eqn:Her; [|discriminate]; injection H as <-; exact (proj1 (erange_sound RSEGS E M k _ lo' hi' HK Her))).
  injection H as <-. cbn [edenot]. rewrite u_lit64. lia.
Qed.

(* [comment removed for export] *)
Lemma sp_frame_ok_sound : forall E (sp : expr) (fr : Z),
  (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)) <= 0x800000000000)%Z -> (0 <= fr)%Z ->
  sp_frame_ok sp fr = true ->
  (bv_unsigned (edenot E (EVar 0)) - 8388608 + fr <= bv_unsigned (edenot E sp)
   <= bv_unsigned (edenot E (EVar 0)))%Z.
Proof.
  intros E sp fr Hsp Hfr H. unfold sp_frame_ok in H.
  destruct (split_lit sp) as [b c] eqn:Hs.
  destruct b as [| [|[|]] | | | | | |]; try discriminate H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite (split_lit_denot E sp (EVar 0) c Hs). rewrite u64_lit by lia. lia.
Qed.

Lemma below_band_sound : forall E M k b o n hi,
  know_ok RSEGS E M k ->
  (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)))%Z ->
  (0 < n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) <= hi)%Z ->
  below_band k b o n hi = true ->
  (bv_unsigned (edenot E b) + o + n <= bv_unsigned (edenot E (EVar 0)) - 8388608)%Z.
Proof.
  intros E M k b o n hi HK Hsp Hn Hhi H. unfold below_band in H.
  apply andb_prop in H as [Hkd Hfar]. apply Z.leb_le in Hfar.
  pose proof (kdisj_apart_x_sound RSEGS E M k k _ _ _ _ _ _ HK HK Hkd) as Hd.
  unfold estart in Hd; cbn [a_base a_off] in Hd.
  rewrite (elenZ_lit E n), (elenZ_lit E 0x800000000000) in Hd by lia.
  unfold SPBAND_LO in Hfar. lia.
Qed.

Lemma apart_e_sound : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_e k e1 n1 e2 n2 = true ->
  rw_ok INFOUB k e1 n1 = true -> rw_ok INFOUB k e2 n2 = true -> (0 < n1)%Z -> (0 < n2)%Z ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2) \/ bv_unsigned (edenot E e2) + n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H R1 R2 Hn1 Hn2. rewrite apart_e_eq in H.
  destruct (rw_ok_sound E M k e1 n1 HK R1 Hn1) as (_ & _ & _ & _ & _ & S1).
  destruct (rw_ok_sound E M k e2 n2 HK R2 Hn2) as (_ & _ & _ & _ & _ & S2).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite S1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma apart_xe_sound : forall E M k e1 n1 e2 n2 m2,
  know_ok RSEGS E M k -> apart_x k e1 (ELit n1) e2 n2 = true ->
  rw_ok INFOUB k e1 n1 = true -> rw_ok INFOUB k e2 m2 = true -> (0 < n1 < 2 ^ 64)%Z -> (0 < m2)%Z ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 m2 HK H R1 R2 Hn1 Hm2. rewrite apart_x_eq in H.
  destruct (rw_ok_sound E M k e1 n1 HK R1 ltac:(lia)) as (_ & _ & _ & _ & _ & S1).
  destruct (rw_ok_sound E M k e2 m2 HK R2 Hm2) as (_ & _ & _ & _ & _ & S2).
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite (elenZ_lit E n1) in Hd by lia.
  rewrite S1, S2. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma apart_e_loc : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_e k e1 n1 e2 n2 = true ->
  (let (b, o) := split_lit e1 in bv_unsigned (edenot E e1) = (bv_unsigned (edenot E b) + o)%Z) ->
  (let (b, o) := split_lit e2 in bv_unsigned (edenot E e2) = (bv_unsigned (edenot E b) + o)%Z) ->
  (bv_unsigned (edenot E e1) + n1 <= bv_unsigned (edenot E e2) \/ bv_unsigned (edenot E e2) + n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H S1 S2. rewrite apart_e_eq in H.
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite S1, S2. exact Hd.
Qed.

Lemma apart_x_loc : forall E M k e1 n1 e2 n2,
  know_ok RSEGS E M k -> apart_x k e1 n1 e2 n2 = true ->
  (let (b, o) := split_lit e1 in bv_unsigned (edenot E e1) = (bv_unsigned (edenot E b) + o)%Z) ->
  (let (b, o) := split_lit e2 in bv_unsigned (edenot E e2) = (bv_unsigned (edenot E b) + o)%Z) ->
  (bv_unsigned (edenot E e1) + elenZ E n1 <= bv_unsigned (edenot E e2)
   \/ bv_unsigned (edenot E e2) + elenZ E n2 <= bv_unsigned (edenot E e1))%Z.
Proof.
  intros E M k e1 n1 e2 n2 HK H S1 S2. rewrite apart_x_eq in H.
  destruct (split_lit e1) as [b1 o1]. destruct (split_lit e2) as [b2 o2].
  pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK H) as Hd. unfold estart in Hd. cbn [a_base a_off] in Hd.
  rewrite S1, S2. exact Hd.
Qed.

Lemma ret_lit_sound : forall E cs R M model r,
  cs_ok E cs R M model -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ (0 <= r < two64)%Z.
Proof.
  intros E cs R M model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound E cs R M model 1 HC ltac:(lia)) as R1. rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.

(* [comment removed for export] *)
Lemma kept_of_not_caller_saved : forall (r : bv 5) (kept : list (bv 5)),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> In (Z_to_bv 5 (Z.of_nat k)) kept) ->
  r <> 0%bv -> ~ In (ridx r) caller_saved -> In r kept.
Proof.
  intros r kept Hk Hr0 Hn. pose proof (ridx_range r) as Hrr.
  assert (Hr : ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold caller_saved in Hn. cbn [In] in Hn.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ ridx r = k).
  { exists (ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (reg_of_ridx r k Hrk). apply Hk. exact Hink.
Qed.

Lemma slots_vars_lt_filter : forall b f ss, slots_vars_lt b ss = true -> slots_vars_lt b (List.filter f ss) = true.
Proof.
  intros b f ss H. unfold slots_vars_lt in *. apply forallb_forall. intros x Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (forallb_forall _ _) H x Hin).
Qed.

Lemma slots_vars_lt_keep : forall b k ub uk un ss, slots_vars_lt b ss = true -> slots_vars_lt b (slots_keep k ub uk un ss) = true.
Proof. intros. unfold slots_keep. apply slots_vars_lt_filter. assumption. Qed.

Lemma fresh_ok_slots : forall cs, fresh_ok nx0 cs = true -> slots_vars_lt (s_next (c_ss cs)) (c_slots cs) = true.
Proof.
  intros cs H. unfold fresh_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H Hs]. exact Hs.
Qed.

Lemma after_call_fresh : forall cs ret rv k' cs', after_call nx0 cs ret rv k' = Some cs' -> fresh_ok nx0 cs = true.
Proof.
  intros cs ret rv k' cs' H. unfold after_call in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma after_call_sound : forall cs ret rv k' cs' E R R' M M' model ss,
  after_call nx0 cs ret rv k' = Some cs' -> cs_ok E cs R M model ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r) ->
  match rv with Some e => getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok RSEGS E M' k' ->
  slots_ok E M' ss -> slots_vars_lt (s_next (c_ss cs)) ss = true ->
  cs_ok (ext_call E (s_next (c_ss cs)) R') (set_slots cs' ss) R' M' model /\ pc (set_slots cs' ss) = ret.
Proof.
  intros cs ret rv k' cs' E R R' M M' model ss H HC Hkept Hrv HK' HSS Hssv.
  unfold after_call in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  lazymatch type of H with Some ?x = Some ?y => assert (Ecs : y = x) by congruence end. subst cs'. clear H.
  apply andb_prop in Hc as [Hc Hv0]. apply Nat.ltb_lt in Hv0.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh _]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv].
  apply andb_prop in Hfresh as [Hsv _].
  split; [|reflexivity].
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL].
  constructor; cbn [set_slots c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - apply (regs_after_call E (s_regs (c_ss cs)) R R'); [exact HR | exact Hsv | exact Hkept |].
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_ext; [apply ext_call_agree | exact Hkv | exact HK'].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - destruct HV; constructor; try assumption.
    + eapply smaps_ok_ext; [apply ext_call_agree | exact Hmv | assumption].
    + match goal with H : vm_init_sp _ = edenot E (EVar 0) |- _ => rewrite H end.
      cbn [edenot]. apply (ext_call_agree E (s_next (c_ss cs)) R'). exact Hv0.
  - eapply slots_ok_ext; [apply ext_call_agree | exact Hssv | exact HSS].
Qed.

Lemma fresh_ok_nx0 : forall cs, fresh_ok nx0 cs = true -> (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs H. unfold fresh_ok in H. apply andb_prop in H as [_ H]. apply Nat.leb_le in H. exact H.
Qed.

Lemma after_call_nx0 : forall cs ret rv k' cs', after_call nx0 cs ret rv k' = Some cs' ->
  (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs ret rv k' cs' H. unfold after_call in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [apply fresh_ok_nx0; exact Hf | cbn [andb] in H; discriminate].
Qed.

(* [comment removed for export] *)
Definition enframe_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe INFOUB -> call_enframe RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Definition enframe_x_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe INFOUB -> call_enframe_x RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition enframe2_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe INFOUB -> call_enframe2 RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

Definition freepro_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_freepro INFOUB -> call_freepro RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition stdio_write_sound_stmt : Prop := forall (FP : FPState) cs cs' fd bs E R M model T,
  cs_ok E cs R M model -> pc cs = t_stdio_write INFOUB ->
  node_stdio_write RSEGS INFOUB nx0 cs = Some (fd, bs, cs') ->
  T [] ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz fd bs) T).

(* [comment removed for export] *)
Definition fuzz_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_fuzz INFOUB -> call_fuzz INFOUB nx0 cs = Some cs' ->
  (forall (FP' : FPState) E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of (FP:=FP') R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of (FP:=FP) R (pc cs) M model) T.

(* [comment removed for export] *)
Definition mainret_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_main_ret INFOUB -> call_mainret INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition printf_sound_stmt : Prop := forall (FP : FPState) cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_printf INFOUB -> call_printf RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.

(* [comment removed for export] *)
Definition exitcall_sound_stmt : Prop := forall (FP : FPState) cs bs code E R M model,
  cs_ok E cs R M model -> pc cs = t_exitc INFOUB -> node_exitcall RSEGS INFOUB cs = Some (bs, code) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz 1 bs) (t_exit (Z_to_bv 64 code) (m_fs model))).

Hypothesis call_enframe_sound : enframe2_sound_stmt.
Hypothesis call_freepro_sound : freepro_sound_stmt.
Hypothesis node_stdio_write_sound : stdio_write_sound_stmt.
Hypothesis call_fuzz_sound : fuzz_sound_stmt.
Hypothesis call_mainret_sound : mainret_sound_stmt.
Hypothesis call_printf_sound : printf_sound_stmt.
Hypothesis node_exitcall_sound : exitcall_sound_stmt.

(* [comment removed for export] *)
Lemma rw_okb_sound : forall E M k b off n,
  know_ok RSEGS E M k -> rw_okb INFOUB k b off n = true -> (0 < n)%Z ->
  let a := (bv_unsigned (edenot E b) + off)%Z in
  store_ok RSEGS M (Z_to_bv 64 a) (Z.to_nat n) = true
  /\ (forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + n <= 0x10000 \/ 0x52000 <= a)%Z
  /\ (0 <= a)%Z /\ (a + n <= 2 ^ 64)%Z.
Proof.
  intros E M k b off n HK H Hn. rewrite rw_okb_eq in H. apply andb_prop in H as [Hw Hoff]. cbv zeta.
  pose proof (kwritable_flat E M k k b off n HK HK Hw) as FL.
  pose proof (kwritable_sound E M k k b off n HK HK Hw ltac:(lia)) as Hst.
  rewrite off_image_eq in Hoff. change (IMG_SZ INFOUB) with 0x042000%Z in Hoff. pose proof (ranges_apart_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite u64_lit in Himg by lia.
  split; [exact Hst|]. split; [|lia].
  intros i Hi.
  pose proof (store_ok_all RSEGS M (Z.to_nat n) (Z_to_bv 64 (bv_unsigned (edenot E b) + off))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst
                (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as W.
  intros HM. apply W. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kn_contra_sound : forall E M k, know_ok RSEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound RSEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    (destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.

Lemma node_call_sound {FP : FPState} : forall sm (args : list expr) cs cs' E R M model T,
  cs_ok E cs R M model ->
  match sm with
  | SumMemcpy => pc cs = t_memcpy INFOUB /\ call_memcpy INFOUB nx0 cs = Some cs'
  | SumFuzz => False
  | SumEnframe => pc cs = t_enframe INFOUB /\ call_enframe2 RSEGS INFOUB nx0 cs = Some cs'
  | SumFreePro => pc cs = t_freepro INFOUB /\ call_freepro RSEGS INFOUB nx0 cs = Some cs'
  | SumMainRet => pc cs = t_main_ret INFOUB /\ call_mainret INFOUB nx0 cs = Some cs'
  | SumPrintf => pc cs = t_printf INFOUB /\ call_printf RSEGS INFOUB nx0 cs = Some cs'
  end ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros sm args cs cs' E R M model T HC Hsm HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  destruct sm; [|destruct Hsm|..]; destruct Hsm as [Hpc Hn].
  2:{ (* [comment removed for export] *) exact (call_enframe_sound FP cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_freepro_sound FP cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_mainret_sound FP cs cs' E R M model T HC Hpc Hn HK). }
  2:{ (* [comment removed for export] *) exact (call_printf_sound FP cs cs' E R M model T HC Hpc Hn HK). }
  - (* [comment removed for export] *)
    unfold call_memcpy in Hn.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (ehi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
    match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hcond Hap].
    apply andb_prop in Hcond as [Hcond Hrs]. apply andb_prop in Hcond as [Hcond Hrd].
    apply andb_prop in Hcond as [Hn0 Hn40]. apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn40.
    destruct (ehi (kn cs) (reg cs 10)) as [dh|] eqn:Hdh; [|discriminate].
    destruct (ehi (kn cs) (reg cs 11)) as [sh|] eqn:Hsh; [|discriminate].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
    destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hnhi) as Hnle.
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hdh) as Hdle.
    pose proof (ehi_sound E M (kn cs) _ _ HKN Hsh) as Hsle.
    set (d := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *. set (nw := edenot E (reg cs 12)) in *.
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 12) HKN Hrd) as (Dst & Ddef & Dimg & D0 & Dnw & Dspl & Dpos).
    fold d in Dst, Ddef, Dimg, D0, Dnw. unfold elenZ in Dst, Ddef, Dimg, Dnw, Dpos. fold nw in Dst, Ddef, Dimg, Dnw, Dpos.
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 11) (reg cs 12) HKN Hrs) as (Sst & Sdef & Simg & S0 & Snw & _ & _).
    fold sr in Sst, Sdef, Simg, S0, Snw. unfold elenZ in Sst, Sdef, Simg, Snw. fold nw in Sst, Sdef, Simg, Snw.
    pose proof (apart_x_sound E M (kn cs) _ _ _ _ HKN Hap Hrd Hrs) as Hdisj. unfold elenZ in Hdisj. fold d sr nw in Hdisj.
    pose proof (u64_range nw) as Hnwr.
    destruct (rdn_defined M (bv_unsigned sr) (Z.to_nat (bv_unsigned nw)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros i Hi; apply Sdef; rewrite Z2Nat.id in Hi by lia; lia)) as (bs & Hbs & Hlen).
    rewrite Z_to_bv_bv_unsigned in Hbs.
    assert (HOK : mcH M d sr (bv_unsigned nw) bs).
    { constructor.
      - lia.
      - exact Hlen.
      - rewrite Hlen. exact Hbs.
      - rewrite Hlen. apply Dst. rewrite Z2Nat.id by lia. lia.
      - lia.
      - lia.
      - lia. }
    pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
    pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
    pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12.
    destruct (ref_memcpy M d sr (bv_unsigned nw) bs (seg_rom RSEGS) HOK R (Z_to_bv 64 ret) Hrok R1 R10 R11
                ltac:(rewrite Z_to_bv_bv_unsigned; exact R12)) as (R' & Hms & Hkeeps).
    unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_memcpy INFOUB)) with (0x1e6dc%bv : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
    destruct (after_call nx0 cs ret (Some (reg cs 10)) (havoc_x (kn cs) (reg cs 10) (reg cs 12))) as [csa|] eqn:Hac; [|discriminate].
    destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd. cbn in Dspl.
    injection Hn as <-.
    destruct (after_call_sound cs ret (Some (reg cs 10)) (havoc_x (kn cs) (reg cs 10) (reg cs 12)) csa E R R' M (wbytes M d bs) model
                (slots_keep (kn cs) db dk (reg cs 12) (c_slots cs)) Hac HC) as [HC' Hpc'].
    + intros r Hr0 Hnin. apply (keeps_getr R R' r Hkeeps).
      apply kept_of_not_caller_saved; [| exact Hr0 | exact Hnin].
      intros k Hk. cbn [In] in Hk. unfold callee_kept.
      repeat (destruct Hk as [<-|Hk]; [cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
        repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end; fail | ]).
      all: try (destruct Hk).
    + cbv delta [d] in R10. rewrite <- R10. apply (keeps_getr R R' _ Hkeeps). unfold callee_kept. cbn [In].
      do 6 right. left. apply bv_eq. reflexivity.
    + eapply know_ok_havoc_x; [exact HKN | exact Hrd | | apply wbytes_grows].
      intros x Hx. fold d in Hx. unfold elenZ in Hx. fold nw in Hx. apply wbytes_out; rewrite Hlen, Z2Nat.id by lia; lia.
    + eapply slots_keep_sound; [exact HKN | exact (co_slots _ _ _ _ _ HC) |].
      unfold estart, elenZ. cbn [a_base a_off]. fold nw. fold d in Dspl. rewrite <- Dspl.
      intros x Hx. apply wbytes_out; rewrite Hlen, Z2Nat.id by lia; lia.
    + apply slots_vars_lt_keep. apply fresh_ok_slots. eapply after_call_fresh. exact Hac.
    + rewrite <- Hpc'. apply (HK (ext_call E (s_next (c_ss cs)) R') R' (wbytes M d bs)); [|exact HC'].
      eapply env_agree_le; [apply ext_call_agree | eapply after_call_nx0; exact Hac].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_vars : forall bfuel fuel p cs s,
  check RSEGS IT INFOUB nx0 bfuel fuel cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros p cs s Hc; [discriminate|].
  cbn [check] in Hc.
  destruct p as [kf ks|k|k|k| |k|sm args k|c k|e mid k1 k2| |].
  10: { destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity. }
  9: { destruct (SP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
       destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT INFOUB nx0 bfuel fuel (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT INFOUB nx0 bfuel fuel (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv.
       rewrite (IH k1 _ s1 H1), (IH k2 _ s2 H2). reflexivity. }
  all: destruct (run_block_gc RSEGS IT bfuel (STOPS INFOUB) cs) as [cs1|] eqn:Hrb; [|discriminate].
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_mmap INFOUB nx0 cs1) as [[csf css]|] eqn:Hn; [|discriminate].
    exact (IH ks css s Hc).
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_munmap cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_ioctl cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - destruct (Z.eqb (pc cs1) (t_stdio_write INFOUB)); [|discriminate].
    destruct (node_stdio_write RSEGS INFOUB nx0 cs1) as [[[fd bs] cs2]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT INFOUB nx0 bfuel fuel cs2 k) as [s2|] eqn:H2; [|discriminate]. injection Hc as <-. cbn [shape_vars_lt].
    exact (IH k cs2 s2 H2).
  - destruct (is_ecall_at RSEGS cs1); [|discriminate].
    destruct (node_exit cs1); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (negb (is_ecall_at RSEGS cs1) && existsb (Z.eqb (pc cs1)) (STOPS INFOUB))%bool; [|discriminate].
    exact (IH k cs1 s Hc).
  - destruct sm;
      match type of Hc with (match ?r with _ => _ end = _) => destruct r as [cs2|] eqn:Hn; [|discriminate] end; exact (IH k cs2 s Hc).
  - destruct (node_cas RSEGS INFOUB c cs1) as [cs2|] eqn:Hn; [|discriminate]. exact (IH k cs2 s Hc).
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_exitc INFOUB)); [|discriminate].
    destruct (node_exitcall RSEGS INFOUB cs1) as [[[|b bs] code]|]; [| |discriminate]; injection Hc as <-; reflexivity.
Qed.

Lemma node_mmap_nx0 : forall cs csf css, node_mmap INFOUB nx0 cs = Some (csf, css) ->
  (nx0 <= s_next (c_ss cs))%nat.
Proof.
  intros cs csf css Hn. unfold node_mmap in Hn.
  repeat match type of Hn with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | (_ && _)%bool => destruct x eqn:?HC; [|discriminate]
      | _ => destruct x; try discriminate
      end
  end.
  match goal with H : (_ && fresh_ok nx0 cs && _)%bool = true |- _ =>
    apply andb_prop in H as [H _]; apply andb_prop in H as [_ Hf]; apply fresh_ok_nx0; exact Hf end.
Qed.

Theorem check_sound : forall fuel bfuel p cs s,
  check RSEGS IT INFOUB nx0 bfuel fuel cs p = COk s ->
  forall (FP : FPState) E R M model, cs_ok E cs R M model ->
  realizes RSEGS (cfg_of R (pc cs) M model) (sd E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel p cs s Hc FP E R M model HC; [discriminate|].
  cbn [check] in Hc.
  (* [comment removed for export] *)
  destruct p as [kf ks|k|k|k| |k|sm args k|c k|e mid k1 k2| |].
  10: { destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
        exact (kn_contra_sound E M (kn cs) (co_know _ _ _ _ _ HC) Hk). }
  9: { destruct (expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
       destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
       destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate].
       destruct (check RSEGS IT INFOUB nx0 bfuel fuel (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
       destruct (check RSEGS IT INFOUB nx0 bfuel fuel (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
       injection Hc as <-. cbn [sd].
       destruct (split_sound cs e mid lo hi E R M model HC Hr) as [HCl HCr].
       destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
       - exact (IH bfuel k1 _ s1 H1 FP E R M model (HCl Hle)).
       - exact (IH bfuel k2 _ s2 H2 FP E R M model (HCr ltac:(lia))). }
  all: destruct (run_block_gc RSEGS IT bfuel (STOPS INFOUB) cs) as [cs1|] eqn:Hrb; [|discriminate].
  all: destruct (run_block_gc_sound IT IT_ok bfuel (STOPS INFOUB) cs cs1 E R M model Hrb HC) as (R1 & M1 & Hms & HC1 & Hmaps).
  all: eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_mmap INFOUB nx0 cs1) as [[csf css]|] eqn:Hn; [|discriminate].
    rename Hc into Hs. rename s into ss.
    pose proof (node_mmap_nx0 cs1 csf css Hn) as Xle.
    eapply (node_mmap_sound cs1 csf css E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    + intros a R' M' model' HC' Hfs.
      rewrite (sd_agree nx0 E (ext1 E (s_next (c_ss cs1)) a) (m_fs model) ss).
      * rewrite <- Hfs. exact (IH bfuel ks css ss Hs FP _ R' M' model' HC').
      * eapply env_agree_le; [apply ext1_agree | exact Xle].
      * eapply check_vars. exact Hs.
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_munmap cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_munmap_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' model' HC' Hfs. rewrite <- Hfs. exact (IH bfuel k cs2 s Hc FP E R' M' model' HC').
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_ioctl cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_ioctl_sound cs1 cs2 E R1 M1 model); [exact HC1 | exact Hec | exact Hn |].
    intros R' M' HC'. exact (IH bfuel k cs2 s Hc FP E R' M' model HC').
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_stdio_write INFOUB)) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
    destruct (node_stdio_write RSEGS INFOUB nx0 cs1) as [[[fd bs] cs2]|] eqn:Hn; [|discriminate].
    destruct (check RSEGS IT INFOUB nx0 bfuel fuel cs2 k) as [s2|] eqn:H2; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_stdio_write_sound FP cs1 cs2 fd bs E R1 M1 model); [exact HC1 | exact Hpc | exact Hn | apply sd_has_nil |].
    intros E' R' M' Hag HC'. rewrite (sd_agree nx0 E E' (m_fs model) s2);
      [ exact (IH bfuel k cs2 s2 H2 FP _ R' M' model HC') | exact Hag | eapply check_vars; exact H2 ].
  - (* [comment removed for export] *)
    destruct (is_ecall_at RSEGS cs1) eqn:Hec; [|discriminate].
    destruct (node_exit cs1) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    destruct (negb (is_ecall_at RSEGS cs1) && existsb (Z.eqb (pc cs1)) (STOPS INFOUB))%bool; [|discriminate].
    exact (IH bfuel k cs1 s Hc FP E R1 M1 model HC1).
  - (* [comment removed for export] *)
    destruct sm.
    all: match type of Hc with (match ?r with _ => _ end = _) => destruct r as [cs2|] eqn:Hn; [|discriminate] end.
    all: lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hpc; [|discriminate] end; apply Z.eqb_eq in Hpc.
    2: { (* [comment removed for export] *)
         eapply (call_fuzz_sound FP cs1 cs2 E R1 M1 model); [exact HC1 | exact Hpc | exact Hn |].
         intros FP' E' R' M' Hag HC'. rewrite (sd_agree nx0 E E' (m_fs model) s);
           [ exact (IH bfuel k cs2 s Hc FP' _ R' M' model HC') | exact Hag | eapply check_vars; exact Hc ]. }
    all: lazymatch type of Hn with
         | call_memcpy _ _ _ = _ => eapply (node_call_sound SumMemcpy args cs1 cs2 E R1 M1)
         | call_enframe2 _ _ _ _ = _ => eapply (node_call_sound SumEnframe args cs1 cs2 E R1 M1)
         | call_freepro _ _ _ _ = _ => eapply (node_call_sound SumFreePro args cs1 cs2 E R1 M1)
         | call_mainret _ _ _ = _ => eapply (node_call_sound SumMainRet args cs1 cs2 E R1 M1)
         | call_printf _ _ _ _ = _ => eapply (node_call_sound SumPrintf args cs1 cs2 E R1 M1)
         end; [exact HC1 | split; [exact Hpc | exact Hn] |].
    all: intros E' R' M' Hag HC'; rewrite (sd_agree nx0 E E' (m_fs model) s);
         [ exact (IH bfuel k cs2 s Hc FP _ R' M' model HC') | exact Hag | eapply check_vars; exact Hc ].
  - (* [comment removed for export] *)
    destruct (node_cas RSEGS INFOUB c cs1) as [cs2|] eqn:Hn; [|discriminate].
    eapply (node_cas_sound c cs1 cs2 E R1 M1 model); [exact HC1 | exact Hn |].
    intros R' M' HC'. exact (IH bfuel k cs2 s Hc FP E R' M' model HC').
  - (* [comment removed for export] *)
    destruct (Z.eqb (pc cs1) (t_exitc INFOUB)) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
    destruct (node_exitcall RSEGS INFOUB cs1) as [[bs code]|] eqn:Hn; [|discriminate].
    pose proof (node_exitcall_sound FP cs1 bs code E R1 M1 model HC1 Hpc Hn) as HX.
    destruct bs as [|b bs]; injection Hc as <-; cbn [sd]; [|exact HX].
    eapply rz_conseq; [exact HX|]. cbn [Wz map]. apply t_emit_nil_eq. apply t_exit_has_nil.
Qed.

End NX0.
End SPS.
End UbSymPlanSound.

Module UbTargetEntry_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan.
Unset Lia Cache.
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

Definition ITAB : itab := mk_itab Ubsan.M.loaded_segments TEXT_LO (text_n INFOUB).

Definition NX0 : nat := 46%nat.
Definition sr_T : list expr :=
  [ELit 0;
   ELit 0x12c5c;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0x314d8;
   EVar 17;
   EVar 18;
   EVar 19;
   EAlu ALU_ADD (EVar 1) (ELit 34);
   EAlu ALU_ADD (EVar 1) (ELit 32);
   EAlu ALU_ADD (EVar 1) (ELit 34);
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit 38);
   EVar 4;
   EVar 26;
   EVar 27;
   EVar 28;
   EVar 29;
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit 38);
   EVar 4;
   EExt true 0 1 (EVar 7);
   ELit 0x213c9;
   ELit 0;
   EVar 36;
   EVar 37;
   EVar 38;
   EVar 39;
   EVar 40;
   EVar 41;
   EVar 42;
   EVar 43].

Definition kn_T0 : list kentry :=
  [KAlign (EVar 0) 16;
   KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x16fe4);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x12ae8);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fff7f7ff000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0x52000 0x7fffff7ef000;
   KWr (SA (EVar 1) (0)) (ELit 69632);
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x800000000000) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x800000000000) (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (ELit 0) 0x10000) (ELit 0x042000) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (ELit 0) 0x10000) (ELit 0x042000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 44);
   KWord (SA (EVar 2) (8)) 8 (ELit 0);
   KWord (SA (EVar 2) (16)) 8 (ELit 101);
   KWord (SA (EVar 2) (24)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 2) (32)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 2) (40)) 8 (EVar 1);
   KWord (SA (EVar 2) (48)) 8 (ELit 0);
   KWord (SA (EVar 2) (56)) 8 (ELit 0x11b20);
   KZero (SA (EVar 2) (64)) (ELit 4032);
   KWord (SA (EVar 1) (0)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 1) (8)) 1 (ELit 0);
   KZero (SA (EVar 1) (9)) (ELit 4);
   KWord (SA (EVar 1) (13)) 1 (ELit 224);
   KWord (SA (EVar 1) (14)) 2 (ELit 1);
   KWord (SA (EVar 1) (28)) 1 (ELit 0);
   KWord (SA (EVar 1) (29)) 1 (ELit 160);
   KWord (SA (EVar 1) (30)) 2 (ELit 1);
   KWord (SA (EVar 1) (65568)) 1 (ELit 0);
   KWord (SA (EVar 1) (69623)) 1 (ELit 0);
   KWord (SA (EVar 1) (69624)) 4 (ELit 4060);
   KZero (SA (EVar 1) (69628)) (ELit 4);
   KBlob (SA (EVar 1) (32)) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 0;
   KWr (SA (ELit 0) 0x21000) (ELit 0x31000);
   KImg 0x0 0x1000;
   KImg 0x10000 0x21380;
   KImg 0x21381 0x213c9;
   KImg 0x313c9 0x31408;
   KImg 0x514e0 0x51500;
   KWord (SA (ELit 0) (201744)) 8 (ELit 0x31410);
   KWord (SA (ELit 0) (201776)) 4 (EVar 3);
   KWord (SA (ELit 0) (201780)) 4 (EVar 11);
   KImg 0x3143c 0x31488;
   KImg 0x31490 0x314a8;
   KImg 0x314b0 0x314c8;
   KImg 0x314d8 0x314e8;
   KImg 0x314f0 0x514e0; KImg 0x51518 0x51744;
   KWord (SA (ELit 0) (333640)) 8 (EVar 45);
   KImg 0x51750 0x51758;
   KImg 0x51769 0x51770;
   KImg 0x51778 0x51780;
   KImg 0x51790 0x51798;
   KWord (SA (ELit 0) (333720)) 8 (ELit 4096);
   KImg 0x517a0 0x517d0;
   KImg 0x517d8 0x517e0;
   KWord (SA (ELit 0) (333792)) 8 (EVar 44);
   KWord (SA (ELit 0) (333800)) 4 (ELit 1);
   KWord (SA (ELit 0) (333804)) 4 (ELit 1);
   KWord (SA (ELit 0) (333808)) 8 (ELit 0);
   KWord (SA (ELit 0) (333816)) 8 (EAlu ALU_ADD (EVar 2) (ELit 64));
   KWord (SA (ELit 0) (333824)) 8 (ELit 100);
   KWord (SA (ELit 0) (333832)) 8 (ELit 0);
   KWord (SA (ELit 0) (333840)) 8 (EVar 10);
   KWord (SA (ELit 0) (333848)) 8 (EVar 2);
   KWord (SA (ELit 0) (333856)) 8 (EVar 2);
   KWord (SA (ELit 0) (333864)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0x51830 0x51990;
   KWord (SA (ELit 0) (334224)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KImg 0x51998 0x519b0;
   KImg 0x519b0 0x51b10;
   KWord (SA (ELit 0) (334608)) 8 (ELit 1);
   KImg 0x51b18 0x51b30;
   KImg 0x51b30 0x51b70;
   KWord (SA (ELit 0) (334704)) 1 (ELit 1);
   KImg 0x51b71 0x51b78;
   KWord (SA (ELit 0) (334712)) 8 (EVar 9);
   KImg 0x51b88 0x52000;
   KRange (EVar 3) 1 4194303;
   KRange (EVar 10) 0 1;
   KRange (EVar 11) 0 4294967295;
   KRange (EVar 5) 0 32767;
   KRange (EVar 6) 0 255;
   KRange (EVar 7) 0 255;
   KRange (EVar 8) 0 255;
   KRange (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 6 65535].

(* [comment removed for export] *)
Definition kn_T (nlo nhi : Z) : list kentry :=
  KRange (EVar 4) nlo nhi :: KRange (EVar 5) 0 (Z.min 32767 (65529 - nlo)) :: kn_T0.

(* [comment removed for export] *)
Definition maps_T : list smap := [SM (EVar 1) (ELit 69632) true; SM (EVar 2) (ELit 4096) false].

(* [comment removed for export] *)
Definition slots_T : list sslot :=
  [SL (EAlu ALU_ADD (EVar 1) (ELit 16)) (ELit 69616) (ELit 65536) (ELit 1) (ELit 0x11b20) 0 (EAlu ALU_ADD (EVar 1) (ELit 32))].

Definition cs_T (nlo nhi : Z) : cstate := CS (SS 0x12db8 sr_T [] (kn_T nlo nhi) NX0) maps_T 4 278528 slots_T.
End UbTargetEntry_defs.

Module UbTargetEntry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.
Import UbTargetEntry_defs.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition vals_T (sp0 gm area tid : Z) (content : list byte) (brkv mas e sec cnr : Z) (R : bvmap 5 word) : list word :=
  [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
   Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content);
   Z_to_bv 64 (hdr_b0 content);
   Z_to_bv 64 (hdr_b1 content);
   Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
   Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e] ++ junk_vals R ++ [Z_to_bv 64 sec; Z_to_bv 64 cnr].

Definition E_T (sp0 gm area tid : Z) (content : list byte) (brkv mas e sec cnr : Z) (R : bvmap 5 word) : env :=
  Env (vals_ev (vals_T sp0 gm area tid content brkv mas e sec cnr R)) (blobs_ev [content]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vadd_ZZ' : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by (cbn; lia). reflexivity.
Qed.

Lemma v_addi_Z : forall x k, (0 <= x < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof. intros. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.

(* [comment removed for export] *)
Lemma rdn1_of_mem : forall M (a : word) (b : byte), M a = Some b -> rdn RSEGS M a 1 = Some [b].
Proof.
  intros M a b H. cbn [rdn]. rewrite H. reflexivity.
Qed.

Lemma w2b1 : forall z, (0 <= z < 256)%Z -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. rewrite u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_defined : forall M (a : Z) (n : Z),
  (forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None) ->
  (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z -> store_ok RSEGS M (Z_to_bv 64 (a + d)) m = true.
Proof.
  intros M a n Hdef Ha Hn d m Hd Hm. destruct m as [|m']; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia.
  replace x with (Z_to_bv 64 (a + (bv_unsigned x - a))) by (apply bv_eq; rewrite u_small by lia; lia).
  pose proof (Hdef (bv_unsigned x - a) ltac:(lia)) as Hm'.
  unfold wview. destruct (M (Z_to_bv 64 (a + (bv_unsigned x - a)))); [discriminate | contradiction].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined_nth : forall M (a : Z) n bs,
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros M a n bs Hr Hdef Ha Hn i Hi.
  pose proof (rdn_nth RSEGS M n (Z_to_bv 64 a) bs (Z.to_nat i) Hr ltac:(lia)) as B.
  rewrite w_add_nat, u_small in B by lia. rewrite Z2Nat.id in B by lia.
  cbn [rdn] in B.
  destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:Hm.
  - cbn in B. injection B as B'. rewrite B'. reflexivity.
  - exfalso. exact (Hdef i Hi Hm).
Qed.

(* [comment removed for export] *)
Lemma seps_conv : forall l, UbTargetPre.seps l -> SPSA.seps l.
Proof.
  intros l H. induction H; constructor; auto.
Qed.

Lemma live_bytes_bound : forall (l : list (word * word)) n b,
  (length l <= n)%nat ->
  Forall (fun p => (0 < bv_unsigned (snd p) <= b)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) l ->
  (0 <= b)%Z -> (live_bytes l <= Z.of_nat n * b)%Z.
Proof.
  intros l. induction l as [|[a sz] l IH]; intros n b Hlen HF Hb; cbn [live_bytes length] in *.
  - lia.
  - apply Forall_cons_iff in HF as [[H1 _] HF]. cbn [snd] in H1.
    destruct n as [|n]; [lia|]. specialize (IH n b ltac:(lia) HF Hb). lia.
Qed.

(* [comment removed for export] *)
Definition ivs_cover (lo hi : Z) : bool :=
  existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv))%bool img_clear_ivs.

Lemma img_clear_cover : forall M lo hi,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
  ivs_cover lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros M lo hi HF Hc i Hi. unfold ivs_cover in Hc. apply existsb_exists in Hc as (iv & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (proj1 (Forall_forall _ _) HF iv Hin). lia.
Qed.

Definition all_regs : list Prelude.reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  Variables (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte).
  Variables (VM : VmMaps) (model : Model) (nlo nhi : Z).
  Hypothesis TP : target_pre sp0 gm area brkv mas tid sec cnr content R M.
  Hypothesis TV : target_vm sp0 gm area VM.
  Hypothesis Mfds : m_fds model = fds_std.
  Hypothesis Mvm : m_vmmaps model = VM.
  Hypothesis Mhalt : m_halted model = None.
  Hypothesis Mlazy : m_vm_lazy model = [].
  Hypothesis Mmat : m_vm_materialized model = [].
  Hypothesis Hn : nlo <= hdr_paylen content <= nhi.
  Variable e : Z.
  Hypothesis He : 0 <= e < 2 ^ 32.
  Hypothesis Ce : cell M 0x31434 4 e.

  Let E : env := E_T sp0 gm area tid content brkv mas e sec cnr R.
  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Lemma EV0 : ev E 0 = Z_to_bv 64 sp0. Proof. reflexivity. Qed.
  Lemma EV1 : ev E 1 = Z_to_bv 64 gm. Proof. reflexivity. Qed.
  Lemma EV2 : ev E 2 = Z_to_bv 64 area. Proof. reflexivity. Qed.
  Lemma EV3 : ev E 3 = Z_to_bv 64 tid. Proof. reflexivity. Qed.
  Lemma EV4 : ev E 4 = Z_to_bv 64 (hdr_paylen content). Proof. reflexivity. Qed.
  Lemma EV5 : ev E 5 = Z_to_bv 64 (hdr_cfglen content). Proof. reflexivity. Qed.
  Lemma EV6 : ev E 6 = Z_to_bv 64 (hdr_b0 content). Proof. reflexivity. Qed.
  Lemma EV7 : ev E 7 = Z_to_bv 64 (hdr_b1 content). Proof. reflexivity. Qed.
  Lemma EV8 : ev E 8 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))). Proof. reflexivity. Qed.
  Lemma EV9 : ev E 9 = Z_to_bv 64 brkv. Proof. reflexivity. Qed.
  Lemma EV10 : ev E 10 = Z_to_bv 64 mas. Proof. reflexivity. Qed.
  Lemma EV11 : ev E 11 = Z_to_bv 64 e. Proof. reflexivity. Qed.
  Lemma EVJ : forall i, (i < 32)%nat -> ev E (12 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, E_T. cbn [ev]. unfold vals_T.
    change (12 + i)%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
       Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content); Z_to_bv 64 (hdr_b0 content);
       Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
       Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e : word] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus. rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; lia).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Lemma EV44 : ev E 44 = Z_to_bv 64 sec. Proof. reflexivity. Qed.
  Lemma EV45 : ev E 45 = Z_to_bv 64 cnr. Proof. reflexivity. Qed.
  Lemma EB0 : eb E 0 = content. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma b0_rng : 0 <= hdr_b0 content < 256. Proof. unfold hdr_b0. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b1_rng : 0 <= hdr_b1 content < 256. Proof. unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b2_rng : 0 <= bv_unsigned (nth 2 content (Z_to_bv 8 0)) < 256. Proof. pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma cfglen_rng : 0 <= hdr_cfglen content < 32768.
  Proof. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Ltac enorm :=
    cbn [edenot a_base a_off];
    rewrite ?alu_add, ?EV0, ?EV1, ?EV2, ?EV3, ?EV4, ?EV5, ?EV6, ?EV7, ?EV8, ?EV9, ?EV10, ?EV11, ?EV44, ?EV45;
    rewrite ?vadd_ZZ'.
  Ltac anorm := unfold adenot, estart, elenZ; enorm; rewrite ?v_addi_Z by lia; rewrite ?u_small by lia.

  Ltac kimg Wimg := split; [lia|]; split; [lia|]; apply (img_clear_cover _ _ _ Wimg); vm_compute; reflexivity.
  Ltac karith := anorm; lia.
  Ltac kflat := apply flat_intro; unfold elenZ; enorm; rewrite ?u_small by lia; lia.
  Ltac kwr_stack Hst := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm;
                    replace (sp0 + -8388608 + d) with (sp0 - 8388608 + d) by lia; apply Hst; lia.
  Ltac kwr_def Hdef := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm; rewrite ?Z.add_0_r;
                    first [ apply (store_ok_of_defined _ _ _ Hdef); lia
                          | replace (area + 0 + d) with (area + d) by lia; apply (store_ok_of_defined _ _ _ Hdef); lia
                          | replace (gm + 0 + d) with (gm + d) by lia; apply (store_ok_of_defined _ _ _ Hdef); lia ].
  Ltac kwr_data := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm; apply store_ok_data; rewrite u_small by lia; lia.
  Ltac kword_abs aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => change (Z_to_bv 64 a) with (Z_to_bv 64 aexp : word) end;
                    first [ exact C | unfold cell in C; rewrite C; reflexivity ].
  Ltac kword_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with aexp by lia end;
                    first [ exact C | unfold cell in C; rewrite C; first [reflexivity | f_equal] ].
  Ltac kbyte_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with aexp by lia end;
                    rewrite (rdn1_of_mem _ _ _ C); rewrite w2b1 by lia; reflexivity.
  Ltac kzero aexp C := split; [kflat|]; intros i Hi; revert i Hi; anorm; intros i Hi;
                    lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (aexp + i) by lia end;
                    apply C; lia.
  Ltac kblob HTC Hdef := split; [kflat|]; split; [rewrite EB0; anorm; lia|];
                intros i Hi; revert i Hi; anorm; rewrite EB0; intros i Hi;
                lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (gm + 32 + i) by lia end;
                apply (rdn_defined_nth _ (gm + 32) (length content) content HTC); try lia;
                intros j Hj; replace (gm + 32 + j) with (gm + (32 + j)) by lia; apply Hdef; lia.

  Theorem target_entry_ok_e :
    cs_ok E (cs_T nlo nhi) R M model.
  Proof.
    pose proof TP as TP'.
    destruct TP' as [tp_ra tp_sp tp_gp tp_tp tp_a0 tp_a1 tp_a2 tp_a3 tp_s0 tp_s1 tp_s2 tp_s3 tp_s4 tp_s5 tp_s6 tp_s7
                     tp_sp0 tp_top tp_len tp_stack TF TW TC].
    pose proof TW as TW'. destruct TW'.
    lazymatch goal with H : enframe_post _ _ _ _ _ _ |- _ => pose proof H as EP0; destruct H end.
    lazymatch goal with x := gm + 16 + 16 * 1 |- _ => subst x end.
    lazymatch goal with x := gm + 16 + 69616 - 4 |- _ => subst x end.
    lazymatch goal with x := 69616 - 4 - 65536 - 16 * 1 |- _ => subst x end.
    lazymatch goal with x := 69616 * 0 / 16 + 1 |- _ => subst x end.
    destruct TF as [mf_ra mf_s0 mf_s1 mf_s2 mf_s3 mf_s4 mf_s5 mf_s6 mf_s7].
    pose proof b0_rng as Hb0. pose proof b1_rng as Hb1. pose proof b2_rng as Hb2. pose proof cfglen_rng as Hcl.
    assert (HL : hdr_paylen content + hdr_cfglen content + 6 = L) by (unfold hdr_paylen; subst L; lia).
    (* [comment removed for export] *)
    replace (gm + 16 + 16 * 1 - 4) with (gm + 28) in Pm4 by lia.
    replace (gm + 16 + 16 * 1 - 3) with (gm + 29) in Pm3 by lia.
    replace (gm + 16 + 16 * 1 - 2) with (gm + 30) in Pm2 by lia.
    replace (gm + 16 + 16 * 1 + 65536) with (gm + 65568) in Pzr by lia.
    replace (gm + 16 + 69616 - 4 - 5) with (gm + 69623) in Pe5 by lia.
    replace (gm + 16 + 69616 - 4 - 4) with (gm + 69624) in Pe4 by lia.
    replace (gm + 16 - 3) with (gm + 13) in Ps3 by lia.
    replace (gm + 16 - 2) with (gm + 14) in Ps2 by lia.
    change (69616 - 4 - 65536 - 16 * 1) with 4060 in Pm3, Pzr, Pe5, Pe4, Pr.
    change (69616 * 0 / 16 + 1) with 1 in Pm2, Pr.
    change (0 + 32 * res_code 4060) with 160 in Pm3.
    specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
    specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
    constructor.
    - (* [comment removed for export] *)
      intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity. }
      pose proof (ridx_range r) as Hri. rewrite <- (ridx_roundtrip r) at 1.
      cbn [c_ss cs_T s_regs].
      generalize (ridx r) Hri. clear r Hr0 Hri. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        [ .. | lia]; rewrite <- nth_all_regs by lia; cbn [nth sr_T all_regs];
        lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                  change (edenot E (EVar n)) with (ev E n);
                  first [ rewrite (EVJ (n - 12)) by lia; reflexivity
                        | rewrite ?EV4, ?EV5; first [exact tp_a1 | exact tp_a3 | exact tp_s2 | exact tp_s4 | idtac] ]
              | |- _ => idtac end;
        try (enorm; first [ reflexivity | exact tp_ra | exact tp_gp | exact tp_tp
                          | rewrite tp_sp; f_equal; lia
                          | rewrite tp_a0; f_equal; lia | rewrite tp_s1; f_equal; lia
                          | rewrite tp_s0; f_equal; lia | rewrite tp_s3; f_equal; lia
                          | rewrite tp_s6; f_equal; lia | rewrite tp_s7; f_equal; lia
                          | rewrite tp_a2; f_equal; lia ]).
      (* [comment removed for export] *)
      rewrite tp_s5. cbn [edenot]. rewrite EV7. unfold ext_val, ext_Z. rewrite u_small by lia.
      change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_1_r, (Z.mod_small _ 256) by lia.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus (8 * N.of_nat 1)) with 128. change (bv_modulus (8 * N.of_nat 1)) with 256.
      destruct (Z.ltb_spec0 (hdr_b1 content) 128).
      + rewrite (Z.mod_small (_ + 128) 256) by lia. f_equal. lia.
      + replace ((hdr_b1 content + 128) mod 256) with (hdr_b1 content + 128 - 256) by
          (apply Z.mod_unique with (q := 1); lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply Z.mod_unique with (q := -1); [lia|]. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      cbn [c_ss cs_T s_know]. unfold kn_T, kn_T0, know_ok.
      repeat (apply Forall_cons; [|try apply Forall_nil]).
      all: cbn [kentry_ok].
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *)
        anorm. pose proof (Z.le_min_l 32767 (65529 - nlo)). pose proof (Z.le_min_r 32767 (65529 - nlo)).
        pose proof (Z.min_spec 32767 (65529 - nlo)). lia.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_stack tp_stack.
      + (* [comment removed for export] *) kword_rel (sp0 - 56) mf_ra.
      + (* [comment removed for export] *) kword_rel (sp0 - 64) mf_s0.
      + (* [comment removed for export] *) kword_rel (sp0 - 72) mf_s1.
      + (* [comment removed for export] *) kword_rel (sp0 - 80) mf_s2.
      + (* [comment removed for export] *) kword_rel (sp0 - 88) mf_s3.
      + (* [comment removed for export] *) kword_rel (sp0 - 96) mf_s4.
      + (* [comment removed for export] *) kword_rel (sp0 - 104) mf_s5.
      + (* [comment removed for export] *) kword_rel (sp0 - 112) mf_s6.
      + (* [comment removed for export] *) kword_rel (sp0 - 120) mf_s7.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_def w_grp_def.
      + (* [comment removed for export] *) kwr_def w_area_def.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kword_rel area w_area_chk.
      + (* [comment removed for export] *) kword_rel (area + 8) w_area_next.
      + (* [comment removed for export] *) kword_rel (area + 16) w_area_ns.
      + (* [comment removed for export] *) kword_rel (area + 24) w_slot0_prev.
      + (* [comment removed for export] *) kword_rel (area + 32) w_slot0_next.
      + (* [comment removed for export] *) kword_rel (area + 40) w_slot0_mem.
      + (* [comment removed for export] *) kword_rel (area + 48) w_slot0_msk.
      + (* [comment removed for export] *) kword_rel (area + 56) w_slot0_W.
      + (* [comment removed for export] *) kzero (area + 64) w_area_rest.
      + (* [comment removed for export] *) kword_rel gm w_grp_meta.
      + (* [comment removed for export] *) kword_rel (gm + 8) w_grp_aidx.
      + (* [comment removed for export] *) kzero (gm + 9) w_grp_pad.
      + (* [comment removed for export] *) kbyte_rel (gm + 13) Ps3.
      + (* [comment removed for export] *) kword_rel (gm + 14) Ps2.
      + (* [comment removed for export] *) kbyte_rel (gm + 28) Pm4.
      + (* [comment removed for export] *) kbyte_rel (gm + 29) Pm3.
      + (* [comment removed for export] *) kword_rel (gm + 30) Pm2.
      + (* [comment removed for export] *) kbyte_rel (gm + 65568) Pzr.
      + (* [comment removed for export] *) kbyte_rel (gm + 69623) Pe5.
      + (* [comment removed for export] *) kword_rel (gm + 69624) Pe4.
      + (* [comment removed for export] *) kzero (gm + 69628) w_grp_tail.
      + (* [comment removed for export] *) kblob TC w_grp_def.
      + (* [comment removed for export] *) kwr_data.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (201744) w_self.
      + (* [comment removed for export] *) kword_abs (201776) w_tid.
      + (* [comment removed for export] *) kword_abs (201780) Ce.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + kimg w_img.
      + (* [comment removed for export] *) kword_abs (333640) w_canary.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (333720) w_pagesz.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_secret) w_secret.
      + (* [comment removed for export] *) kword_abs (ctx_init_done) w_init.
      + (* [comment removed for export] *) kword_abs (ctx_mmap_counter) w_ctr.
      + (* [comment removed for export] *) kword_abs (ctx_free_meta_head) w_fmh.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta) w_am.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_count) w_amc.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_area_count) w_amac.
      + (* [comment removed for export] *) kword_abs (ctx_meta_alloc_shift) w_mas.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_head) w_mah.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_tail) w_mat.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_areas) w_amas.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_active 44) w_active44.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_usage 44) w_usage44.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_seq) w_seq.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_brk) w_brk.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) exact Mhalt.
    - (* [comment removed for export] *) exact Mlazy.
    - (* [comment removed for export] *) exact Mmat.
    - (* [comment removed for export] *) exact Mfds.
    - (* [comment removed for export] *)
      rewrite Mvm.
      destruct TV as [Vres Vsp Vhas Varea Vlen Vsmall Vseps Vlim].
      constructor; cbn [c_maps c_nmaps c_live cs_T].
      + exact Vres.
      + unfold maps_T. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold smap_ok; cbn [sm_base sm_len sm_exact edenot];
          rewrite ?EV1, ?EV2; rewrite ?u_small by lia.
        * split; [lia|]. split; [lia|]. exact Vhas.
        * split; [lia|]. split; [lia|]. exact Varea.
      + lia.
      + unfold vm_live_bytes. pose proof (live_bytes_bound (vm_maps VM) 4 69632 Vlen Vsmall ltac:(lia)). lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + apply seps_conv. exact Vseps.
      + rewrite Vlim. unfold target_alloc_limit. lia.
      + rewrite Vsp. enorm. reflexivity.
      + rewrite Vsp. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      cbn [c_slots cs_T]. unfold slots_T, slots_ok. apply Forall_cons; [|apply Forall_nil].
      unfold slot_ok. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p split_lit is_lit]. unfold uE. enorm.
      rewrite !u_small by lia.
      split; [exact EP0 | repeat split; try lia].
      (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lazymatch goal with H : gm mod 4096 = 0 |- _ => clear -H; lia end.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
End Entry.

Theorem target_entry_ok :
  forall (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model) (nlo nhi : Z),
    target_pre sp0 gm area brkv mas tid sec cnr content R M ->
    target_vm sp0 gm area VM ->
    m_fds model = fds_std -> m_vmmaps model = VM -> m_halted model = None ->
    m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    nlo <= hdr_paylen content <= nhi ->
    exists e, 0 <= e < 2 ^ 32 /\
      cs_ok (E_T sp0 gm area tid content brkv mas e sec cnr R) (cs_T nlo nhi) R M model.
Proof.
  intros sp0 gm area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn.
  destruct (w_errno _ _ _ _ _ _ _ _ (tp_world _ _ _ _ _ _ _ _ _ _ _ TP)) as (e & He & Ce).
  exists e. split; [exact He|].
  apply (target_entry_ok_e sp0 gm area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn e He Ce).
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbTargetEntry.

Module UbTargetEntryK_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK.
Unset Lia Cache.
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

Definition NX0k : nat := 46%nat.
Definition sr_Tk (k : Z) : list expr :=
  [ELit 0;
   ELit 0x12c5c;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0x314d8;
   EVar 17;
   EVar 18;
   EVar 19;
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EAlu ALU_ADD (EVar 1) (ELit (offk k));
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EVar 26;
   EVar 27;
   EVar 28;
   EVar 29;
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EExt true 0 1 (EVar 7);
   ELit 0x213c9;
   ELit 0;
   EVar 36;
   EVar 37;
   EVar 38;
   EVar 39;
   EVar 40;
   EVar 41;
   EVar 42;
   EVar 43].

Definition kn_Tk0 (k : Z) : list kentry :=
  [KAlign (EVar 0) 16;
   KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x16fe4);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x12ae8);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fff7f7ff000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0x52000 (0x7fffff800000 - nbk k);
   KWr (SA (EVar 1) (0)) (ELit (nbk k));
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x800000000000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x800000000000) (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0x042000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0x042000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 44);
   KWord (SA (EVar 2) (8)) 8 (ELit 0);
   KWord (SA (EVar 2) (16)) 4 (ELit 101);
   KWord (SA (EVar 2) (slotC k 0)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 8)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 16)) 8 (EVar 1);
   KWord (SA (EVar 2) (slotC k 0 + 24)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 28)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 32)) 8 (ELit (Wk k));
   KWord (SA (EVar 2) (slotF k 0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 8)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 16)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 24)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 32)) 8 (ELit 0);
   KZero (SA (EVar 2) (104)) (ELit (4096 - 104));
   KWord (SA (EVar 1) (0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotC k 0)));
   KWord (SA (EVar 1) (8)) 1 (ELit 0);
   KZero (SA (EVar 1) (9)) (ELit 4);
   KWord (SA (EVar 1) (13)) 1 (ELit 224);
   KWord (SA (EVar 1) (14)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k - 4)) 1 (ELit 0);
   KWord (SA (EVar 1) (offk k - 3)) 1 (ELit 160);
   KWord (SA (EVar 1) (offk k - 2)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k + capk k)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 9)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 8)) 4 (ELit (resk k));
   KZero (SA (EVar 1) (nbk k - 4)) (ELit 4);
   KBlob (SA (EVar 1) (offk k)) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 0;
   KWr (SA (ELit 0) 0x21000) (ELit 0x31000);
   KImg 0x0 0x1000;
   KImg 0x10000 0x21380;
   KImg 0x21381 0x213c9;
   KImg 0x313c9 0x31408;
   KImg 0x514e0 0x51500;
   KWord (SA (ELit 0) (201744)) 8 (ELit 0x31410);
   KWord (SA (ELit 0) (201776)) 4 (EVar 3);
   KWord (SA (ELit 0) (201780)) 4 (EVar 11);
   KImg 0x3143c 0x31488;
   KImg 0x31490 0x314a8;
   KImg 0x314b0 0x314c8;
   KImg 0x314d8 0x314e8;
   KImg 0x314f0 0x514e0; KImg 0x51518 0x51744;
   KWord (SA (ELit 0) (333640)) 8 (EVar 45);
   KImg 0x51750 0x51758;
   KImg 0x51769 0x51770;
   KImg 0x51778 0x51780;
   KImg 0x51790 0x51798;
   KWord (SA (ELit 0) (333720)) 8 (ELit 4096);
   KImg 0x517a0 0x517d0;
   KImg 0x517d8 0x517e0;
   KWord (SA (ELit 0) (333792)) 8 (EVar 44);
   KWord (SA (ELit 0) (333800)) 4 (ELit 1);
   KWord (SA (ELit 0) (333804)) 4 (ELit (1 + k));
   KWord (SA (ELit 0) (333808)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (ELit 0) (333816)) 8 (EAlu ALU_ADD (EVar 2) (ELit 104));
   KWord (SA (ELit 0) (333824)) 8 (ELit 99);
   KWord (SA (ELit 0) (333832)) 8 (ELit 0);
   KWord (SA (ELit 0) (333840)) 8 (EVar 10);
   KWord (SA (ELit 0) (333848)) 8 (EVar 2);
   KWord (SA (ELit 0) (333856)) 8 (EVar 2);
   KWord (SA (ELit 0) (333864)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0x51830 0x51990;
   KWord (SA (ELit 0) (334224)) 8 (ELit 0);
   KImg 0x51998 0x519b0;
   KImg 0x519b0 0x51b10;
   KWord (SA (ELit 0) (334608)) 8 (ELit 0);
   KImg 0x51b18 0x51b30;
   KImg 0x51b30 0x51b70;
   KWord (SA (ELit 0) (334704)) 1 (ELit (1 + 2 * k));
   KImg 0x51b71 0x51b78;
   KWord (SA (ELit 0) (334712)) 8 (EVar 9);
   KImg 0x51b88 0x52000;
   KRange (EVar 3) 1 4194303;
   KRange (EVar 10) 0 1;
   KRange (EVar 11) 0 4294967295;
   KRange (EVar 5) 0 32767;
   KRange (EVar 6) 0 255;
   KRange (EVar 7) 0 255;
   KRange (EVar 8) 0 255;
   KRange (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) (capk (k - 1)) (capk k - 1)].

(* [comment removed for export] *)
Definition kn_Tk (k nlo nhi : Z) : list kentry :=
  KRange (EVar 4) nlo nhi :: KRange (EVar 5) 0 (Z.min 32767 (capk k - 7 - nlo)) :: kn_Tk0 k.

(* [comment removed for export] *)
Definition maps_Tk (k : Z) : list smap := [SM (EVar 1) (ELit (nbk k)) true; SM (EVar 2) (ELit 4096) false].

(* [comment removed for export] *)
Definition slots_Tk (k : Z) : list sslot :=
  [SL (EAlu ALU_ADD (EVar 1) (ELit 16)) (ELit (nbk k - 16)) (ELit (capk k)) (ELit (k + 1)) (ELit (Wk k)) 0 (EAlu ALU_ADD (EVar 1) (ELit (offk k)))].

(* [comment removed for export] *)
Definition cs_Tk (k nlo nhi : Z) : cstate := CS (SS 0x12db8 (sr_Tk k) [] (kn_Tk k nlo nhi) NX0k) (maps_Tk k) 9 (nbk k + 2^20 + 8192) (slots_Tk k).
End UbTargetEntryK_defs.

Module UbTargetEntryK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPreK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbTargetEntry UbTargetEntryK_defs.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1. Context {FP : PropExec.FPState}.
Section EntryK.
  Variables (k sp0 gm area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte).
  Variables (VM : VmMaps) (model : Model) (nlo nhi : Z).
  Hypothesis TP : target_pre_k k sp0 gm area brkv mas tid sec cnr content R M.
  Hypothesis TV : target_vm_k k sp0 gm area VM.
  Hypothesis Mfds : m_fds model = fds_std.
  Hypothesis Mvm : m_vmmaps model = VM.
  Hypothesis Mhalt : m_halted model = None.
  Hypothesis Mlazy : m_vm_lazy model = [].
  Hypothesis Mmat : m_vm_materialized model = [].
  Hypothesis Hn : nlo <= hdr_paylen content <= nhi.
  Variable e : Z.
  Hypothesis He : 0 <= e < 2 ^ 32.
  Hypothesis Ce : cell M 0x31434 4 e.

  Let E : env := E_T sp0 gm area tid content brkv mas e sec cnr R.
  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Lemma EV0 : ev E 0 = Z_to_bv 64 sp0. Proof. reflexivity. Qed.
  Lemma EV1 : ev E 1 = Z_to_bv 64 gm. Proof. reflexivity. Qed.
  Lemma EV2 : ev E 2 = Z_to_bv 64 area. Proof. reflexivity. Qed.
  Lemma EV3 : ev E 3 = Z_to_bv 64 tid. Proof. reflexivity. Qed.
  Lemma EV4 : ev E 4 = Z_to_bv 64 (hdr_paylen content). Proof. reflexivity. Qed.
  Lemma EV5 : ev E 5 = Z_to_bv 64 (hdr_cfglen content). Proof. reflexivity. Qed.
  Lemma EV6 : ev E 6 = Z_to_bv 64 (hdr_b0 content). Proof. reflexivity. Qed.
  Lemma EV7 : ev E 7 = Z_to_bv 64 (hdr_b1 content). Proof. reflexivity. Qed.
  Lemma EV8 : ev E 8 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))). Proof. reflexivity. Qed.
  Lemma EV9 : ev E 9 = Z_to_bv 64 brkv. Proof. reflexivity. Qed.
  Lemma EV10 : ev E 10 = Z_to_bv 64 mas. Proof. reflexivity. Qed.
  Lemma EV11 : ev E 11 = Z_to_bv 64 e. Proof. reflexivity. Qed.
  Lemma EVJ : forall i, (i < 32)%nat -> ev E (12 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, E_T. cbn [ev]. unfold vals_T.
    change (12 + i)%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
       Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content); Z_to_bv 64 (hdr_b0 content);
       Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
       Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e : word] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus. rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; lia).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Lemma EV44 : ev E 44 = Z_to_bv 64 sec. Proof. reflexivity. Qed.
  Lemma EV45 : ev E 45 = Z_to_bv 64 cnr. Proof. reflexivity. Qed.
  Lemma EB0 : eb E 0 = content. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma b0_rng : 0 <= hdr_b0 content < 256. Proof. unfold hdr_b0. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b1_rng : 0 <= hdr_b1 content < 256. Proof. unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b2_rng : 0 <= bv_unsigned (nth 2 content (Z_to_bv 8 0)) < 256. Proof. pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma cfglen_rng : 0 <= hdr_cfglen content < 32768.
  Proof. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Ltac enorm :=
    cbn [edenot a_base a_off];
    rewrite ?alu_add, ?EV0, ?EV1, ?EV2, ?EV3, ?EV4, ?EV5, ?EV6, ?EV7, ?EV8, ?EV9, ?EV10, ?EV11, ?EV44, ?EV45;
    rewrite ?vadd_ZZ'.
  Ltac anorm := unfold adenot, estart, elenZ; enorm; unfold slotC, slotF, offk, nbk, resk, Wk in *; rewrite ?v_addi_Z by lia; rewrite ?u_small by lia.

  Ltac klia := unfold slotC, slotF, offk, nbk, resk, Wk in *; lia.
  Ltac kimg Wimg := split; [lia|]; split; [lia|]; apply (img_clear_cover _ _ _ Wimg); vm_compute; reflexivity.
  Ltac karith := anorm; klia.
  Ltac kflat := apply flat_intro; unfold elenZ; enorm; rewrite ?u_small by klia; klia.
  Ltac kwr_stack Hst := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm;
                    replace (sp0 + -8388608 + d) with (sp0 - 8388608 + d) by lia; apply Hst; lia.
  Ltac kwr_def Hdef := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm; rewrite ?Z.add_0_r;
                    lazymatch goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true =>
                      lazymatch type of Hdef with (forall i, _ -> ?MM (Z_to_bv 64 (?base + i)) <> None) =>
                        replace a with (base + (a - base)) by klia end end;
                    apply (store_ok_of_defined _ _ _ Hdef); klia.
  Ltac kwr_data := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by klia; anorm; apply store_ok_data; rewrite u_small by lia; lia.
  (* [comment removed for export] *)
  Ltac kwordC C := split; [cbn; lia|]; split; [kflat|]; anorm; unfold cell in C;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                      lazymatch type of C with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a' with a in C by klia end end;
                    first [ exact C | rewrite C; apply f_equal; apply f_equal; apply f_equal; klia ].
  Ltac kword_abs aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => change (Z_to_bv 64 a) with (Z_to_bv 64 aexp : word) end;
                    first [ exact C | unfold cell in C; rewrite C; first [ reflexivity | apply f_equal; apply f_equal; apply f_equal; klia ] ].
  Ltac kword_rel aexp C := kwordC C.
  Ltac kbyte_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                      lazymatch type of C with _ (Z_to_bv 64 ?a') = Some _ => replace a' with a in C by klia end end;
                    rewrite (rdn1_of_mem _ _ _ C); rewrite w2b1 by lia; reflexivity.
  Ltac kzero aexp C := split; [kflat|]; intros i Hi; revert i Hi; anorm; intros i Hi; unfold zero_bytes in C;
                    lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ =>
                      lazymatch type of C with (forall j, _ -> _ (Z_to_bv 64 (?base + j)) = _) =>
                        replace a with (base + (a - base)) by klia end end;
                    apply C; klia.
  Ltac kblob HTC Hdef := split; [kflat|]; split; [rewrite EB0; anorm; klia|];
                intros i Hi; revert i Hi; anorm; rewrite EB0; intros i Hi;
                lazymatch type of HTC with rdn _ _ (Z_to_bv 64 ?buf) _ = _ =>
                  lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (buf + i) by klia end;
                  apply (rdn_defined_nth _ buf (length content) content HTC); try klia;
                  intros j Hj;
                  lazymatch type of Hdef with (forall i, _ -> ?MM (Z_to_bv 64 (?base + i)) <> None) =>
                    replace (buf + j) with (base + (buf + j - base)) by klia end;
                  apply Hdef; klia end.

  Theorem target_entry_k_ok_e :
    cs_ok E (cs_Tk k nlo nhi) R M model.
  Proof.
    pose proof TP as TP'.
    destruct TP' as [tp_ra tp_sp tp_gp tp_tp tp_a0 tp_a1 tp_a2 tp_a3 tp_s0 tp_s1 tp_s2 tp_s3 tp_s4 tp_s5 tp_s6 tp_s7
                     tp_sp0 tk_top tp_len tk_L tk_stack TF TW tk_content].
    pose proof TW as TW'. destruct TW'.
    lazymatch goal with H : enframe_post _ _ _ _ _ _ |- _ => pose proof H as EP0; destruct H end.
    lazymatch goal with x := gm + 16 + 16 * (k + 1) |- _ => subst x end.
    lazymatch goal with x := gm + 16 + (nbk k - 16) - 4 |- _ => subst x end.
    lazymatch goal with x := nbk k - 16 - 4 - capk k - 16 * (k + 1) |- _ => subst x end.
    lazymatch goal with x := (nbk k - 16) * 0 / 16 + (k + 1) |- _ => subst x end.
    destruct TF as [mf_ra mf_s0 mf_s1 mf_s2 mf_s3 mf_s4 mf_s5 mf_s6 mf_s7].
    pose proof b0_rng as Hb0. pose proof b1_rng as Hb1. pose proof b2_rng as Hb2. pose proof cfglen_rng as Hcl.
    assert (HL : hdr_paylen content + hdr_cfglen content + 6 = L) by (unfold hdr_paylen; subst L; lia).
    pose proof (capk_pos k ltac:(lia)) as Hck. pose proof (capk_le k ltac:(lia)) as Hck2.
    pose proof (capk_pos (k - 1) ltac:(lia)) as Hck1.
    assert (Hm2 : 0 <= k mod 2 <= 1) by (pose proof (Z.mod_pos_bound k 2 ltac:(lia)); lia).
    (* [comment removed for export] *)
    replace (gm + 16 + 16 * (k + 1) - 4) with (gm + (offk k - 4)) in Pm4 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) - 3) with (gm + (offk k - 3)) in Pm3 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) - 2) with (gm + (offk k - 2)) in Pm2 by (unfold offk; lia).
    replace (gm + 16 + 16 * (k + 1) + capk k) with (gm + (offk k + capk k)) in Pzr by (unfold offk; lia).
    replace (gm + 16 + (nbk k - 16) - 4 - 5) with (gm + (nbk k - 9)) in Pe5 by lia.
    replace (gm + 16 + (nbk k - 16) - 4 - 4) with (gm + (nbk k - 8)) in Pe4 by lia.
    replace (gm + 16 - 3) with (gm + 13) in Ps3 by lia.
    replace (gm + 16 - 2) with (gm + 14) in Ps2 by lia.
    replace (nbk k - 16 - 4 - capk k - 16 * (k + 1)) with (resk k) in Pm3, Pzr, Pe5, Pe4, Pr by (unfold resk, nbk; lia).
    replace ((nbk k - 16) * 0 / 16 + (k + 1)) with (k + 1) in Pm2, Pr by (rewrite Z.mul_0_r; reflexivity).
    assert (Hres : 5 <= resk k) by (unfold resk; lia).
    replace (0 + 32 * res_code (resk k)) with 160 in Pm3
      by (unfold res_code; destruct (Z.ltb_spec0 (resk k) 5); lia).
    specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
    specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
    unfold slotC, slotF, offk, nbk, resk, Wk in *.
    constructor.
    - (* [comment removed for export] *)
      intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity. }
      pose proof (ridx_range r) as Hri. rewrite <- (ridx_roundtrip r) at 1.
      cbn [c_ss cs_Tk s_regs].
      generalize (ridx r) Hri. clear r Hr0 Hri. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        [ .. | lia]; rewrite <- nth_all_regs by lia; cbn [nth sr_Tk all_regs];
        lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                  change (edenot E (EVar n)) with (ev E n);
                  first [ rewrite (EVJ (n - 12)) by lia; reflexivity
                        | rewrite ?EV4, ?EV5; first [exact tp_a1 | exact tp_a3 | exact tp_s2 | exact tp_s4 | idtac] ]
              | |- _ => idtac end;
        try (enorm; first [ reflexivity | exact tp_ra | exact tp_gp | exact tp_tp
                          | rewrite tp_sp; f_equal; klia
                          | rewrite tp_a0; f_equal; klia | rewrite tp_s1; f_equal; klia
                          | rewrite tp_s0; f_equal; klia | rewrite tp_s3; f_equal; klia
                          | rewrite tp_s6; f_equal; klia | rewrite tp_s7; f_equal; klia
                          | rewrite tp_a2; f_equal; klia ]).
      (* [comment removed for export] *)
      rewrite tp_s5. cbn [edenot]. rewrite EV7. unfold ext_val, ext_Z. rewrite u_small by lia.
      change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_1_r, (Z.mod_small _ 256) by lia.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus (8 * N.of_nat 1)) with 128. change (bv_modulus (8 * N.of_nat 1)) with 256.
      destruct (Z.ltb_spec0 (hdr_b1 content) 128).
      + rewrite (Z.mod_small (_ + 128) 256) by lia. f_equal. lia.
      + replace ((hdr_b1 content + 128) mod 256) with (hdr_b1 content + 128 - 256) by
          (apply Z.mod_unique with (q := 1); lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply Z.mod_unique with (q := -1); [lia|]. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      cbn [c_ss cs_Tk s_know]. unfold kn_Tk, kn_Tk0, know_ok.
      repeat (apply Forall_cons; [|try apply Forall_nil]).
      all: cbn [kentry_ok].
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *)
        anorm. pose proof (Z.le_min_l 32767 (capk k - 7 - nlo)). pose proof (Z.le_min_r 32767 (capk k - 7 - nlo)).
        pose proof (Z.min_spec 32767 (capk k - 7 - nlo)). lia.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_stack tk_stack.
      + (* [comment removed for export] *) kword_rel (sp0 - 56) mf_ra.
      + (* [comment removed for export] *) kword_rel (sp0 - 64) mf_s0.
      + (* [comment removed for export] *) kword_rel (sp0 - 72) mf_s1.
      + (* [comment removed for export] *) kword_rel (sp0 - 80) mf_s2.
      + (* [comment removed for export] *) kword_rel (sp0 - 88) mf_s3.
      + (* [comment removed for export] *) kword_rel (sp0 - 96) mf_s4.
      + (* [comment removed for export] *) kword_rel (sp0 - 104) mf_s5.
      + (* [comment removed for export] *) kword_rel (sp0 - 112) mf_s6.
      + (* [comment removed for export] *) kword_rel (sp0 - 120) mf_s7.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_def wk_grp_def.
      + (* [comment removed for export] *) kwr_def wk_area_def.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kword_rel area wk_area_chk.
      + (* [comment removed for export] *) kword_rel (area + 8) wk_area_next.
      + (* [comment removed for export] *) kword_rel (area + 16) wk_area_ns.
      + (* [comment removed for export] *) kword_rel (slotC k area) wk_cur_prev.
      + (* [comment removed for export] *) kword_rel (slotC k area + 8) wk_cur_next.
      + (* [comment removed for export] *) kword_rel (slotC k area + 16) wk_cur_mem.
      + (* [comment removed for export] *) kword_rel (slotC k area + 24) wk_cur_avail.
      + (* [comment removed for export] *) kword_rel (slotC k area + 28) wk_cur_freed.
      + (* [comment removed for export] *) kword_rel (slotC k area + 32) wk_cur_W.
      + (* [comment removed for export] *) kword_rel (slotF k area) wk_free_prev.
      + (* [comment removed for export] *) kword_rel (slotF k area + 8) wk_free_next.
      + (* [comment removed for export] *) kword_rel (slotF k area + 16) wk_free_mem.
      + (* [comment removed for export] *) kword_rel (slotF k area + 24) wk_free_msk.
      + (* [comment removed for export] *) kword_rel (slotF k area + 32) wk_free_W.
      + (* [comment removed for export] *) kzero (area + 104) wk_area_rest.
      + (* [comment removed for export] *) kword_rel gm wk_grp_meta.
      + (* [comment removed for export] *) kword_rel (gm + 8) wk_grp_aidx.
      + (* [comment removed for export] *) kzero (gm + 9) wk_grp_pad.
      + (* [comment removed for export] *) kbyte_rel (gm + 13) Ps3.
      + (* [comment removed for export] *) kword_rel (gm + 14) Ps2.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k - 4)) Pm4.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k - 3)) Pm3.
      + (* [comment removed for export] *) kword_rel (gm + (offk k - 2)) Pm2.
      + (* [comment removed for export] *) kbyte_rel (gm + (offk k + capk k)) Pzr.
      + (* [comment removed for export] *) kbyte_rel (gm + (nbk k - 9)) Pe5.
      + (* [comment removed for export] *) kword_rel (gm + (nbk k - 8)) Pe4.
      + (* [comment removed for export] *) kzero (gm + nbk k - 4) wk_grp_tail.
      + (* [comment removed for export] *) kblob tk_content wk_grp_def.
      + (* [comment removed for export] *) kwr_data.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (201744) wk_self.
      + (* [comment removed for export] *) kword_abs (201776) wk_tid.
      + (* [comment removed for export] *) kword_abs (201780) Ce.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + kimg wk_img.
      + (* [comment removed for export] *) kword_abs (333640) wk_canary.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (333720) wk_pagesz.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_secret) wk_secret.
      + (* [comment removed for export] *) kword_abs (ctx_init_done) wk_init.
      + (* [comment removed for export] *) kword_abs (ctx_mmap_counter) wk_ctr.
      + (* [comment removed for export] *) kword_abs (ctx_free_meta_head) wk_fmh.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta) wk_am.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_count) wk_amc.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_area_count) wk_amac.
      + (* [comment removed for export] *) kword_abs (ctx_meta_alloc_shift) wk_mas.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_head) wk_mah.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_tail) wk_mat.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_areas) wk_amas.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_active 44) wk_active44.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_usage 44) wk_usage44.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_seq) wk_seq.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) kword_abs (ctx_brk) wk_brk.
      + (* [comment removed for export] *) kimg wk_img.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) exact Mhalt.
    - (* [comment removed for export] *) exact Mlazy.
    - (* [comment removed for export] *) exact Mmat.
    - (* [comment removed for export] *) exact Mfds.
    - (* [comment removed for export] *)
      rewrite Mvm.
      destruct TV as [Vres Vsp Vlim Vhas Varea Vlen Vsmall Vseps Vlive].
      pose proof (capk_pos k ltac:(lia)) as Hck'. pose proof (capk_le k ltac:(lia)) as Hck2'.
      constructor; cbn [c_maps c_nmaps c_live cs_Tk].
      + exact Vres.
      + unfold maps_Tk. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold smap_ok; cbn [sm_base sm_len sm_exact edenot];
          rewrite ?EV1, ?EV2; rewrite ?u_small by klia.
        * split; [unfold nbk; lia|]. split; [unfold nbk in *; lia|]. exact Vhas.
        * split; [lia|]. split; [lia|]. exact Varea.
      + lia.
      + unfold vm_live_bytes. pose proof Vlive. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + apply seps_conv. exact Vseps.
      + rewrite Vlim. unfold target_alloc_limit. lia.
      + rewrite Vsp. enorm. reflexivity.
      + rewrite Vsp. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      cbn [c_slots cs_Tk]. unfold slots_Tk, slots_ok. apply Forall_cons; [|apply Forall_nil].
      unfold slot_ok. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p split_lit is_lit]. unfold uE. enorm.
      unfold Wk, offk in *. unfold nbk in *. unfold capk in *.
      rewrite !u_small by lia.
      split; [exact EP0 | ].
      assert (HWf : w_maplen (65536 * 2 ^ k + 4096 + 4064) = 16 * 2 ^ k + 1 /\ w_lastidx (65536 * 2 ^ k + 4096 + 4064) = 0
                    /\ w_sizeclass (65536 * 2 ^ k + 4096 + 4064) = 63).
      { unfold w_maplen, w_lastidx, w_sizeclass.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        (* [comment removed for export] *)
        repeat split; (clear - Hck Hck2 wk_k; first [lia | nia]).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      destruct HWf as (Hml & Hli & Hscl).
      rewrite Hml, Hli, Hscl. unfold slot_stride. cbn [negb Z.eqb andb].
      replace (16 * 2 ^ k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. unfold UNIT.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; (clear - Hck Hck2 wk_B_al wk_B_rng wk_k; first [lia | nia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
End EntryK.

Theorem target_entry_k_ok :
  forall (k sp0 B area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model) (nlo nhi : Z),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M ->
    target_vm_k k sp0 B area VM ->
    m_fds model = fds_std -> m_vmmaps model = VM -> m_halted model = None ->
    m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    nlo <= hdr_paylen content <= nhi ->
    exists e, 0 <= e < 2 ^ 32 /\
      cs_ok (E_T sp0 B area tid content brkv mas e sec cnr R) (cs_Tk k nlo nhi) R M model.
Proof.
  intros k sp0 B area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn.
  destruct (wk_errno _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ _ TP)) as (e & He & Ce).
  exists e. split; [exact He|].
  apply (target_entry_k_ok_e k sp0 B area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn e He Ce).
Qed.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbTargetEntryK.

Module UbTargetShape.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Fixpoint nocase (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmit _ _ s' => nocase s'
  | SAlt2 a b => nocase a && nocase b
  | SCase _ _ _ _ => false
  end.

Lemma t_eq_emit : forall evs T T', t_eq T T' -> t_eq (t_emit evs T) (t_emit evs T').
Proof.
  intros evs T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.

Lemma t_eq_alt2 : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
  intros A A' B B' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctest : Type := (expr * Z * bool)%type.

Fixpoint stest (tests : list ctest) (e : expr) (mid : Z) : option bool :=
  match tests with
  | [] => None
  | (e', mid', b) :: rest => if (expr_eqb e e' && Z.eqb mid mid')%bool then Some b else stest rest e mid
  end.

Fixpoint sresolve (tests : list ctest) (s : shape) : option shape :=
  match s with
  | SNil => Some SNil
  | SExit c => Some (SExit c)
  | SEmit fd bs s' => match sresolve tests s' with Some s'' => Some (SEmit fd bs s'') | None => None end
  | SAlt2 a b =>
      match sresolve tests a, sresolve tests b with
      | Some a', Some b' => Some (SAlt2 a' b')
      | _, _ => None
      end
  | SCase e mid s1 s2 =>
      match stest tests e mid with
      | Some true => sresolve tests s1
      | Some false => sresolve tests s2
      | None => None
      end
  end.

Definition ctest_ok (E : env) (t : ctest) : Prop :=
  let '(e, mid, b) := t in Z.leb (bv_unsigned (edenot E e)) mid = b.

Lemma stest_sound : forall E tests e mid b,
  Forall (ctest_ok E) tests -> stest tests e mid = Some b ->
  Z.leb (bv_unsigned (edenot E e)) mid = b.
Proof.
  intros E tests e mid b HT. induction HT as [|[[e' mid'] b'] rest Ht HT IH]; cbn [stest]; intros H; [discriminate|].
  destruct (expr_eqb e e' && (mid =? mid'))%bool eqn:Eq.
  - apply andb_prop in Eq as [E1 E2]. apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. subst e' mid'.
    injection H as <-. exact Ht.
  - apply IH. exact H.
Qed.

Theorem sresolve_sound : forall E fs tests s s',
  Forall (ctest_ok E) tests -> sresolve tests s = Some s' ->
  t_eq (sd E fs s) (sd E fs s').
Proof.
  intros E fs tests s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros s' HT H; cbn [sresolve] in H.
  - injection H as <-. apply t_eq_refl.
  - injection H as <-. apply t_eq_refl.
  - destruct (sresolve tests s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [sd].
    apply t_eq_emit. apply IH; [exact HT | reflexivity].
  - destruct (sresolve tests a) as [a'|] eqn:Ha; [|discriminate].
    destruct (sresolve tests b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [sd].
    apply t_eq_alt2; [apply IHa | apply IHb]; first [exact HT | reflexivity].
  - destruct (stest tests e mid) as [tb|] eqn:Ht; [|discriminate].
    pose proof (stest_sound E tests e mid tb HT Ht) as Hv. cbn [sd]. rewrite Hv.
    destruct tb; [apply IH1 | apply IH2]; assumption.
Qed.

Lemma sresolve_nocase : forall tests s s', sresolve tests s = Some s' -> nocase s' = true.
Proof.
  intros tests s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros s' H; cbn [sresolve] in H.
  - injection H as <-. reflexivity.
  - injection H as <-. reflexivity.
  - destruct (sresolve tests s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [nocase]. apply IH. reflexivity.
  - destruct (sresolve tests a) as [a'|] eqn:Ha; [|discriminate].
    destruct (sresolve tests b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [nocase].
    rewrite (IHa a' eq_refl), (IHb b' eq_refl). reflexivity.
  - destruct (stest tests e mid) as [[|]|]; [apply IH1 | apply IH2 | discriminate]; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sev : Type := SW (fd b : Z) | SX (code : Z).

Definition sev_eqb (x y : sev) : bool :=
  match x, y with
  | SW f a, SW g b => Z.eqb f g && Z.eqb a b
  | SX c, SX d => Z.eqb c d
  | _, _ => false
  end.

Lemma sev_eqb_eq : forall x y, sev_eqb x y = true -> x = y.
Proof.
  intros [f a|c] [g b|d] H; cbn in H; try discriminate.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint paths (s : shape) : list (list sev) :=
  match s with
  | SNil => [[]]
  | SExit c => [[SX c]]
  | SEmit fd bs s' => map (fun p => map (SW fd) bs ++ p) (paths s')
  | SAlt2 a b => paths a ++ paths b
  | SCase _ _ a b => paths a ++ paths b
  end.

Fixpoint prefixb (p q : list sev) : bool :=
  match p, q with
  | [], _ => true
  | _ :: _, [] => false
  | x :: p', y :: q' => sev_eqb x y && prefixb p' q'
  end.

Definition sub_paths (P Q : list (list sev)) : bool :=
  forallb (fun p => existsb (fun q => prefixb p q) Q) P.

Definition shape_equiv (s1 s2 : shape) : bool :=
  sub_paths (paths s1) (paths s2) && sub_paths (paths s2) (paths s1).

Definition sev_ev (fs : Fs.Fs) (v : sev) : event :=
  match v with
  | SW fd b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)
  | SX c => ExitEv (Z_to_bv 64 c) fs
  end.
Definition events (fs : Fs.Fs) (p : list sev) : list event := map (sev_ev fs) p.

Lemma paths_ne : forall s, paths s <> [].
Proof.
  induction s; cbn [paths]; try discriminate.
  - destruct (paths s); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
Qed.

Lemma Wz_events : forall fs fd bs, Wz fd bs = events fs (map (SW fd) bs).
Proof. intros fs fd bs. unfold Wz, events. rewrite map_map. reflexivity. Qed.

Lemma is_prefix_app_l {A} : forall (l a b : list A), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]]. Qed.

(* [comment removed for export] *)
Theorem sd_paths : forall E fs s, nocase s = true ->
  forall tr, sd E fs s tr <-> exists p, In p (paths s) /\ is_prefix tr (events fs p).
Proof.
  intros E fs s. induction s as [|c|fd bs s IH|a IHa b IHb|e mid s1 IH1 s2 IH2]; intros Hnc tr; cbn [nocase] in Hnc; try discriminate; cbn [sd paths].
  - unfold t_nil. split.
    + intros ->. exists []. split; [left; reflexivity | exact I].
    + intros (p & [<-|[]] & Hp). apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_exit, t_emit, t_nil. split.
    + intros [Hp | (tr' & -> & ->)]; exists [SX c]; (split; [left; reflexivity|]); [exact Hp | cbn; auto].
    + intros (p & [<-|[]] & Hp). left. exact Hp.
  - specialize (IH Hnc). unfold t_emit. rewrite (Wz_events fs). split.
    + intros [Hp | (tr' & -> & HT)].
      * destruct (paths s) as [|p0 P] eqn:EP; [exfalso; exact (paths_ne s EP)|].
        exists (map (SW fd) bs ++ p0). split; [apply in_map; left; reflexivity|].
        unfold events in *. rewrite map_app. apply is_prefix_app_r. exact Hp.
      * apply IH in HT as (p & Hin & Hp). exists (map (SW fd) bs ++ p). split; [apply in_map; exact Hin|].
        unfold events in *. rewrite map_app. apply is_prefix_app_l. exact Hp.
    + intros (q & Hin & Hq). apply in_map_iff in Hin as (p & <- & Hin).
      unfold events in Hq. rewrite map_app in Hq. apply is_prefix_app_split in Hq as [Hq | (b' & -> & Hq)].
      * left. exact Hq.
      * right. exists b'. split; [reflexivity|]. apply IH. exists p. split; [exact Hin | exact Hq].
  - apply andb_prop in Hnc as [Ha Hb]. specialize (IHa Ha). specialize (IHb Hb). unfold t_alt2. split.
    + intros [H|H]; [apply IHa in H | apply IHb in H]; destruct H as (p & Hin & Hp); exists p; split;
        [apply in_app_iff; left; exact Hin | exact Hp | apply in_app_iff; right; exact Hin | exact Hp].
    + intros (p & Hin & Hp). apply in_app_iff in Hin as [Hin|Hin]; [left; apply IHa | right; apply IHb]; exists p; split; assumption.
Qed.

Lemma prefixb_sound : forall fs p q, prefixb p q = true -> is_prefix (events fs p) (events fs q).
Proof.
  intros fs p. induction p as [|x p IH]; intros q H; cbn [prefixb] in H.
  - apply is_prefix_nil.
  - destruct q as [|y q]; [discriminate|]. apply andb_prop in H as [H1 H2]. apply sev_eqb_eq in H1. subst y.
    cbn. split; [reflexivity | apply IH; exact H2].
Qed.

Lemma sub_paths_sound : forall E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  sub_paths (paths s1) (paths s2) = true -> forall tr, sd E fs s1 tr -> sd E fs s2 tr.
Proof.
  intros E fs s1 s2 H1 H2 HS tr Htr.
  apply (sd_paths E fs s1 H1) in Htr as (p & Hin & Hp).
  unfold sub_paths in HS. rewrite forallb_forall in HS. specialize (HS p Hin).
  apply existsb_exists in HS as (q & Hq & Hpq).
  apply (sd_paths E fs s2 H2). exists q. split; [exact Hq|].
  eapply is_prefix_trans; [exact Hp | apply prefixb_sound; exact Hpq].
Qed.

Theorem shape_equiv_sound : forall E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  shape_equiv s1 s2 = true -> t_eq (sd E fs s1) (sd E fs s2).
Proof.
  intros E fs s1 s2 H1 H2 HE tr. unfold shape_equiv in HE. apply andb_prop in HE as [HA HB].
  split; apply sub_paths_sound; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition starget (calls : nat) (npos cm : bool) : shape :=
  SEmit 1 (concat (repeat [48; 10] calls)) (SExit 0).

Lemma starget_nocase : forall calls npos cm, nocase (starget calls npos cm) = true.
Proof. intros calls npos cm; reflexivity. Qed.

Lemma Wz_zero_lines : forall calls, Wz 1 (concat (repeat [48; 10] calls)) = W 1 (zero_lines calls).
Proof.
  induction calls as [|c IH]; [reflexivity|]. cbn [repeat concat zero_lines app]. unfold Wz, W in *. cbn [map]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition calls_of (content : list byte) : nat :=
  if (hdr_cfglen content =? 0)%Z then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4)).
Definition npos_of (content : list byte) : bool := (0 <? hdr_paylen content)%Z.
Definition cm_of (content : list byte) : bool := (128 <=? hdr_b1 content)%Z.

Lemma counting_cm : forall content, (32768 <=? hdr_cfg content)%Z = cm_of content.
Proof.
  intros content. unfold cm_of, hdr_cfg, hdr_b0, hdr_b1.
  pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
  change (bv_modulus 8) with 256%Z in B0, B1.
  destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0))));
    [apply Z.leb_le | apply Z.leb_gt]; lia.
Qed.

Theorem starget_sound : forall E fs content,
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  t_eq (sd E fs (starget (calls_of content) (npos_of content) (cm_of content))) (t_target content fs).
Proof.
  intros E fs content Hlen.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  unfold t_target. fold (hdr_cfglen content).
  assert (EC : match Z.to_nat (hdr_cfglen content) with
               | 0%nat => 1%nat
               | S _ => S (Z.to_nat (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4))
               end = calls_of content).
  { unfold calls_of. destruct (Z.eqb_spec (hdr_cfglen content) 0) as [E0|E0].
    - rewrite E0. reflexivity.
    - destruct (Z.to_nat (hdr_cfglen content)) eqn:En; [lia | reflexivity]. }
  rewrite EC. unfold starget. cbn [sd]. rewrite Wz_zero_lines. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

Lemma XC_denot : forall E content,
  eb E 0 = content -> (2 < length content)%nat ->
  bv_unsigned (edenot E XC) = (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4)%Z.
Proof.
  intros E content Hb Hlen. unfold XC. cbn [edenot]. rewrite Hb.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  assert (BV : blob_val false content 2 1 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))).
  { unfold blob_val, blob_bytes. f_equal.
    destruct content as [|c0 [|c1 [|c2 rest]]]; cbn [length] in Hlen; try lia.
    change (Z.to_nat 2) with 2%nat. cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l. apply Z.lor_0_r. }
  rewrite BV. rewrite alu_and. unfold v_and. rewrite (u_small (bv_unsigned (nth 2 content (Z_to_bv 8 0)))) by lia.
  change (bv_unsigned (Z_to_bv 64 3)) with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)). rewrite u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition tests_of (cfg0 : bool) (c : Z) (cm : bool) : list ctest :=
  [(EVar 5, 0, cfg0); (XC, 0, (c - 1 <=? 0)%Z); (XC, 1, (c - 1 <=? 1)%Z); (XC, 2, (c - 1 <=? 2)%Z);
   (EVar 7, 127, negb cm)].

Definition variant_ok (npos : bool) (s : shape) (cfg0 : bool) (c : Z) (cm : bool) : bool :=
  match sresolve (tests_of cfg0 c cm) s with
  | Some s' => shape_equiv s' (starget (if cfg0 then 1%nat else Z.to_nat c) npos cm)
  | None => false
  end.

(* [comment removed for export] *)
Definition class_shape_ok (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun cfg0 => forallb (fun c => variant_ok npos s cfg0 c cm) [1; 2; 3; 4]%Z)
                             [true; false]) [true; false].

(* [comment removed for export] *)
Theorem class_shape_sound : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  class_shape_ok (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB Hlen HC.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (cfg0 := (hdr_cfglen content =? 0)%Z). set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  (* [comment removed for export] *)
  assert (V : variant_ok (npos_of content) s cfg0 c cm = true).
  { unfold class_shape_ok in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    specialize (HC cfg0 ltac:(destruct cfg0; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of cfg0 c cm) s) as [s'|] eqn:Hs; [|discriminate].
  (* [comment removed for export] *)
  assert (TT : Forall (ctest_ok E) (tests_of cfg0 c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite u_small by lia. unfold cfg0. destruct (Z.eqb_spec (hdr_cfglen content) 0); [apply Z.leb_le | apply Z.leb_gt]; lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace (if cfg0 then 1%nat else Z.to_nat c) with (calls_of content).
  - apply starget_sound. exact Hlen.
  - unfold calls_of, cfg0, c. destruct (hdr_cfglen content =? 0)%Z; [reflexivity|].
    rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbTargetShape.

Module UbTargetShapeTop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbTargetShape.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition class_shape_ok0 (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun c => variant_ok npos s true c cm) [1; 2; 3; 4]%Z) [true; false].

Theorem class_shape_sound0 : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  hdr_cfglen content = 0 ->
  (6 <= Z.of_nat (length content))%Z ->
  class_shape_ok0 (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB C0 Hlen HC.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  assert (V : variant_ok (npos_of content) s true c cm = true).
  { unfold class_shape_ok0 in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of true c cm) s) as [s'|] eqn:Hs; [|discriminate].
  assert (TT : Forall (ctest_ok E) (tests_of true c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite C0. reflexivity.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace 1%nat with (calls_of content) by (unfold calls_of; rewrite C0; reflexivity).
  apply starget_sound. lia.
Qed.

(* [comment removed for export] *)
Definition class_shape_ok1 (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun c => variant_ok npos s false c cm) [1; 2; 3; 4]%Z) [true; false].

Theorem class_shape_sound1 : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  (1 <= hdr_cfglen content)%Z ->
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  class_shape_ok1 (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB C1 Hlen HC.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  assert (V : variant_ok (npos_of content) s false c cm = true).
  { unfold class_shape_ok1 in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of false c cm) s) as [s'|] eqn:Hs; [|discriminate].
  assert (TT : Forall (ctest_ok E) (tests_of false c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite u_small by lia. apply Z.leb_gt. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace (Z.to_nat c) with (calls_of content).
  - apply starget_sound. exact Hlen.
  - unfold calls_of, c. destruct (Z.eqb_spec (hdr_cfglen content) 0); [lia|]. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbTargetShapeTop.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExec.

Module UbSymPlanSoundH.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase UbLibCas UbLibCas2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbFreePro.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Lemma kread8e_rdn : forall E M k b off v,
  know_ok RSEGS E M k -> kread8e RSEGS k b off = Some v -> flat E (SA b off) 8 ->
  rdn RSEGS M (adenot E (SA b off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k b off v HK H Hfl. apply (kread_rdn RSEGS E M k b off 8 v HK); [exact H | lia | lia | exact Hfl].
Qed.

Lemma times16_denot : forall E e, edenot E (times16 e) = Z_to_bv 64 (16 * bv_unsigned (edenot E e)).
Proof.
  intros E e. unfold times16. rewrite mkMd_denot. apply bv_eq. rewrite u_mul64. cbn [edenot].
  rewrite (u64_lit 16) by lia. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity.
Qed.

Lemma flat_sub : forall E b k n k' n', flat E (SA b k) n -> k <= k' -> 0 < n' -> k' + n' <= k + n -> flat E (SA b k') n'.
Proof. intros E b k n k' n' (F1 & F2 & F3 & F4) H1 H2 H3. unfold flat, estart in *. cbn [a_base a_off] in *. lia. Qed.

Lemma adenot_Z : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. reflexivity. Qed.

Lemma wle_low4 : forall z, word_to_le_bytes 4 (Z_to_bv 64 z) = word_to_le_bytes 4 (Z_to_bv 64 (z mod 2 ^ 32)).
Proof.
  intros z. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z_to_le_bytes_mod 4 (z mod 2 ^ 64)), <- (Z_to_le_bytes_mod 4 ((z mod 2 ^ 32) mod 2 ^ 64)).
  f_equal. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  assert (D : (2 ^ 32 | 2 ^ 64)) by (exists (2 ^ 32); reflexivity).
  rewrite (Z.mod_mod_divide z (2 ^ 64) (2 ^ 32)) by exact D.
  rewrite (Z.mod_mod_divide (z mod 2 ^ 32) (2 ^ 64) (2 ^ 32)) by exact D.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.



(* [comment removed for export] *)
Fixpoint sr_upds (sr : list expr) (ovr : list (nat * expr)) : list expr :=
  match ovr with [] => sr | (i, e) :: r => sr_upds (sr_upd sr i e) r end.

Lemma nth_sr_upds_out : forall ovr sr i, ~ In i (map fst ovr) -> nth i (sr_upds sr ovr) (ELit 0) = nth i sr (ELit 0).
Proof.
  induction ovr as [|[j e] r IH]; intros sr i Hn; cbn [sr_upds]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i j) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_upds_in : forall ovr sr i e, List.NoDup (map fst ovr) -> In (i, e) ovr -> nth i (sr_upds sr ovr) (ELit 0) = e.
Proof.
  induction ovr as [|[j e'] r IH]; intros sr i e Hnd Hin; [destruct Hin|].
  cbn [map fst] in Hnd. inversion Hnd as [|j' r' Hnotin Hnd']; subst.
  cbn [sr_upds]. destruct Hin as [Hin|Hin].
  - injection Hin as -> ->. rewrite nth_sr_upds_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. reflexivity.
  - apply IH; assumption.
Qed.

Lemma regs_after_ovr : forall E sr R R' nx (ovr : list (nat * expr)),
  regs_ok E sr R -> SP.sr_vars_lt nx sr = true ->
  List.NoDup (map fst ovr) ->
  (forall io, In io ovr -> SP.expr_vars_lt nx (snd io) = true /\ getr R' (Z_to_bv 5 (Z.of_nat (fst io))) = edenot E (snd io)) ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> ~ In (ridx r) (map fst ovr) -> getr R' r = getr R r) ->
  regs_ok (ext_call E nx R') (sr_upds (sr_fresh sr caller_saved nx) ovr) R'.
Proof.
  intros E sr R R' nx ovr HR Hsv Hnd Hovr Hkept.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq. clear -Hsv Hi. revert i Hi. induction sr as [|e t IH]; intros i Hi; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; [exact H2 | lia]]. }
  apply regs_ok_pointwise. intros r Hr0. pose proof (ridx_range r) as Hrr.
  destruct (in_dec Nat.eq_dec (ridx r) (map fst ovr)) as [Hin|Hnin].
  - apply in_map_iff in Hin as ([i e] & Hi & Hin). cbn [fst] in Hi. subst i.
    rewrite (nth_sr_upds_in ovr _ (ridx r) e Hnd Hin).
    destruct (Hovr _ Hin) as [Hv Hg]. cbn [fst snd] in Hv, Hg.
    rewrite <- (reg_of_ridx r _ eq_refl) in Hg. rewrite Hg. apply (edenot_agree nx); [exact Hag | rewrite <- expr_vars_lt_eq; exact Hv].
  - rewrite nth_sr_upds_out by exact Hnin.
    destruct (in_dec Nat.eq_dec (ridx r) caller_saved) as [Hcs|Hncs].
    + destruct (In_nth caller_saved (ridx r) 0%nat Hcs) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    + rewrite nth_sr_fresh_out by exact Hncs. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hncs Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X.
Qed.

(* [comment removed for export] *)
Lemma flat_abs : forall E k n, 0 <= k -> 0 <= n -> k + n < 2 ^ 64 -> flat E (SA (ELit 0) k) n.
Proof.
  intros E k n Hk Hn Hkn. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
Qed.

Lemma testbit_mod32 : forall a i, 0 <= i < 32 -> Z.testbit (a mod 2 ^ 32) i = Z.testbit a i.
Proof. intros a i Hi. apply Z.mod_pow2_bits_low. lia. Qed.


(* [comment removed for export] *)
Lemma decode_W_sound : forall E We Se c,
  decode_W We = Some (Se, c) ->
  (4096 * bv_unsigned (edenot E Se) + c < 2 ^ 64)%Z ->
  bv_unsigned (edenot E We) = (4096 * bv_unsigned (edenot E Se) + c)%Z /\ (0 <= c < 4096)%Z.
Proof.
  intros E We Se c H Hb. unfold decode_W in H.
  destruct We as [w|v|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try discriminate.
  - (* [comment removed for export] *) injection H as <- <-. cbn [edenot]. rewrite !u_lit64.
    pose proof (Z.mod_pos_bound w two64 ltac:(unfold two64; lia)) as Hw. unfold two64 in *.
    pose proof (Z.div_mod (w mod 2 ^ 64) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (w mod 2 ^ 64) 4096 ltac:(lia)).
    pose proof (Z.div_pos (w mod 2 ^ 64) 4096 ltac:(lia) ltac:(lia)).
    rewrite (Z.mod_small ((w mod 2 ^ 64) / 4096)) by nia. lia.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct a as [| | | |mo ma mb| | |]; try discriminate.
    destruct mo; try discriminate. destruct ma as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    split; [|lia]. cbn [edenot]. rewrite alu_add, m_mul. unfold v_add, v_mul. rewrite !u_lit64. unfold two64.
    pose proof (u64_range (edenot E mb)).
    rewrite (Z.mod_small (4096 * _)) by lia. rewrite (Z.mod_small c') by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    injection H as <- <-. split; [|lia]. cbn [edenot]. rewrite m_mul. unfold v_mul. rewrite !u_lit64. unfold two64.
    pose proof (u64_range (edenot E b)). rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

Lemma decode_W_range : forall We Se c, decode_W We = Some (Se, c) -> (0 <= c < 4096)%Z.
Proof.
  intros We Se c H. unfold decode_W in H.
  destruct We as [w|v|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try discriminate.
  - injection H as <- <-. pose proof (Z.mod_pos_bound (w mod two64) 4096 ltac:(lia)). lia.
  - destruct op; try discriminate. destruct a as [| | | |mo ma mb| | |]; try discriminate.
    destruct mo; try discriminate. destruct ma as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    injection H as <- <-. lia.
Qed.

Lemma W_fields : forall m c, (0 <= m)%Z -> (0 <= c < 4096)%Z ->
  w_maplen (4096 * m + c) = m /\ w_lastidx (4096 * m + c) = (c mod 32)%Z /\ w_sizeclass (4096 * m + c) = ((c / 64) mod 64)%Z.
Proof.
  intros m c Hm Hc. unfold w_maplen, w_lastidx, w_sizeclass.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End NX0.
End UbSymPlanSoundH.

Module UbSymPlanSoundFP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase UbLibCas UbLibCas2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbFreePro.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Hypothesis nx0_pos : (0 < nx0)%nat.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma slots_vars_lt_carry : forall b k log ss, slots_vars_lt b ss = true -> slots_vars_lt b (slots_carry k log ss) = true.
Proof.
  intros b k log ss H. rewrite slots_carry_eq. (* [comment removed for export] *)
  induction log as [|[[bb o] w v] older IH]; cbn [slots_carry_ref]; [exact H|].
  apply slots_vars_lt_keep. exact IH.
Qed.

(* [comment removed for export] *)
Lemma call_freepro_sound' {FP : FPState} : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_freepro INFOUB -> call_freepro RSEGS INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_freepro in Hn.
  destruct (find_slot (kn cs) (reg cs 10) (c_slots cs)) as [s|] eqn:Hfind; [|discriminate].
  cbv zeta in Hn.
  set (strd := sl_stride s) in Hn. set (idx := sl_idx s) in Hn.
  set (sidx := match strd with ELit z => Some ((z mod two64) * idx)%Z | _ => if idx =? 0 then Some 0%Z else None end) in Hn.
  destruct (decode_W (sl_W s)) as [[Se c]|] eqn:HdW; [|discriminate].
  destruct (xlo (kn cs) strd) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xhi (kn cs) strd) as [shi|] eqn:Hshi; [|discriminate].
  destruct sidx as [si|] eqn:Hsidx; [|discriminate].
  cbv zeta in Hn.
  set (Me := mkAlu ALU_ADD (sl_start s) (ELit (- (16 + si)))) in Hn.
  destruct (split_lit Me) as [mb mk] eqn:Hsme.
  destruct (kread8e RSEGS (kn cs) mb mk) as [ge|] eqn:Hge; [|discriminate].
  destruct (split_lit ge) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me'|] eqn:HMe'; [|discriminate].
  destruct (kread8e RSEGS (kn cs) gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 24) 4) as [avail|] eqn:Hav; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 28) 4) as [freed|] eqn:Hfr; [|discriminate].
  destruct (lin_lowbits_kn (kn cs) ge 12) as [gm12|] eqn:Hlow; [|discriminate].
  set (area := mkAlu ALU_ADD ge (ELit (- gm12))) in Hn.
  destruct (split_lit area) as [ab ak] eqn:Hsa.
  destruct (split_lit (sl_start s)) as [hb hk] eqn:Hsh.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-48))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  set (eexp := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-4)))) in Hn.
  destruct (split_lit eexp) as [eb ek] eqn:Hsee.
  destruct (kread8e RSEGS (kn cs) ab ak) as [se|] eqn:Hse; [|discriminate].
  change (d_malloc_ctx INFOUB) with 0x517e0%Z in Hn.
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0x517e0) as [se'|] eqn:Hse'; [|discriminate].
  destruct (xlo (kn cs) (sl_off s)) as [olo|] eqn:Holo; [|discriminate].
  destruct (xhi (kn cs) (sl_off s)) as [ohi|] eqn:Hohi; [|discriminate].
  destruct (ehi (kn cs) ge) as [ghi|] eqn:Hghi; [|discriminate].
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) hb) as [hh|] eqn:Hhh; [|discriminate].
  destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
  destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
  set (reserved := mkAlu ALU_SUB (mkAlu ALU_ADD strd (ELit (-4))) (mkAlu ALU_ADD (sl_n s) (times16 (sl_off s)))) in Hn.
  set (e12 := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-16)))) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (log := [SE (SA qb (qk + 8)) 8 (reg cs 19); SE (SA qb (qk + 16)) 8 (reg cs 18);
               SE (SA qb (qk + 24)) 8 (reg cs 9); SE (SA qb (qk + 32)) 8 (reg cs 8);
               SE (SA qb (qk + 40)) 8 (reg cs 1)]) in Hn.
  destruct (carry log (kn cs) []) as [[kn' scs] hs] eqn:Hcar.
  destruct scs; [|discriminate].
  destruct (kn_vars_lt (s_next (c_ss cs)) kn') eqn:Hkv; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvars]. apply andb_prop in Hcond as [Hcond Hs3]. apply andb_prop in Hcond as [Hcond Hs2].
  apply andb_prop in Hcond as [Hcond Hs1]. apply andb_prop in Hcond as [Hcond Hstk]. apply andb_prop in Hcond as [Hcond Himg].
  apply andb_prop in Hcond as [Hcond Hflh]. apply andb_prop in Hcond as [Hcond Hrwe]. apply andb_prop in Hcond as [Hcond Hend].
  apply andb_prop in Hcond as [Hcond Hfla]. apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hflm].
  apply andb_prop in Hcond as [Hcond Hsec]. apply andb_prop in Hcond as [Hcond Hfrb]. apply andb_prop in Hcond as [Hcond Havb].
  apply andb_prop in Hcond as [Hcond Holo0]. apply andb_prop in Hcond as [Hcond Hml]. apply andb_prop in Hcond as [Hcond Hsc].
  apply andb_prop in Hcond as [Hcond Hli]. apply andb_prop in Hcond as [Hcond Hidx0]. apply andb_prop in Hcond as [Hcond HShi40].
  apply andb_prop in Hcond as [HMe Hw]. apply Z.leb_le in HShi40.
  rename Hli into Hidxl. apply Z.leb_le in Hidx0. apply Z.leb_le in Hidxl.
  apply Z.leb_le in Holo0.
  apply negb_true_iff in Havb. apply negb_true_iff in Hfrb.
  apply expr_eqb_eq in Hsec. subst se'.
  apply Z.leb_le in Hs3.
  apply expr_eqb_eq in Hw.
  (* [comment removed for export] *)
  apply find_some in Hfind as [Hsin Hsp].
  pose proof (proj1 (Forall_forall _ _) HSL s Hsin) as HS.
  unfold slot_ok in HS. rewrite Hsh in HS. fold strd idx in HS.
  destruct (split_lit (sl_p s)) as [pb pk] eqn:Hspp.
  destruct HS as (P & Hp & Hh & Hpp & Hsd & Hsc48 & Hsd2 & Hmod & Hmod2 & Hlo & Hnw & Hidx32 & Hq).
  unfold uE in P, Hp, Hh, Hpp, Hsd, Hsc48, Hsd2, Hmod, Hmod2, Hlo, Hnw, Hidx32, Hq.
  set (st := bv_unsigned (edenot E (sl_start s))) in *.
  set (nn := bv_unsigned (edenot E (sl_n s))) in *.
  set (o := bv_unsigned (edenot E (sl_off s))) in *.
  set (stride := bv_unsigned (edenot E strd)) in *.
  set (W := bv_unsigned (edenot E (sl_W s))) in *.
  pose proof (u64_range (edenot E (sl_n s))) as Hnnr. fold nn in Hnnr.
  pose proof (u64_range (edenot E (sl_off s))) as Hor. fold o in Hor.
  pose proof (u64_range (edenot E strd)) as Hstr_r. fold stride in Hstr_r.
  pose proof (u64_range (edenot E (sl_W s))) as HW_r. fold W in HW_r.
  pose proof (xlo_sound RSEGS E M (kn cs) strd slo HKN Hslo) as Hslo'. fold stride in Hslo'.
  pose proof (xhi_sound RSEGS E M (kn cs) strd shi HKN Hshi) as Hshi'. fold stride in Hshi'.
  pose proof (xlo_sound RSEGS E M (kn cs) Se Slo HKN HSlo) as HSlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) Se Shi HKN HShi) as HShi'.
  pose proof (u64_range (edenot E Se)) as HSer.
  pose proof (decode_W_range _ _ _ HdW) as Hc.
  destruct (decode_W_sound E (sl_W s) Se c HdW ltac:(lia)) as [HWdec _]. fold W in HWdec.
  destruct (W_fields (bv_unsigned (edenot E Se)) c ltac:(lia) Hc) as (Fml & Fli & Fsc). rewrite <- HWdec in Fml, Fli, Fsc.
  assert (Hsi : si = (stride * idx)%Z).
  { subst sidx. destruct strd as [z| | | | | | |];
      first [ injection Hsidx as <-; subst stride; cbn [edenot]; rewrite u_lit64; reflexivity
            | destruct (idx =? 0) eqn:Hi0; [|discriminate]; injection Hsidx as <-; apply Z.eqb_eq in Hi0; rewrite Hi0; lia ]. }
  subst si.
  pose proof P as P'. destruct P' as [pp pe pr pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. subst pp pe pr pq.
  (* [comment removed for export] *)
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  assert (Epa : edenot E (reg cs 10) = Z_to_bv 64 (st + 16 * o)).
  { assert (Ep : edenot E (sl_p s) = edenot E (reg cs 10)).
    { destruct (expr_eqb (sl_p s) (reg cs 10)) eqn:Heq.
      - apply expr_eqb_eq in Heq. rewrite Heq. reflexivity.
      - exact (len_eqb_sound E M (kn cs) _ _ HKN Hsp). }
    rewrite <- Ep, <- Hp. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Epa in R10.
  (* [comment removed for export] *)
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  set (spv := bv_unsigned (edenot E (reg cs 2))) in *.
  pose proof (elo_sound E M (kn cs) (reg cs 2) splo HKN Hsplo) as Hsplo'. fold spv in Hsplo'.
  pose proof (u64_range (edenot E (reg cs 2))) as Hspr. fold spv in Hspr.
  assert (R2' : getr R (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 spv) by (rewrite R2; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (rw_okb_sound E M (kn cs) qb qk 48 HKN Hstk ltac:(lia)) as (Qst & Qdef & Qimg & Q0 & Qnw).
  assert (Hspm : edenot E spm = Z_to_bv 64 (spv - 48)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold spv. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hq1. rewrite Hspm in Hq1.
  apply (f_equal bv_unsigned) in Hq1. rewrite !u64_lit in Hq1 by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  pose proof (split_lit_denot E ge gb gk Hsg) as Hgd.
  set (g := (bv_unsigned (edenot E gb) + gk)%Z) in *.
  assert (Fg' : (0 <= g)%Z /\ (g + 40 <= 2 ^ 64)%Z) by (destruct Fg as (F1 & F2 & F3 & F4); unfold estart in *; cbn [a_base a_off] in *; lia).
  assert (Hug : bv_unsigned (edenot E ge) = g) by (rewrite Hgd, u64_lit by lia; reflexivity).
  pose proof (ehi_sound E M (kn cs) ge ghi HKN Hghi) as Hghi'. rewrite Hug in Hghi'.
  (* [comment removed for export] *)
  assert (Hsp0 : (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)) <= 0x800000000000)%Z).
  { pose proof (co_vm _ _ _ _ _ HC) as HV. rewrite <- (vo_sp _ _ _ _ _ HV). exact (vo_sprange _ _ _ _ _ HV). }
  assert (Hg88 : (g + 88 <= spv)%Z).
  { destruct (ghi + 88 <=? splo) eqn:Hnum.
    - apply Z.leb_le in Hnum. lia.
    - apply andb_prop in Hs2 as [Hbb Hfr2].
      pose proof (below_band_sound E M (kn cs) gb gk 88 (ghi - gk) HKN ltac:(lia) ltac:(lia) ltac:(subst g; lia) Hbb) as D.
      pose proof (sp_frame_ok_sound E (reg cs 2) 48 Hsp0 ltac:(lia) Hfr2) as F. fold spv in F.
      subst g. lia. }
  (* [comment removed for export] *)
  set (Mz := (st - 16 - stride * idx)%Z).
  pose proof (flat_b_sound E M (kn cs) mb mk 8 HKN Hflm) as Fm.
  assert (HMe_d : edenot E Me = Z_to_bv 64 Mz).
  { subst Me. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold st. rewrite Z.add_mod_idemp_r by lia. f_equal. subst Mz. lia. }
  assert (Amb : adenot E (SA mb mk) = Z_to_bv 64 Mz).
  { rewrite adenot_Z, <- (split_lit_denot E Me mb mk Hsme). exact HMe_d. }
  pose proof (kread8e_rdn E M (kn cs) mb mk ge HKN Hge Fm) as Rmeta. rewrite Amb in Rmeta.
  (* [comment removed for export] *)
  assert (A16 : adenot E (SA gb (gk + 16)) = Z_to_bv 64 (g + 16)) by (rewrite adenot_Z; f_equal; subst g; lia).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me' HKN HMe' ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as Rmem.
  rewrite A16 in Rmem. rewrite (len_eqb_sound E M (kn cs) _ _ HKN HMe), HMe_d in Rmem.
  (* [comment removed for export] *)
  assert (A32 : adenot E (SA gb (gk + 32)) = Z_to_bv 64 (g + 32)) by (rewrite adenot_Z; f_equal; subst g; lia).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 32) We HKN HWe ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as RW.
  rewrite A32 in RW. rewrite Hw in RW. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (sl_W s))) in RW. fold W in RW.
  (* [comment removed for export] *)
  assert (A24 : adenot E (SA gb (gk + 24)) = Z_to_bv 64 (g + 24)) by (rewrite adenot_Z; f_equal; subst g; lia).
  assert (A28 : adenot E (SA gb (gk + 28)) = Z_to_bv 64 (g + 28)) by (rewrite adenot_Z; f_equal; subst g; lia).
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 24) 4 avail HKN Hav ltac:(lia) ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as [Rav Hav_r].
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 28) 4 freed HKN Hfr ltac:(lia) ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as [Rfr Hfr_r].
  rewrite A24, wle_low4 in Rav. rewrite A28, wle_low4 in Rfr.
  (* [comment removed for export] *)
  destruct (lin_lowbits_kn_sound RSEGS E M (kn cs) ge 12 gm12 HKN ltac:(lia) Hlow) as [Hgm Hgm_r]. rewrite Hug in Hgm.
  change (2 ^ 12)%Z with 4096%Z in Hgm, Hgm_r.
  pose proof (flat_b_sound E M (kn cs) ab ak 8 HKN Hfla) as Fa.
  assert (Aar : adenot E (SA ab ak) = Z_to_bv 64 (g - g mod 4096)).
  { rewrite adenot_Z, <- (split_lit_denot E area ab ak Hsa). subst area. rewrite mkAlu_denot. cbn [edenot].
    rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Hug.
    rewrite Z.add_mod_idemp_r by lia. f_equal. lia. }
  pose proof (kread8e_rdn E M (kn cs) ab ak se HKN Hse Fa) as Rar. rewrite Aar in Rar.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0x517e0 se HKN Hse' ltac:(apply flat_abs; lia)) as Rsec.
  rewrite adenot_Z in Rsec. cbn [edenot] in Rsec. rewrite (u64_lit 0) in Rsec by lia. cbn [Z.add] in Rsec.
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) hb (hk - 4) (shi + 5) HKN Hflh) as Fh.
  destruct (rw_okb_sound E M (kn cs) eb ek 1 HKN Hrwe ltac:(lia)) as (_ & Edef & _ & E0 & Enw).
  destruct (kreadZ_rdn E M (kn cs) eb ek 1 0 HKN ltac:(destruct (kreadZ RSEGS (kn cs) eb ek 1) as [z|]; [destruct z; try discriminate; reflexivity | discriminate])
              ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [Rend _].
  rewrite adenot_Z, w2lb1 in Rend.
  assert (Aee : Z_to_bv 64 (bv_unsigned (edenot E eb) + ek) = (Z_to_bv 64 (st + stride - 4) : word)).
  { rewrite <- (split_lit_denot E eexp eb ek Hsee). subst eexp. rewrite mkAlu_denot. cbn [edenot]. rewrite mkAlu_denot. cbn [edenot].
    rewrite !alu_add. unfold v_add. rewrite !alu_add. unfold v_add. fold st stride. apply eqm_Z_to_bv.
    pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-4)))) as [q1 H1].
    pose proof (eqm_u_lit (-4)) as [q2 H2].
    exists (q1 + q2)%Z. lia. }
  assert (Mend : M (Z_to_bv 64 (st + stride - 4)) = Some (Z_to_bv 8 0)).
  { rewrite <- Aee. specialize (Edef 0 ltac:(lia)). rewrite Z.add_0_r in Edef.
    destruct (M (Z_to_bv 64 (bv_unsigned (edenot E eb) + ek))) as [b|] eqn:HMb; [|contradiction].
    cbn [rdn] in Rend. rewrite HMb in Rend. cbn in Rend. congruence. }
  (* [comment removed for export] *)
  assert (IMG : sz_img M).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. change (d_sizeclasses INFOUB) with 0x1050c%Z in H1, H2.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKimg. cbn [kentry_ok] in HKimg. destruct HKimg as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  pose proof (xlo_sound RSEGS E M (kn cs) (sl_off s) olo HKN Holo) as Holo'. fold o in Holo'.
  pose proof (xhi_sound RSEGS E M (kn cs) (sl_off s) ohi HKN Hohi) as Hohi'. fold o in Hohi'.
  pose proof (ehi_sound E M (kn cs) hb hh HKN Hhh) as Hhh'.
  (* [comment removed for export] *)
  assert (HE4 : (st + stride - 4 + 4 <= spv - 48)%Z).
  { destruct Fh as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F3, F4; cbn [a_base a_off] in F1, F2, F3, F4.
    destruct (hh + hk + shi + 48 <=? splo) eqn:Hnum.
    - apply Z.leb_le in Hnum. lia.
    - apply andb_prop in Hs1 as [Hs1 Hfr1]. apply andb_prop in Hs1 as [Hkd Hhi]. apply Z.leb_le in Hhi.
      pose proof (kdisj_apart_x_sound RSEGS E M (kn cs) (kn cs) _ _ _ _ _ _ HKN HKN Hkd) as Hd.
      unfold estart in Hd; cbn [a_base a_off] in Hd.
      rewrite (elenZ_lit E 4), (elenZ_lit E 0x800000000000) in Hd by lia.
      assert (Eek : (bv_unsigned (edenot E eb) + ek = st + stride - 4)%Z).
      { pose proof Aee as A. apply (f_equal bv_unsigned) in A. rewrite !u_small in A; [exact A | | ];
        unfold flat, estart in E0, Enw; cbn [a_base a_off] in E0, Enw; lia. }
      pose proof (sp_frame_ok_sound E (reg cs 2) 48 Hsp0 ltac:(lia) Hfr1) as F. fold spv in F.
      rewrite Eek in Hd. unfold SPBAND_LO in *. lia. }
  (* [comment removed for export] *)
  set (e := (st + stride - 4)%Z). set (r := (stride - 4 - nn - 16 * o)%Z). set (q := (stride * idx / 16 + o)%Z).
  assert (PRE : free_pre M spv (st + 16 * o) e Mz g idx o nn stride r q W (avail mod 2 ^ 32) (freed mod 2 ^ 32) (edenot E se)).
  { constructor.
    - exact Hsd.
    - subst Mz. lia.
    - subst e Mz. lia.
    - reflexivity.
    - reflexivity.
    - replace (st + 16 * o)%Z with (st + o * 16)%Z by lia. rewrite Z.mod_add by lia. exact Hmod2.
    - subst Mz. nia.
    - rewrite Fli. lia.
    - lia.
    - lia.
    - subst r. lia.
    - subst q. lia.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      rewrite Fsc, Fml, Fli. subst q.
      apply orb_prop in Hsc as [Hsc|Hsc].
      + left. apply andb_prop in Hsc as [Hsc H3]. apply andb_prop in Hsc as [H1 H2].
        apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
      + right. apply andb_prop in Hsc as [Hsc H3]. apply andb_prop in Hsc as [H1 H2].
        apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
    - intros Hml0. rewrite Fml in Hml0. subst q.
      apply orb_prop in Hml as [Hml|Hml]; [apply Z.eqb_eq in Hml; lia | apply Z.leb_le in Hml; rewrite Fml].
      clear - Hml Hohi' HSlo'. nia.
    - apply Z.mod_pos_bound. lia.
    - rewrite testbit_mod32 by lia. exact Havb.
    - apply Z.mod_pos_bound. lia.
    - rewrite testbit_mod32 by lia. exact Hfrb.
    - lia.
    - subst e. lia.
    - rewrite Hq1. exact Qst.
    - exact Pm4.
    - exact Pm3.
    - exact Pm2.
    - exact Pzr.
    - exact Pe5.
    - exact Pe4.
    - exact Mend.
    - rewrite <- Hug, Z_to_bv_bv_unsigned. exact Rmeta.
    - exact Rmem.
    - exact RW.
    - exact Rav.
    - exact Rfr.
    - exact Rar.
    - exact Rsec.
    - exact IMG. }
  (* [comment removed for export] *)
  destruct (ref_free_pro R M (seg_rom RSEGS) spv (st + 16 * o) e Mz g idx o nn stride r q W _ _ _ PRE R2' R10)
    as (R' & Hms & G2 & G9 & G8 & G10 & G11 & G14 & G15 & G18 & G19 & G3 & G4 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  set (M1 := free_mem1 M spv (getr R 1) (getr R 8) (getr R 9) (getr R 18) (getr R 19)) in Hms.
  (* [comment removed for export] *)
  assert (LF : log_flat E log).
  { subst log. cbn [log_flat]. unfold flat, estart; cbn [a_base a_off]. repeat split; try lia. }
  assert (HM1 : mem_denot E M log = M1).
  { subst log M1. cbn [mem_denot]. unfold free_mem1.
    rewrite !adenot_Z.
    rewrite <- (reg_sound E cs R M model 19 HC ltac:(lia)), <- (reg_sound E cs R M model 18 HC ltac:(lia)),
            <- (reg_sound E cs R M model 9 HC ltac:(lia)), <- (reg_sound E cs R M model 8 HC ltac:(lia)),
            <- (reg_sound E cs R M model 1 HC ltac:(lia)).
    replace (bv_unsigned (edenot E qb) + (qk + 8))%Z with (spv - 40)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 16))%Z with (spv - 32)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 24))%Z with (spv - 24)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 32))%Z with (spv - 16)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 40))%Z with (spv - 8)%Z by lia.
    reflexivity. }
  pose proof (carry_sound RSEGS E M M log (kn cs) [] kn' [] hs Hcar LF HKN ltac:(constructor)) as HK1. rewrite HM1 in HK1.
  (* [comment removed for export] *)
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv]. apply andb_prop in Hfresh as [Hsv Hkv0]. apply Nat.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  set (E' := ext_call E nx R').
  pose proof (ext_call_agree E nx R') as Hag. fold E' in Hag.
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_freepro INFOUB)) with (0x178a4%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  specialize (HK E' R' M1 ltac:(eapply env_agree_le; [exact Hag | exact Hnx0])).
  rewrite Ecs in HK. unfold cfg_of in HK. cbn [pc c_ss s_pc] in HK.
  replace (Z_to_bv 64 (t_freepro_k INFOUB)) with (0x17980%bv : word) in HK by (apply bv_eq; reflexivity).
  apply HK. clear HK.
  destruct HC as [HR HKc HL Hhalt Hlz Hmt Hfd HV HSLc].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - (* [comment removed for export] *)
    change (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_fresh (s_regs (c_ss cs)) caller_saved nx) 2 spm) 9 (reg cs 10))
              8 (ELit idx)) 10 ge) 11 We) 14 reserved) 15 e12)
      with (sr_upds (sr_fresh (s_regs (c_ss cs)) caller_saved nx)
              [(2%nat, spm); (9%nat, reg cs 10); (8%nat, ELit idx); (10%nat, ge); (11%nat, We); (14%nat, reserved); (15%nat, e12)]).
    apply andb_prop in Hvars as [Hvars VWe]. apply andb_prop in Hvars as [Hvars Vpa]. apply andb_prop in Hvars as [Hvars Ve12].
    apply andb_prop in Hvars as [Hvars Vres]. apply andb_prop in Hvars as [Vge Vspm].
    assert (Eres : edenot E reserved = Z_to_bv 64 r).
    { subst reserved. rewrite mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite times16_denot.
      fold o. rewrite !alu_sub, !alu_add. unfold v_sub, v_add. rewrite ?alu_add. unfold v_add. fold nn stride.
      apply eqm_Z_to_bv. subst r.
      pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-4)))) as [q1 H1]. pose proof (eqm_u_lit (-4)) as [q4 H4].
      pose proof (eqm_u_lit (16 * o)) as [q2 H2].
      pose proof (eqm_u_lit (nn + bv_unsigned (Z_to_bv 64 (16 * o)))) as [q3 H3].
      exists (q1 + q4 - q3 - q2)%Z. clear - H1 H2 H3 H4. lia. }
    assert (Ee12 : edenot E e12 = Z_to_bv 64 (e - 12)).
    { subst e12. rewrite !mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite !alu_add. unfold v_add.
      rewrite ?alu_add. unfold v_add. fold st stride. apply eqm_Z_to_bv. subst e.
      pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-16)))) as [q1 H1]. pose proof (eqm_u_lit (-16)) as [q2 H2].
      exists (q1 + q2)%Z. lia. }
    apply (regs_after_ovr E (s_regs (c_ss cs)) R R' nx); [exact HR | exact Hsv | |  |].
    + cbn [map fst]. repeat (constructor; [cbn [In]; lia|]). constructor.
    + intros io Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd]; split;
        first [ exact Vspm | exact Vpa | exact Vge | exact Vres | exact Ve12 | exact VWe | reflexivity | idtac ].
      * replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G2, Hspm. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G9, Epa. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G8. cbn [edenot]. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10, <- Hug, Z_to_bv_bv_unsigned. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G11, Hw. subst W. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, Eres. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15, Ee12. reflexivity.
    + intros rr Hr0 Hncs Hnov. cbn [map fst In] in Hnov. unfold caller_saved in Hncs. cbn [In] in Hncs.
      pose proof (ridx_range rr) as Hrr.
      assert (KEPT : forall k : nat, In k [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
                     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. cbn [In] in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
          lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            first [ replace (Z_to_bv 5 (Z.of_nat k)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
          end. }
      rewrite (reg_of_ridx rr _ eq_refl). apply KEPT. cbn [In].
      assert (Hz : ridx rr <> 0%nat).
      { intros X. apply Hr0. rewrite (reg_of_ridx rr 0%nat X). apply bv_eq. reflexivity. }
      lia.
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HK1].
  - reflexivity.
  - exact Hhalt.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - destruct HV; constructor; try assumption.
    + eapply smaps_ok_ext; [exact Hag | exact Hmv | assumption].
    + match goal with H : vm_init_sp _ = edenot E (EVar 0) |- _ => rewrite H end.
      cbn [edenot]. apply Hag. lia.
  - eapply slots_ok_ext; [exact Hag | |].
    + apply slots_vars_lt_carry. unfold remove_slot. apply slots_vars_lt_filter. exact Hslv.
    + rewrite <- HM1. eapply slots_carry_sound; [exact HK1 | exact LF | apply slots_ok_filter; exact HSLc].
Qed.

Theorem call_freepro_ok : freepro_sound_stmt nx0.
Proof. intros FP. exact call_freepro_sound'. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End NX0.
End UbSymPlanSoundFP.

Module UbSymPlanSoundEF.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase UbLibCas UbLibCas2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbFreePro.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Hypothesis nx0_pos : (0 < nx0)%nat.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma memF_out : forall (m : word -> option byte) idx n stride start off (x : word),
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= start -> start + stride < 2 ^ 64 ->
  ~ (start - 3 <= bv_unsigned x < start + 16 * off) ->
  ~ (start + 16 * off + n <= bv_unsigned x < start + stride - 4) ->
  memF m idx n stride start off x = m x.
Proof.
  intros m idx n stride start off x Hoff Hn Hstr Hst Hnw Hx1 Hx2.
  pose proof (u64_range x) as Hxr.
  Ltac miss1 := rewrite wbytes_miss;
    [ | rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u64_lit by lia; lia
      | rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u64_lit by lia; lia ].
  unfold memF, mF. miss1.
  unfold mE. cbv zeta.
  assert (D : mD start off m x = m x).
  { unfold mD. destruct (off =? 0) eqn:Eo; [reflexivity|]. apply Z.eqb_neq in Eo. miss1. miss1. miss1. reflexivity. }
  assert (E1 : mE1 idx stride start off (mD start off m) x = m x).
  { unfold mE1. miss1. miss1. exact D. }
  destruct (stride - 4 - n - 16 * off =? 0) eqn:Er; [exact E1|]. apply Z.eqb_neq in Er.
  destruct (stride - 4 - n - 16 * off <? 5) eqn:Er5.
  - apply Z.ltb_lt in Er5. miss1. exact E1.
  - apply Z.ltb_ge in Er5. miss1. miss1. miss1. exact E1.
Qed.

Lemma memF_grows : forall (m : word -> option byte) idx n stride start off,
  mem_grows m (memF m idx n stride start off).
Proof.
  intros. unfold memF. eapply mem_grows_trans; [| apply grows_mF].
  eapply mem_grows_trans; [apply grows_mD | apply grows_mE].
Qed.

(* [comment removed for export] *)
Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite (A1 n Hn); apply A2; exact Hn | congruence]. Qed.

(* [comment removed for export] *)
Lemma cs_ok_bump1 : forall E cs R M model a,
  cs_ok E cs R M model -> fresh_ok nx0 cs = true ->
  cs_ok (ext1 E (s_next (c_ss cs)) a) (bump_next cs 1) R M model.
Proof.
  intros E cs R M model a HC Hf. unfold fresh_ok in Hf.
  apply andb_prop in Hf as [Hf Hnx]. apply andb_prop in Hf as [Hf Hslv]. apply andb_prop in Hf as [Hf Hmv].
  apply andb_prop in Hf as [Hsv Hkv].
  pose proof (ext1_agree E (s_next (c_ss cs)) a) as Hag.
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL].
  constructor; cbn [bump_next c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - eapply regs_ok_ext; [exact Hag | exact Hsv | exact HR].
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HK].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - destruct HV; constructor; try assumption.
    + eapply smaps_ok_ext; [exact Hag | exact Hmv | assumption].
    + match goal with H : vm_init_sp _ = edenot E (EVar 0) |- _ => rewrite H end.
      cbn [edenot]. apply Hag. apply Nat.leb_le in Hnx. lia.
  - eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL].
Qed.

Lemma expr_vars_lt_mono : forall b b' e, (b <= b')%nat -> SP.expr_vars_lt b e = true -> SP.expr_vars_lt b' e = true.
Proof.
  intros b b' e Hle. induction e; cbn [SP.expr_vars_lt]; intros He; try reflexivity.
  - apply Nat.ltb_lt in He. apply Nat.ltb_lt. lia.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - exact (IHe He).
Qed.

Lemma slots_vars_lt_mono : forall b b' ss, (b <= b')%nat -> slots_vars_lt b ss = true -> slots_vars_lt b' ss = true.
Proof.
  intros b b' ss Hle H. unfold slots_vars_lt in *. apply forallb_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Hs. unfold slot_vars_lt in *.
  repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
  rewrite !(expr_vars_lt_mono b b') by assumption. reflexivity.
Qed.

Lemma rdn1_byte : forall (M : word -> option byte) (a : word) b, M a = Some b -> rdn RSEGS M a 1 = Some [b].
Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma slot_lit_words_ok : forall E (M : word -> option byte) sb sk idx stride n st,
  enframe_post M idx n stride st 0 ->
  bv_unsigned (edenot E sb) + sk = st -> 4 <= st -> st + stride < 2 ^ 64 -> 0 <= n -> n + 4 <= stride ->
  know_ok RSEGS E M (slot_lit_words sb sk idx stride n).
Proof.
  intros E M sb sk idx stride n st P Hsb Hst Hnw Hn0 Hn4.
  destruct P as [pp pe pr pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst pp pe pr pq.
  replace (st + 16 * 0) with st in * by lia. replace (stride - 4 - n - 16 * 0) with (stride - 4 - n) in * by lia.
  replace (stride * idx / 16 + 0) with (stride * idx / 16) in * by lia.
  assert (AD : forall k, adenot E (SA sb k) = Z_to_bv 64 (st + (k - sk))).
  { intros k. rewrite adenot_Z. f_equal. lia. }
  assert (FL : forall k w, 0 <= st + (k - sk) -> st + (k - sk) + w <= 2 ^ 64 -> 0 < w -> flat E (SA sb k) w).
  { intros k w H1 H2 H3. unfold flat, estart. cbn [a_base a_off]. lia. }
  unfold slot_lit_words. cbv zeta.
  apply Forall_cons.
  { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
    replace (st + (sk - 3 - sk)) with (st - 3) by lia. apply rdn1_byte. exact Pm3. }
  apply Forall_cons.
  { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD.
    replace (st + (sk - 2 - sk)) with (st - 2) by lia. exact Pm2. }
  apply Forall_app. split.
  - destruct (0 <? stride - 4 - n) eqn:Er; [|constructor]. apply Z.ltb_lt in Er.
    apply Forall_one. cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
    replace (st + (sk + n - sk)) with (st + n) by lia. apply rdn1_byte. apply Pzr. exact Er.
  - destruct (5 <=? stride - 4 - n) eqn:Er; [|constructor]. apply Z.leb_le in Er.
    apply Forall_cons.
    { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
      replace (st + (sk + stride - 4 - 5 - sk)) with (st + stride - 4 - 5) by lia. apply rdn1_byte. apply Pe5. exact Er. }
    apply Forall_one. cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD.
    replace (st + (sk + stride - 4 - 4 - sk)) with (st + stride - 4 - 4) by lia. apply Pe4. exact Er.
Qed.

(* [comment removed for export] *)
Lemma enframe_core {FP : FPState} : forall cs cs1 csa E E1 R R' M model T (ret : Z) (v nx1 : nat)
    (p sb pnb len1 len2 sde : expr) (sk pnk : Z) (k0 kl : list kentry) (s : sslot)
    (idx stride st n off : Z),
  let MF := memF M idx n stride st off in
  let ss := s :: slots_keep (kn cs) sb (sk - 4) sde (c_slots cs) in
  (forall E' R'' M', env_agree nx0 E E' -> cs_ok E' (set_slots csa ss) R'' M' model ->
      realizes RSEGS (cfg_of R'' (pc (set_slots csa ss)) M' model) T) ->
  after_call nx0 cs1 ret (Some p) (kl ++ kn_havoc (kn_havoc k0 sb (sk - 3) len1) pnb pnk len2) = Some csa ->
  cs_ok E1 cs1 R M model -> know_ok RSEGS E1 M (kn cs) -> slots_ok E1 M (c_slots cs) ->
  fresh_ok nx0 cs = true -> v = s_next (c_ss cs) -> s_next (c_ss cs1) = nx1 -> (v <= nx1)%nat ->
  env_agree v E E1 ->
  know_ok RSEGS E1 M k0 ->
  bv_unsigned (edenot E1 sb) + sk = st ->
  bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n ->
  elenZ E1 len1 = 16 * off + 3 -> elenZ E1 len2 = stride - 4 - n - 16 * off -> elenZ E1 sde = stride ->
  edenot E1 p = Z_to_bv 64 (st + 16 * off) ->
  know_ok RSEGS E1 MF kl -> slot_ok E1 MF s -> slot_vars_lt nx1 s = true ->
  keeps_cs R R' -> getr R' 10%bv = Z_to_bv 64 (st + 16 * off) ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= st -> st + stride < 2 ^ 64 ->
  realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 ret) MF (seg_rom RSEGS)) model) T.
Proof.
  intros cs cs1 csa E E1 R R' M model T ret v nx1 p sb pnb len1 len2 sde sk pnk k0 kl s idx stride st n off MF ss
         HK Hac HC1 HK1 HSL1 Hfresh Hv Hnx1 Hvle Hag1 K0 SB PNB Elen1 Elen2 Esde Ep1 KL SLOT Hvsl Hkeeps HA0
         Hoff Hn0 Hfit Hst4 Hnw.
  (* [comment removed for export] *)
  set (M1 := fun x : word => if ((st - 3 <=? bv_unsigned x) && (bv_unsigned x <? st + 16 * off))%bool then MF x else M x).
  pose proof (memF_grows M idx n stride st off) as HgF. fold MF in HgF.
  assert (OUT : forall x : word, ~ (st - 3 <= bv_unsigned x < st + 16 * off) ->
                               ~ (st + 16 * off + n <= bv_unsigned x < st + stride - 4) -> MF x = M x).
  { intros x Hx1 Hx2. subst MF. apply memF_out; lia. }
  assert (K1 : know_ok RSEGS E1 M1 (kn_havoc k0 sb (sk - 3) len1)).
  { apply (know_ok_havoc E1 M M1 k0 sb (sk - 3) len1 K0).
    - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite Elen1 in Hx. subst M1. cbv beta.
      destruct (Z.leb_spec (st - 3) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (st + 16 * off)); cbn [andb]; try reflexivity. lia.
    - intros x Hx. subst M1. cbv beta. destruct (_ && _)%bool; [apply HgF; exact Hx | exact Hx]. }
  assert (K2 : know_ok RSEGS E1 MF (kn_havoc (kn_havoc k0 sb (sk - 3) len1) pnb pnk len2)).
  { apply (know_ok_havoc E1 M1 MF _ pnb pnk len2 K1).
    - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite PNB, Elen2 in Hx. subst M1. cbv beta.
      destruct (Z.leb_spec (st - 3) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (st + 16 * off)); cbn [andb]; try reflexivity;
        apply OUT; lia.
    - intros x Hx. subst M1. cbv beta in Hx. destruct (_ && _)%bool; [exact Hx | apply HgF; exact Hx]. }
  (* [comment removed for export] *)
  destruct (after_call_sound nx0 cs1 ret (Some p) _ csa E1 R R' M MF model ss Hac HC1) as [HC' Hpc'].
  - (* [comment removed for export] *)
    intros r Hr0 Hnin. apply (keeps_cs_getr R R' r Hkeeps).
    apply kept_of_not_caller_saved; [| exact Hr0 | exact Hnin].
    intros k Hk. cbn [In] in Hk. unfold callee_saved.
    repeat (destruct Hk as [<-|Hk]; [cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
      repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end; fail | ]).
    all: try (destruct Hk).
  - (* [comment removed for export] *)
    rewrite Ep1. exact HA0.
  - (* [comment removed for export] *)
    apply Forall_app. split; [exact KL | exact K2].
  - (* [comment removed for export] *)
    apply Forall_cons; [exact SLOT|].
    eapply slots_keep_sound; [exact HK1 | exact HSL1 |].
    unfold estart. cbn [a_base a_off]. rewrite Esde. intros x Hx. apply OUT; lia.
  - (* [comment removed for export] *)
    rewrite Hnx1. subst ss. unfold slots_vars_lt. cbn [forallb]. fold (slots_vars_lt nx1 (slots_keep (kn cs) sb (sk - 4) sde (c_slots cs))).
    rewrite Hvsl. cbn [andb]. apply slots_vars_lt_keep. apply (slots_vars_lt_mono v nx1); [exact Hvle|].
    subst v. apply (fresh_ok_slots nx0). exact Hfresh.
  - (* [comment removed for export] *)
    rewrite <- Hpc'.
    apply (HK (ext_call E1 (s_next (c_ss cs1)) R') R' MF); [|exact HC'].
    apply (env_agree_trans' nx0 E E1).
    + eapply env_agree_le; [exact Hag1 | subst v; exact (fresh_ok_nx0 nx0 cs Hfresh)].
    + eapply env_agree_le; [apply ext_call_agree |]. rewrite Hnx1.
      pose proof (fresh_ok_nx0 nx0 cs Hfresh). subst v. lia.
Qed.

Theorem call_enframe_ok : enframe_sound_stmt nx0.
Proof.
  unfold enframe_sound_stmt. intros FP cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_enframe in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [idx|] eqn:H11; [|discriminate].
  cbv zeta in Hn.
  destruct (split_lit (reg cs 10)) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me|] eqn:HMe; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 32) 8) as [W|] eqn:HW; [|discriminate].
  set (stride := slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)) in Hn.
  set (start := mkAlu ALU_ADD Me (ELit (16 + stride * idx))) in Hn.
  destruct (split_lit start) as [sb sk] eqn:Hss.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (ehi (kn cs) Me) as [mh|] eqn:Hmh; [|discriminate].
  set (shs := (stride - 4 - nlo) / 16) in Hn.
  set (symb := negb (shs =? 0)) in Hn.
  set (v := s_next (c_ss cs)) in Hn.
  set (offe := if symb then EVar v else ELit 0) in Hn.
  set (p := mkAlu ALU_ADD start (times16 offe)) in Hn.
  destruct (split_lit p) as [pb pk] eqn:Hsp.
  set (ne := reg cs 12) in *.
  set (pn := mkAlu ALU_ADD p ne) in Hn.
  destruct (split_lit pn) as [pnb pnk] eqn:Hspn.
  set (kf := if symb then [KRange (EVar v) 0 (Z.min 255 shs); KRange (mkAlu ALU_ADD (times16 (EVar v)) ne) nlo (stride - 4)] else []) in Hn.
  set (s := SL start (ELit stride) ne offe (ELit W) idx p) in Hn.
  set (nx1 := if symb then S v else v) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (cs1 := if symb then bump_next cs 1 else cs) in Hn.
  set (len1 := mkAlu ALU_ADD (times16 offe) (ELit 3)) in Hn.
  set (len2 := mkAlu ALU_SUB (ELit (stride - 4)) (mkAlu ALU_ADD ne (times16 offe))) in Hn.
  set (k1 := kn_havoc (kf ++ kn cs) sb (sk - 3) len1) in Hn.
  set (k2 := kn_havoc k1 pnb pnk len2) in Hn.
  set (kl := if symb then [] else match ne with ELit n0 => slot_lit_words sb sk idx stride (n0 mod two64) | _ => [] end) in Hn.
  destruct (after_call nx0 cs1 ret (Some p) (kl ++ k2)) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvsl].
  apply andb_prop in Hcond as [Hcond Hvn]. apply andb_prop in Hcond as [Hcond Hvs].
  apply andb_prop in Hcond as [Hcond Hflpn]. apply andb_prop in Hcond as [Hcond Hflp].
  apply andb_prop in Hcond as [Hcond Himg]. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hr4]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hmhb].
  apply andb_prop in Hcond as [Hcond Hnhi4]. apply andb_prop in Hcond as [Hcond Hnlo0].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond Hq].
  apply andb_prop in Hcond as [Hcond Hidx32]. apply andb_prop in Hcond as [Hcond Hidx0].
  apply andb_prop in Hcond as [Hcond Hm16]. apply andb_prop in Hcond as [Hcond H31].
  apply andb_prop in Hcond as [Hsc H16].
  apply Z.leb_le in H16. apply Z.ltb_lt in H31. apply Z.eqb_eq in Hm16. apply Z.leb_le in Hidx0. apply Z.ltb_lt in Hidx32.
  apply Z.leb_le in Hq. apply Z.leb_le in Hal. apply Z.leb_le in Hnlo0. apply Z.leb_le in Hnhi4. apply Z.leb_le in Hmhb.
  unfold two64 in Hmhb.
  assert (Hscp : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48).
  { intros Hd. destruct (w_sizeclass W <? 48) eqn:E48; [apply Z.ltb_lt in E48; exact E48|].
    exfalso. destruct Hd as [Hd|Hd].
    - rewrite (proj2 (Z.eqb_eq _ _) Hd) in Hsc. cbn in Hsc. discriminate.
    - destruct (w_lastidx W =? 0) eqn:El; [apply Z.eqb_eq in El; lia|]. destruct (w_maplen W =? 0); cbn in Hsc; discriminate. }
  clear Hsc.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 11 idx HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12. fold ne in R12.
  set (c := getr R (Z_to_bv 5 13)).
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw). pose proof (u64_range nw) as Hnwr. fold n in Hnwr.
  pose proof (xlo_sound RSEGS E M (kn cs) ne nlo HKN Hnlo) as Hnlo'. fold nw n in Hnlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) ne nhi HKN Hnhi) as Hnhi'. fold nw n in Hnhi'.
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  set (g := bv_unsigned (edenot E gb) + gk) in *.
  assert (Hg40 : 0 <= g /\ g + 40 <= 2 ^ 64) by (unfold flat, estart in Fg; cbn [a_base a_off] in Fg; lia).
  assert (R10' : getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 g) by (rewrite R10; exact (split_lit_denot E _ _ _ Hsg)).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me HKN HMe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RM.
  rewrite adenot_Z in RM. replace (bv_unsigned (edenot E gb) + (gk + 16)) with (g + 16) in RM by lia.
  set (M0 := bv_unsigned (edenot E Me)). pose proof (u64_range (edenot E Me)) as HM0r. fold M0 in HM0r.
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 32) 8 W HKN HW ltac:(lia) ltac:(eapply flat_sub; [exact Fg | lia | cbn; lia | cbn; lia])) as [RW HWr].
  rewrite adenot_Z in RW. replace (bv_unsigned (edenot E gb) + (gk + 32)) with (g + 32) in RW by lia. unfold two64 in HWr.
  pose proof (ehi_sound E M (kn cs) Me mh HKN Hmh) as Hmh'. fold M0 in Hmh'.
  (* [comment removed for export] *)
  set (st := M0 + 16 + stride * idx).
  assert (Hsidx : 0 <= stride * idx) by nia.
  assert (Est : edenot E start = Z_to_bv 64 st).
  { subst start. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. subst st M0. f_equal. lia. }
  assert (Ust : bv_unsigned (edenot E start) = st) by (rewrite Est; apply u64_lit; lia).
  (* [comment removed for export] *)
  destruct (rw_okb_sound E M (kn cs) sb (sk - 4) stride HKN Hrw ltac:(lia)) as (OKh & DEFh & IMGh & H0h & Hnwh).
  pose proof (split_lit_denot E start sb sk Hss) as Esb. rewrite Est in Esb.
  assert (SB : bv_unsigned (edenot E sb) + sk = st).
  { apply (f_equal bv_unsigned) in Esb. rewrite !u64_lit in Esb by lia. lia. }
  replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in OKh, DEFh, IMGh, H0h, Hnwh by lia.
  replace (Z_to_bv 64 (bv_unsigned (edenot E sb) + (sk - 4))) with (Z_to_bv 64 (st - 4) : word) in OKh by (f_equal; lia).
  (* [comment removed for export] *)
  destruct (kreadZ RSEGS (kn cs) sb (sk - 4) 1) as [z4|] eqn:Hz4; [|discriminate]. destruct z4; try discriminate. clear Hr4.
  destruct (kreadZ_rdn E M (kn cs) sb (sk - 4) 1 0 HKN Hz4 ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [R4r _].
  rewrite adenot_Z, w2lb1 in R4r. replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in R4r by lia.
  assert (R4 : M (Z_to_bv 64 (st - 4)) = Some (Z_to_bv 8 0)).
  { pose proof (DEFh 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn] in R4r.
    destruct (M (Z_to_bv 64 (st - 4))) as [b4|]; [|exfalso; apply D0; reflexivity].
    cbn in R4r. congruence. }
  clear R4r.
  (* [comment removed for export] *)
  destruct (M (Z_to_bv 64 (st - 3))) as [b3|] eqn:HM3.
  2:{ exfalso. apply (DEFh 1 ltac:(lia)). replace (st - 4 + 1) with (st - 3) by lia. exact HM3. }
  pose proof (u8_range b3) as Hb3.
  destruct (rdn_defined M (st - 2) 2 ltac:(lia) ltac:(cbn; lia)
              ltac:(intros i Hi; replace (st - 2 + i) with (st - 4 + (2 + i)) by lia; apply DEFh; cbn in Hi; lia)) as (bs2 & Hbs2 & Hlen2).
  set (o16 := bytes_le_to_Z bs2).
  pose proof (bytes_le_to_Z_bound bs2) as Ho16. rewrite Hlen2 in Ho16. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in Ho16. fold o16 in Ho16.
  (* [comment removed for export] *)
  assert (OK3 : store_ok RSEGS M (Z_to_bv 64 (st - 3)) (Z.to_nat (stride - 1)) = true).
  { eapply (store_ok_sub RSEGS M (Z_to_bv 64 (st - 4)) _ (Z.to_nat stride)); rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia. exact OKh. }
  (* [comment removed for export] *)
  assert (TBL : sc_tbl_clear M).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih. change (d_sizeclasses INFOUB) with 0x1050c%Z in Hil, Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros j Hj. apply Hnone. unfold SCT. lia. }
  (* [comment removed for export] *)
  pose proof (ranges_apart_sound RSEGS E M (kn cs) gb (gk + 16) 8 sb (sk - 3) (stride - 1) HKN Hap) as Hdisj.
  unfold estart in Hdisj. cbn [a_base a_off] in Hdisj.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) start HKN) as [Heal Hdiv]. rewrite Ust in Hdiv.
  assert (Hst16 : st mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) start - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  set (off := enframe_off (slack_of stride n) ((if bv_unsigned b3 =? 0 then bv_unsigned c else o16 + 1) mod 256)).
  assert (EF : efH M c g M0 W idx n (bv_unsigned b3) o16 stride st off).
  { constructor.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hg40.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hscp.
    - exact H31.
    - exact Hq.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite RM. subst M0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact RW.
    - exact R4.
    - rewrite Z_to_bv_bv_unsigned. exact HM3.
    - intros _. rewrite Hbs2. subst o16. rewrite word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
    - exact OK3.
    - exact TBL. }
  pose proof (off_facts M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF) as (Ooff & O255 & O16 & Oslack).
  assert (R12' : getr R (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 n) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (enframe_run M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF R (seg_rom RSEGS) (Z_to_bv 64 ret)
              R1 Hrok R10' R11 R12' eq_refl) as (R' & Hms & Hkeeps & HA0).
  pose proof (post_memF M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF) as POST.
  set (MF := memF M idx n stride st off) in *.
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_enframe INFOUB)) with (0x18e44%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |]. clear Hms.
  (* [comment removed for export] *)
  assert (Hslack : slack_of stride n <= shs).
  { subst shs. unfold slack_of, IB, UNIT. apply Z.div_le_mono; lia. }
  set (offw := (Z_to_bv 64 off : word)).
  set (E1 := if symb then ext1 E v offw else E).
  assert (Hag1 : env_agree v E E1) by (subst E1; destruct symb; [apply ext1_agree | apply env_agree_refl']).
  assert (HC1 : cs_ok E1 cs1 R M model).
  { subst E1 cs1. destruct symb; [apply cs_ok_bump1; [exact HC | exact Hfresh] | exact HC]. }
  assert (Hnx1 : s_next (c_ss cs1) = nx1).
  { subst cs1 nx1. destruct symb; [cbn [bump_next c_ss s_next]; subst v; apply Nat.add_1_r | reflexivity]. }
  assert (Eoffe : edenot E1 offe = offw).
  { subst E1 offe offw. destruct symb eqn:Hsy.
    - apply ext1_at.
    - cbn [edenot]. f_equal. subst symb. apply negb_false_iff in Hsy. apply Z.eqb_eq in Hsy. lia. }
  assert (Estart1 : edenot E1 start = Z_to_bv 64 st).
  { rewrite <- (edenot_agree v E E1 start Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvs). exact Est. }
  assert (Ene1 : edenot E1 ne = nw).
  { rewrite <- (edenot_agree v E E1 ne Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvn). reflexivity. }
  assert (Esb1 : edenot E1 sb = edenot E sb).
  { symmetry. apply (edenot_agree v E E1 sb Hag1). rewrite <- expr_vars_lt_eq. eapply split_lit_vars; [exact Hss | exact Hvs]. }
  assert (Hoffw : bv_unsigned offw = off) by (subst offw; apply u64_lit; lia).
  assert (Etimes : edenot E1 (times16 offe) = Z_to_bv 64 (16 * off)) by (rewrite times16_denot, Eoffe, Hoffw; reflexivity).
  assert (Ep1 : edenot E1 p = Z_to_bv 64 (st + 16 * off)).
  { subst p. rewrite mkAlu_denot, alu_add, Estart1, Etimes. unfold v_add. rewrite !u64_lit by lia. reflexivity. }
  assert (Epn1 : edenot E1 pn = Z_to_bv 64 (st + 16 * off + n)).
  { subst pn. rewrite mkAlu_denot, alu_add, Ep1, Ene1. unfold v_add. rewrite u64_lit by lia. reflexivity. }
  assert (Elen1 : elenZ E1 len1 = 16 * off + 3).
  { unfold elenZ. subst len1. rewrite mkAlu_denot, alu_add, Etimes. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (16 * off)), (u64_lit 3) by lia. apply u64_lit. lia. }
  assert (Elen2 : elenZ E1 len2 = stride - 4 - n - 16 * off).
  { unfold elenZ. subst len2. rewrite mkAlu_denot, alu_sub. cbn [edenot]. rewrite mkAlu_denot, alu_add, Ene1, Etimes.
    unfold v_sub, v_add. fold n. rewrite (u64_lit (16 * off)), (u64_lit (stride - 4)) by lia.
    rewrite (u64_lit (n + 16 * off)) by lia. rewrite u64_lit by lia. lia. }
  assert (Hn_eq : bv_unsigned nw = n) by reflexivity.
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E1 M (kn cs)).
  { pose proof (co_know _ _ _ _ _ HC1) as X. subst cs1. destruct symb; exact X. }
  assert (HSL1 : slots_ok E1 M (c_slots cs)).
  { pose proof (co_slots _ _ _ _ _ HC1) as X. subst cs1. destruct symb; exact X. }
  assert (Hkf : know_ok RSEGS E1 M kf).
  { pose proof Eoffe as Eo. subst kf offe. destruct symb; [|constructor].
    apply Forall_cons; [|apply Forall_one]; cbn [kentry_ok].
    - rewrite Eo, Hoffw. lia.
    - rewrite mkAlu_denot, alu_add, times16_denot, Eo, Hoffw, Ene1. unfold v_add.
      rewrite (u64_lit (16 * off)) by lia. rewrite Hn_eq. rewrite u64_lit by lia. lia. }
  assert (K0 : know_ok RSEGS E1 M (kf ++ kn cs)) by (apply Forall_app; split; [exact Hkf | exact HK1]).
  (* [comment removed for export] *)
  assert (PB : bv_unsigned (edenot E1 pb) + pk = st + 16 * off).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pb pk 1 K0 Hflp) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 p pb pk Hsp) as X. rewrite Ep1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (PNB : bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pnb pnk 1 K0 Hflpn) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 pn pnb pnk Hspn) as X. rewrite Epn1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (KL : know_ok RSEGS E1 MF kl).
  { subst kl. destruct symb eqn:Hsy; [constructor|].
    assert (Hoff0 : off = 0).
    { subst symb. apply negb_false_iff in Hsy. apply Z.eqb_eq in Hsy. lia. }
    destruct ne as [n0| | | | | | |] eqn:Hne; try (apply Forall_nil).
    assert (Hn0 : n = n0 mod two64).
    { rewrite <- Hn_eq. subst nw. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. }
    rewrite <- Hn0. apply (slot_lit_words_ok E1 MF sb sk idx stride n st); try lia.
    - rewrite <- Hoff0. exact POST.
    - rewrite Esb1. exact SB. }
  assert (SLOT : slot_ok E1 MF s).
  { unfold slot_ok. subst s. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p]. rewrite Hss, Hsp.
    unfold uE. rewrite Estart1, Ene1, Eoffe, Ep1, Hn_eq, Hoffw. cbn [edenot].
    rewrite (u64_lit st), (u64_lit stride), (u64_lit W), (u64_lit (st + 16 * off)) by lia.
    rewrite Esb1.
    split; [exact POST|]. split; [reflexivity|]. split; [exact SB|]. split; [exact PB|].
    split; [reflexivity|]. split; [exact Hscp|]. repeat split; lia. }
  subst cs' k1 k2.
  apply (enframe_core cs cs1 csa E E1 R R' M model T ret v nx1 p sb pnb len1 len2 (ELit stride) sk pnk (kf ++ kn cs) kl s
           idx stride st n off HK Hac HC1 HK1 HSL1 Hfresh eq_refl Hnx1); try assumption; try lia.
  - subst nx1. destruct symb; lia.
  - rewrite Esb1. exact SB.
  - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma W_fields : forall S c, 1 <= S -> 0 <= c < 4096 -> c mod 32 = 0 ->
  w_maplen (4096 * S + c) = S /\ w_lastidx (4096 * S + c) = 0
  /\ slot_stride (w_maplen (4096 * S + c)) (w_lastidx (4096 * S + c)) (w_sizeclass (4096 * S + c)) = 4096 * S - 16.
Proof.
  intros S c HS Hc Hc32. unfold w_maplen, w_lastidx.
  assert (A : (4096 * S + c) / 4096 = S) by lia.
  assert (B : (4096 * S + c) mod 32 = 0) by lia.
  rewrite A, B. split; [reflexivity|]. split; [reflexivity|].
  unfold slot_stride, UNIT. destruct (S =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. cbn [negb andb Z.eqb]. lia.
Qed.

Lemma stride_mod16 : forall S, (4096 * S - 16) mod 16 = 0.
Proof. intros. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma decode_W_sound : forall E We Se c,
  decode_W We = Some (Se, c) -> 4096 * bv_unsigned (edenot E Se) + 4096 <= 2 ^ 64 ->
  bv_unsigned (edenot E We) = 4096 * bv_unsigned (edenot E Se) + c /\ 0 <= c < 4096.
Proof.
  intros E We Se c H Hb. unfold decode_W in H.
  destruct We as [w|i|op a b|opw aw bw|op a b|opmw am bm|sx lo nn ee|sx kk ii nn]; try discriminate.
  - injection H as <- <-. cbn [edenot]. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
    pose proof (Z.mod_pos_bound w (2 ^ 64) ltac:(lia)) as Hw.
    rewrite (Z.mod_small (w mod 2 ^ 64 / 4096)).
    2:{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pose proof (Z.div_mod (w mod 2 ^ 64) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (w mod 2 ^ 64) 4096 ltac:(lia)). lia.
  - destruct op; try discriminate. destruct a as [| | | |op2 a1 a2| | |]; try discriminate.
    destruct op2; try discriminate. destruct a1 as [z| | | | | | |]; try discriminate.
    destruct z; try discriminate. repeat (destruct p; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    cbn [edenot]. rewrite alu_add. unfold v_add. rewrite u_mul64. rewrite (u64_lit 4096) by lia.
    rewrite (Z.mod_small (4096 * _)) by (pose proof (u64_range (edenot E a2)); lia).
    rewrite (u64_lit c') by lia. rewrite u64_lit by (pose proof (u64_range (edenot E a2)); lia). lia.
  - destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z; try discriminate. repeat (destruct p; try discriminate). injection H as <- <-.
    cbn [edenot]. rewrite u_mul64. rewrite (u64_lit 4096) by lia.
    rewrite Z.mod_small by (pose proof (u64_range (edenot E b)); lia). lia.
Qed.

Lemma stride_e_denot : forall E Se, 1 <= bv_unsigned (edenot E Se) -> 4096 * bv_unsigned (edenot E Se) <= 2 ^ 64 ->
  edenot E (mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16))) = Z_to_bv 64 (4096 * bv_unsigned (edenot E Se) - 16).
Proof.
  intros E Se H1 H2. rewrite mkAlu_denot, alu_add, mkMd_denot. unfold v_add. rewrite u_mul64. cbn [edenot].
  rewrite (u64_lit 4096) by lia. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.eq_dec (4096 * bv_unsigned (edenot E Se)) (2 ^ 64)) as [E64|N64].
  - rewrite E64. rewrite Z_mod_same_full. change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16). reflexivity.
  - rewrite (Z.mod_small (4096 * _)) by lia. change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
    replace (4096 * bv_unsigned (edenot E Se) + (2 ^ 64 - 16)) with ((4096 * bv_unsigned (edenot E Se) - 16) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_okb_x_sound : forall E M k b off ne,
  know_ok RSEGS E M k -> rw_okb_x INFOUB k b off ne = true ->
  let a := bv_unsigned (edenot E b) + off in
  let N := elenZ E ne in
  (forall m, Z.of_nat m <= N -> store_ok RSEGS M (Z_to_bv 64 a) m = true)
  /\ (forall i, 0 <= i < N -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + N <= 0x10000 \/ 0x52000 <= a)
  /\ 0 <= a /\ a + N <= 2 ^ 64.
Proof.
  intros E M k b off ne HK H. rewrite rw_okb_x_eq in H. apply andb_prop in H as [Hw Hoff]. cbv zeta.
  destruct (kwritable_x_sound E M k k b off ne HK HK Hw) as (Hst & F1 & F2).
  rewrite off_image_x_eq in Hoff. change (IMG_SZ INFOUB) with 0x042000%Z in Hoff. pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite elenZ_lit in Himg. rewrite u64_lit in Himg by lia.
  2:{ lia. }
  pose proof (u64_range (edenot E ne)) as Hnr. unfold elenZ in *.
  split; [exact Hst|]. split; [|lia].
  intros i Hi.
  pose proof (Hst (Z.to_nat (bv_unsigned (edenot E ne))) ltac:(rewrite Z2Nat.id by lia; lia)) as Hst'.
  pose proof (store_ok_all RSEGS M (Z.to_nat (bv_unsigned (edenot E ne))) (Z_to_bv 64 (bv_unsigned (edenot E b) + off))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst'
                (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as Wv.
  intros HM. apply Wv. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

Theorem call_enframe_x_ok : enframe_x_sound_stmt nx0.
Proof.
  unfold enframe_x_sound_stmt. intros FP cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_enframe_x in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [idx|] eqn:H11; [|discriminate].
  destruct idx; try discriminate.
  cbv zeta in Hn.
  destruct (split_lit (reg cs 10)) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me|] eqn:HMe; [|discriminate].
  destruct (kread8e RSEGS (kn cs) gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
  destruct (decode_W We) as [[Se c]|] eqn:HdW; [|discriminate].
  cbv zeta in Hn.
  set (strideE := mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16))) in Hn.
  set (start := mkAlu ALU_ADD Me (ELit 16)) in Hn.
  destruct (split_lit start) as [sb sk] eqn:Hss.
  set (ne := reg cs 12) in *.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (ehi (kn cs) Me) as [mh|] eqn:Hmh; [|discriminate].
  destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
  destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
  cbv zeta in Hn.
  set (shi := 4096 * Shi - 16) in Hn.
  set (shs := (shi - 4 - nlo) / 16) in Hn.
  set (v := s_next (c_ss cs)) in Hn.
  set (offe := EVar v) in Hn.
  set (p := mkAlu ALU_ADD start (times16 offe)) in Hn.
  destruct (split_lit p) as [pb pk] eqn:Hsp.
  set (pn := mkAlu ALU_ADD p ne) in Hn.
  destruct (split_lit pn) as [pnb pnk] eqn:Hspn.
  set (rexp := mkAlu ALU_SUB strideE (mkAlu ALU_ADD ne (times16 offe))) in Hn.
  set (kf := [KRange offe 0 (Z.min 255 shs); KRange rexp 4 (shi - nlo)]) in Hn.
  set (s := SL start strideE ne offe We 0 p) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (cs1 := bump_next cs 1) in Hn.
  set (len1 := mkAlu ALU_ADD (times16 offe) (ELit 3)) in Hn.
  set (len2 := mkAlu ALU_ADD rexp (ELit (-4))) in Hn.
  set (k1 := kn_havoc (kf ++ kn cs) sb (sk - 3) len1) in Hn.
  set (k2 := kn_havoc k1 pnb pnk len2) in Hn.
  destruct (after_call nx0 cs1 ret (Some p) k2) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvsl].
  apply andb_prop in Hcond as [Hcond HvW]. apply andb_prop in Hcond as [Hcond Hvstr].
  apply andb_prop in Hcond as [Hcond Hvn]. apply andb_prop in Hcond as [Hcond Hvs].
  apply andb_prop in Hcond as [Hcond Hflpn]. apply andb_prop in Hcond as [Hcond Hflp].
  apply andb_prop in Hcond as [Hcond Himg]. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hr4]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hmhb].
  apply andb_prop in Hcond as [Hcond Hge]. apply andb_prop in Hcond as [Hcond Hnlo0].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond HShi19].
  apply andb_prop in Hcond as [Hc32 HSlo1].
  apply Z.eqb_eq in Hc32. apply Z.leb_le in HSlo1. apply Z.leb_le in HShi19. apply Z.leb_le in Hal.
  apply Z.leb_le in Hnlo0. apply Z.leb_le in Hmhb. unfold two64 in Hmhb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 11 0 HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12. fold ne in R12.
  set (c13 := getr R (Z_to_bv 5 13)).
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw). pose proof (u64_range nw) as Hnwr. fold n in Hnwr.
  pose proof (xlo_sound RSEGS E M (kn cs) ne nlo HKN Hnlo) as Hnlo'. fold nw n in Hnlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) ne nhi HKN Hnhi) as Hnhi'. fold nw n in Hnhi'.
  (* [comment removed for export] *)
  set (Sv := bv_unsigned (edenot E Se)).
  pose proof (xlo_sound RSEGS E M (kn cs) Se Slo HKN HSlo) as HSlo'. fold Sv in HSlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) Se Shi HKN HShi) as HShi'. fold Sv in HShi'.
  set (stride := 4096 * Sv - 16).
  assert (Estr : edenot E strideE = Z_to_bv 64 stride) by (subst strideE stride Sv; apply stride_e_denot; lia).
  assert (Ustr : bv_unsigned (edenot E strideE) = stride) by (rewrite Estr; apply u64_lit; lia).
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  set (g := bv_unsigned (edenot E gb) + gk) in *.
  assert (Hg40 : 0 <= g /\ g + 40 <= 2 ^ 64) by (unfold flat, estart in Fg; cbn [a_base a_off] in Fg; lia).
  assert (R10' : getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 g) by (rewrite R10; exact (split_lit_denot E _ _ _ Hsg)).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me HKN HMe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RM.
  rewrite adenot_Z in RM. replace (bv_unsigned (edenot E gb) + (gk + 16)) with (g + 16) in RM by lia.
  set (M0 := bv_unsigned (edenot E Me)). pose proof (u64_range (edenot E Me)) as HM0r. fold M0 in HM0r.
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 32) We HKN HWe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RW.
  rewrite adenot_Z in RW. replace (bv_unsigned (edenot E gb) + (gk + 32)) with (g + 32) in RW by lia.
  set (W := bv_unsigned (edenot E We)). pose proof (u64_range (edenot E We)) as HWr. fold W in HWr.
  destruct (decode_W_sound E We Se c HdW ltac:(fold Sv; lia)) as [HWdec Hc]. fold W Sv in HWdec.
  destruct (W_fields Sv c ltac:(lia) Hc Hc32) as (Hml & Hli & Hss_stride). rewrite <- HWdec in Hml, Hli, Hss_stride.
  pose proof (ehi_sound E M (kn cs) Me mh HKN Hmh) as Hmh'. fold M0 in Hmh'.
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HKN Hge) as Hge'. cbn [xt_den] in Hge'. rewrite Ustr in Hge'.
  fold nw in Hge'. fold n in Hge'.
  (* [comment removed for export] *)
  set (st := M0 + 16).
  assert (Est : edenot E start = Z_to_bv 64 st).
  { subst start. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. subst st M0. reflexivity. }
  assert (Ust : bv_unsigned (edenot E start) = st) by (rewrite Est; apply u64_lit; lia).
  (* [comment removed for export] *)
  destruct (rw_okb_x_sound E M (kn cs) sb (sk - 4) strideE HKN Hrw) as (OKh & DEFh & IMGh & H0h & Hnwh).
  unfold elenZ in OKh, DEFh, IMGh, Hnwh. rewrite Ustr in OKh, DEFh, IMGh, Hnwh.
  pose proof (split_lit_denot E start sb sk Hss) as Esb. rewrite Est in Esb.
  assert (SB : bv_unsigned (edenot E sb) + sk = st).
  { apply (f_equal bv_unsigned) in Esb. rewrite !u64_lit in Esb by lia. lia. }
  replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in OKh, DEFh, IMGh, H0h, Hnwh by lia.
  (* [comment removed for export] *)
  destruct (kreadZ RSEGS (kn cs) sb (sk - 4) 1) as [z4|] eqn:Hz4; [|discriminate]. destruct z4; try discriminate. clear Hr4.
  destruct (kreadZ_rdn E M (kn cs) sb (sk - 4) 1 0 HKN Hz4 ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [R4r _].
  rewrite adenot_Z, w2lb1 in R4r. replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in R4r by lia.
  assert (R4 : M (Z_to_bv 64 (st - 4)) = Some (Z_to_bv 8 0)).
  { pose proof (DEFh 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn] in R4r.
    destruct (M (Z_to_bv 64 (st - 4))) as [b4|]; [|exfalso; apply D0; reflexivity].
    cbn in R4r. congruence. }
  clear R4r.
  (* [comment removed for export] *)
  destruct (M (Z_to_bv 64 (st - 3))) as [b3|] eqn:HM3.
  2:{ exfalso. apply (DEFh 1 ltac:(lia)). replace (st - 4 + 1) with (st - 3) by lia. exact HM3. }
  pose proof (u8_range b3) as Hb3.
  destruct (rdn_defined M (st - 2) 2 ltac:(lia) ltac:(cbn; lia)
              ltac:(intros i Hi; replace (st - 2 + i) with (st - 4 + (2 + i)) by lia; apply DEFh; cbn in Hi; lia)) as (bs2 & Hbs2 & Hlen2).
  set (o16 := bytes_le_to_Z bs2).
  pose proof (bytes_le_to_Z_bound bs2) as Ho16. rewrite Hlen2 in Ho16. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in Ho16. fold o16 in Ho16.
  assert (OK3 : store_ok RSEGS M (Z_to_bv 64 (st - 3)) (Z.to_nat (stride - 1)) = true).
  { eapply (store_ok_sub RSEGS M (Z_to_bv 64 (st - 4)) _ (Z.to_nat stride)); rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia.
    apply OKh. rewrite Z2Nat.id by lia. lia. }
  assert (TBL : sc_tbl_clear M).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih. change (d_sizeclasses INFOUB) with 0x1050c%Z in Hil, Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros j Hj. apply Hnone. unfold SCT. lia. }
  pose proof (ranges_apart_x_sound RSEGS E M (kn cs) gb (gk + 16) (ELit 8) sb (sk - 3) (mkAlu ALU_ADD strideE (ELit (-1))) HKN Hap) as Hdisj.
  unfold estart in Hdisj. cbn [a_base a_off] in Hdisj. rewrite elenZ_lit in Hdisj. change (8 mod 2 ^ 64) with 8 in Hdisj.
  assert (Elm1 : elenZ E (mkAlu ALU_ADD strideE (ELit (-1))) = stride - 1).
  { unfold elenZ. rewrite mkAlu_denot, alu_add, Estr. cbn [edenot]. unfold v_add. rewrite (u64_lit stride) by lia.
    rewrite (Z_to_bv_unsigned 64 (-1)), bv_wrap64_mod. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace (stride + (2 ^ 64 - 1)) with ((stride - 1) + 1 * 2 ^ 64) by lia.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite Elm1 in Hdisj.
  destruct (ealign_sound RSEGS E M (kn cs) start HKN) as [Heal Hdiv]. rewrite Ust in Hdiv.
  assert (Hst16 : st mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) start - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  set (off := enframe_off (slack_of stride n) ((if bv_unsigned b3 =? 0 then bv_unsigned c13 else o16 + 1) mod 256)).
  assert (EF : efH M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off).
  { constructor.
    - symmetry. exact Hss_stride.
    - unfold slot_start, UNIT. lia.
    - reflexivity.
    - exact Hg40.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros Hd. exfalso. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite RM. subst M0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite RW. subst W. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact R4.
    - rewrite Z_to_bv_bv_unsigned. exact HM3.
    - intros _. rewrite Hbs2. subst o16. rewrite word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
    - exact OK3.
    - exact TBL. }
  pose proof (off_facts M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF) as (Ooff & O255 & O16 & Oslack).
  assert (R12' : getr R (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 n) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (enframe_run M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF R (seg_rom RSEGS) (Z_to_bv 64 ret)
              R1 Hrok R10' R11 R12' eq_refl) as (R' & Hms & Hkeeps & HA0).
  pose proof (post_memF M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF) as POST.
  set (MF := memF M 0 n stride st off) in *.
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_enframe INFOUB)) with (0x18e44%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |]. clear Hms.
  (* [comment removed for export] *)
  assert (Hslack : slack_of stride n <= shs).
  { subst shs shi. unfold slack_of, IB, UNIT. apply Z.div_le_mono; lia. }
  set (offw := (Z_to_bv 64 off : word)).
  set (E1 := ext1 E v offw).
  assert (Hag1 : env_agree v E E1) by (subst E1; apply ext1_agree).
  assert (HC1 : cs_ok E1 cs1 R M model) by (subst E1 cs1 v; apply cs_ok_bump1; [exact HC | exact Hfresh]).
  assert (Hnx1 : s_next (c_ss cs1) = S v) by (subst cs1; cbn [bump_next c_ss s_next]; subst v; apply Nat.add_1_r).
  assert (Eoffe : edenot E1 offe = offw) by (subst E1 offe; apply ext1_at).
  assert (Estart1 : edenot E1 start = Z_to_bv 64 st).
  { rewrite <- (edenot_agree v E E1 start Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvs). exact Est. }
  assert (Ene1 : edenot E1 ne = nw).
  { rewrite <- (edenot_agree v E E1 ne Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvn). reflexivity. }
  assert (Estr1 : edenot E1 strideE = Z_to_bv 64 stride).
  { rewrite <- (edenot_agree v E E1 strideE Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvstr). exact Estr. }
  assert (EWe1 : edenot E1 We = edenot E We).
  { symmetry. apply (edenot_agree v E E1 We Hag1). rewrite <- expr_vars_lt_eq. exact HvW. }
  assert (Esb1 : edenot E1 sb = edenot E sb).
  { symmetry. apply (edenot_agree v E E1 sb Hag1). rewrite <- expr_vars_lt_eq. eapply split_lit_vars; [exact Hss | exact Hvs]. }
  assert (Hoffw : bv_unsigned offw = off) by (subst offw; apply u64_lit; lia).
  assert (Etimes : edenot E1 (times16 offe) = Z_to_bv 64 (16 * off)) by (rewrite times16_denot, Eoffe, Hoffw; reflexivity).
  assert (Ep1 : edenot E1 p = Z_to_bv 64 (st + 16 * off)).
  { subst p. rewrite mkAlu_denot, alu_add, Estart1, Etimes. unfold v_add. rewrite !u64_lit by lia. reflexivity. }
  assert (Epn1 : edenot E1 pn = Z_to_bv 64 (st + 16 * off + n)).
  { subst pn. rewrite mkAlu_denot, alu_add, Ep1, Ene1. unfold v_add. rewrite u64_lit by lia. reflexivity. }
  assert (Elen1 : elenZ E1 len1 = 16 * off + 3).
  { unfold elenZ. subst len1. rewrite mkAlu_denot, alu_add, Etimes. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (16 * off)), (u64_lit 3) by lia. apply u64_lit. lia. }
  assert (Hn_eq : bv_unsigned nw = n) by reflexivity.
  assert (Erexp : edenot E1 rexp = Z_to_bv 64 (stride - n - 16 * off)).
  { subst rexp. rewrite mkAlu_denot, alu_sub, Estr1. rewrite mkAlu_denot, alu_add, Ene1, Etimes.
    unfold v_sub, v_add. rewrite (u64_lit (16 * off)), (u64_lit stride), Hn_eq by lia.
    rewrite (u64_lit (n + 16 * off)) by lia. f_equal. lia. }
  assert (Elen2 : elenZ E1 len2 = stride - 4 - n - 16 * off).
  { unfold elenZ. subst len2. rewrite mkAlu_denot, alu_add, Erexp. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (stride - n - 16 * off)) by lia. rewrite (Z_to_bv_unsigned 64 (-4)), bv_wrap64_mod. change ((-4) mod 2 ^ 64) with (2 ^ 64 - 4).
    replace (stride - n - 16 * off + (2 ^ 64 - 4)) with ((stride - 4 - n - 16 * off) + 1 * 2 ^ 64) by lia.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z_mod_plus_full. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E1 M (kn cs)) by exact (co_know _ _ _ _ _ HC1).
  assert (HSL1 : slots_ok E1 M (c_slots cs)) by exact (co_slots _ _ _ _ _ HC1).
  assert (Hkf : know_ok RSEGS E1 M kf).
  { subst kf. apply Forall_cons; [|apply Forall_one]; cbn [kentry_ok].
    - rewrite Eoffe, Hoffw. lia.
    - rewrite Erexp. rewrite u64_lit by lia. lia. }
  assert (K0 : know_ok RSEGS E1 M (kf ++ kn cs)) by (apply Forall_app; split; [exact Hkf | exact HK1]).
  assert (PB : bv_unsigned (edenot E1 pb) + pk = st + 16 * off).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pb pk 1 K0 Hflp) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 p pb pk Hsp) as X. rewrite Ep1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (PNB : bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pnb pnk 1 K0 Hflpn) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 pn pnb pnk Hspn) as X. rewrite Epn1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  (* [comment removed for export] *)
  assert (SLOT : slot_ok E1 MF s).
  { unfold slot_ok. subst s. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p]. rewrite Hss, Hsp.
    unfold uE. rewrite Estart1, Ene1, Eoffe, Ep1, Hn_eq, Hoffw, Estr1, EWe1. fold W.
    rewrite (u64_lit st), (u64_lit stride), (u64_lit (st + 16 * off)) by lia.
    rewrite Esb1.
    split; [exact POST|]. split; [reflexivity|]. split; [exact SB|]. split; [exact PB|].
    split; [symmetry; exact Hss_stride|]. split; [intros Hd; exfalso; lia|].
    pose proof (stride_mod16 Sv). fold stride in H. repeat split; lia. }
  subst cs' k1 k2.
  apply (enframe_core cs cs1 csa E E1 R R' M model T ret v (S v) p sb pnb len1 len2 strideE sk pnk (kf ++ kn cs) [] s
           0 stride st n off HK Hac HC1 HK1 HSL1 Hfresh eq_refl Hnx1); try assumption; try lia.
  4:{ split; [lia|]. cbv. reflexivity. }
  - rewrite Esb1. exact SB.
  - unfold elenZ. rewrite Estr1. apply u64_lit. lia.
  - constructor.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Theorem call_enframe2_ok : enframe2_sound_stmt nx0.
Proof.
  unfold enframe2_sound_stmt. intros FP cs cs' E R M model T HC Hpc Hn HK.
  unfold call_enframe2 in Hn.
  destruct (call_enframe RSEGS INFOUB nx0 cs) as [cs1|] eqn:H1.
  - injection Hn as <-. exact (call_enframe_ok FP cs cs1 E R M model T HC Hpc H1 HK).
  - exact (call_enframe_x_ok FP cs cs' E R M model T HC Hpc Hn HK).
Qed.

End NX0.
End UbSymPlanSoundEF.

Module UbSymPlanSoundSW.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition ref_stdio_write_stmt : Prop :=
  forall (FP : FPState) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x21000 <= f)%Z -> (f + 232 <= 0x51748)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     realizes RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst regs (0x19ae4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).

Section NX0.
Variable nx0 : nat.
Hypothesis REF : ref_stdio_write_stmt.

(* [comment removed for export] *)

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence.
Qed.

(* [comment removed for export] *)
Lemma know_ok_havoc3 : forall E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M k ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + elenZ E n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + elenZ E n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + elenZ E n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_havoc (kn_havoc (kn_havoc k b1 o1 n1) b2 o2 n2) b3 o3 n3)
  /\ (forall ss, slots_ok E M ss ->
        slots_ok E M' (slots_keep k b3 o3 n3 (slots_keep k b2 o2 n2 (slots_keep k b1 o1 n1 ss)))).
Proof.
  intros E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3 HK Hout Hg.
  set (a1 := estart E (SA b1 o1)). set (l1 := elenZ E n1).
  set (a2 := estart E (SA b2 o2)). set (l2 := elenZ E n2).
  set (a3 := estart E (SA b3 o3)). set (l3 := elenZ E n3).
  set (M1 := fun x : word => if (inr a2 l2 x || inr a3 l3 x)%bool then M x else M' x).
  set (M2 := fun x : word => if inr a3 l3 x then M x else M' x).
  assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + l1 <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 l2 x) eqn:E2; [reflexivity|]. destruct (inr a3 l3 x) eqn:E3; [reflexivity|].
    cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. unfold M1. destruct (inr a2 l2 x || inr a3 l3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
  assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + l2 <= bv_unsigned x)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a3 l3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
    destruct (inr a2 l2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a3 l3 x); [rewrite orb_true_r in Hx; exact Hx|].
    destruct (inr a2 l2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
  assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + l3 <= bv_unsigned x)%Z -> M' x = M2 x).
  { intros x Hx. unfold M2. destruct (inr a3 l3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
  assert (G3 : mem_grows M2 M').
  { intros x Hx. unfold M2 in Hx. destruct (inr a3 l3 x); [exact (Hg x Hx) | exact Hx]. }
  split.
  - eapply know_ok_havoc; [| exact O3 | exact G3].
    eapply know_ok_havoc; [| exact O2 | exact G2].
    eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
  - intros ss HS.
    eapply (slots_keep_sound E M k); [exact HK | | exact O3].
    eapply (slots_keep_sound E M k); [exact HK | | exact O2].
    eapply (slots_keep_sound E M k); [exact HK | exact HS | exact O1].
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

(* [comment removed for export] *)

Lemma kept_regs : forall (R R' : bvmap 5 word),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r.
Proof.
  intros R R' Hk r Hr0 Hn.
  pose proof (kept_of_not_caller_saved r
    (map (fun k => Z_to_bv 5 (Z.of_nat k)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat)
    ltac:(intros k Hin; apply (in_map (fun k : nat => Z_to_bv 5 (Z.of_nat k))); exact Hin) Hr0 Hn) as Hin.
  apply in_map_iff in Hin as (k & <- & Hin). apply Hk. exact Hin.
Qed.

Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.

Lemma adenot_abs0 : forall E off, adenot E (SA (ELit 0) off) = Z_to_bv 64 off.
Proof. intros E off. rewrite adenot_SA, u_lit0. f_equal. Qed.

(* [comment removed for export] *)

Theorem node_stdio_write_sound' : stdio_write_sound_stmt nx0.
Proof.
  unfold stdio_write_sound_stmt.
  intros FP cs cs' fd bs E R M model T HC Hpc Hn HT HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold node_stdio_write in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 10) as [f|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [l|] eqn:H12; [|discriminate].
  destruct (negb (Z.eqb f (d_stdout INFOUB))) eqn:Hf; [discriminate|].
  apply negb_false_iff in Hf. apply Z.eqb_eq in Hf. change (d_stdout INFOUB) with 0x21288%Z in Hf.
  change (d_canary_got INFOUB) with 0x20158%Z in Hn. change (d_canary INFOUB) with 0x51748%Z in Hn.
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 120) 4) as [fd'|] eqn:Hfd; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (f + 88)) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (f + 96)) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) 0x20158 8) as [cg|] eqn:Hcg; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0x51748) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hss.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-112))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (kread_bytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
  destruct (kread_bytes RSEGS (Z.to_nat l) (kn cs) sb sk) as [extra|] eqn:Hextra; [|discriminate].
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (ehi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kimg_cut (kn cs) (f + 32) 16) (f + 56) 8) in Hn.
  set (k1 := kn_havoc k0 qb qk (ELit 112)) in Hn.
  set (k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16)) in Hn.
  set (k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8)) in Hn.
  set (k4 := KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
             :: KWord (SA (ELit 0) (f + 40)) 8 bufp :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3) in Hn.
  destruct (after_call nx0 cs ret (Some (ELit l)) k4) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some (?a, ?b, ?c) = Some (fd, bs, cs') =>
    assert (Efd : fd = a) by congruence; assert (Ebs : bs = b) by congruence; assert (Ecs : cs' = c) by congruence end.
  clear Hn. subst fd bs.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hds]. apply andb_prop in Hcond as [Hcond Hdw].
  apply andb_prop in Hcond as [Hcond Hfls]. apply andb_prop in Hcond as [Hcond Hsl64].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hcg8]. apply andb_prop in Hcond as [Hcond Hcg0].
  apply andb_prop in Hcond as [Hcond Hcan8]. apply andb_prop in Hcond as [Hcond Hf232]. apply andb_prop in Hcond as [Hcond Hf0].
  apply andb_prop in Hcond as [Hcond Hmax]. apply andb_prop in Hcond as [Hcond Hnp0].
  apply andb_prop in Hcond as [Hfd1 Hcgv].
  apply Z.eqb_eq in Hfd1. subst fd'. apply Z.eqb_eq in Hcgv.
  apply Z.leb_le in Hnp0. apply Z.leb_le in Hmax. apply Z.leb_le in Hf0. apply Z.leb_le in Hf232.
  apply andb_prop in Hsl64 as [Hsl64 Hwp47]. apply Z.leb_le in Hwp47.
  apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'. apply Z.leb_le in Hsl64.
  clear Hcan8 Hcg0 Hcg8.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 10 f HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 12 l HC ltac:(lia) H12) as [R12 Hlr]. unfold two64 in Hlr.
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in R12 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  set (s := edenot E (reg cs 11)) in *.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hshi) as Hshi2. fold s in Hshi2.
  pose proof (u64_range s) as Hsr. pose proof (u64_range sp) as Hspr. fold su in Hspr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 112)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 112 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 112)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  assert (FL8 : forall off, (0 <= off)%Z -> (off + 8 <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) 8).
  { intros off A B. apply flat_abs0; lia. }
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 120) 4 1 HKN Hfd ltac:(lia) ltac:(apply flat_abs0; lia)) as [Rfd _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 40) 8 wp HKN Hwp ltac:(lia) ltac:(apply FL8; lia)) as [Rwp Hwpr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 56) 8 wb HKN Hwb ltac:(lia) ltac:(apply FL8; lia)) as [Rwb Hwbr].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (f + 88) bufp HKN Hbufp ltac:(apply FL8; lia)) as Rbufp.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (f + 96) bufsz HKN Hbufsz ltac:(apply FL8; lia)) as Rbufsz.
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0x20158 8 cg HKN Hcg ltac:(lia) ltac:(apply FL8; lia)) as [Rcg _].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0x51748 canv HKN Hcan ltac:(apply FL8; lia)) as Rcan.
  rewrite adenot_abs0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan. unfold two64 in Hwpr, Hwbr.
  (* [comment removed for export] *)
  destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat (wp - wb)) (ELit 0) wb pend HKN Hpend
              ltac:(rewrite u_lit0; lia) ltac:(rewrite u_lit0; lia)) as [Rpend Lpend].
  rewrite u_lit0, Z.add_0_l in Rpend.
  pose proof (flat_b_sound E M (kn cs) sb sk (Z.max l 1) HKN Hfls) as Hfl. unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl.
  destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat l) sb sk extra HKN Hextra ltac:(lia) ltac:(lia)) as [Rextra Lextra].
  pose proof (split_lit_denot E (reg cs 11) sb sk Hss) as Hsd. fold s in Hsd.
  assert (Hsu : bv_unsigned s = (bv_unsigned (edenot E sb) + sk)%Z) by (rewrite Hsd, u64_lit by lia; reflexivity).
  rewrite <- Hsu, Z_to_bv_bv_unsigned in Rextra.
  (* [comment removed for export] *)
  assert (Dw : (wp <= su - 112 \/ su <= wb)%Z).
  { apply orb_prop in Hdw as [Hx|Hx]; apply (lin_ge0_sound RSEGS E M (kn cs)) in Hx; [|exact HKN| |exact HKN];
      cbn [xt_den edenot] in Hx; rewrite ?u64_lit in Hx by lia; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold sp su in Hx; lia. }
  assert (Ds : (bv_unsigned s + l <= su - 112 \/ su <= bv_unsigned s)%Z).
  { apply orb_prop in Hds as [Hx|Hx]; apply (lin_ge0_sound RSEGS E M (kn cs)) in Hx; [|exact HKN| |exact HKN];
      cbn [xt_den] in Hx; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold s sp su in Hx; lia. }
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_stdio_write INFOUB)) with (0x19ae4%bv : word) by (apply bv_eq; reflexivity).
  rewrite Wz_map, map_app.
  eapply (REF FP R M model su f wb wp 1 s (Z_to_bv 64 l) (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            (map (fun z => Z_to_bv 8 z) pend) (map (fun z => Z_to_bv 8 z) extra) T).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst.
  - lia.
  - lia.
  - constructor; [exact Rwp | exact Rwb | exact Rfd | exact Rbufp | exact Rbufsz].
  - split; [rewrite Rcg, Hcgv; reflexivity | exact Rcan].
  - lia.
  - apply fd_lookup_std1. exact (co_fds _ _ _ _ _ HC).
  - exact (co_halt _ _ _ _ _ HC).
  - exact (co_lazy _ _ _ _ _ HC).
  - lia.
  - lia.
  - rewrite length_map, Lpend. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite length_map, Lextra, u64_lit by lia. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite !length_map, Lpend, Lextra, !Z2Nat.id by lia. pose proof rw_bytes_max_ge17. lia.
  - rewrite !length_map, Lpend, Lextra, !Z2Nat.id by lia. lia.
  - exact Dw.
  - rewrite u64_lit by lia. exact Ds.
  - rewrite u64_lit by lia. lia.
  - rewrite length_map, Lpend. exact Rpend.
  - rewrite length_map, Lextra. exact Rextra.
  - exact Hrok.
  - exact HT.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply Nat.leb_le in Hnx0.
    set (nx := s_next (c_ss cs)) in *.
    pose proof (ext_call_agree E nx R') as Hag.
    destruct (after_call_sound nx0 cs ret (Some (ELit l)) k4 csa E R R' M M' model
                (slots_keep (kn cs) (ELit 0) (f + 56) (ELit 8)
                   (slots_keep (kn cs) (ELit 0) (f + 32) (ELit 16)
                      (slots_keep (kn cs) qb qk (ELit 112) (c_slots cs)))) Hac HC) as [HC' Hpc'].
    + (* [comment removed for export] *)
      apply kept_regs. intros kk Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
          first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
        end.
    + (* [comment removed for export] *)
      replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. cbn [edenot]. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, HKN).
      destruct (know_ok_havoc3 E M M' k0 qb qk (ELit 112) (ELit 0) (f + 32) (ELit 16) (ELit 0) (f + 56) (ELit 8) HK0) as [HK3 _].
      { intros x N1 N2 N3. apply Pagree.
        - unfold estart in N1. cbn [a_base a_off] in N1. rewrite Hq, elenZ_lit in N1 by lia. lia.
        - unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0, elenZ_lit in N2 by lia. lia.
        - unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0, elenZ_lit in N3 by lia. lia. }
      { exact Pgrows. }
      subst k4 k3 k2 k1.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL8; lia|]); rewrite adenot_abs0.
      * rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. exact Pwend.
      * exact Pwpos.
      * exact Pwbase.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      destruct (know_ok_havoc3 E M M' (kn cs) qb qk (ELit 112) (ELit 0) (f + 32) (ELit 16) (ELit 0) (f + 56) (ELit 8) HKN) as [_ HS3].
      { intros x N1 N2 N3. apply Pagree.
        - unfold estart in N1. cbn [a_base a_off] in N1. rewrite Hq, elenZ_lit in N1 by lia. lia.
        - unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0, elenZ_lit in N2 by lia. lia.
        - unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0, elenZ_lit in N3 by lia. lia. }
      { exact Pgrows. }
      apply HS3. exact HSL.
    + (* [comment removed for export] *)
      apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
    + (* [comment removed for export] *)
      subst cs'. specialize (HK (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact Hnx0]) HC').
      rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem node_stdio_write_ok : stdio_write_sound_stmt nx0.
Proof. exact node_stdio_write_sound'. Qed.

End NX0.
End UbSymPlanSoundSW.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require StreamSim FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbPrintfBufBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymAux RefPrintfLib.

Module UbPrintfBuf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymAux OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefPrintfLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPrintfBufBase.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Definition pf_stops : list Z := [0x12e94].
Definition pf_fuel : nat := 3000.

(* [comment removed for export] *)
Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0x21288, 4); (SA (ELit 0) 0x212b0, 8); (SA (EVar 1) 0, 2)].

(* [comment removed for export] *)
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x12f40) mem rom) (mkst regs' (Z_to_bv 64 0x12e94) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x21288, 4);
                          (Z_to_bv 64 0x212b0, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x212b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x21288) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x12e94.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
  Proof.
    intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
    change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x12f40 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x12e94 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0x212b0 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0x21288 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    destruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x12f40 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
    exists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x21288, 4);
               (Z_to_bv 64 0x212b0, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) pf_regions).
      2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
    - pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_var1 in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + rewrite Z.add_0_r in B0. apply B0.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
      + rewrite u64_lit by lia. apply B1.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x212b0 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x21288 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.
End WithFP1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP2. Context {FP : PropExec.FPState}.
Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x12f40 pf_sr [] pf_kn 40) [].

(* [comment removed for export] *)
Definition dirsA : list bool := [true; false; false; true; false].  (* [comment removed for export] *)
Definition dirsB : list bool := [false; true; true; true; true].    (* [comment removed for export] *)

Definition dirsC : list bool := [false; true; true; true; false].   (* [comment removed for export] *)
Definition dirsD : list bool := [false; true; true; false; false].  (* [comment removed for export] *)

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).
End WithFP2.


(* [comment removed for export] *)
Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.

Section WithFP3. Context {FP : PropExec.FPState}.
Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x12e94 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.

Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x12e94 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.

Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x12e94 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.

Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x12e94 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x12e94 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x12f40) mem rom) (mkst regs' (Z_to_bv 64 0x12e94) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x21288, 4);
                          (Z_to_bv 64 0x212b0, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x212b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x21288) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.
End WithFP3.


End UbPrintfBuf.

Module UbSymPlanSoundPF.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPrintfBufBase UbPrintfBuf.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH UbSymPlanSoundSW.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rng_lo (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => estart E (SA b o) end.
Definition rng_len (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => elenZ E n end.

Fixpoint inrs (E : env) (rs : list (expr * Z * expr)) (x : word) : bool :=
  match rs with
  | [] => false
  | r :: rest => inr (rng_lo E r) (rng_len E r) x || inrs E rest x
  end.

(* [comment removed for export] *)
Fixpoint slots_keeps (k : list kentry) (rs : list (expr * Z * expr)) (ss : list sslot) : list sslot :=
  match rs with
  | [] => ss
  | (b, o, n) :: rest => slots_keeps k rest (slots_keep k b o n ss)
  end.

(* [comment removed for export] *)
Lemma know_ok_memeq : forall E M M' k,
  (forall x : word, M' x = M x) -> know_ok RSEGS E M k -> know_ok RSEGS E M' k.
Proof.
  intros E M M' k EQ HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  eapply (kentry_keep_sem E M M' K (match kfoot E K with Some (s, l) => s + l | None => 0 end) 0);
    [exact HKK | unfold kfoot_apart; destruct (kfoot E K) as [[s l]|]; [lia | exact I] | intros x _; apply EQ].
Qed.

Lemma slots_ok_memeq : forall E M M' ss,
  (forall x : word, M' x = M x) -> slots_ok E M ss -> slots_ok E M' ss.
Proof.
  intros E M M' ss EQ HS. unfold slots_ok in *. apply Forall_forall. intros s Hin.
  eapply slot_ok_agree; [exact (proj1 (Forall_forall _ _) HS s Hin) | intros x _ _; apply EQ].
Qed.

(* [comment removed for export] *)
Lemma havocs_frame : forall E rs M0 k0 M M',
  know_ok RSEGS E M0 k0 ->
  (forall x : word, inrs E rs x = false -> M' x = M x) ->
  mem_grows M M' ->
  (forall k, know_ok RSEGS E M k -> know_ok RSEGS E M' (kn_havocs k rs))
  /\ (forall ss, slots_ok E M ss -> slots_ok E M' (slots_keeps k0 rs ss)).
Proof.
  intros E rs M0 k0. induction rs as [|[[b o] n] rest IH]; intros M M' HK0 Hout Hg.
  - assert (EQ : forall x, M' x = M x) by (intros x; apply Hout; reflexivity).
    split; [intros k HK; cbn [kn_havocs]; eapply know_ok_memeq; eassumption
          | intros ss HS; cbn [slots_keeps]; eapply slots_ok_memeq; eassumption].
  - set (a := estart E (SA b o)). set (l := elenZ E n).
    set (M1 := fun x : word => if inrs E rest x then M x else M' x).
    assert (O1 : forall x : word, (bv_unsigned x < a \/ a + l <= bv_unsigned x)%Z -> M1 x = M x).
    { intros x Hx. unfold M1. destruct (inrs E rest x) eqn:Er; [reflexivity|].
      apply Hout. cbn [inrs]. rewrite Er, orb_false_r. apply inr_false. unfold rng_lo, rng_len. fold a l. lia. }
    assert (G1 : mem_grows M M1).
    { intros x Hx. unfold M1. destruct (inrs E rest x); [exact Hx | exact (Hg x Hx)]. }
    assert (O2 : forall x : word, inrs E rest x = false -> M' x = M1 x).
    { intros x Hx. unfold M1. rewrite Hx. reflexivity. }
    assert (G2 : mem_grows M1 M').
    { intros x Hx. unfold M1 in Hx. destruct (inrs E rest x); [exact (Hg x Hx) | exact Hx]. }
    destruct (IH M1 M' HK0 O2 G2) as [IHk IHs].
    split.
    + intros k HK. cbn [kn_havocs]. apply IHk. eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
    + intros ss HS. cbn [slots_keeps]. apply IHs. eapply (slots_keep_sound E M0 k0); [exact HK0 | exact HS | exact O1].
Qed.

(* [comment removed for export] *)
Lemma outside_of_inrs : forall E rs (regs : list (word * Z)) x,
  Forall2 (fun r g => bv_unsigned (fst g) = rng_lo E r /\ snd g = rng_len E r /\ 0 <= rng_lo E r /\ rng_lo E r + rng_len E r <= 2 ^ 64) rs regs ->
  inrs E rs x = false -> outside x regs.
Proof.
  intros E rs regs x HF. induction HF as [|r [gb gn] rs' regs' (H1 & H2 & H3 & H4) HF IH]; intros Hin; cbn [outside]; [exact I|].
  cbn [inrs] in Hin. apply Bool.orb_false_iff in Hin as [Hr Hrest]. cbn [fst snd] in H1, H2.
  split; [| apply IH; exact Hrest].
  apply inr_false in Hr. unfold in_rng. subst gn. rewrite H1. lia.
Qed.

(* [comment removed for export] *)

Lemma w2b2_0a30 : forall E, word_to_le_bytes 2 (edenot E (ELit 0x0a30)) = [Z_to_bv 8 0x30; Z_to_bv 8 0x0a].
Proof.
  intros E. cbn [edenot]. unfold word_to_le_bytes. rewrite u64_lit by lia. cbn [Z_to_le_bytes].
  f_equal; apply bv_eq; reflexivity.
Qed.

Lemma rdn_split2 : forall M (a : Z) b0 b1,
  0 <= a -> a + 2 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) 2 = Some [b0; b1] ->
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [b0] /\ rdn RSEGS M (Z_to_bv 64 (a + 1)) 1 = Some [b1].
Proof.
  intros M a b0 b1 Ha Ha2 H. cbn [rdn] in *.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [x|]; [|discriminate].
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1) : word) in H.
  2:{ apply bv_eq. rewrite (u_add1 (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite !u64_lit by lia. reflexivity. }
  destruct (match M (Z_to_bv 64 (a + 1)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + 1)) end) as [y|]; [|discriminate].
  injection H as <- <-. split; reflexivity.
Qed.

Section NX0.
Variable nx0 : nat.

(* [comment removed for export] *)

Theorem call_printf_sound' : printf_sound_stmt nx0.
Proof.
  unfold printf_sound_stmt.
  intros FP cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_printf in Hn.
  change (d_stdout INFOUB) with 0x21288%Z in Hn. change (d_stdout_buf INFOUB) with 0x51bb0%Z in Hn.
  change (d_canary INFOUB) with 0x51748%Z in Hn. change (t_printf_ret INFOUB) with 0x12e94%Z in Hn.
  change (d_data_lo INFOUB) with 0x21000%Z in Hn. change (d_sp_lo INFOUB) with 0x52420%Z in Hn.
  change (- PF_WIN)%Z with (-1056)%Z in Hn. unfold PF_WIN in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [[|p11|p11]|] eqn:H11; try discriminate.
  destruct (negb (Z.eqb ret 0x12e94)) eqn:Hreq; [discriminate|].
  apply negb_false_iff in Hreq. apply Z.eqb_eq in Hreq. subst ret.
  destruct (kreadZ RSEGS (kn cs) (ELit 0) 0x21288 4) as [flags|] eqn:Hflags; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 32) 8) as [wend|] eqn:Hwend; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 40) 8) as [w|] eqn:Hw; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 144) 4) as [lbf|] eqn:Hlbf; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0x51748) as [canv|] eqn:Hcan; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-1056))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kimg_cut (kimg_cut (kn cs) 0x21288 4) (0x21288 + 40) 8) w 2) in Hn.
  set (k4 := kn_havoc (kn_havoc (kn_havoc (kn_havoc k0 qb qk (ELit 1056)) (ELit 0) 0x21288 (ELit 4))
                        (ELit 0) (0x21288 + 40) (ELit 8)) (ELit 0) w (ELit 2)) in Hn.
  set (k5 := KWord (SA (ELit 0) 0x21288) 4 (ELit 5)
             :: KWord (SA (ELit 0) (0x21288 + 40)) 8 (ELit (w + 2))
             :: KWord (SA (ELit 0) w) 2 (ELit 0x0a30) :: k4) in Hn.
  destruct (after_call nx0 cs 0x12e94 None k5) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?c = Some cs' => assert (Ecs : cs' = c) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond Heal]. apply andb_prop in Hcond as [Hcond Himg].
  apply andb_prop in Hcond as [Hcond Hlbf']. apply andb_prop in Hcond as [Hcond Hlock']. apply andb_prop in Hcond as [Hcond Hbsz'].
  apply andb_prop in Hcond as [Hcond Hwhi]. apply andb_prop in Hcond as [Hcond Hwlo]. apply andb_prop in Hcond as [Hflags' Hwend'].
  apply Z.eqb_eq in Hflags'. apply Z.eqb_eq in Hwend'. apply Z.leb_le in Hwlo. apply Z.leb_le in Hwhi. apply Z.eqb_eq in Hbsz'.
  apply Z.eqb_eq in Hlock'. apply Z.eqb_eq in Hlbf'. apply Z.leb_le in Heal. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  subst flags wend bsz lock lbf.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model 0x12e94 HC Hret) as (R1 & Hrok & _).
  destruct (reg_lit_sound E cs R M model 11 0 HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 1056)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 1056 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 1056)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) (reg cs 2) HKN) as [Heal0 Hdiv]. fold sp in Hdiv. fold su in Hdiv.
  assert (Hsu16 : su mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) (reg cs 2) - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C D. apply flat_abs0; lia. }
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0x21288 4 5 HKN Hflags ltac:(lia) ltac:(apply FL; lia)) as [Rflags _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 32) 8 _ HKN Hwend ltac:(lia) ltac:(apply FL; lia)) as [Rwend _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 40) 8 w HKN Hw ltac:(lia) ltac:(apply FL; lia)) as [Rw Hwr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 96) 8 _ HKN Hbsz ltac:(lia) ltac:(apply FL; lia)) as [Rbsz _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 140) 4 _ HKN Hlock ltac:(lia) ltac:(apply FL; lia)) as [Rlock _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 144) 4 _ HKN Hlbf ltac:(lia) ltac:(apply FL; lia)) as [Rlbf _].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0x51748 canv HKN Hcan ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_abs0 in Rflags, Rwend, Rw, Rbsz, Rlock, Rlbf, Rcan.
  (* [comment removed for export] *)
  assert (IMG : forall i, 0x10000 <= i < 0x21000 -> M (Z_to_bv 64 i) = None).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  assert (PH : pfH M sp w (bv_unsigned (edenot E canv))).
  { constructor.
    - exact Hsu16.
    - lia.
    - lia.
    - unfold SymRun.stk_ok, PF_FR. intros a n Ha Hn.
      eapply (store_ok_sub RSEGS M (Z_to_bv 64 (su - 1056)) a (Z.to_nat 1056) n);
        rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia. exact Wst.
    - exact IMG.
    - exact Rflags.
    - exact Rwend.
    - exact Rw.
    - lia.
    - exact Rbsz.
    - exact Rlock.
    - exact Rlbf.
    - rewrite Z_to_bv_bv_unsigned. exact Rcan.
    - apply u64_range. }
  destruct (printf0_buffered R M (seg_rom RSEGS) sp w (bv_unsigned (edenot E canv)) PH R1 ltac:(exact R2) R11)
    as (R' & M' & Hms & Hkeeps & Hframe & Bw & Bwpos & Bflags).
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. change (t_printf INFOUB) with 0x12f40%Z.
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply Nat.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  pose proof (ext_call_agree E nx R') as Hag.
  destruct Hframe as [Hout Hgrows].
  set (rs := [(qb, qk, ELit 1056); (ELit 0, 0x21288%Z, ELit 4); (ELit 0, (0x21288 + 40)%Z, ELit 8); (ELit 0, w, ELit 2)]).
  assert (HOUT : forall x : word, inrs E rs x = false -> M' x = M x).
  { intros x Hx. apply Hout. eapply (outside_of_inrs E rs); [|exact Hx]. subst rs.
    repeat apply Forall2_cons; try apply Forall2_nil; unfold rng_lo, rng_len, estart; cbn [fst snd a_base a_off edenot];
      rewrite ?Hq; unfold elenZ; cbn [edenot]; rewrite !u64_lit by lia; lia. }
  destruct (havocs_frame E rs M (kn cs) M M' HKN HOUT Hgrows) as [HKV HSV].
  destruct (after_call_sound nx0 cs 0x12e94 None k5 csa E R R' M M' model
              (slots_keep (kn cs) (ELit 0) w (ELit 2)
                 (slots_keep (kn cs) (ELit 0) (0x21288 + 40) (ELit 8)
                    (slots_keep (kn cs) (ELit 0) 0x21288 (ELit 4)
                       (slots_keep (kn cs) qb qk (ELit 1056) (c_slots cs))))) Hac HC) as [HC' Hpc'].
  - (* [comment removed for export] *)
    apply kept_regs. intros kk Hin.
    assert (KEPT : forall r : bv 5, In r RefMemcpyLib.callee_saved -> getr R' r = getr R r) by exact Hkeeps.
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      (apply KEPT; unfold RefMemcpyLib.callee_saved; cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end).
  - exact I.
  - (* [comment removed for export] *)
    assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, kimg_cut_sound, HKN).
    pose proof (HKV k0 HK0) as HK4. change (kn_havocs k0 rs) with k4 in HK4.
    subst k5.
    pose proof (rdn_split2 M' w _ _ ltac:(lia) ltac:(lia) Bw) as [B0 B1].
    repeat apply Forall_cons; [ | | | exact HK4]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL; lia|]); rewrite adenot_abs0.
    + exact Bflags.
    + cbn [edenot]. exact Bwpos.
    + rewrite w2b2_0a30. exact Bw.
  - (* [comment removed for export] *)
    pose proof (HSV (c_slots cs) HSL) as HS4. exact HS4.
  - (* [comment removed for export] *)
    apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
  - (* [comment removed for export] *)
    subst cs'. specialize (HK (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact Hnx0]) HC').
    rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem call_printf_ok : printf_sound_stmt nx0.
Proof. exact call_printf_sound'. Qed.

End NX0.
End UbSymPlanSoundPF.

Module UbSymPlanSoundFZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH UbSymPlanSoundSW UbSymPlanSoundPF.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rsegs_ranges :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) RSEGS
  = [(0x10000, 0x2000); (0x12000, 0x00e000); (0x20000, 0x1000); (0x21000, 0x31000)]%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rsegs_inside : forall i, (i < 0x10000 \/ 0x52000 <= i)%Z ->
  Forall (fun seg => (i < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= i)%Z) RSEGS.
Proof.
  intros i Hi. apply Forall_forall. intros seg Hin.
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) RSEGS seg Hin) as H.
  rewrite rsegs_ranges in H. cbn [In] in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as E1 E2; rewrite <- E1, <- E2; lia.
Qed.

(* [comment removed for export] *)
Lemma gfool_store_ok : forall M, store_ok RSEGS M (Z_to_bv 64 (fa_gfool infoub_abi)) 4 = true.
Proof. intros M. apply store_ok_wseg. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_rom_defined : forall M (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall j, (j < n)%nat -> seg_rom RSEGS (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None) ->
  exists bs, rdn RSEGS M a n = Some bs.
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a Hnw Hrom.
  - exists []. reflexivity.
  - cbn [rdn].
    assert (Hb : exists b, match M a with Some b => Some b | None => seg_rom RSEGS a end = Some b).
    { destruct (M a) as [b|]; [exists b; reflexivity|].
      pose proof (Hrom 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
      destruct (seg_rom RSEGS a) as [b|]; [exists b; reflexivity | exfalso; apply H0; reflexivity]. }
    destruct Hb as [b ->].
    destruct n as [|n'].
    + exists [b]. reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn in Hnw; lia).
      destruct (IH (a + 1)%bv ltac:(rewrite Hu1; lia)) as [bs Hbs].
      { intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
        apply Hrom. lia. }
      rewrite Hbs. exists (b :: bs). reflexivity.
Qed.

Lemma gfool_rdn : forall M, exists gb, rdn RSEGS M (Z_to_bv 64 (fa_gfool infoub_abi)) 4 = Some gb.
Proof.
  intros M. apply rdn_rom_defined; [cbn [fa_gfool infoub_abi]; rewrite u64_lit by lia; cbn; lia|].
  intros j Hj. cbn [fa_gfool infoub_abi]. rewrite u64_lit by lia.
  destruct j as [|[|[|[|j]]]]; [ | | | | lia];
    lazymatch goal with |- seg_rom _ ?a <> None => let v := eval vm_compute in (seg_rom RSEGS a) in change (v <> None) end;
    discriminate.
Qed.

(* [comment removed for export] *)

Definition mem_bytes (M : word -> option byte) (a : Z) (n : nat) : list byte :=
  map (fun j => match M (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n).

Lemma mem_bytes_length : forall M a n, length (mem_bytes M a n) = n.
Proof. intros. unfold mem_bytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma mem_bytes_nth : forall M a n i, (0 <= i < Z.of_nat n)%Z ->
  M (Z_to_bv 64 (a + i)) <> None ->
  M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) (mem_bytes M a n) (Z_to_bv 8 0)).
Proof.
  intros M a n i Hi Hdef. unfold mem_bytes.
  set (f := fun j : nat => match M (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
  rewrite (nth_indep _ (Z_to_bv 8 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth. rewrite seq_nth by lia. subst f. cbv beta. rewrite Nat.add_0_l, Z2Nat.id by lia.
  destruct (M (Z_to_bv 64 (a + i))) as [b|]; [reflexivity | exfalso; apply Hdef; reflexivity].
Qed.

(* [comment removed for export] *)

Section NX0.
Variable nx0 : nat.
Hypothesis LIB : fuzz_contract RSEGS infoub_abi.

Theorem call_fuzz_sound' : fuzz_sound_stmt nx0.
Proof.
  unfold fuzz_sound_stmt.
  intros FP cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_fuzz in Hn.
  change (t_fuzz_depth INFOUB) with 1824%Z in Hn. change (d_gfool INFOUB) with 0x31400%Z in Hn.
  change (t_fuzz_ret INFOUB) with 0x12e84%Z in Hn. change (d_empty INFOUB) with 0x313e0%Z in Hn.
  change (d_img_hi INFOUB) with 0x52000%Z in Hn. change (d_fuzz_ro_lo INFOUB) with 0x103ec%Z in Hn.
  change (d_fuzz_ro_hi INFOUB) with 0x10490%Z in Hn. change (- (1824))%Z with (-1824)%Z in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (ehi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (negb (Z.eqb ret 0x12e84)) eqn:Hreq; [discriminate|].
  apply negb_false_iff in Hreq. apply Z.eqb_eq in Hreq. subst ret.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-1824))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (elo (kn cs) (reg cs 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kn cs) 0x31400 4) in Hn.
  set (k2 := kn_havoc (kn_havoc k0 qb qk (ELit 1824)) (ELit 0) 0x31400 (ELit 4)) in Hn.
  destruct (after_call nx0 cs 0x12e84 (Some (ELit 0)) k2) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?c = Some cs' => assert (Ecs : cs' = c) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hro].
  apply andb_prop in Hcond as [Hcond Hro3]. apply andb_prop in Hcond as [Hcond Hro2]. apply andb_prop in Hcond as [Hcond Hro1].
  apply andb_prop in Hcond as [Hcond Heg]. apply andb_prop in Hcond as [Hcond He2]. apply andb_prop in Hcond as [Hcond He1].
  apply andb_prop in Hcond as [Hcond Hg2]. apply andb_prop in Hcond as [Hcond Hg1].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond HD].
  apply andb_prop in Hcond as [Hcond Healsp]. apply andb_prop in Hcond as [Hcond Heald].
  apply andb_prop in Hcond as [Hcond Hdlo']. apply Z.leb_le in Hdlo'.
  apply andb_prop in Hcond as [Hnhi26 Hdata].
  apply Z.ltb_lt in Hnhi26. apply Z.leb_le in Healsp. apply Z.leb_le in Heald. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2. apply Z.leb_le in He1. apply Z.leb_le in He2.
  apply Z.leb_le in Hro1. apply Z.leb_le in Hro2. apply Z.leb_le in Hro3.
  clear HD.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model 0x12e84 HC Hret) as (R1 & Hrok & _).
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  set (data := edenot E (reg cs 10)) in *. set (du := bv_unsigned data).
  set (nw := edenot E (reg cs 11)) in *. set (n := bv_unsigned nw).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hnhi) as Hnhi2. fold nw in Hnhi2. fold n in Hnhi2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hdhi) as Hdhi2. fold data in Hdhi2. fold du in Hdhi2.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hdlo) as Hdlo2. fold data in Hdlo2. fold du in Hdlo2.
  assert (Hdpos : (0 < du)%Z) by lia.
  pose proof (u64_range sp) as Hspr. fold su in Hspr.
  pose proof (u64_range nw) as Hnwr. fold n in Hnwr.
  pose proof (u64_range data) as Hdr. fold du in Hdr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 1824)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 1824 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 1824)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  assert (AL : forall e, (4 <= ealign (kn cs) e)%Z -> (bv_unsigned (edenot E e) mod 16 = 0)%Z).
  { intros e He. destruct (ealign_sound RSEGS E M (kn cs) e HKN) as [He0 Hdiv].
    apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) e - 4))%Z. change 16 with (2 ^ 4)%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  pose proof (AL _ Healsp) as Hsu16. fold sp in Hsu16. fold su in Hsu16.
  pose proof (AL _ Heald) as Hdu16. fold data in Hdu16. fold du in Hdu16.
  clear AL.
  (* [comment removed for export] *)
  assert (RO : forall i, (0x103ec <= i < 0x10490)%Z -> M (Z_to_bv 64 i) = None).
  { unfold kimg_covers in Hro. apply existsb_exists in Hro as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  assert (DATA : exists bs : list byte,
            Z.of_nat (length bs) = n
            /\ (forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (du + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)))
            /\ (du + n < 2 ^ 47)%Z
            /\ (du + n <= su - 1824 \/ su <= du)%Z
            /\ (du + n <= 0x31400 \/ 0x31400 + 4 <= du)%Z).
  { apply orb_prop in Hdata as [Hz|Hpos].
    - (* [comment removed for export] *)
      apply andb_prop in Hz as [Hn0 Heq]. apply Z.eqb_eq in Hn0. apply expr_eqb_eq in Heq.
      assert (N0 : n = 0%Z) by lia.
      assert (DU : du = 0x313e0%Z).
      { subst du data. rewrite Heq. cbn [edenot]. rewrite u64_lit by lia. reflexivity. }
      exists []. rewrite N0, DU. cbn [length Z.of_nat]. split; [reflexivity|]. split; [intros i Hi; lia|].
      apply orb_prop in Heg as [Heg|Heg]; apply Z.leb_le in Heg; lia.
    - (* [comment removed for export] *)
      apply andb_prop in Hpos as [Hpos Hnw64]. apply andb_prop in Hpos as [Hrwd Hap].
      destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN Hrwd) as (Dst & Ddef & Dimg & D0 & Dnw & Dspl & Dpos).
      fold data in Dst, Ddef, Dimg, D0, Dnw, Dspl. unfold elenZ in Ddef, Dimg, Dnw, Dpos. fold nw in Ddef, Dimg, Dnw, Dpos.
      fold du in Ddef, Dimg, D0, Dnw, Dspl. fold n in Ddef, Dimg, Dnw, Dpos.
      (* [comment removed for export] *)
      assert (Hn47 : (du + n < 2 ^ 47)%Z).
      { apply orb_prop in Hnw64 as [Hnw64|Hnw64].
        - apply Z.ltb_lt in Hnw64. lia.
        - assert (Hsp0 : (0x7fff80000000 <= bv_unsigned (edenot E (EVar 0)) <= 0x800000000000)%Z).
          { pose proof (co_vm _ _ _ _ _ HC) as HV. rewrite <- (vo_sp _ _ _ _ _ HV). exact (vo_sprange _ _ _ _ _ HV). }
          destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsd.
          pose proof (below_band_x_sound E M (kn cs) db dk (reg cs 11) dhi nhi HKN ltac:(lia)
                        ltac:(unfold elenZ; fold nw; fold n; lia) ltac:(lia) Hnw64) as D.
          unfold elenZ in D. fold nw in D. fold n in D. lia. }
      clear Hnw64.
      exists (mem_bytes M du (Z.to_nat n)).
      split; [rewrite mem_bytes_length, Z2Nat.id by lia; reflexivity|].
      split; [intros i Hi; apply mem_bytes_nth; [rewrite Z2Nat.id by lia; exact Hi | apply Ddef; exact Hi]|].
      split; [lia|].
      split; [|lia].
      (* [comment removed for export] *)
      rewrite apart_x_eq in Hap. rewrite Hsq in Hap. destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsd.
      pose proof (ranges_apart_x_sound RSEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as Hd.
      unfold estart in Hd. cbn [a_base a_off] in Hd. rewrite elenZ_lit in Hd by lia. unfold elenZ in Hd. fold nw in Hd. fold n in Hd.
      rewrite Hq, <- Dspl in Hd. lia. }
  destruct DATA as (bs & Hlen & Hbs & Hnw64 & Hdsp & Hdg).
  (* [comment removed for export] *)
  destruct (LIB FP R M (seg_rom RSEGS) (Z_to_bv 64 0x12e84) sp data n bs
              R1 Hrok R2 R10 ltac:(unfold n; rewrite Z_to_bv_bv_unsigned; exact R11)
              ltac:(lia) Hlen Hsu16 Hdu16 ltac:(cbn [fa_depth infoub_abi]; lia) ltac:(lia) Hdpos Hnw64 Hbs
              ltac:(cbn [fa_depth infoub_abi]; exact Wst)
              ltac:(cbn [fa_depth infoub_abi]; intros i Hi; apply rsegs_inside; lia)
              (gfool_store_ok M) (gfool_rdn M)
              ltac:(cbn [fa_ro_lo fa_ro_hi infoub_abi]; exact RO)
              ltac:(cbn [fa_depth infoub_abi]; lia) ltac:(cbn [fa_gfool infoub_abi]; lia) ltac:(cbn [fa_gfool fa_depth infoub_abi]; lia))
    as (FP' & R' & M' & Hms & Ha0 & Hkeeps & Hframe).
  cbn [fa_entry fa_depth fa_gfool infoub_abi] in Hms, Hframe.
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. change (t_fuzz INFOUB) with 0x12f88%Z.
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply Nat.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  pose proof (ext_call_agree E nx R') as Hag.
  destruct Hframe as [Hout Hgrows].
  set (rs := [(qb, qk, ELit 1824); (ELit 0, 0x31400%Z, ELit 4)]).
  assert (HOUT : forall x : word, inrs E rs x = false -> M' x = M x).
  { intros x Hx. apply Hout. eapply (outside_of_inrs E rs); [|exact Hx]. subst rs.
    repeat apply Forall2_cons; try apply Forall2_nil; unfold rng_lo, rng_len, estart; cbn [fst snd a_base a_off edenot];
      rewrite ?Hq; unfold elenZ; cbn [edenot]; rewrite !u64_lit by lia; lia. }
  destruct (havocs_frame E rs M (kn cs) M M' HKN HOUT Hgrows) as [HKV HSV].
  destruct (after_call_sound nx0 cs 0x12e84 (Some (ELit 0)) k2 csa E R R' M M' model
              (slots_keep (kn cs) (ELit 0) 0x31400 (ELit 4)
                 (slots_keep (kn cs) qb qk (ELit 1824) (c_slots cs))) Hac HC) as [HC' Hpc'].
  - (* [comment removed for export] *)
    apply kept_regs. intros kk Hin.
    apply Hkeeps. unfold fuzz_kept. cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      (cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end).
  - (* [comment removed for export] *)
    cbn [edenot]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact Ha0.
  - (* [comment removed for export] *)
    assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, HKN).
    pose proof (HKV k0 HK0) as HK2. change (kn_havocs k0 rs) with k2 in HK2. exact HK2.
  - (* [comment removed for export] *)
    exact (HSV (c_slots cs) HSL).
  - (* [comment removed for export] *)
    apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
  - (* [comment removed for export] *)
    subst cs'. specialize (HK FP' (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact Hnx0]) HC').
    rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem call_fuzz_ok : fuzz_sound_stmt nx0.
Proof. exact call_fuzz_sound'. Qed.

End NX0.
End UbSymPlanSoundFZ.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_1299c_12db8.

Module UbLibMainRet.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1299c_12db8.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Theorem main_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x12c5c : word) mem rom) (mkst regs' (0x12cdc : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_12c5c D_12c5c ltac:(exact Hc).
      stepn F_12c68 D_12c68.
      stepn F_12db0 D_12db0.
      stepret F_12db4 D_12db4 (Z_to_bv 64 0x12c6c) ltac:(reflexivity).
      stepn F_12c6c D_12c6c.
      stepn F_12c70 D_12c70.
      stepb_tk F_12c74 D_12c74 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_12c5c D_12c5c ltac:(exact Hc).
      stepn F_12c60 D_12c60.
      stepn F_12c64 D_12c64.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbLibMainRet.

Module UbSymPlanSoundMR.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec UbLibMainRet OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Hypothesis nx0_pos : (0 < nx0)%nat.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma call_mainret_sound' {FP : FPState} : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_main_ret INFOUB -> call_mainret INFOUB nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hpc Hn HK.
  unfold call_mainret in Hn.
  destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10; try discriminate.
  destruct (fresh_ok nx0 cs) eqn:Hfresh; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn. subst cs'.
  destruct (reg_lit_sound E cs R M model 10 0 HC ltac:(lia) H10) as [R10 _].
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  destruct (main_ret_0 R M (seg_rom RSEGS) R10) as (R' & Hms & G8 & G10 & Goth).
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_main_ret INFOUB)) with (0x12c5c%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  set (nx := s_next (c_ss cs)).
  set (E' := ext1 (ext1 E nx (getr R' 1)) (S nx) (getr R' 11)).
  assert (Hag : env_agree nx E E').
  { eapply env_agree_le; [| apply Nat.le_refl].
    split; [|reflexivity]. intros n Hn. unfold E'. cbn [ext1 ev].
    destruct (Nat.eqb_spec n (S nx)); [lia|]. destruct (Nat.eqb_spec n nx); [lia|]. reflexivity. }
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv]. apply andb_prop in Hfresh as [Hsv Hkv]. apply Nat.leb_le in Hnx0.
  fold nx in Hnx0, Hslv, Hmv, Hsv, Hkv.
  specialize (HK E' R' M ltac:(eapply env_agree_le; [exact Hag | exact Hnx0])).
  unfold cfg_of in HK. cbn [pc c_ss s_pc] in HK.
  replace (Z_to_bv 64 (t_main_join INFOUB)) with (0x12cdc%bv : word) in HK by (apply bv_eq; reflexivity).
  apply HK. clear HK.
  destruct HC as [HR HKN HL Hh Hlz Hmt Hfd HV HSL].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (ridx_range r) as Hrr.
    destruct (Nat.eqb_spec (ridx r) 11) as [E11|N11].
    { rewrite (reg_of_ridx r 11 E11). cbn [edenot]. unfold E'. rewrite ext1_at.
      replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 10) as [E10|N10].
    { rewrite (reg_of_ridx r 10 E10). cbn [edenot].
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 8) as [E8|N8].
    { rewrite (reg_of_ridx r 8 E8). cbn [edenot].
      replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G8. reflexivity. }
    destruct (Nat.eqb_spec (ridx r) 1) as [E1|N1].
    { rewrite (reg_of_ridx r 1 E1). cbn [edenot]. unfold E'. cbn [ext1 ev]. fold nx.
      destruct (Nat.eqb_spec nx (S nx)); [lia|]. rewrite Nat.eqb_refl.
      replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
    rewrite Goth; [| intros X; subst r; apply N1; reflexivity | intros X; subst r; apply N8; reflexivity
                   | intros X; subst r; apply N10; reflexivity | intros X; subst r; apply N11; reflexivity].
    pose proof (HR r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
    rewrite X. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq.
    clear -Hsv Hrr. revert Hsv. generalize (ridx r) as i. generalize (s_regs (c_ss cs)) as sr.
    induction sr as [|e t IH]; intros i Hsv; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; exact H2].
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HKN].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - destruct HV; constructor; try assumption.
    + eapply smaps_ok_ext; [exact Hag | exact Hmv | assumption].
    + match goal with H : vm_init_sp _ = edenot E (EVar 0) |- _ => rewrite H end.
      cbn [edenot]. apply Hag. lia.
  - eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL].
Qed.

Theorem call_mainret_ok : mainret_sound_stmt nx0.
Proof. intros FP. exact call_mainret_sound'. Qed.

End NX0.
End UbSymPlanSoundMR.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbExit.

Module UbSymPlanSoundEX.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH UbSymPlanSoundSW.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Lemma kread4e_rdn : forall E M k b off v,
  know_ok RSEGS E M k -> kread4e RSEGS k b off = Some v -> flat E (SA b off) 4 ->
  rdn RSEGS M (adenot E (SA b off)) 4 = Some (word_to_le_bytes 4 (edenot E v)).
Proof.
  intros E M k b off v HK H Hfl. apply (kread_rdn RSEGS E M k b off 4 v HK); [exact H | lia | lia | exact Hfl].
Qed.

(* [comment removed for export] *)
Lemma cells_ok_one : forall E M k cells a n v,
  know_ok RSEGS E M k -> cells_ok RSEGS k cells = true -> In (a, n, v) cells ->
  (1 <= n <= 8)%nat -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros E M k cells a n v HK H Hin Hn Ha0 Ha8.
  unfold cells_ok in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn beta iota in H.
  destruct (kreadZ RSEGS k (ELit 0) a n) as [z|] eqn:Hz; [|discriminate]. apply Z.eqb_eq in H. subst z.
  destruct (kreadZ_rdn E M k (ELit 0) a n v HK Hz Hn ltac:(apply flat_abs0; lia)) as [R _].
  rewrite adenot_abs0 in R. exact R.
Qed.

Lemma w2b1_0 : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. rewrite w2lb1. reflexivity. Qed.

(* [comment removed for export] *)

Theorem node_exitcall_sound' : exitcall_sound_stmt.
Proof.
  unfold exitcall_sound_stmt.
  intros FP cs bs code E R M model HC Hpc Hn.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  unfold node_exitcall in Hn.
  change (d_stdout INFOUB) with 0x21288%Z in Hn. change (d_stderr INFOUB) with 0x21198%Z in Hn.
  change (d_canary INFOUB) with 0x51748%Z in Hn. change (d_canary_got INFOUB) with 0x20158%Z in Hn.
  change (t_stdio_write INFOUB) with 0x19ae4%Z in Hn. change (d_img_hi INFOUB) with 0x52000%Z in Hn.
  destruct (reg_lit cs 10) as [c|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:H4; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-144))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (kread4e RSEGS (kn cs) (ELit 0) (tp - 168)) as [tide|] eqn:Htid; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21288 + 8)) as [rp|] eqn:Hrp; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21288 + 16)) as [re|] eqn:Hre; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21198 + 40)) as [w2|] eqn:Hw2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21198 + 56)) as [b2|] eqn:Hb2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21198 + 8)) as [r2|] eqn:Hr2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21198 + 16)) as [e2|] eqn:He2; [|discriminate].
  destruct (elo (kn cs) tide) as [tlo|] eqn:Htlo; [|discriminate].
  destruct (ehi (kn cs) tide) as [thi|] eqn:Hthi; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hthi']. apply andb_prop in Hcond as [Hcond Htlo'].
  apply andb_prop in Hcond as [Hcond Htphi]. apply andb_prop in Hcond as [Hcond Htplo].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Eq2]. apply andb_prop in Hcond as [Hcond Eqw2]. apply andb_prop in Hcond as [Hcond Eqrp].
  apply andb_prop in Hcond as [Hcells Hlock'].
  apply Z.ltb_lt in Hthi'. apply Z.leb_le in Htlo'. apply Z.leb_le in Htphi. apply Z.leb_le in Htplo.
  apply Z.leb_le in Hsphi'. apply Z.leb_le in Hsplo'. apply Z.eqb_eq in Hlock'. subst lock.
  apply expr_eqb_eq in Eq2. apply expr_eqb_eq in Eqw2. apply expr_eqb_eq in Eqrp. subst e2 b2 re.
  (* [comment removed for export] *)
  destruct (reg_lit_sound E cs R M model 10 c HC ltac:(lia) H10) as [R10 Hc].
  destruct (reg_lit_sound E cs R M model 4 tp HC ltac:(lia) H4) as [R4 Htp].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (elo_sound E M (kn cs) _ _ HKN Htlo) as Htlo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hthi) as Hthi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr. unfold two64 in Htp, Hc.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 144)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 144 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 144)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C D. apply flat_abs0; lia. }
  pose proof (kread4e_rdn E M (kn cs) (ELit 0) (tp - 168) tide HKN Htid ltac:(apply FL; lia)) as Rtid.
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 140) 4 _ HKN Hlock ltac:(lia) ltac:(apply FL; lia)) as [Rlock _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 40) 8 wp HKN Hwp ltac:(lia) ltac:(apply FL; lia)) as [Rwp Hwpr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 56) 8 wb HKN Hwb ltac:(lia) ltac:(apply FL; lia)) as [Rwb Hwbr].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21288 + 8) rp HKN Hrp ltac:(apply FL; lia)) as Rrp.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21288 + 16) rp HKN Hre ltac:(apply FL; lia)) as Rre.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21198 + 40) w2 HKN Hw2 ltac:(apply FL; lia)) as Rw2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21198 + 56) w2 HKN Hb2 ltac:(apply FL; lia)) as Rb2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21198 + 8) r2 HKN Hr2 ltac:(apply FL; lia)) as Rr2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21198 + 16) r2 HKN He2 ltac:(apply FL; lia)) as Re2.
  rewrite adenot_abs0 in Rtid, Rlock, Rwp, Rwb, Rrp, Rre, Rw2, Rb2, Rr2, Re2. unfold two64 in Hwpr, Hwbr.
  (* [comment removed for export] *)
  change (e_cells INFOUB) with
    [(0x51740, 4%nat, 0); (0x20160, 8%nat, 0x200c8); (0x20168, 8%nat, 0x200c0); (0x200c0, 8%nat, 0x12a58);
     (0x213c8, 1%nat, 0); (0x20108, 8%nat, 0x17440); (0x20110, 8%nat, 0);
     (0x5176b, 1%nat, 0); (0x51b98, 8%nat, 0); (0x51b88, 8%nat, 0);
     (0x21370, 8%nat, 0x21288); (0x21280, 8%nat, 0x21198); (0x21198 + 140, 4%nat, 4294967295);
     (0x21170, 8%nat, 0x21170); (0x51524, 4%nat, 0); (0x51530, 8%nat, 0x51538); (0x51528, 4%nat, 1); (0x51538, 8%nat, 0); (0x51540, 8%nat, 0x17508); (0x51640, 8%nat, 0x12f10); (0x313d4, 1%nat, 0)]%Z in Hcells.
  assert (CELL : forall a n v, In (a, n, v)
     [(0x51740, 4%nat, 0); (0x20160, 8%nat, 0x200c8); (0x20168, 8%nat, 0x200c0); (0x200c0, 8%nat, 0x12a58);
      (0x213c8, 1%nat, 0); (0x20108, 8%nat, 0x17440); (0x20110, 8%nat, 0);
      (0x5176b, 1%nat, 0); (0x51b98, 8%nat, 0); (0x51b88, 8%nat, 0);
      (0x21370, 8%nat, 0x21288); (0x21280, 8%nat, 0x21198); (0x21198 + 140, 4%nat, 4294967295);
     (0x21170, 8%nat, 0x21170); (0x51524, 4%nat, 0); (0x51530, 8%nat, 0x51538); (0x51528, 4%nat, 1); (0x51538, 8%nat, 0); (0x51540, 8%nat, 0x17508); (0x51640, 8%nat, 0x12f10); (0x313d4, 1%nat, 0)]%Z ->
     (1 <= n <= 8)%nat -> 0 <= a -> a + 8 <= 2 ^ 64 ->
     rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v))).
  { intros a n v Hin Hn8 A B. eapply cells_ok_one; [exact HKN | exact Hcells | exact Hin | exact Hn8 | exact A | exact B]. }
  (* [comment removed for export] *)
  assert (EC : exit_common R M sp (Z_to_bv 64 tp) (Z_to_bv 64 c) (bv_unsigned (edenot E tide)) (edenot E w2) (edenot E r2)).
  { constructor.
    - exact R2.
    - exact R4.
    - exact R10.
    - lia.
    - lia.
    - exact Wst.
    - rewrite u64_lit by lia. lia.
    - rewrite u64_lit by lia. lia.
    - lia.
    - rewrite u64_lit by lia. rewrite Z_to_bv_bv_unsigned. exact Rtid.
    - apply (CELL 0x51740 4%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x20160 8%nat 0x200c8); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x20168 8%nat 0x200c0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x200c0 8%nat 0x12a58); [cbn; noncert_qtauto | lia | lia | lia].
    - rewrite <- w2b1_0. apply (CELL 0x213c8 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x20108 8%nat 0x17440); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x20110 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - repeat split.
      + rewrite <- w2b1_0. apply (CELL 0x5176b 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51b98 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51b88 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x21370 8%nat 0x21288); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x21280 8%nat 0x21198); [cbn; noncert_qtauto | lia | lia | lia].
    - repeat split.
      + apply (CELL (0x21198 + 140) 4%nat 4294967295); [cbn; noncert_qtauto | lia | lia | lia].
      + exact Rw2.
      + exact Rb2.
      + exact Rr2.
      + exact Re2.
    - apply (CELL 0x21170 8%nat 0x21170); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0x51524 4%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - right. unfold ax_one. repeat split.
      + apply (CELL 0x51530 8%nat 0x51538); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51528 4%nat 1); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51538 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51540 8%nat 0x17508); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0x51640 8%nat 0x12f10); [cbn; noncert_qtauto | lia | lia | lia].
      + rewrite <- w2b1_0. apply (CELL 0x313d4 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia]. }
  (* [comment removed for export] *)
  assert (Hcode : Z_to_bv 64 (Z.land c 255) = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)).
  { apply bv_eq. rewrite !bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    assert (Hl : (0 <= Z.land c 255 < 256)%Z).
    { split; [apply Z.land_nonneg; lia|]. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound c (2^8) ltac:(lia)). lia. }
    rewrite !Z.mod_small; try lia. }
  unfold cfg_of. rewrite Hpc. change (t_exitc INFOUB) with 0x1755c%Z.
  (* [comment removed for export] *)
  destruct (Z.eqb_spec wb wp) as [Ewb|Nwb].
  - (* [comment removed for export] *)
    injection Hn as <- <-. cbn [Wz map]. rewrite Hcode. change (@nil event) with (W 1 []).
    apply ref_exit_Z. exists sp, (Z_to_bv 64 tp), (bv_unsigned (edenot E tide)), (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt _ _ _ _ _ HC)|]. split; [exact (co_lazy _ _ _ _ _ HC)|].
    left. split; [reflexivity|]. exists (Z_to_bv 64 wp), (edenot E rp).
    repeat split; [exact Rlock | exact Rwp | subst wb; exact Rwb | exact Rrp | exact Rre].
  - (* [comment removed for export] *)
    destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 72) 8) as [wr|] eqn:Hwr; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21288 + 88)) as [bufp|] eqn:Hbufp; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) (0x21288 + 96)) as [bufsz|] eqn:Hbufsz; [|discriminate].
    destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x21288 + 120) 4) as [fd|] eqn:Hfd; [|discriminate].
    destruct (kreadZ RSEGS (kn cs) (ELit 0) 0x20158 8) as [cg|] eqn:Hcg; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) 0x51748) as [canv|] eqn:Hcan; [|discriminate].
    destruct (kread_bytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
    match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc2; [|discriminate] end.
    injection Hn as <- <-.
    apply andb_prop in Hc2 as [Hc2 Hmax]. apply andb_prop in Hc2 as [Hc2 Hwphi]. apply andb_prop in Hc2 as [Hc2 Hlt].
    apply andb_prop in Hc2 as [Hc2 Hwblo]. apply andb_prop in Hc2 as [Hc2 Hcgv]. apply andb_prop in Hc2 as [Hwr' Hfd'].
    apply Z.leb_le in Hmax. apply Z.leb_le in Hwphi. apply Z.ltb_lt in Hlt. apply Z.leb_le in Hwblo.
    apply Z.eqb_eq in Hcgv. apply Z.eqb_eq in Hwr'. apply Z.eqb_eq in Hfd'. subst wr fd cg.
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 72) 8 _ HKN Hwr ltac:(lia) ltac:(apply FL; lia)) as [Rwr _].
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21288 + 88) bufp HKN Hbufp ltac:(apply FL; lia)) as Rbufp.
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0x21288 + 96) bufsz HKN Hbufsz ltac:(apply FL; lia)) as Rbufsz.
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x21288 + 120) 4 1 HKN Hfd ltac:(lia) ltac:(apply FL; lia)) as [Rfd _].
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0x20158 8 _ HKN Hcg ltac:(lia) ltac:(apply FL; lia)) as [Rcg _].
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0x51748 canv HKN Hcan ltac:(apply FL; lia)) as Rcan.
    rewrite adenot_abs0 in Rwr, Rbufp, Rbufsz, Rfd, Rcg, Rcan.
    destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat (wp - wb)) (ELit 0) wb pend HKN Hpend
                ltac:(cbn [edenot]; rewrite u64_lit by lia; lia) ltac:(cbn [edenot]; rewrite u64_lit by lia; lia)) as [Rpend Lpend].
    cbn [edenot] in Rpend. rewrite (u64_lit 0) in Rpend by lia. rewrite Z.add_0_l in Rpend.
    rewrite Wz_map, Hcode. change (map (WriteEv (Z_to_bv 64 1)) ?l) with (W 1 l).
    apply ref_exit_Z. exists sp, (Z_to_bv 64 tp), (bv_unsigned (edenot E tide)), (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt _ _ _ _ _ HC)|]. split; [exact (co_lazy _ _ _ _ _ HC)|].
    right. exists wb, wp, (edenot E bufp), (edenot E bufsz), (edenot E rp), (edenot E canv).
    split; [| apply fd_lookup_std1; exact (co_fds _ _ _ _ _ HC)].
    constructor.
    + exact Rlock.
    + exact Rwp.
    + exact Rwb.
    + exact Rwr.
    + exact Rbufp.
    + exact Rbufsz.
    + exact Rfd.
    + exact Rrp.
    + exact Rre.
    + lia.
    + rewrite length_map, Lpend, Z2Nat.id by lia. reflexivity.
    + rewrite length_map, Lpend, Z2Nat.id by lia. pose proof rw_bytes_max_ge17. lia.
    + rewrite length_map, Lpend. exact Rpend.
    + split; [exact Rcg | exact Rcan].
Qed.

Theorem node_exitcall_ok : exitcall_sound_stmt.
Proof. exact node_exitcall_sound'. Qed.
End UbSymPlanSoundEX.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbStdioWrite.

Module UbTargetAssembly.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPreK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH UbSymPlanSoundFP UbSymPlanSoundEF UbSymPlanSoundSW UbSymPlanSoundFZ UbSymPlanSoundMR UbSymPlanSoundPF UbSymPlanSoundEX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioWrite OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract UbTargetEntry_defs UbTargetEntry UbTargetEntryK_defs UbTargetEntryK UbTargetShape.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition lib_ok : Prop := fuzz_contract RSEGS infoub_abi.

Section WithFP1. Context {FP : PropExec.FPState}.
Section LIB.
Hypothesis LIB : lib_ok.

(* [comment removed for export] *)
Lemma npos_class : forall nlo nhi content,
  0 <= nlo -> (nlo = 0 -> nhi = 0) -> nlo <= hdr_paylen content <= nhi ->
  (0 <? nlo) = npos_of content.
Proof.
  intros nlo nhi content H0 Hz Hn. unfold npos_of.
  destruct (Z.ltb_spec 0 nlo); [symmetry; apply Z.ltb_lt; lia|].
  assert (nlo = 0) by lia. specialize (Hz H1). symmetry. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma ref_stdio_write_ok : ref_stdio_write_stmt.
Proof. exact @ref_stdio_write. Qed.

(* [comment removed for export] *)
Lemma ITAB_ok : itab_sound RSEGS ITAB.
Proof. exact (mk_itab_sound RSEGS TEXT_LO (text_n INFOUB)). Qed.

Lemma check_sound_all : forall nx0 fuel bfuel p cs s,
  (0 < nx0)%nat ->
  check RSEGS ITAB INFOUB nx0 bfuel fuel cs p = COk s ->
  forall E R M model, cs_ok E cs R M model ->
  realizes RSEGS (cfg_of R (pc cs) M model) (sd E (m_fs model) s).
Proof.
  intros nx0 fuel bfuel p cs s Hnx0 HC E R M model CS.
  exact (check_sound nx0 ITAB ITAB_ok (call_enframe2_ok nx0 Hnx0) (call_freepro_ok nx0 Hnx0) (node_stdio_write_ok nx0 ref_stdio_write_ok)
           (call_fuzz_ok nx0 LIB) (call_mainret_ok nx0 Hnx0) (call_printf_ok nx0) node_exitcall_ok
           fuel bfuel p cs s HC FP E R M model CS).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB INFOUB NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec cnr content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS H0 Hz sp0 gm area brkv mas tid sec cnr content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & He & CS).
  eapply rz_conseq.
  - exact (check_sound_all NX0 fuel bfuel p (cs_T nlo nhi) s ltac:(cbv; lia) HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (proj1 (tp_len _ _ _ _ _ _ _ _ _ _ _ TP)).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB INFOUB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 B area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS H0 Hz sp0 B area brkv mas tid sec cnr content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & He & CS).
  eapply rz_conseq.
  - exact (check_sound_all NX0k fuel bfuel p (cs_Tk k nlo nhi) s ltac:(cbv; lia) HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (tk_len _ _ _ _ _ _ _ _ _ _ _ _ TP).
Qed.

End LIB.
End WithFP1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbTargetAssembly.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbSymPlanSoundA. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbSymPlanSoundA.UbSymSlots. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbSymPlanSoundA. Import UbSymPlanSound. Import UbTargetEntry_defs. Import UbTargetEntry. Import UbTargetEntryK_defs. Import UbTargetEntryK. Import UbTargetShape. Import UbTargetShapeTop. Import UbTargetAssembly.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section LIB.
Hypothesis LIB : lib_ok.

(* [comment removed for export] *)
Theorem target_class_sound_top : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB INFOUB NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  65529 <= nlo ->
  forall (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec cnr content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS Htop sp0 gm area brkv mas tid sec cnr content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & He & CS).
  pose proof (tp_len _ _ _ _ _ _ _ _ _ _ _ TP) as HL.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all LIB NX0 fuel bfuel p (cs_T nlo nhi) s ltac:(cbv; lia) HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_top_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB INFOUB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  capk k - 7 <= nlo ->
  forall (sp0 B area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Htop sp0 B area brkv mas tid sec cnr content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & He & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ _ _ TP) as HK.
  pose proof (capk_pos (k - 1) ltac:(pose proof (wk_k _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ _ TP)); lia)) as Hc.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all LIB NX0k fuel bfuel p (cs_Tk k nlo nhi) s ltac:(cbv; lia) HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; unfold hdr_paylen in *; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_low_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB INFOUB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok1 (0 <? nlo) s = true ->
  nhi + 6 < capk (k - 1) ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 B area brkv mas tid sec cnr : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Hlow H0 Hz sp0 B area brkv mas tid sec cnr content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec cnr content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & He & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ _ _ TP) as HK.
  assert (C1 : 1 <= hdr_cfglen content) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all LIB NX0k fuel bfuel p (cs_Tk k nlo nhi) s ltac:(cbv; lia) HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound1 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C1 | exact HL | exact HS].
Qed.

End LIB.
End WithFP1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
