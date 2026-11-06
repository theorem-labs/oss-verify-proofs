(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTPlan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTGlue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac in_list_solve := cbn; repeat (first [left; reflexivity | right]).
Strategy opaque [hR0 hV0b hVSb1 hVSb2 hVPb1 hVPb2 hVFb hV0n hV1_0 hV1_Sn hV1_Sb hV1_F holeEA holePA holeEB holePB].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition env3 (b0 b1 b2 : Z) : env := Env (fun n => if Nat.eqb n 4 then Z_to_bv 64 b0 else if Nat.eqb n 5 then Z_to_bv 64 b1 else if Nat.eqb n 6 then Z_to_bv 64 b2 else Z_to_bv 64 0) (fun _ => []).
Definition cfgxF (b0 b1 : Z) : Z := uE (env3 b0 b1 0) CFGX.
Definition b1sF (b1 : Z) : Z := uE (env3 0 b1 0) B1S.
Definition callsbF (b2 : Z) : Z := uE (env3 0 0 b2) CALLSB.

Lemma uE_CFGX_env : forall E, uE E CFGX = cfgxF (uE E B0) (uE E B1).
Proof. intros E. unfold cfgxF, uE, env3. cbn. rewrite !Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma uE_B1S_env : forall E, uE E B1S = b1sF (uE E B1).
Proof. intros E. unfold b1sF, uE, env3. cbn. rewrite !Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma uE_CALLSB_env : forall E, uE E CALLSB = callsbF (uE E B2).
Proof. intros E. unfold callsbF, uE, env3. cbn. rewrite !Z_to_bv_bv_unsigned. reflexivity. Qed.

Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | Datatypes.S n' => a :: zseq (a + 1) n' end.
Lemma zseq_In : forall n a z, a <= z < a + Z.of_nat n -> In z (zseq a n).
Proof. induction n as [|n IH]; intros a z Hz; [lia|]. cbn [zseq]. destruct (Z.eq_dec a z); [left; exact e | right; apply IH; lia]. Qed.

(* [comment removed for export] *)
Lemma cfgx_split : forall b0 b1, 0 <= b0 < 256 -> cfgxF b0 b1 = Z.lor (cfgxF 0 b1) b0.
Proof.
  intros b0 b1 Hb0. unfold cfgxF, uE, env3. cbn. rewrite !bv_or_unsigned, !u64_lit by lia. rewrite Z.lor_0_r. reflexivity.
Qed.
Lemma cfgx_chk : forallb (fun b1 => Z.eqb (cfgxF 0 b1) (256 * (b1 mod 128))) (zseq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma land_high_low : forall m b0, 0 <= m -> 0 <= b0 < 256 -> Z.land (256 * m) b0 = 0.
Proof.
  intros m b0 Hm Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i 8).
  - replace (256 * m) with (m * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec b0 0) as [->|Hnz]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 b0 i); [apply andb_false_r | lia |].
    apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_high_low : forall m b0, 0 <= m -> 0 <= b0 < 256 -> Z.lor (256 * m) b0 = 256 * m + b0.
Proof.
  intros m b0 Hm Hb. rewrite <- Z.lxor_lor by (apply land_high_low; lia). symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.
Lemma b1s_chk : forallb (fun b1 => Bool.eqb (Z.ltb M63 (b1sF b1)) (Z.leb 128 b1)) (zseq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma callsb_chk : forallb (fun b2 => Z.eqb (callsbF b2) (b2 mod 4 + 1)) (zseq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cfgx_bytes : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> cfgxF b0 b1 = (b0 + 256 * b1) mod 32768.
Proof.
  intros b0 b1 H0 H1. rewrite cfgx_split by lia.
  pose proof (proj1 (forallb_forall _ _) cfgx_chk b1 (zseq_In 256 0 b1 ltac:(lia))) as X. apply Z.eqb_eq in X. rewrite X.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as Hr. pose proof (Z.div_mod b1 128 ltac:(lia)) as Hd.
  rewrite lor_high_low by lia.
  apply (Z.mod_unique_pos _ 32768 (b1 / 128)); lia.
Qed.
Lemma b1s_bytes : forall b1, 0 <= b1 < 256 -> Z.ltb M63 (b1sF b1) = Z.leb 128 b1.
Proof.
  intros b1 H1. pose proof (proj1 (forallb_forall _ _) b1s_chk b1 (zseq_In 256 0 b1 ltac:(lia))) as X. apply Bool.eqb_prop in X. exact X.
Qed.
Lemma callsb_bytes : forall b2, 0 <= b2 < 256 -> callsbF b2 = b2 mod 4 + 1.
Proof.
  intros b2 H2. pose proof (proj1 (forallb_forall _ _) callsb_chk b2 (zseq_In 256 0 b2 ltac:(lia))) as X. apply Z.eqb_eq in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma hdr_byte_range' : forall data i, 0 <= hdr_byte data i < 256.
Proof. intros data i. unfold hdr_byte. apply u8_range. Qed.

Section Hdr.
Variable data : list byte.
Variable E : env.
Hypothesis HB0 : uE E B0 = hdr_byte data 0.
Hypothesis HB1 : uE E B1 = hdr_byte data 1.
Hypothesis HB2 : uE E B2 = hdr_byte data 2.
Hypothesis HLEN : uE E LEN = Z.of_nat (length data).

Lemma cfglenZ_hdr : cfglenZ E = hdr_cfglen data.
Proof.
  unfold cfglenZ, hdr_cfglen, hdr_cfg. rewrite uE_CFGX_env, HB0, HB1.
  apply cfgx_bytes; apply hdr_byte_range'.
Qed.
Lemma cmode_hdr : cmode E = hdr_count_mode data.
Proof.
  unfold cmode, hdr_count_mode, hdr_cfg. rewrite uE_B1S_env, HB1, b1s_bytes by apply hdr_byte_range'.
  pose proof (hdr_byte_range' data 0). pose proof (hdr_byte_range' data 1).
  destruct (Z.leb_spec 128 (hdr_byte data 1)); destruct (Z.leb_spec 32768 (hdr_byte data 0 + 256 * hdr_byte data 1)); try reflexivity; lia.
Qed.
Lemma paylenZ_hdr : paylenZ E = hdr_paylen data.
Proof. unfold paylenZ, hdr_paylen. rewrite cfglenZ_hdr, HLEN. lia. Qed.
Lemma callsZ_hdr : callsZ E = hdr_calls data.
Proof.
  unfold callsZ, hdr_calls. rewrite cfglenZ_hdr. destruct (hdr_cfglen data =? 0); [reflexivity|].
  rewrite uE_CALLSB_env, HB2, callsb_bytes by apply hdr_byte_range'.
  pose proof (hdr_byte_range' data 2). rewrite Z2Nat.inj_add by (try apply Z.mod_pos_bound; lia). change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r. reflexivity.
Qed.
End Hdr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TH_CL : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EBlob false 7 0 1; EBlob false 7 1 1; EBlob false 7 2 1].
Lemma selfent_CLb : entails_t ADRV 0 T_CLb T_CLb TH_CL = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ecall_CLb : is_ecall_at RSEGS T_CLb = true /\ reg_lit T_CLb 17 = Some 57 /\ reg_lit T_CLb 10 = Some 3. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma ecall_CLn : is_ecall_at RSEGS T_CLn = true /\ reg_lit T_CLn 17 = Some 57 /\ reg_lit T_CLn 10 = Some 3. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sub_CLb_1 : forallb (fun K => existsb (kentry_eqb K) (kn T_CLb)) (RA_CLOSE :: knBC) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sub_CLn_1 : forallb (fun K => existsb (kentry_eqb K) (kn T_CLn)) (RA_CLOSE :: knBC) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sub_CLb_B : forallb (fun K => existsb (kentry_eqb K) (kn T_CLb)) (RA_CLOSE :: knB) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hav_BC : kn_havoc (RA_CLOSE :: knBC) (ELit 0) READ_STAGE (ELit 65536) = RA_CLOSE :: knBC. Proof. vm_compute. reflexivity. Qed.
Lemma hav_B : kn_havoc (RA_CLOSE :: knB) (ELit 0) READ_STAGE (ELit 65536) = RA_CLOSE :: knB. Proof. vm_compute. reflexivity. Qed.
Lemma planCL1_ok : GPS.gplan_ok planCL1 = true. Proof. reflexivity. Qed.
Lemma planCL_ok : GPS.gplan_ok planCL = true. Proof. reflexivity. Qed.

Lemma bytes_le_single' : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. apply bytes_le_single. Qed.

Section Close.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GPLAIN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okR TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok U).
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD APLAIN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GPLAIN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzE.ce.

Variables (p : Fs.path) (data : list byte) (TOP : Z) (M0 : word -> option byte).
#[local] Notation L := (L data).
#[local] Notation hdr := (hdr data).

(* [comment removed for export] *)
Lemma CL1_sound : forall E fx R M model,
  cs_okR TOP (m_fs model) fds_std M0 (U_cl1 data) E tCL1 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tCL1) M model) (t_die msg_short (m_fs model)).
Proof.
  intros E fx R M model HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1' fds_std_2' (U_cl1 data) (U_cl1_agree data)
            (HSof1 tinC1n) (fun _ _ fs => t_die msg_short fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_die_has_nil msg_short fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planCL1 tCL1 (SHole 1) E fx R M model planCL1_ok certCL1 HC eq_refl).
  intros h ch Hh. destruct h as [|[|h]]; cbn [HSof1] in Hh; try discriminate Hh. injection Hh as <-.
  intros E' fx' R' M' model' HC'.
  refine (S3_C1n_sound SR SRX HFR HMB TOP M0 E' fx' R' M' model' _). eapply cs_ok_uinv; [| intros _; exact I]. rewrite <- (co_fs HC') in HC'. exact HC'.
Qed.

Lemma CL2_sound : forall E fx R M model,
  cs_okR TOP (m_fs model) fds_std M0 (U_cl3 data) E tCL2 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tCL2) M model) (t_die msg_overrun (m_fs model)).
Proof.
  intros E fx R M model HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1' fds_std_2' (U_cl3 data) (U_cl3_agree data)
            (HSof1 tinC2) (fun _ _ fs => t_die msg_overrun fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_die_has_nil msg_overrun fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planCL tCL2 (SHole 1) E fx R M model planCL_ok certCL2 HC eq_refl).
  intros h ch Hh. destruct h as [|[|h]]; cbn [HSof1] in Hh; try discriminate Hh. injection Hh as <-.
  intros E' fx' R' M' model' HC'.
  refine (S3_C2_sound SR SRX HFR HMB TOP M0 E' fx' R' M' model' _). eapply cs_ok_uinv; [| intros _; exact I]. rewrite <- (co_fs HC') in HC'. exact HC'.
Qed.

Definition T_PAY (fs : Fs.Fs) : TSet := t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data) fs.
Lemma CL3_sound : forall E fx R M model,
  cs_okR TOP (m_fs model) fds_std M0 (U_cl3 data) E tCL3 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tCL3) M model) (T_PAY (m_fs model)).
Proof.
  intros E fx R M model HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1' fds_std_2' (U_cl3 data) (U_cl3_agree data)
            (HSof1 tinC3) (fun _ _ fs => T_PAY fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_payload_has_nil _ _ _ fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planCL tCL3 (SHole 1) E fx R M model planCL_ok certCL3 HC eq_refl).
  intros h ch Hh. destruct h as [|[|h]]; cbn [HSof1] in Hh; try discriminate Hh. injection Hh as <-.
  intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UL & U0 & U1 & U2).
  unfold T_PAY. rewrite <- (cmode_hdr data E' U1), <- (paylenZ_hdr data E' U0 U1 UL), <- (callsZ_hdr data E' U0 U1 U2).
  refine (S3_C3_sound SR SRX HFR HMB HMA GC_T FZN_sound FZE_sound TOP M0 E' fx' R' M' model' _).
  eapply cs_ok_uinv; [| intros _; exact I]. rewrite <- (co_fs HC') in HC'. exact HC'.
Qed.

(* [comment removed for export] *)
Lemma hdr_kword : forall E M (i : nat), (i < 3)%nat ->
  kentry_ok RSEGS E M (KBlob (SA BUF 0) (ELit 3) 7) ->
  edenot E (EVar (4 + i)) = blob_val false (eb E 7) (Z.of_nat i) 1 ->
  kentry_ok RSEGS E M (KWord (SA BUF (Z.of_nat i)) 1 (EVar (4 + i))).
Proof.
  intros E M i Hi (Bflat & Blen & Bbytes) Hv. cbn [kentry_ok].
  unfold elenZ in *. rewrite edenot_lit, u64_lit in Bflat, Blen, Bbytes by lia.
  unfold flat in *. rewrite APS.estart_SA in *. cbn [a_off] in *. rewrite Z.add_0_r in *.
  split; [lia|]. split; [lia|].
  rewrite GCL.adenot_SA, APS.estart_SA. cbn [a_off].
  specialize (Bbytes (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in Bbytes.
  rewrite (rdn_one RSEGS M _ (nth i (eb E 7) (Z_to_bv 8 0))) by (rewrite Bbytes; reflexivity).
  rewrite Hv. unfold blob_val, blob_bytes. rewrite Nat2Z.id.
  assert (Hpiece : firstn 1 (skipn i (eb E 7)) = [nth i (eb E 7) (Z_to_bv 8 0)]).
  { assert (Hl : (i < length (eb E 7))%nat) by lia.
    revert Hl. generalize (eb E 7). clear. induction i as [|i IH]; intros l Hl; destruct l as [|x l]; cbn in Hl |- *; try lia; [reflexivity|]. apply IH. lia. }
  rewrite Hpiece. f_equal. symmetry. apply (GCL.word_to_le_bytes_of_bytes_n 1); [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma close_hole_b : forall len cap E fx R M model,
  len = L -> 3 <= L -> L < 2 ^ 26 ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len cap) E T_CLb fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (t_body data (m_fs model)).
Proof.
  intros len cap E fx R M model Hlen HL3 HL26 HC.
  destruct ecall_CLb as (Hec & H17 & H10).
  change P_ECALL with (pc T_CLb).
  eapply (close_step SR p TOP M0 (m_fs model) _ E T_CLb fx R M model len); [exact HC | exact Hec | reflexivity | exact H17 | exact H10 |].
  destruct (co_uinv HC) as (UL & UC & UF & UB).
  assert (HCAP : kentry_ok RSEGS E M (KRange CAP 65536 (2 ^ 26))) by (eapply (kn_In_ok TOP M0); [exact HC | in_list_solve]).
  unfold t_body. fold (Spec4.MAX_INPUT). unfold L in *.
  replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
  destruct (Z.ltb_spec (Z.of_nat (length data)) 6) as [Hlt6|Hge6].
  - (* [comment removed for export] *)
    assert (HC1 : cs_okR TOP (m_fs model) fds_std M0 (U_rd data len cap) E tCL1 fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 0))
                    (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds fds_std model)).
    { eapply (xfer_ok TOP (m_fs model) (FDSr p len) fds_std M0 (U_rd data len cap) E T_CLb tCL1 (ELit 0)
                [KRange LEN 0 5; KRange CAP 65536 (2 ^ 26)] (RA_CLOSE :: knBC));
        [exact HC | reflexivity | reflexivity | reflexivity | exact sub_CLb_1 | exact hav_BC
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia |].
      constructor; [cbn [kentry_ok]; unfold uE in UL; lia|]. constructor; [exact HCAP | constructor]. }
    cbn [write_to_mem] in HC1.
    replace (t_die msg_short (m_fs model)) with (t_die msg_short (m_fs (with_fds fds_std model))) by reflexivity.
    exact (CL1_sound E fx _ _ (with_fds fds_std model) (cs_ok_uinv _ _ _ _ _ _ (U_cl1 data) E tCL1 fx _ _ _ HC1 ltac:(intros _; unfold U_cl1, L; rewrite <- Hlen; exact UL))).
  - (* [comment removed for export] *)
    set (E' := tenv E TH_CL).
    assert (HEB : eb E' 7 = hdr) by (unfold E'; cbn [tenv eb]; exact UB).
    assert (Hhdr3 : length hdr = 3%nat) by (unfold hdr; rewrite length_firstn; lia).
    assert (Hnth : forall i, (i < 3)%nat -> nth i hdr (Z_to_bv 8 0) = nth i data (Z_to_bv 8 0)).
    { intros i Hi. unfold DrvS2Sound.hdr. clear -Hi HL3.
      destruct data as [|d0 [|d1 [|d2 drest]]]; [cbn in HL3; lia | cbn in HL3; lia | cbn in HL3; lia |].
      destruct i as [|[|[|i]]]; try reflexivity; lia. }
    assert (HBi : forall i, (i < 3)%nat -> edenot E' (EVar (4 + i)) = blob_val false (eb E' 7) (Z.of_nat i) 1 /\ uE E' (EVar (4 + i)) = hdr_byte data i).
    { intros i Hi.
      assert (Ev : edenot E' (EVar (4 + i)) = blob_val false (eb E' 7) (Z.of_nat i) 1).
      { unfold E'. destruct i as [|[|[|i]]]; try lia; reflexivity. }
      split; [exact Ev|]. unfold uE. rewrite Ev, HEB. unfold blob_val, blob_bytes. rewrite Nat2Z.id.
      replace (firstn 1 (skipn i hdr)) with [nth i hdr (Z_to_bv 8 0)].
      2: { revert Hi. rewrite <- Hhdr3. generalize hdr. clear. induction i as [|i IH]; intros l Hl; destruct l as [|x l]; cbn in Hl |- *; try lia; [reflexivity|]. apply IH. lia. }
      rewrite bytes_le_single', u64_lit by (pose proof (u8_range (nth i hdr (Z_to_bv 8 0))); lia). unfold hdr_byte. rewrite Hnth by lia. reflexivity. }
    destruct (HBi 0%nat ltac:(lia)) as [Ev0 Hb0]. destruct (HBi 1%nat ltac:(lia)) as [Ev1 Hb1]. destruct (HBi 2%nat ltac:(lia)) as [Ev2 Hb2].
    cbn [plus] in Ev0, Hb0, Ev1, Hb1, Ev2, Hb2.
    assert (HU3 : U_cl3 data E').
    { split; [| repeat split; assumption]. change (uE E' LEN) with (uE E LEN). rewrite UL, Hlen. reflexivity. }
    destruct (entails_t_tenv PERM_Tc TOP (m_fs model) (FDSr p len) (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0) (U_rd data len cap) (U_cl3 data)
                E T_CLb T_CLb TH_CL fx R M model HC selfent_CLb HU3) as [HC' _]. fold E' in HC'.
    destruct HU3 as (UL' & U0 & U1 & U2).
    pose proof (kn_In_ok TOP M0 _ _ _ E' T_CLb fx R M model (KBlob (SA BUF 0) (ELit 3) 7) HC' ltac:(in_list_solve)) as HBLOB.
    pose proof (hdr_kword E' M 0 ltac:(lia) HBLOB Ev0) as KW0. pose proof (hdr_kword E' M 1 ltac:(lia) HBLOB Ev1) as KW1. pose proof (hdr_kword E' M 2 ltac:(lia) HBLOB Ev2) as KW2.
    cbn [plus Z.of_nat Pos.of_succ_nat Pos.succ] in KW0, KW1, KW2.
    assert (HHDR : Forall (kentry_ok RSEGS E' M) knHDR).
    { unfold knHDR. pose proof (hdr_byte_range' data 0). pose proof (hdr_byte_range' data 1). pose proof (hdr_byte_range' data 2).
      unfold uE in U0, U1, U2. unfold nthb, hdr_byte in *.
      constructor; [cbn [kentry_ok]; lia|]. constructor; [cbn [kentry_ok]; lia|]. constructor; [cbn [kentry_ok]; lia|].
      constructor; [cbn [kentry_ok]; pose proof (u64_range (edenot E' B1S)); lia|].
      constructor; [exact KW0|]. constructor; [exact KW1|]. constructor; [exact KW2|]. constructor. }
    assert (HCAP' : kentry_ok RSEGS E' M (KRange CAP 65536 (2 ^ 26))) by (eapply (kn_In_ok TOP M0); [exact HC' | in_list_solve]).
    pose proof (cfglenZ_hdr data E' U0 U1) as Hcfg. pose proof (hdr_cfglen_range data) as Hcfgr.
    destruct (Z.ltb_spec (Z.of_nat (length data)) (6 + hdr_cfglen data)) as [Hov|Hfit].
    + (* [comment removed for export] *)
      assert (HOVX : kentry_ok RSEGS E' M (KRange OVX 0 32767)).
      { cbn [kentry_ok]. fold (uE E' OVX).
        assert (HB : eqm (uE E' OVX) (cfglenZ E' + 5 - uE E' LEN)).
        { unfold OVX, esub, eadd, uE. rewrite mkAlu_denot. eapply eqm_trans; [apply u_sub_eqm|]. rewrite mkAlu_denot.
          unfold Z.sub. apply eqm_add; [| exists 0; lia].
          eapply eqm_trans; [apply u_add_eqm|]. cbn [edenot]. unfold cfglenZ, uE. apply eqm_add; [apply eqm_refl | apply eqm_u_lit]. }
        rewrite Hcfg, UL' in HB. destruct HB as [q Hq]. pose proof (u64_range (edenot E' OVX)) as HR. unfold uE in Hq |- *. unfold L in Hq. nia. }
      assert (HC2 : cs_okR TOP (m_fs model) fds_std M0 (U_cl3 data) E' tCL2 fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 0))
                      (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds fds_std model)).
      { eapply (xfer_ok TOP (m_fs model) (FDSr p len) fds_std M0 (U_cl3 data) E' T_CLb tCL2 (ELit 0)
                  ([KRange LEN 6 (2 ^ 26 - 1); KRange OVX 0 32767] ++ knHDR) (RA_CLOSE :: knB));
          [exact HC' | reflexivity | reflexivity | reflexivity | exact sub_CLb_B | exact hav_B
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia |].
        constructor; [cbn [kentry_ok]; unfold uE in UL'; unfold L in UL'; lia|]. constructor; [exact HOVX | exact HHDR]. }
      cbn [write_to_mem] in HC2.
      replace (t_die msg_overrun (m_fs model)) with (t_die msg_overrun (m_fs (with_fds fds_std model))) by reflexivity.
      exact (CL2_sound E' fx _ _ (with_fds fds_std model) HC2).
    + (* [comment removed for export] *)
      assert (HPAYX : kentry_ok RSEGS E' M (KRange PAYX 0 (2 ^ 26))).
      { cbn [kentry_ok]. fold (uE E' PAYX). pose proof (uE_PAYX E') as HB. unfold paylenZ in HB. rewrite Hcfg, UL' in HB.
        destruct HB as [q Hq]. pose proof (u64_range (edenot E' PAYX)) as HR. unfold uE in Hq |- *. unfold L in Hq. nia. }
      assert (HC3 : cs_okR TOP (m_fs model) fds_std M0 (U_cl3 data) E' tCL3 fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 0))
                      (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds fds_std model)).
      { eapply (xfer_ok TOP (m_fs model) (FDSr p len) fds_std M0 (U_cl3 data) E' T_CLb tCL3 (ELit 0)
                  ([KRange LEN 6 (2 ^ 26 - 1); KRange PAYX 0 (2 ^ 26)] ++ knHDR) (RA_CLOSE :: knB));
          [exact HC' | reflexivity | reflexivity | reflexivity | exact sub_CLb_B | exact hav_B
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia |].
        constructor; [cbn [kentry_ok]; unfold uE in UL'; unfold L in UL'; lia|]. constructor; [exact HPAYX | exact HHDR]. }
      cbn [write_to_mem] in HC3. unfold T_PAY in *.
      replace (m_fs model) with (m_fs (with_fds fds_std model)) by reflexivity.
      exact (CL3_sound E' fx _ _ (with_fds fds_std model) HC3).
Qed.

(* [comment removed for export] *)
Lemma close_hole_n : forall len (U : env -> Prop) E fx R M model,
  len = L -> L <= 2 -> (U E -> uE E LEN = len) ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 U E T_CLn fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (t_body data (m_fs model)).
Proof.
  intros len U E fx R M model Hlen HL2 HUL HC.
  destruct ecall_CLn as (Hec & H17 & H10).
  change P_ECALL with (pc T_CLn).
  eapply (close_step SR p TOP M0 (m_fs model) _ E T_CLn fx R M model len); [exact HC | exact Hec | reflexivity | exact H17 | exact H10 |].
  pose proof (HUL (co_uinv HC)) as UL.
  assert (HCAP : kentry_ok RSEGS E M (KRange CAP 65536 65536)) by (eapply (kn_In_ok TOP M0); [exact HC | in_list_solve]).
  unfold t_body. unfold L in *.
  replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
  replace (Z.of_nat (length data) <? 6) with true by (symmetry; apply Z.ltb_lt; lia).
  assert (HC1 : cs_okR TOP (m_fs model) fds_std M0 U E tCL1 fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 0))
                  (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds fds_std model)).
  { eapply (xfer_ok TOP (m_fs model) (FDSr p len) fds_std M0 U E T_CLn tCL1 (ELit 0)
              [KRange LEN 0 5; KRange CAP 65536 (2 ^ 26)] (RA_CLOSE :: knBC));
      [exact HC | reflexivity | reflexivity | reflexivity | exact sub_CLn_1 | exact hav_BC
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia |].
    constructor; [cbn [kentry_ok]; unfold uE in UL; lia|]. constructor; [cbn [kentry_ok] in HCAP |- *; lia | constructor]. }
  cbn [write_to_mem] in HC1.
  replace (t_die msg_short (m_fs model)) with (t_die msg_short (m_fs (with_fds fds_std model))) by reflexivity.
  exact (CL1_sound E fx _ _ (with_fds fds_std model) (cs_ok_uinv _ _ _ _ _ _ (U_cl1 data) E tCL1 fx _ _ _ HC1 ltac:(intros HU; unfold U_cl1, L; rewrite <- Hlen; exact (HUL HU)))).
Qed.
End Close.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tenv_ev : forall E th i e, nth_error th i = Some e -> ev (tenv E th) i = edenot E e.
Proof.
  intros E th i e H. cbn [tenv ev]. destruct (Nat.ltb_spec i (length th)) as [Hl|Hl].
  - rewrite (nth_error_nth _ _ _ H). reflexivity.
  - exfalso. apply nth_error_None in Hl. rewrite Hl in H. discriminate.
Qed.
Lemma tenv_uE : forall E th i e, nth_error th i = Some e -> uE (tenv E th) (EVar i) = uE E e.
Proof. intros E th i e H. unfold uE. cbn [edenot]. rewrite (tenv_ev E th i e H). reflexivity. Qed.
Lemma tenv_eb : forall E th, eb (tenv E th) = eb E. Proof. reflexivity. Qed.

Lemma RD_has_nil : forall data cap fs, RD data cap fs [].
Proof. intros. unfold RD. apply t_body_has_nil. Qed.

(* [comment removed for export] *)
Lemma HSof1_stmt : forall {RC : run_ceil} PERMc TOP FS0 FDS0 AINV (U : env -> Prop) (HOLES : nat -> env -> Fs.Fs -> TSet) (RZ : GPS.rz_t) (a : acs),
  (forall E fx R M model, GPS.cs_ok RSEGS PERMc TOP FS0 FDS0 AINV fx_ok U E a fx R M model -> RZ (cfgF RSEGS fx R (pc a) M model) (HOLES 1%nat E (m_fs model))) ->
  GPS.holes_stmt RSEGS (HSof1 a) PERMc TOP FS0 FDS0 AINV fx_ok U HOLES RZ.
Proof. intros RC PERMc TOP FS0 FDS0 AINV U HOLES RZ a H h ch Hh. destruct h as [|[|h]]; cbn [HSof1] in Hh; [discriminate Hh | | discriminate Hh]. injection Hh as <-. exact H. Qed.
Lemma HSof2_stmt : forall {RC : run_ceil} PERMc TOP FS0 FDS0 AINV (U : env -> Prop) (HOLES : nat -> env -> Fs.Fs -> TSet) (RZ : GPS.rz_t) (a b : acs),
  (forall E fx R M model, GPS.cs_ok RSEGS PERMc TOP FS0 FDS0 AINV fx_ok U E a fx R M model -> RZ (cfgF RSEGS fx R (pc a) M model) (HOLES 1%nat E (m_fs model))) ->
  (forall E fx R M model, GPS.cs_ok RSEGS PERMc TOP FS0 FDS0 AINV fx_ok U E b fx R M model -> RZ (cfgF RSEGS fx R (pc b) M model) (HOLES 2%nat E (m_fs model))) ->
  GPS.holes_stmt RSEGS (HSof2 a b) PERMc TOP FS0 FDS0 AINV fx_ok U HOLES RZ.
Proof.
  intros RC PERMc TOP FS0 FDS0 AINV U HOLES RZ a b Ha Hb h ch Hh.
  destruct h as [|[|[|h]]]; cbn [HSof2] in Hh; [discriminate Hh | | | discriminate Hh]; injection Hh as <-; [exact Ha | exact Hb].
Qed.

(* [comment removed for export] *)
Inductive rkind := RKb (w : want) | RKn | RK1.
Definition T_of (k : rkind) : acs := match k with RKb w => T_RDb w | RKn => T_RDn | RK1 => T_RD1 end.
Definition is_pow64k (cap : Z) : Prop := exists j, 0 <= j <= 10 /\ cap = 65536 * 2 ^ j.

Section Rounds.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GPLAIN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okR TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok U).
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD APLAIN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GPLAIN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzE.ce.
Variables (p : Fs.path) (data : list byte) (TOP : Z) (M0 : word -> option byte).
#[local] Notation L := (L data).
#[local] Notation LB := (LB data).
#[local] Notation hdr := (hdr data).
(* [comment removed for export] *)
Hypothesis REF_sound : forall len E fx R M model,
  cs_okR TOP (m_fs model) (FDSr p (len + (2 ^ 26 - len))) M0 (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVRb) M model) (t_die msg_refused (m_fs model)).

Definition U_of (k : rkind) (len cap : Z) : env -> Prop := match k with RK1 => U_1 data | _ => U_rd data len cap end.
Definition WF (k : rkind) (len cap : Z) : Prop :=
  match k with
  | RKb _ => 3 <= len /\ is_pow64k cap
  | RKn => 1 <= len <= 2 /\ len = L /\ cap = 65536
  | RK1 => len = 0 /\ cap = 65536
  end.
(* [comment removed for export] *)
Definition RDH (m : nat) : Prop := forall k len cap E fx R M model,
  (Z.to_nat (L - len) < m)%nat -> WF k len cap -> 0 <= len <= L ->
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_of k len cap) E (T_of k) fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (RD data cap (m_fs model)).

Lemma planV0_ok : GPS.gplan_ok planV0 = true. Proof. reflexivity. Qed.
Lemma planVS_ok : GPS.gplan_ok planVS = true. Proof. reflexivity. Qed.
Lemma planVF_ok : GPS.gplan_ok planVF = true. Proof. reflexivity. Qed.
Lemma planV1F_ok : GPS.gplan_ok planV1F = true. Proof. reflexivity. Qed.
Lemma planV1S_ok : GPS.gplan_ok planV1S = true. Proof. reflexivity. Qed.
Lemma planR0_ok : GPS.gplan_ok planR0 = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma thV0b : nth_error (TH hV0b T_CLb []) 2 = Some CAP /\ nth_error (TH hV0b T_CLb []) 3 = Some LEN /\ nth_error (TH hV0b T_CLb []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma V0b_sound : forall len cap E fx R M model,
  len = L -> 3 <= L -> L < cap -> cap <= 2 ^ 26 ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len cap) E tV0b fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV0b) M model) (t_body data (m_fs model)).
Proof.
  intros len cap E fx R M model Hlen HL3 HLc Hc26 HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p len) M0 (fds3_1 _ _) (fds3_2 _ _) (U_rd data len cap) (U_rd_agree data len cap)
            (HSof1 hV0b) (fun _ _ fs => t_body data fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_body_has_nil data fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV0 tV0b (SHole 1) E fx R M model planV0_ok certV0b HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'.
  destruct thV0b as (T2 & T3 & T4). destruct (co_uinv HC') as (UL & UC & UF & UB).
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p len) _ (U_rd data len cap) (U_rd data len cap) E' hV0b T_CLb [] fx' R' M' model' HC' entV0b) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ T3); exact UL|]. split; [rewrite (tenv_uE _ _ _ _ T2); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc T_CLb) with P_ECALL. pose proof (co_fs HC') as Hfs. rewrite <- Hfs in HC2.
  eapply (close_hole_b SR SRX HFR HMB HMA GC_T FZN_sound FZE_sound p data TOP M0 len cap); [exact Hlen | exact HL3 | lia | exact HC2].
Qed.

Lemma LB_eq : L < 2 ^ 40 -> LB = L.
Proof. intros H. unfold DrvS2Sound.LB. lia. Qed.

Lemma thVSb1 : nth_error (TH hVSb1 (T_RDb WA) []) 2 = Some CAP /\ nth_error (TH hVSb1 (T_RDb WA) []) 3 = Some FLEN /\ nth_error (TH hVSb1 (T_RDb WA) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma thVSb2 : nth_error (TH hVSb2 (T_RDb WB) []) 2 = Some CAP /\ nth_error (TH hVSb2 (T_RDb WB) []) 3 = Some FLEN /\ nth_error (TH hVSb2 (T_RDb WB) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma VSb_sound : forall m len cap E fx R M model,
  RDH m -> (0 < m)%nat -> 3 <= len -> len < L -> L < cap -> is_pow64k cap ->
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p L) M0 (U_rd data len cap) E tVSb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVSb) M model) (RD data cap (m_fs model)).
Proof.
  intros m len cap E fx R M model IH Hm Hlen3 HlenL HLc Hpow Hfs HC.
  assert (W1 : (Z.to_nat (L - L) < m)%nat) by (rewrite Z.sub_diag; exact Hm).
  assert (W2 : WF (RKb WA) L cap /\ WF (RKb WB) L cap) by (split; split; [lia | exact Hpow | lia | exact Hpow]).
  assert (W3 : 0 <= L <= L) by lia.
  assert (Hc26 : cap <= 2 ^ 26) by (destruct Hpow as (j & Hj & ->); pose proof (Z.pow_le_mono_r 2 j 10 ltac:(lia) ltac:(lia)); change (2 ^ 26) with (65536 * 2 ^ 10); nia).
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p L) M0 (fds3_1 _ _) (fds3_2 _ _) (U_rd data len cap) (U_rd_agree data len cap)
            (HSof2 hVSb1 hVSb2) (fun _ _ fs => RD data cap fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data cap fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planVS tVSb (SHole 1) E fx R M model planVS_ok certVSb HC eq_refl).
  apply HSof2_stmt; intros E' fx' R' M' model' HC'; destruct (co_uinv HC') as (UL & UC & UF & UB); pose proof (co_fs HC') as Hfs'.
  - destruct thVSb1 as (T2 & T3 & T4).
    destruct (ENT_tenv PERM_Tc TOP _ (FDSr p L) _ (U_rd data len cap) (U_rd data L cap) E' hVSb1 (T_RDb WA) [] fx' R' M' model' HC' entVSb1) as [HC2 Hpc].
    { split; [rewrite (tenv_uE _ _ _ _ T3), UF; apply LB_eq; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
    rewrite <- Hpc. change (pc (T_RDb WA)) with P_ECALL. rewrite <- Hfs' in HC2.
    apply (IH (RKb WA) L cap _ fx' R' M' model' W1 (proj1 W2) W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
  - destruct thVSb2 as (T2 & T3 & T4).
    destruct (ENT_tenv PERM_Tc TOP _ (FDSr p L) _ (U_rd data len cap) (U_rd data L cap) E' hVSb2 (T_RDb WB) [] fx' R' M' model' HC' entVSb2) as [HC2 Hpc].
    { split; [rewrite (tenv_uE _ _ _ _ T3), UF; apply LB_eq; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
    rewrite <- Hpc. change (pc (T_RDb WB)) with P_ECALL. rewrite <- Hfs' in HC2.
    apply (IH (RKb WB) L cap _ fx' R' M' model' W1 (proj2 W2) W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

Lemma thVPb1 : nth_error (TH hVPb1 (T_RDb WA) []) 2 = Some CAP /\ nth_error (TH hVPb1 (T_RDb WA) []) 3 = Some (EAlu Instr.ALU_ADD LEN (ELit 65536)) /\ nth_error (TH hVPb1 (T_RDb WA) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma thVPb2 : nth_error (TH hVPb2 (T_RDb WB) []) 2 = Some CAP /\ nth_error (TH hVPb2 (T_RDb WB) []) 3 = Some (EAlu Instr.ALU_ADD LEN (ELit 65536)) /\ nth_error (TH hVPb2 (T_RDb WB) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma uE_add_lit : forall E e c, 0 <= c -> uE E e + c < 2 ^ 64 -> uE E (EAlu Instr.ALU_ADD e (ELit c)) = uE E e + c.
Proof.
  intros E e c Hc Hb. unfold uE in *. cbn [edenot]. rewrite u_add64, u64_lit by (pose proof (u64_range (edenot E e)); lia).
  apply Z.mod_small. pose proof (u64_range (edenot E e)). lia.
Qed.
Lemma uE_mul2 : forall E e, 2 * uE E e < 2 ^ 64 -> uE E (EMd Instr.M_MUL (ELit 2) e) = 2 * uE E e.
Proof.
  intros E e Hb. unfold uE in *. cbn [edenot]. rewrite u_mul64, u64_lit by lia. apply Z.mod_small. pose proof (u64_range (edenot E e)). lia.
Qed.

(* [comment removed for export] *)
Lemma VPb_sound : forall m len cap E fx R M model,
  RDH m -> (Z.to_nat (L - (len + 65536)) < m)%nat -> 3 <= len -> len + 65536 <= L -> len + 65536 < cap -> is_pow64k cap ->
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p (len + 65536)) M0 (U_rd data len cap) E tVPb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVPb) M model) (RD data cap (m_fs model)).
Proof.
  intros m len cap E fx R M model IH Hm Hlen3 HlenL HLc Hpow Hfs HC.
  assert (W2 : WF (RKb WA) (len + 65536) cap /\ WF (RKb WB) (len + 65536) cap) by (split; split; [lia | exact Hpow | lia | exact Hpow]).
  assert (W3 : 0 <= len + 65536 <= L) by lia.
  assert (Hc26 : cap <= 2 ^ 26) by (destruct Hpow as (j & Hj & ->); pose proof (Z.pow_le_mono_r 2 j 10 ltac:(lia) ltac:(lia)); change (2 ^ 26) with (65536 * 2 ^ 10); nia).
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p (len + 65536)) M0 (fds3_1 _ _) (fds3_2 _ _) (U_rd data len cap) (U_rd_agree data len cap)
            (HSof2 hVPb1 hVPb2) (fun _ _ fs => RD data cap fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data cap fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planVS tVPb (SHole 1) E fx R M model planVS_ok certVPb HC eq_refl).
  apply HSof2_stmt; intros E' fx' R' M' model' HC'; destruct (co_uinv HC') as (UL & UC & UF & UB); pose proof (co_fs HC') as Hfs'.
  - destruct thVPb1 as (T2 & T3 & T4).
    destruct (ENT_tenv PERM_Tc TOP _ (FDSr p (len + 65536)) _ (U_rd data len cap) (U_rd data (len + 65536) cap) E' hVPb1 (T_RDb WA) [] fx' R' M' model' HC' entVPb1) as [HC2 Hpc].
    { split; [rewrite (tenv_uE _ _ _ _ T3), uE_add_lit, UL; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
    rewrite <- Hpc. change (pc (T_RDb WA)) with P_ECALL. rewrite <- Hfs' in HC2.
    apply (IH (RKb WA) (len + 65536) cap _ fx' R' M' model' Hm (proj1 W2) W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
  - destruct thVPb2 as (T2 & T3 & T4).
    destruct (ENT_tenv PERM_Tc TOP _ (FDSr p (len + 65536)) _ (U_rd data len cap) (U_rd data (len + 65536) cap) E' hVPb2 (T_RDb WB) [] fx' R' M' model' HC' entVPb2) as [HC2 Hpc].
    { split; [rewrite (tenv_uE _ _ _ _ T3), uE_add_lit, UL; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
    rewrite <- Hpc. change (pc (T_RDb WB)) with P_ECALL. rewrite <- Hfs' in HC2.
    apply (IH (RKb WB) (len + 65536) cap _ fx' R' M' model' Hm (proj2 W2) W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

Lemma thVFb : nth_error (TH hVFb (T_RDb WA) []) 2 = Some (EMd Instr.M_MUL (ELit 2) CAP) /\ nth_error (TH hVFb (T_RDb WA) []) 3 = Some CAP /\ nth_error (TH hVFb (T_RDb WA) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma VFb_sound : forall m len cap E fx R M model,
  RDH m -> (Z.to_nat (L - cap) < m)%nat -> 3 <= len -> len < cap -> cap <= L -> is_pow64k cap -> 2 * cap <= 2 ^ 26 ->
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p cap) M0 (U_rd data len cap) E tVFb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVFb) M model) (RD data cap (m_fs model)).
Proof.
  intros m len cap E fx R M model IH Hm Hlen3 Hlc HcL Hpow Hc2 Hfs HC.
  assert (Hpow2 : is_pow64k (2 * cap)).
  { destruct Hpow as (j & Hj & ->). exists (j + 1). split; [| rewrite Z.pow_add_r by lia; lia].
    destruct (Z_lt_ge_dec j 10); [lia|]. exfalso. assert (j = 10) by lia. subst j. change (2 ^ 10) with 1024 in Hc2. lia. }
  assert (W2 : WF (RKb WA) cap (2 * cap)) by (split; [lia | exact Hpow2]).
  assert (W3 : 0 <= cap <= L) by lia.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p cap) M0 (fds3_1 _ _) (fds3_2 _ _) (U_rd data len cap) (U_rd_agree data len cap)
            (HSof1 hVFb) (fun _ _ fs => RD data (2 * cap) fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data (2 * cap) fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planVF tVFb (SHole 1) E fx R M model planVF_ok certVFb HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UL & UC & UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct thVFb as (T2 & T3 & T4).
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p cap) _ (U_rd data len cap) (U_rd data cap (2 * cap)) E' hVFb (T_RDb WA) [] fx' R' M' model' HC' entVFb) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ T3); exact UC|]. split; [rewrite (tenv_uE _ _ _ _ T2), uE_mul2, UC; lia|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc (T_RDb WA)) with P_ECALL. rewrite <- Hfs' in HC2.
  apply (IH (RKb WA) cap (2 * cap) _ fx' R' M' model' Hm W2 W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

Lemma thV0n : nth_error (TH hV0n T_CLn []) 3 = Some LEN.
Proof. vm_compute. reflexivity. Qed.
Lemma thV1_0 : nth_error (TH hV1_0 T_CLn []) 3 = Some (ELit 0).
Proof. vm_compute. reflexivity. Qed.
Lemma thV1_Sn : nth_error (TH hV1_Sn T_RDn W1S) 2 = Some (ELit 65536) /\ nth_error (TH hV1_Sn T_RDn W1S) 3 = Some FLEN /\ nth_error (TH hV1_Sn T_RDn W1S) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma thV1_Sb : nth_error (TH hV1_Sb (T_RDb WB) W1S) 2 = Some (ELit 65536) /\ nth_error (TH hV1_Sb (T_RDb WB) W1S) 3 = Some FLEN /\ nth_error (TH hV1_Sb (T_RDb WB) W1S) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma thV1_F : nth_error (TH hV1_F (T_RDb WA) []) 2 = Some (ELit 131072) /\ nth_error (TH hV1_F (T_RDb WA) []) 3 = Some (ELit 65536) /\ nth_error (TH hV1_F (T_RDb WA) []) 4 = Some FLEN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. intros E z Hz. unfold uE. cbn [edenot]. apply u64_lit. exact Hz. Qed.
Lemma pow64k_0 : is_pow64k 65536. Proof. exists 0. split; [lia | reflexivity]. Qed.
Lemma pow64k_1 : is_pow64k 131072. Proof. exists 1. split; [lia | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma V0n_sound : forall len E fx R M model,
  len = L -> L <= 2 ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len 65536) E tV0n fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV0n) M model) (t_body data (m_fs model)).
Proof.
  intros len E fx R M model Hlen HL2 HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p len) M0 (fds3_1 _ _) (fds3_2 _ _) (U_rd data len 65536) (U_rd_agree data len 65536)
            (HSof1 hV0n) (fun _ _ fs => t_body data fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_body_has_nil data fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV0 tV0n (SHole 1) E fx R M model planV0_ok certV0n HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UL & UC & UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p len) _ (U_rd data len 65536) (fun E => uE E LEN = len) E' hV0n T_CLn [] fx' R' M' model' HC' entV0n) as [HC2 Hpc].
  { rewrite (tenv_uE _ _ _ _ thV0n). exact UL. }
  rewrite <- Hpc. change (pc T_CLn) with P_ECALL. rewrite <- Hfs' in HC2.
  eapply (close_hole_n SR SRX HFR HMB p data TOP M0 len); [exact Hlen | exact HL2 | intros HU; exact HU | exact HC2].
Qed.

(* [comment removed for export] *)
Lemma V1_0_sound : forall E fx R M model,
  L = 0 ->
  cs_okR TOP (m_fs model) (FDSr p 0) M0 (U_1 data) E tV1_0 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV1_0) M model) (t_body data (m_fs model)).
Proof.
  intros E fx R M model HL0 HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p 0) M0 (fds3_1 _ _) (fds3_2 _ _) (U_1 data) (U_1_agree data)
            (HSof1 hV1_0) (fun _ _ fs => t_body data fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_body_has_nil data fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV0 tV1_0 (SHole 1) E fx R M model planV0_ok certV1_0 HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. pose proof (co_fs HC') as Hfs'.
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p 0) _ (U_1 data) (fun E => uE E LEN = 0) E' hV1_0 T_CLn [] fx' R' M' model' HC' entV1_0) as [HC2 Hpc].
  { rewrite (tenv_uE _ _ _ _ thV1_0). apply uE_lit. lia. }
  rewrite <- Hpc. change (pc T_CLn) with P_ECALL. rewrite <- Hfs' in HC2.
  eapply (close_hole_n SR SRX HFR HMB p data TOP M0 0); [symmetry; exact HL0 | lia | intros HU; exact HU | exact HC2].
Qed.

(* [comment removed for export] *)
Lemma V1_Sn_sound : forall m E fx R M model,
  RDH m -> (0 < m)%nat -> 1 <= L <= 2 -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p L) M0 (U_1 data) E tV1_Sn fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV1_Sn) M model) (RD data 65536 (m_fs model)).
Proof.
  intros m E fx R M model IH Hm HL Hfs HC.
  assert (W1 : (Z.to_nat (L - L) < m)%nat) by (rewrite Z.sub_diag; exact Hm).
  assert (W2 : WF RKn L 65536) by (cbn; lia).
  assert (W3 : 0 <= L <= L) by lia.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p L) M0 (fds3_1 _ _) (fds3_2 _ _) (U_1 data) (U_1_agree data)
            (HSof1 hV1_Sn) (fun _ _ fs => RD data 65536 fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data 65536 fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV1S tV1_Sn (SHole 1) E fx R M model planV1S_ok certV1_Sn HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct thV1_Sn as (T2 & T3 & T4).
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p L) _ (U_1 data) (U_rd data L 65536) E' hV1_Sn T_RDn W1S fx' R' M' model' HC' entV1_Sn) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ T3), UF; apply LB_eq; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); apply uE_lit; lia|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc T_RDn) with P_ECALL. rewrite <- Hfs' in HC2.
  apply (IH RKn L 65536 _ fx' R' M' model' W1 W2 W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

(* [comment removed for export] *)
Lemma V1_Sb_sound : forall m E fx R M model,
  RDH m -> (0 < m)%nat -> 3 <= L <= 65535 -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p L) M0 (U_1 data) E tV1_Sb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV1_Sb) M model) (RD data 65536 (m_fs model)).
Proof.
  intros m E fx R M model IH Hm HL Hfs HC.
  assert (W1 : (Z.to_nat (L - L) < m)%nat) by (rewrite Z.sub_diag; exact Hm).
  assert (W2 : WF (RKb WB) L 65536) by (split; [lia | exact pow64k_0]).
  assert (W3 : 0 <= L <= L) by lia.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p L) M0 (fds3_1 _ _) (fds3_2 _ _) (U_1 data) (U_1_agree data)
            (HSof1 hV1_Sb) (fun _ _ fs => RD data 65536 fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data 65536 fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV1S tV1_Sb (SHole 1) E fx R M model planV1S_ok certV1_Sb HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct thV1_Sb as (T2 & T3 & T4).
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p L) _ (U_1 data) (U_rd data L 65536) E' hV1_Sb (T_RDb WB) W1S fx' R' M' model' HC' entV1_Sb) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ T3), UF; apply LB_eq; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); apply uE_lit; lia|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc (T_RDb WB)) with P_ECALL. rewrite <- Hfs' in HC2.
  apply (IH (RKb WB) L 65536 _ fx' R' M' model' W1 W2 W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

(* [comment removed for export] *)
Lemma V1_F_sound : forall m E fx R M model,
  RDH m -> (Z.to_nat (L - 65536) < m)%nat -> 65536 <= L -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p 65536) M0 (U_1 data) E tV1_F fx R M model ->
  RZ (cfgF RSEGS fx R (pc tV1_F) M model) (RD data 65536 (m_fs model)).
Proof.
  intros m E fx R M model IH Hm HL Hfs HC.
  assert (W2 : WF (RKb WA) 65536 131072) by (split; [lia | exact pow64k_1]).
  assert (W3 : 0 <= 65536 <= L) by lia.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p 65536) M0 (fds3_1 _ _) (fds3_2 _ _) (U_1 data) (U_1_agree data)
            (HSof1 hV1_F) (fun _ _ fs => RD data 131072 fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data 131072 fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planV1F tV1_F (SHole 1) E fx R M model planV1F_ok certV1_F HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct thV1_F as (T2 & T3 & T4).
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p 65536) _ (U_1 data) (U_rd data 65536 131072) E' hV1_F (T_RDb WA) [] fx' R' M' model' HC' entV1_F) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ T3); apply uE_lit; lia|]. split; [rewrite (tenv_uE _ _ _ _ T2); apply uE_lit; lia|]. split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc (T_RDb WA)) with P_ECALL. rewrite <- Hfs' in HC2.
  apply (IH (RKb WA) 65536 131072 _ fx' R' M' model' Hm W2 W3 ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ecall_RDb : forall w, is_ecall_at RSEGS (T_RDb w) = true /\ reg_lit (T_RDb w) 17 = Some 63 /\ reg_lit (T_RDb w) 10 = Some 3 /\ reg_lit (T_RDb w) 11 = Some READ_STAGE.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma ecall_RDn : is_ecall_at RSEGS T_RDn = true /\ reg_lit T_RDn 17 = Some 63 /\ reg_lit T_RDn 10 = Some 3 /\ reg_lit T_RDn 11 = Some READ_STAGE.
Proof. vm_compute; repeat split; reflexivity. Qed.
Lemma ecall_RD1 : is_ecall_at RSEGS T_RD1 = true /\ reg_lit T_RD1 17 = Some 63 /\ reg_lit T_RD1 10 = Some 3 /\ reg_lit T_RD1 11 = Some READ_STAGE.
Proof. vm_compute; repeat split; reflexivity. Qed.
Lemma sub_RDb : forall w, forallb (fun K => existsb (kentry_eqb K) (kn (T_RDb w))) (RA_READ :: knB) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma sub_RDn : forallb (fun K => existsb (kentry_eqb K) (kn T_RDn)) (RA_READ :: knN) = true. Proof. vm_compute; reflexivity. Qed.
Lemma sub_RD1 : forallb (fun K => existsb (kentry_eqb K) (kn T_RD1)) (RA_READ :: kn1) = true. Proof. vm_compute; reflexivity. Qed.
Lemma hav_RB : kn_havoc (RA_READ :: knB) (ELit 0) READ_STAGE (ELit 65536) = RA_READ :: knB. Proof. vm_compute; reflexivity. Qed.
Lemma hav_RN : kn_havoc (RA_READ :: knN) (ELit 0) READ_STAGE (ELit 65536) = RA_READ :: knN. Proof. vm_compute; reflexivity. Qed.
Lemma hav_R1 : kn_havoc (RA_READ :: kn1) (ELit 0) READ_STAGE (ELit 65536) = RA_READ :: kn1. Proof. vm_compute; reflexivity. Qed.

Lemma uE_esub : forall E a b, eqm (uE E (esub a b)) (uE E a - uE E b).
Proof. intros E a b. unfold esub, uE. rewrite mkAlu_denot. apply u_sub_eqm. Qed.
(* [comment removed for export] *)
Lemma esub_exact : forall E a b lo hi, lo <= uE E (esub a b) <= hi -> 0 <= lo -> hi < 2 ^ 62 ->
  - 2 ^ 62 < uE E a - uE E b < 2 ^ 62 -> uE E (esub a b) = uE E a - uE E b.
Proof.
  intros E a b lo hi Hr Hlo Hhi Hd. destruct (uE_esub E a b) as [q Hq]. pose proof (uE_rng E (esub a b)) as HR. nia.
Qed.
Lemma word_of_uE_esub : forall E a b z, uE E (esub a b) = z -> edenot E (esub a b) = Z_to_bv 64 z.
Proof. intros E a b z H. pose proof (uE_rng E (esub a b)) as HR. apply bv_eq. rewrite u64_lit by lia. unfold uE in H. exact H. Qed.
Lemma len_word_nat : forall (bs : list byte), len_word bs = Z_to_bv 64 (Z.of_nat (length bs)). Proof. reflexivity. Qed.
Lemma length_file_read_Z : forall len cnt, 0 <= len -> 0 <= cnt -> len + cnt < 2 ^ 64 ->
  Z.of_nat (length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt))) = Z.min cnt (Z.max 0 (L - len)).
Proof.
  intros len cnt Hl Hc Hb. rewrite length_file_read. unfold word_to_nat. rewrite !u64_lit by lia. unfold DrvS2Sound.L. lia.
Qed.
(* [comment removed for export] *)
Lemma rsblob_ok : forall E M bs, eb E 7 = hdr -> 3 <= Z.of_nat (length bs) <= 65536 -> firstn 3 bs = hdr ->
  kentry_ok RSEGS E (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) RSBLOB.
Proof.
  intros E M bs HE Hl3 Hf. cbn [kentry_ok RSBLOB]. unfold flat, elenZ. rewrite estart_lit0, edenot_lit, u64_lit by lia. rewrite HE.
  assert (Hh3 : length hdr = 3%nat) by (rewrite <- Hf, length_firstn; lia).
  split; [unfold READ_STAGE; lia|]. split; [rewrite Hh3; reflexivity|].
  intros i Hi. rewrite write_to_mem_wbytes.
  pose proof (wbytes_nth bs M (Z_to_bv 64 READ_STAGE) (Z.to_nat i)) as W. rewrite u64_lit in W by (unfold READ_STAGE; lia).
  rewrite Z2Nat.id in W by lia. rewrite W by (unfold READ_STAGE; lia). f_equal. rewrite <- Hf.
  clear -Hi Hl3. revert Hi Hl3. intros Hi Hl3. destruct bs as [|x0 [|x1 [|x2 l]]]; cbn in Hl3; try lia.
  assert (HZ : (Z.to_nat i = 0 \/ Z.to_nat i = 1 \/ Z.to_nat i = 2)%nat) by lia. destruct HZ as [->|[->| ->]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma RDb_want : forall w len cap E fx R M model FDS,
  cs_okR TOP (m_fs model) FDS M0 (U_rd data len cap) E (T_RDb w) fx R M model -> 0 <= len <= 2 ^ 27 -> 0 <= cap <= 2 ^ 27 ->
  match w with
  | WA => bv_unsigned (getr R (Z_to_bv 5 12)) = 65536 /\ 65536 <= cap - len
  | WB => bv_unsigned (getr R (Z_to_bv 5 12)) = cap - len /\ 1 <= cap - len <= 65535
  end.
Proof.
  intros w len cap E fx R M model FDS HC Hlen Hcap. destruct (co_uinv HC) as (UL & UC & UF & UB).
  pose proof (reg_expr_get TOP M0 _ _ _ E (T_RDb w) fx R M model 12 HC ltac:(lia)) as G12.
  change (Z_to_bv 5 (Z.of_nat 12)) with (Z_to_bv 5 12) in G12. rewrite G12. change (reg (T_RDb w) 12) with (K 16). fold (uE E (K 16)).
  destruct w.
  - pose proof (kn_In_ok TOP M0 _ _ _ E (T_RDb WA) fx R M model (KRange (K 16) 65536 65536) HC ltac:(in_list_solve)) as F1.
    pose proof (kn_In_ok TOP M0 _ _ _ E (T_RDb WA) fx R M model (KRange (esub CAP LEN) 65536 (2 ^ 26)) HC ltac:(in_list_solve)) as F2.
    cbn [kentry_ok] in F1, F2. fold (uE E (K 16)) in F1. fold (uE E (esub CAP LEN)) in F2.
    rewrite (esub_exact E CAP LEN 65536 (2 ^ 26) F2) in F2 by (rewrite ?UC, ?UL; lia). rewrite UC, UL in F2. lia.
  - pose proof (kn_In_ok TOP M0 _ _ _ E (T_RDb WB) fx R M model (KRange (esub (K 16) (esub CAP LEN)) 0 0) HC ltac:(in_list_solve)) as F1.
    pose proof (kn_In_ok TOP M0 _ _ _ E (T_RDb WB) fx R M model (KRange (esub CAP LEN) 1 65535) HC ltac:(in_list_solve)) as F2.
    cbn [kentry_ok] in F1, F2. fold (uE E (esub (K 16) (esub CAP LEN))) in F1. fold (uE E (esub CAP LEN)) in F2.
    pose proof (esub_exact E CAP LEN 1 65535 F2 ltac:(lia) ltac:(lia) ltac:(rewrite UC, UL; lia)) as X2. rewrite UC, UL in X2.
    pose proof (uE_rng E (K 16)) as RK. rewrite X2 in F2.
    destruct (uE_esub E (K 16) (esub CAP LEN)) as [q Hq]. rewrite X2 in Hq. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow64k_le : forall cap, is_pow64k cap -> 65536 <= cap <= 2 ^ 26 /\ (2 * cap <= 2 ^ 26 \/ cap = 2 ^ 26).
Proof.
  intros cap (j & Hj & ->). pose proof (Z.pow_le_mono_r 2 j 10 ltac:(lia) ltac:(lia)) as H10. pose proof (Z.pow_nonneg 2 j ltac:(lia)) as Hnn.
  change (2 ^ 26) with (65536 * 2 ^ 10). split; [nia|].
  destruct (Z_lt_ge_dec j 10) as [Hl|Hg]; [left | right; replace j with 10 by lia; reflexivity].
  pose proof (Z.pow_le_mono_r 2 (j + 1) 10 ltac:(lia) ltac:(lia)) as H11. rewrite Z.pow_add_r in H11 by lia. nia.
Qed.

Lemma regs_AR : forall w rv facts, s_regs (a_ss (T_AR rv facts knB LEN CAP (K 17) [(BUF, CAP)])) = sr_upd (s_regs (a_ss (T_RDb w))) 10 rv.
Proof. intros [|] rv facts; reflexivity. Qed.

(* [comment removed for export] *)
Lemma rd_b : forall m, RDH m -> forall w len cap E fx R M model,
  (Z.to_nat (L - len) < Datatypes.S m)%nat -> 3 <= len -> is_pow64k cap -> 0 <= len <= L ->
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len cap) E (T_RDb w) fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (RD data cap (m_fs model)).
Proof.
  intros m IH w len cap E fx R M model Hm Hlen3 Hpow HlenL Hfs HC.
  destruct (pow64k_le cap Hpow) as [Hcap Hcap2]. destruct (co_uinv HC) as (UL & UC & UF & UB).
  destruct (ecall_RDb w) as (Hec & H17 & H10 & H11).
  set (cnt := match w with WA => 65536 | WB => cap - len end).
  assert (Hlen26 : len <= 2 ^ 26).
  { pose proof (kn_In_ok TOP M0 _ _ _ E (T_RDb w) fx R M model (KRange LEN 3 (2 ^ 26 - 1)) HC ltac:(destruct w; in_list_solve)) as F.
    cbn [kentry_ok] in F. fold (uE E LEN) in F. rewrite UL in F. lia. }
  pose proof (RDb_want w len cap E fx R M model _ HC ltac:(lia) ltac:(lia)) as HW.
  assert (Hcnt : bv_unsigned (getr R (Z_to_bv 5 12)) = cnt /\ 1 <= cnt <= 65536 /\ cnt <= cap - len /\ (w = WA -> 65536 <= cap - len)).
  { subst cnt. destruct w; [destruct HW as [HW1 HW2] | destruct HW as [HW1 HW2]]; (split; [exact HW1|]); repeat split; try lia; intros X; try discriminate X; lia. }
  destruct Hcnt as (Hc1 & Hc2 & Hc3 & Hc4). clear HW.
  (* [comment removed for export] *)
  assert (HCL : uE E (esub CAP LEN) = cap - len).
  { destruct (uE_esub E CAP LEN) as [q Hq]. rewrite UC, UL in Hq. pose proof (uE_rng E (esub CAP LEN)). nia. }
  replace P_ECALL with (pc (T_RDb w)) by (destruct w; reflexivity).
  eapply (read_step SR p data TOP M0 (m_fs model) _ E (T_RDb w) fx R M model len cnt);
    [exact HC | exact Hec | destruct w; reflexivity | exact H17 | exact H10 | exact H11 | exact Hc1 | lia | exact Hfs | lia | lia |].
  cbv zeta. set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt)).
  pose proof (length_file_read_Z len cnt ltac:(lia) ltac:(lia) ltac:(lia)) as Hn. fold bs in Hn.
  destruct (Z.eq_dec len L) as [HeqL | HneL].
  - (* [comment removed for export] *)
    assert (Hbs : bs = []) by (apply length_zero_iff_nil; lia). rewrite Hbs. cbn [length Z.of_nat]. rewrite Z.add_0_r.
    assert (HC' : cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len cap) E tV0b fx (regupd R (Z_to_bv 5 10) (len_word (@nil byte)))
                   (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds (FDSr p len) model)).
    { eapply (xfer_ok TOP (m_fs model) (FDSr p len) (FDSr p len) M0 (U_rd data len cap) E (T_RDb w) tV0b (ELit 0) [] (RA_READ :: knB));
        [exact HC | apply regs_AR | reflexivity | reflexivity | apply sub_RDb | exact hav_RB
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia | constructor]. }
    change P_AFTER_ECALL with (pc tV0b). change (m_fs model) with (m_fs (with_fds (FDSr p len) model)).
    exact (V0b_sound len cap E fx _ _ (with_fds (FDSr p len) model) HeqL ltac:(lia) ltac:(lia) ltac:(lia) HC').
  - destruct (Z_lt_ge_dec (L - len) cnt) as [Hshort | Hfull].
    + (* [comment removed for export] *)
      assert (HnZ : Z.of_nat (length bs) = L - len) by lia.
      assert (HLB : LB = L) by (apply LB_eq; lia).
      assert (HFL : uE E (esub FLEN LEN) = L - len).
      { destruct (uE_esub E FLEN LEN) as [q Hq]. rewrite UF, UL, HLB in Hq. pose proof (uE_rng E (esub FLEN LEN)). nia. }
      assert (HCF : uE E (esub CAP FLEN) = cap - L).
      { destruct (uE_esub E CAP FLEN) as [q Hq]. rewrite UF, UC, HLB in Hq. pose proof (uE_rng E (esub CAP FLEN)). nia. }
      assert (HC' : cs_okR TOP (m_fs model) (FDSr p L) M0 (U_rd data len cap) E tVSb fx (regupd R (Z_to_bv 5 10) (len_word bs))
                     (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p L) model)).
      { eapply (xfer_ok TOP (m_fs model) (FDSr p len) (FDSr p L) M0 (U_rd data len cap) E (T_RDb w) tVSb (esub FLEN LEN)
                  [KRange FLEN 4 (2 ^ 26); KRange (esub FLEN LEN) 1 65535; KRange (esub CAP FLEN) 1 (2 ^ 26)] (RA_READ :: knB) fx R M model bs);
          [exact HC | apply regs_AR | reflexivity | reflexivity | apply sub_RDb | exact hav_RB
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | lia |].
        - rewrite len_word_nat, HnZ. apply word_of_uE_esub. exact HFL.
        - constructor; [cbn [kentry_ok]; fold (uE E FLEN); rewrite UF, HLB; lia|].
          constructor; [cbn [kentry_ok]; fold (uE E (esub FLEN LEN)); rewrite HFL; lia|].
          constructor; [cbn [kentry_ok]; fold (uE E (esub CAP FLEN)); rewrite HCF; lia | constructor]. }
      replace (len + Z.of_nat (length bs)) with L by lia.
      change P_AFTER_ECALL with (pc tVSb). change (m_fs model) with (m_fs (with_fds (FDSr p L) model)).
      exact (VSb_sound m len cap E fx _ _ (with_fds (FDSr p L) model) IH ltac:(lia) Hlen3 ltac:(lia) ltac:(lia) Hpow Hfs HC').
    + (* [comment removed for export] *)
      assert (HnZ : Z.of_nat (length bs) = cnt) by lia.
      destruct (Z.eq_dec cnt (cap - len)) as [Hfill | Hpart].
      * (* [comment removed for export] *)
        assert (Hrv : edenot E (esub CAP LEN) = len_word bs) by (rewrite len_word_nat, HnZ, Hfill; apply word_of_uE_esub; exact HCL).
        destruct Hcap2 as [Hg2 | Hc26].
        -- (* [comment removed for export] *)
           assert (HC' : cs_okR TOP (m_fs model) (FDSr p cap) M0 (U_rd data len cap) E tVFb fx (regupd R (Z_to_bv 5 10) (len_word bs))
                          (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p cap) model)).
           { eapply (xfer_ok TOP (m_fs model) (FDSr p len) (FDSr p cap) M0 (U_rd data len cap) E (T_RDb w) tVFb (esub CAP LEN)
                       [KRange (esub CAP LEN) 1 65536; KRange CAP 65536 (2 ^ 25)] (RA_READ :: knB) fx R M model bs);
               [exact HC | apply regs_AR | reflexivity | reflexivity | apply sub_RDb | exact hav_RB
               | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hrv | lia |].
             constructor; [cbn [kentry_ok]; fold (uE E (esub CAP LEN)); rewrite HCL; lia|].
             constructor; [cbn [kentry_ok]; fold (uE E CAP); rewrite UC; lia | constructor]. }
           replace (len + Z.of_nat (length bs)) with cap by lia.
           change P_AFTER_ECALL with (pc tVFb). change (m_fs model) with (m_fs (with_fds (FDSr p cap) model)).
           exact (VFb_sound m len cap E fx _ _ (with_fds (FDSr p cap) model) IH ltac:(lia) Hlen3 ltac:(lia) ltac:(lia) Hpow Hg2 Hfs HC').
        -- (* [comment removed for export] *)
           assert (HC' : cs_okR TOP (m_fs model) (FDSr p (len + (2 ^ 26 - len))) M0 (U_rd data len (2 ^ 26)) E tVRb fx (regupd R (Z_to_bv 5 10) (len_word bs))
                          (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p (len + (2 ^ 26 - len))) model)).
           { rewrite <- Hc26. eapply (xfer_ok TOP (m_fs model) (FDSr p len) _ M0 (U_rd data len cap) E (T_RDb w) tVRb (esub CAP LEN)
                       [KRange (esub CAP LEN) 1 65536; KRange CAP (2 ^ 26) (2 ^ 26)] (RA_READ :: knB) fx R M model bs);
               [exact HC | apply regs_AR | reflexivity | reflexivity | apply sub_RDb | exact hav_RB
               | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hrv | lia |].
             constructor; [cbn [kentry_ok]; fold (uE E (esub CAP LEN)); rewrite HCL; lia|].
             constructor; [cbn [kentry_ok]; fold (uE E CAP); rewrite UC; lia | constructor]. }
           replace (len + Z.of_nat (length bs)) with (len + (2 ^ 26 - len)) by lia.
           unfold RD.
           unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; unfold DrvS2Sound.L in *; lia).
           change P_AFTER_ECALL with (pc tVRb). change (m_fs model) with (m_fs (with_fds (FDSr p (len + (2 ^ 26 - len))) model)).
           exact (REF_sound len E fx _ _ (with_fds (FDSr p (len + (2 ^ 26 - len))) model) HC').
      * (* [comment removed for export] *)
        assert (Hw : w = WA) by (destruct w; [reflexivity | exfalso; subst cnt; lia]).
        assert (Hc65 : cnt = 65536) by (subst cnt; rewrite Hw; reflexivity).
        assert (HC' : cs_okR TOP (m_fs model) (FDSr p (len + 65536)) M0 (U_rd data len cap) E tVPb fx (regupd R (Z_to_bv 5 10) (len_word bs))
                       (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p (len + 65536)) model)).
        { eapply (xfer_ok TOP (m_fs model) (FDSr p len) _ M0 (U_rd data len cap) E (T_RDb w) tVPb (ELit 65536)
                    [KRange (esub CAP LEN) 65537 (2 ^ 26)] (RA_READ :: knB) fx R M model bs);
            [exact HC | apply regs_AR | reflexivity | reflexivity | apply sub_RDb | exact hav_RB
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite len_word_nat, HnZ, Hc65; reflexivity | lia |].
          constructor; [cbn [kentry_ok]; fold (uE E (esub CAP LEN)); rewrite HCL; specialize (Hc4 Hw); lia | constructor]. }
        replace (len + Z.of_nat (length bs)) with (len + 65536) by lia.
        change P_AFTER_ECALL with (pc tVPb). change (m_fs model) with (m_fs (with_fds (FDSr p (len + 65536)) model)).
        exact (VPb_sound m len cap E fx _ _ (with_fds (FDSr p (len + 65536)) model) IH ltac:(lia) Hlen3 ltac:(lia) ltac:(lia) Hpow Hfs HC').
Qed.

(* [comment removed for export] *)
Lemma rd_n : forall len E fx R M model,
  1 <= len <= 2 -> len = L -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len 65536) E T_RDn fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (RD data 65536 (m_fs model)).
Proof.
  intros len E fx R M model Hlen HlenL Hfs HC.
  destruct (co_uinv HC) as (UL & UC & UF & UB). destruct ecall_RDn as (Hec & H17 & H10 & H11).
  assert (HCL : uE E (esub CAP LEN) = 65536 - len).
  { destruct (uE_esub E CAP LEN) as [q Hq]. rewrite UC, UL in Hq. pose proof (uE_rng E (esub CAP LEN)). nia. }
  assert (Hc1 : bv_unsigned (getr R (Z_to_bv 5 12)) = 65536 - len).
  { pose proof (reg_expr_get TOP M0 _ _ _ E T_RDn fx R M model 12 HC ltac:(lia)) as G12.
    change (Z_to_bv 5 (Z.of_nat 12)) with (Z_to_bv 5 12) in G12. rewrite G12. change (reg T_RDn 12) with (K 16). fold (uE E (K 16)).
    pose proof (kn_In_ok TOP M0 _ _ _ E T_RDn fx R M model (KRange (esub (K 16) (esub CAP LEN)) 0 0) HC ltac:(in_list_solve)) as F1.
    cbn [kentry_ok] in F1. fold (uE E (esub (K 16) (esub CAP LEN))) in F1.
    pose proof (uE_rng E (K 16)) as RK. destruct (uE_esub E (K 16) (esub CAP LEN)) as [q Hq]. rewrite HCL in Hq. nia. }
  change P_ECALL with (pc T_RDn).
  eapply (read_step SR p data TOP M0 (m_fs model) _ E T_RDn fx R M model len (65536 - len));
    [exact HC | exact Hec | reflexivity | exact H17 | exact H10 | exact H11 | exact Hc1 | lia | exact Hfs | lia | lia |].
  cbv zeta. set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 (65536 - len))).
  pose proof (length_file_read_Z len (65536 - len) ltac:(lia) ltac:(lia) ltac:(lia)) as Hn. fold bs in Hn.
  assert (Hbs : bs = []) by (apply length_zero_iff_nil; lia). rewrite Hbs. cbn [length Z.of_nat]. rewrite Z.add_0_r.
  assert (HC' : cs_okR TOP (m_fs model) (FDSr p len) M0 (U_rd data len 65536) E tV0n fx (regupd R (Z_to_bv 5 10) (len_word (@nil byte)))
                 (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds (FDSr p len) model)).
  { eapply (xfer_ok TOP (m_fs model) (FDSr p len) (FDSr p len) M0 (U_rd data len 65536) E T_RDn tV0n (ELit 0) [] (RA_READ :: knN));
      [exact HC | reflexivity | reflexivity | reflexivity | exact sub_RDn | exact hav_RN
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia | constructor]. }
  change P_AFTER_ECALL with (pc tV0n). change (m_fs model) with (m_fs (with_fds (FDSr p len) model)).
  exact (V0n_sound len E fx _ _ (with_fds (FDSr p len) model) HlenL ltac:(lia) HC').
Qed.

Lemma regs_AR1 : forall rv facts, s_regs (a_ss (T_AR rv facts kn1 (ELit 0) (ELit 65536) BUF [(BUF, ELit 65536)])) = sr_upd (s_regs (a_ss T_RD1)) 10 rv.
Proof. intros rv facts; reflexivity. Qed.
Lemma firstn_file_read0 : forall cnt, 3 <= cnt -> cnt < 2 ^ 64 -> 3 <= L ->
  firstn 3 (file_read data (Z_to_bv 64 0) (Z_to_bv 64 cnt)) = hdr.
Proof.
  intros cnt H3 H64 HL. rewrite file_read_unguarded. unfold word_to_nat. rewrite !u64_lit by lia. cbn [Z.to_nat skipn].
  rewrite firstn_firstn. replace (Nat.min 3 (Z.to_nat cnt)) with 3%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rd_1 : forall m, RDH m -> forall E fx R M model,
  (Z.to_nat L < Datatypes.S m)%nat -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p 0) M0 (U_1 data) E T_RD1 fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (RD data 65536 (m_fs model)).
Proof.
  intros m IH E fx R M model Hm Hfs HC.
  destruct (co_uinv HC) as (UF & UB). destruct ecall_RD1 as (Hec & H17 & H10 & H11).
  assert (Hc1 : bv_unsigned (getr R (Z_to_bv 5 12)) = 65536).
  { pose proof (reg_expr_get TOP M0 _ _ _ E T_RD1 fx R M model 12 HC ltac:(lia)) as G12.
    change (Z_to_bv 5 (Z.of_nat 12)) with (Z_to_bv 5 12) in G12. rewrite G12. change (reg T_RD1 12) with (K 16). fold (uE E (K 16)).
    pose proof (kn_In_ok TOP M0 _ _ _ E T_RD1 fx R M model (KRange (K 16) 65536 65536) HC ltac:(in_list_solve)) as F1.
    cbn [kentry_ok] in F1. fold (uE E (K 16)) in F1. lia. }
  pose proof (Zle_0_nat (length data)) as HL0. change (Z.of_nat (length data)) with L in HL0.
  change P_ECALL with (pc T_RD1).
  eapply (read_step SR p data TOP M0 (m_fs model) _ E T_RD1 fx R M model 0 65536);
    [exact HC | exact Hec | reflexivity | exact H17 | exact H10 | exact H11 | exact Hc1 | lia | exact Hfs | lia | lia |].
  cbv zeta. set (bs := file_read data (Z_to_bv 64 0) (Z_to_bv 64 65536)).
  pose proof (length_file_read_Z 0 65536 ltac:(lia) ltac:(lia) ltac:(lia)) as Hn. fold bs in Hn. rewrite Z.sub_0_r in Hn. rewrite Z.add_0_l.
  destruct (Z.eq_dec L 0) as [HL0' | HLpos].
  - (* [comment removed for export] *)
    assert (Hbs : bs = []) by (apply length_zero_iff_nil; lia). rewrite Hbs. cbn [length Z.of_nat].
    assert (HC' : cs_okR TOP (m_fs model) (FDSr p 0) M0 (U_1 data) E tV1_0 fx (regupd R (Z_to_bv 5 10) (len_word (@nil byte)))
                   (write_to_mem M (Z_to_bv 64 READ_STAGE) []) (with_fds (FDSr p 0) model)).
    { eapply (xfer_ok TOP (m_fs model) (FDSr p 0) (FDSr p 0) M0 (U_1 data) E T_RD1 tV1_0 (ELit 0) [] (RA_READ :: kn1));
        [exact HC | apply regs_AR1 | reflexivity | reflexivity | exact sub_RD1 | exact hav_R1
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia | constructor]. }
    change P_AFTER_ECALL with (pc tV1_0). change (m_fs model) with (m_fs (with_fds (FDSr p 0) model)).
    exact (V1_0_sound E fx _ _ (with_fds (FDSr p 0) model) HL0' HC').
  - assert (HLB : L < 2 ^ 40 -> LB = L) by (intros; apply LB_eq; lia).
    destruct (Z_lt_ge_dec L 65536) as [Hshort | Hbig].
    + (* [comment removed for export] *)
      assert (HnZ : Z.of_nat (length bs) = L) by lia. rewrite HnZ.
      assert (Hrv : edenot E FLEN = len_word bs).
      { rewrite len_word_nat, HnZ. apply bv_eq. pose proof (uE_rng E FLEN) as RF. rewrite u64_lit by lia. unfold uE in UF. rewrite UF. apply HLB. lia. }
      destruct (Z_lt_ge_dec L 3) as [Htiny | H3].
      * (* [comment removed for export] *)
        assert (HC' : cs_okR TOP (m_fs model) (FDSr p L) M0 (U_1 data) E tV1_Sn fx (regupd R (Z_to_bv 5 10) (len_word bs))
                       (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p L) model)).
        { eapply (xfer_ok TOP (m_fs model) (FDSr p 0) (FDSr p L) M0 (U_1 data) E T_RD1 tV1_Sn FLEN [KRange FLEN 1 2] (RA_READ :: kn1) fx R M model bs);
            [exact HC | apply regs_AR1 | reflexivity | reflexivity | exact sub_RD1 | exact hav_R1
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hrv | lia |].
          constructor; [cbn [kentry_ok]; fold (uE E FLEN); rewrite UF, HLB; lia | constructor]. }
        change (m_fs model) with (m_fs (with_fds (FDSr p L) model)).
        change P_AFTER_ECALL with (pc tV1_Sn).
        exact (V1_Sn_sound m E fx _ _ (with_fds (FDSr p L) model) IH ltac:(lia) ltac:(lia) Hfs HC').
      * (* [comment removed for export] *)
        assert (HC' : cs_okR TOP (m_fs model) (FDSr p L) M0 (U_1 data) E tV1_Sb fx (regupd R (Z_to_bv 5 10) (len_word bs))
                       (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p L) model)).
        { eapply (xfer_ok TOP (m_fs model) (FDSr p 0) (FDSr p L) M0 (U_1 data) E T_RD1 tV1_Sb FLEN [KRange FLEN 3 65535; RSBLOB] (RA_READ :: kn1) fx R M model bs);
            [exact HC | apply regs_AR1 | reflexivity | reflexivity | exact sub_RD1 | exact hav_R1
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hrv | lia |].
          constructor; [cbn [kentry_ok]; fold (uE E FLEN); rewrite UF, HLB; lia|].
          constructor; [apply rsblob_ok; [exact UB | lia | apply firstn_file_read0; lia] | constructor]. }
        change (m_fs model) with (m_fs (with_fds (FDSr p L) model)).
        change P_AFTER_ECALL with (pc tV1_Sb).
        exact (V1_Sb_sound m E fx _ _ (with_fds (FDSr p L) model) IH ltac:(lia) ltac:(lia) Hfs HC').
    + (* [comment removed for export] *)
      assert (HnZ : Z.of_nat (length bs) = 65536) by lia. rewrite HnZ.
      assert (HC' : cs_okR TOP (m_fs model) (FDSr p 65536) M0 (U_1 data) E tV1_F fx (regupd R (Z_to_bv 5 10) (len_word bs))
                     (write_to_mem M (Z_to_bv 64 READ_STAGE) bs) (with_fds (FDSr p 65536) model)).
      { eapply (xfer_ok TOP (m_fs model) (FDSr p 0) (FDSr p 65536) M0 (U_1 data) E T_RD1 tV1_F (ELit 65536) [RSBLOB] (RA_READ :: kn1) fx R M model bs);
          [exact HC | apply regs_AR1 | reflexivity | reflexivity | exact sub_RD1 | exact hav_R1
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite len_word_nat, HnZ; reflexivity | lia |].
        constructor; [apply rsblob_ok; [exact UB | lia | apply firstn_file_read0; lia] | constructor]. }
      change P_AFTER_ECALL with (pc tV1_F). change (m_fs model) with (m_fs (with_fds (FDSr p 65536) model)).
      exact (V1_F_sound m E fx _ _ (with_fds (FDSr p 65536) model) IH ltac:(lia) ltac:(lia) Hfs HC').
Qed.

(* [comment removed for export] *)
Theorem rd_main : forall m, RDH m.
Proof.
  induction m as [|m IH].
  - intros k len cap E fx R M model Hm. lia.
  - intros k len cap E fx R M model Hm HWF HlenL Hfs HC. destruct k as [w| |].
    + destruct HWF as [H3 Hpow]. exact (rd_b m IH w len cap E fx R M model Hm H3 Hpow HlenL Hfs HC).
    + destruct HWF as (H12 & HL & ->). exact (rd_n len E fx R M model H12 HL Hfs HC).
    + destruct HWF as (-> & ->). rewrite Z.sub_0_r in Hm. exact (rd_1 m IH E fx R M model Hm Hfs HC).
Qed.

(* [comment removed for export] *)
Theorem RD_sound : forall k len cap E fx R M model,
  WF k len cap -> 0 <= len <= L -> fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p len) M0 (U_of k len cap) E (T_of k) fx R M model ->
  RZ (cfgF RSEGS fx R P_ECALL M model) (RD data cap (m_fs model)).
Proof. intros k len cap E fx R M model. apply (rd_main (Datatypes.S (Z.to_nat (L - len)))). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma thR0 : nth_error (TH hR0 T_RD1 []) 4 = Some FLEN. Proof. vm_compute. reflexivity. Qed.

Theorem R0_sound : forall E fx R M model,
  fs_lookup (m_fs model) p = Some data ->
  cs_okR TOP (m_fs model) (FDSr p 0) M0 (U_1 data) E tR0 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tR0) M model) (RD data 65536 (m_fs model)).
Proof.
  intros E fx R M model Hfs HC.
  refine (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) (FDSr p 0) M0 (fds3_1 _ _) (fds3_2 _ _) (U_1 data) (U_1_agree data)
            (HSof1 hR0) (fun _ _ fs => RD data 65536 fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => RD_has_nil data 65536 fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planR0 tR0 (SHole 1) E fx R M model planR0_ok certR0 HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. destruct (co_uinv HC') as (UF & UB). pose proof (co_fs HC') as Hfs'.
  destruct (ENT_tenv PERM_Tc TOP _ (FDSr p 0) _ (U_1 data) (U_1 data) E' hR0 T_RD1 [] fx' R' M' model' HC' entR0) as [HC2 Hpc].
  { split; [rewrite (tenv_uE _ _ _ _ thR0); exact UF | rewrite tenv_eb; exact UB]. }
  rewrite <- Hpc. change (pc T_RD1) with P_ECALL. rewrite <- Hfs' in HC2.
  pose proof (Zle_0_nat (length data)) as HL0. change (Z.of_nat (length data)) with L in HL0.
  exact (RD_sound RK1 0 65536 _ fx' R' M' model' (conj eq_refl eq_refl) ltac:(lia) ltac:(rewrite Hfs'; exact Hfs) HC2).
Qed.
End Rounds.
