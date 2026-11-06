(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTPlan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTGlue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac in_list_solve := cbn; repeat (first [left; reflexivity | right]).
(* [comment removed for export] *)
Strategy opaque [holeEA holePA holeEB holePB].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma certC3s : CHKs HSC BF FUEL tinC3 planC3 = COk shapeC3.
Proof. vm_compute. reflexivity. Qed.

Lemma certC2s : CHKs HS0 BF FUEL tinC2 planD = COk (shapeD zmsg_overrun). Proof. vm_compute. reflexivity. Qed.
Lemma certC1ns : CHKs HS0 BF FUEL tinC1n planD = COk (shapeD zmsg_short). Proof. vm_compute. reflexivity. Qed.
Lemma planD_ok : GPS.gplan_ok planD = true. Proof. reflexivity. Qed.
Lemma zmsg_short_ok : map (Z_to_bv 8) zmsg_short = msg_short. Proof. vm_compute. reflexivity. Qed.
Lemma zmsg_overrun_ok : map (Z_to_bv 8) zmsg_overrun = msg_overrun. Proof. vm_compute. reflexivity. Qed.
Lemma sd_shapeD : forall HOLES D E fs zm m, map (Z_to_bv 8) zm = m -> t_eq (sd HOLES D E fs (shapeD zm)) (t_die m fs).
Proof.
  intros HOLES D E fs zm m Hm. unfold shapeD, t_die. cbn [sd]. unfold Wp, Spec4.W. cbn [flat_map piece_den]. rewrite app_nil_r, Hm.
  apply Spec4.AgentLib.t_emit_congr. unfold exit_code. apply t_emit_nil_eq. apply t_exit_has_nil.
Qed.

(* [comment removed for export] *)
Lemma holeEA_facts : In (KRange CFGX 0 0) (kn holeEA) /\ In (KRange PAYX 0 0) (kn holeEA).
Proof. vm_compute. repeat split; in_list_solve. Qed.
Lemma holePA_facts : In (KRange CFGX 0 0) (kn holePA) /\ In (KRange PAYX 1 (2 ^ 26)) (kn holePA).
Proof. vm_compute. repeat split; in_list_solve. Qed.
Lemma holeEB_facts : In (KRange CFGX 1 32767) (kn holeEB) /\ In (KRange PAYX 0 0) (kn holeEB).
Proof. vm_compute. repeat split; in_list_solve. Qed.
Lemma holePB_facts : In (KRange CFGX 1 32767) (kn holePB) /\ In (KRange PAYX 1 (2 ^ 26)) (kn holePB).
Proof. vm_compute. repeat split; in_list_solve. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfglenZ (E : env) : Z := uE E CFGX.
Definition paylenZ (E : env) : Z := uE E LEN - cfglenZ E - 6.
Definition callsZ (E : env) : nat := if cfglenZ E =? 0 then 1%nat else Z.to_nat (uE E CALLSB).
Definition cmode (E : env) : bool := M63 <? uE E B1S.
(* [comment removed for export] *)
Definition HOLES3 (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_payload (cmode E) (paylenZ E) (callsZ E) fs.

Lemma uE_agree9 : forall E E' e, env_agree NXD E E' -> expr_vars_lt NXD e = true -> uE E' e = uE E e.
Proof. intros E E' e Hag Hv. unfold uE. f_equal. symmetry. eapply (edenot_agree' NXD); [exact Hag | exact Hv]. Qed.

Lemma HOLES3_agree : forall h E E' fs, env_agree NXD E E' -> HOLES3 h E fs = HOLES3 h E' fs.
Proof.
  intros h E E' fs Hag. unfold HOLES3, cmode, paylenZ, callsZ, cfglenZ.
  rewrite (uE_agree9 E E' CFGX Hag eq_refl), (uE_agree9 E E' LEN Hag eq_refl), (uE_agree9 E E' CALLSB Hag eq_refl), (uE_agree9 E E' B1S Hag eq_refl).
  reflexivity.
Qed.
Lemma HOLES3_nil : forall h E fs, HOLES3 h E fs []. Proof. intros. apply t_payload_has_nil. Qed.
Lemma HOLES3_same : forall h E fs, HOLES3 h E fs = HOLES3 0%nat E fs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma eqm_neg : forall a b, eqm a b -> eqm (- a) (- b).
Proof. intros a b [q H]. exists (- q). lia. Qed.
Lemma uE_PAYX : forall E, eqm (uE E PAYX) (paylenZ E).
Proof.
  intros E. unfold paylenZ, cfglenZ, PAYX, esub, eadd, uE. rewrite mkAlu_denot.
  eapply eqm_trans; [apply u_sub_eqm|]. rewrite mkAlu_denot.
  replace (bv_unsigned (edenot E LEN) - bv_unsigned (edenot E CFGX) - 6) with (bv_unsigned (edenot E LEN) + - (bv_unsigned (edenot E CFGX) + 6)) by lia.
  unfold Z.sub. apply eqm_add; [apply eqm_refl|]. apply eqm_neg.
  eapply eqm_trans; [apply u_add_eqm|]. cbn [edenot]. apply eqm_add; [apply eqm_refl | apply eqm_u_lit].
Qed.
Lemma eqm_small : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> - 2 ^ 64 < b < 2 ^ 64 ->
  (0 <= b -> a = b) /\ (b < 0 -> a = b + 2 ^ 64).
Proof. intros a b [q H] Ha Hb. split; intros Hs; nia. Qed.
Lemma uE_rng : forall E e, 0 <= uE E e < 2 ^ 64.
Proof. intros E e. unfold uE. apply u64_range. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section S3.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
(* [comment removed for export] *)
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GPLAIN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okT TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE).
#[local] Notation cs_okS TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE).
(* [comment removed for export] *)
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD APLAIN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GPLAIN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzE.ce.

Lemma fds_std_1 : fd_lookup fds_std (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. reflexivity. Qed.
Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kn_range : forall TOP FS0 M0 E cs fx R M model e lo hi,
  cs_okS TOP FS0 M0 E cs fx R M model -> In (KRange e lo hi) (kn cs) -> lo <= uE E e <= hi.
Proof.
  intros TOP FS0 M0 E cs fx R M model e lo hi HC Hin.
  pose proof (kn_fact _ _ _ _ _ _ _ E cs fx R M model (KRange e lo hi) HC Hin) as H. cbn [kentry_ok] in H. unfold uE. exact H.
Qed.

(* [comment removed for export] *)
Lemma holeA_E : forall E, uE E CFGX = 0 -> uE E PAYX = 0 -> paylenZ E = 0 /\ callsZ E = 1%nat.
Proof.
  intros E Hc Hp. unfold callsZ, cfglenZ. rewrite Hc, Z.eqb_refl. split; [|reflexivity].
  pose proof (uE_rng E LEN) as HL.
  assert (HB : - 2 ^ 64 < paylenZ E < 2 ^ 64) by (unfold paylenZ, cfglenZ; rewrite Hc; lia).
  destruct (eqm_small _ _ (uE_PAYX E) (uE_rng E PAYX) HB) as [X Y].
  destruct (Z_lt_ge_dec (paylenZ E) 0) as [Hn|Hn]; [| pose proof (X ltac:(lia)); lia].
  exfalso. pose proof (Y Hn). unfold paylenZ, cfglenZ in *. lia.
Qed.
Lemma holeA_P : forall E, uE E CFGX = 0 -> 1 <= uE E PAYX <= 2 ^ 26 -> paylenZ E = uE E PAYX /\ callsZ E = 1%nat.
Proof.
  intros E Hc Hp. unfold callsZ. unfold cfglenZ. rewrite Hc, Z.eqb_refl. split; [|reflexivity].
  pose proof (uE_rng E LEN) as HL.
  assert (HB : - 2 ^ 64 < paylenZ E < 2 ^ 64) by (unfold paylenZ, cfglenZ; rewrite Hc; lia).
  destruct (eqm_small _ _ (uE_PAYX E) (uE_rng E PAYX) HB) as [X Y].
  destruct (Z_lt_ge_dec (paylenZ E) 0) as [Hn|Hn]; [| symmetry; apply X; lia].
  exfalso. pose proof (Y Hn). unfold paylenZ, cfglenZ in *. lia.
Qed.
Lemma holeB_E : forall E, 1 <= uE E CFGX <= 32767 -> uE E PAYX = 0 -> paylenZ E = 0 /\ callsZ E = callsB E.
Proof.
  intros E Hc Hp. unfold callsZ, callsB, cfglenZ. replace (uE E CFGX =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; [|reflexivity].
  pose proof (uE_rng E LEN) as HL.
  assert (HB : - 2 ^ 64 < paylenZ E < 2 ^ 64) by (unfold paylenZ, cfglenZ; lia).
  destruct (eqm_small _ _ (uE_PAYX E) (uE_rng E PAYX) HB) as [X Y].
  destruct (Z_lt_ge_dec (paylenZ E) 0) as [Hn|Hn]; [| pose proof (X ltac:(lia)); lia].
  exfalso. pose proof (Y Hn). unfold paylenZ, cfglenZ in *. lia.
Qed.
Lemma holeB_P : forall E, 1 <= uE E CFGX <= 32767 -> 1 <= uE E PAYX <= 2 ^ 26 -> paylenZ E = uE E PAYX /\ callsZ E = callsB E.
Proof.
  intros E Hc Hp. unfold callsZ, callsB, cfglenZ. replace (uE E CFGX =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; [|reflexivity].
  pose proof (uE_rng E LEN) as HL.
  assert (HB : - 2 ^ 64 < paylenZ E < 2 ^ 64) by (unfold paylenZ, cfglenZ; lia).
  destruct (eqm_small _ _ (uE_PAYX E) (uE_rng E PAYX) HB) as [X Y].
  destruct (Z_lt_ge_dec (paylenZ E) 0) as [Hn|Hn]; [| symmetry; apply X; lia].
  exfalso. pose proof (Y Hn). unfold paylenZ, cfglenZ in *. lia.
Qed.

(* [comment removed for export] *)
Lemma holes_stmt_of_table : forall TOP FS0 M0 (HS : nat -> option acs) (HOLES : nat -> env -> Fs.Fs -> TSet),
  (forall h, match HS h with
             | Some ch => forall E fx R M model, cs_okS TOP FS0 M0 E ch fx R M model -> RZ (cfgF RSEGS fx R (pc ch) M model) (HOLES h E (m_fs model))
             | None => True end) ->
  GPS.holes_stmt RSEGS HS PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE HOLES RZ.
Proof. intros TOP FS0 M0 HS HOLES H h ch Hh. specialize (H h). rewrite Hh in H. exact H. Qed.

Lemma HS3_sound : forall TOP FS0 M0, GPS.holes_stmt RSEGS HSC PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE HOLES3 RZ.
Proof.
  intros TOP FS0 M0; apply holes_stmt_of_table; intros h.
  pose proof (glue_EA SR SRX GC_T FZN_sound FZE_sound TOP M0) as GEA; cbv delta [tinEA] in GEA.
  pose proof (glue_EB SR SRX GC_T FZN_sound FZE_sound TOP M0) as GEB; cbv delta [tinEB] in GEB.
  pose proof (glue_payA SR SRX HMA GC_T FZN_sound FZE_sound TOP M0) as GPA; cbv delta [tinPA] in GPA.
  pose proof (glue_payB SR SRX HMA GC_T FZN_sound FZE_sound TOP M0) as GPB; cbv delta [tinPB] in GPB.
  destruct h as [|[|[|[|[|h]]]]]; cbn [HSC]; [exact I| | | | |exact I]; intros E fx R M model HC; pose proof (co_fs HC) as Hfs; subst FS0.
  - (* [comment removed for export] *)
    destruct holeEA_facts as (F1 & F2).
    pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F1) as X1. pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F2) as X2. clear F1 F2.
    specialize (GEA E fx R M model HC). revert GEA. generalize (pc holeEA). clear HC. intros p G.
    destruct (holeA_E E ltac:(lia) ltac:(lia)) as [P1 P2]. unfold HOLES3. rewrite P1, P2. rewrite t_payload_none by lia. exact G.
  - (* [comment removed for export] *)
    destruct holePA_facts as (F1 & F2).
    pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F1) as X1. pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F2) as X2. clear F1 F2.
    specialize (GPA E fx R M model HC). revert GPA. generalize (pc holePA). clear HC. intros p G.
    destruct (holeA_P E ltac:(lia) X2) as [P1 P2]. unfold HOLES3. rewrite P1, P2. exact G.
  - (* [comment removed for export] *)
    destruct holeEB_facts as (F1 & F2).
    pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F1) as X1. pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F2) as X2. clear F1 F2.
    specialize (GEB E fx R M model HC). revert GEB. generalize (pc holeEB). clear HC. intros p G.
    destruct (holeB_E E X1 ltac:(lia)) as [P1 P2]. unfold HOLES3. rewrite P1, P2. rewrite t_payload_none by lia. exact G.
  - (* [comment removed for export] *)
    destruct holePB_facts as (F1 & F2).
    pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F1) as X1. pose proof (kn_range _ _ _ _ _ _ _ _ _ _ _ _ HC F2) as X2. clear F1 F2.
    specialize (GPB E fx R M model HC). revert GPB. generalize (pc holePB). clear HC. intros p G.
    destruct (holeB_P E X1 X2) as [P1 P2]. unfold HOLES3. rewrite P1, P2. exact G.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sd_shapeC3 : forall D E fs, sd HOLES3 D E fs shapeC3 = HOLES3 0%nat E fs.
Proof.
  intros D E fs. unfold shapeC3. cbn [sd].
  destruct (bv_unsigned (edenot E CFGX) <=? 0); destruct (bv_unsigned (edenot E PAYX) <=? 0); reflexivity.
Qed.

Lemma HS0_sound : forall TOP FS0 M0 HOLES, GPS.holes_stmt RSEGS HS0 PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE HOLES RZ.
Proof. intros TOP FS0 M0 HOLES h ch Hh. discriminate Hh. Qed.

Theorem S3_C1n_sound : forall TOP M0 E fx R M model,
  cs_okS TOP (m_fs model) M0 E tinC1n fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinC1n) M model) (t_die msg_short (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HC.
  eapply (sr_conseq RSEGS SR); [| apply (sd_shapeD HOLES_T t_nil E (m_fs model) zmsg_short msg_short zmsg_short_ok)].
  exact (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1 fds_std_2 UTRUE UTRUE_agree HS0 HOLES_T (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
           (HS0_sound TOP (m_fs model) M0 HOLES_T) BF FUEL planD tinC1n (shapeD zmsg_short) E fx R M model planD_ok certC1ns HC eq_refl).
Qed.
Theorem S3_C2_sound : forall TOP M0 E fx R M model,
  cs_okS TOP (m_fs model) M0 E tinC2 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinC2) M model) (t_die msg_overrun (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HC.
  eapply (sr_conseq RSEGS SR); [| apply (sd_shapeD HOLES_T t_nil E (m_fs model) zmsg_overrun msg_overrun zmsg_overrun_ok)].
  exact (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1 fds_std_2 UTRUE UTRUE_agree HS0 HOLES_T (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
           (HS0_sound TOP (m_fs model) M0 HOLES_T) BF FUEL planD tinC2 (shapeD zmsg_overrun) E fx R M model planD_ok certC2s HC eq_refl).
Qed.

Theorem S3_C3_sound : forall TOP M0 E fx R M model,
  cs_okS TOP (m_fs model) M0 E tinC3 fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinC3) M model) (t_payload (cmode E) (paylenZ E) (callsZ E) (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HC.
  pose proof (drvS_cert_sound SR SRX HFR HMB TOP (m_fs model) fds_std M0 fds_std_1 fds_std_2 UTRUE UTRUE_agree HSC HOLES3 HOLES3_agree HOLES3_nil HOLES3_same
                (HS3_sound TOP (m_fs model) M0) BF FUEL planC3 tinC3 shapeC3 E fx R M model planC3_ok certC3s HC eq_refl) as H.
  rewrite sd_shapeC3 in H. exact H.
Qed.
End S3.
