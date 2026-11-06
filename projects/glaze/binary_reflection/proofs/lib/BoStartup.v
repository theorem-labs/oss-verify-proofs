(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_eda0c_edd44.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End Bo_code_eda0c_edd44.
Require Stdlib.Lists.List Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoCertM1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_1a : cert_okB IT1 T900 both_init_S s1_planP = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_1b : cert_okB IT1 T901 HS_900 s1_q4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_4 : cert_okB IT1 T11_13 HS_903 s1_q11 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5a : cert_okB IT1 T916J HS_11J s1_planT = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma cert_5a2 : cert_okB IT1 T916Jb HS_915 s1_planTb = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BoCertM1.
Module BoCertS2a.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2a : cert_okB IT2a T950 HS_0 s2a_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BoCertS2a.
Module BoCertS2b.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2b : cert_okB IT2b T951 HS_950 s2b_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BoCertS2b.
Module BoCertS2c.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2c : cert_okB IT2c T1_2 HS_951 s2c_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BoCertS2c.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoStartupTabsOk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
Open Scope Z_scope.
Lemma IT1_ok : itab_sound BSEGS IT1.   Proof. exact (APS.mk_itab_ranges_sound BSEGS s1_plan_ranges). Qed.
Lemma IT2a_ok : itab_sound BSEGS IT2a. Proof. exact (APS.mk_itab_ranges_sound BSEGS s2a_plan_ranges). Qed.
Lemma IT2b_ok : itab_sound BSEGS IT2b. Proof. exact (APS.mk_itab_ranges_sound BSEGS s2b_plan_ranges). Qed.
Lemma IT2c_ok : itab_sound BSEGS IT2c. Proof. exact (APS.mk_itab_ranges_sound BSEGS s2c_plan_ranges). Qed.
End BoStartupTabsOk.
Require Stdlib.NArith.NArith Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoStartupSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section Startup.
  (* [comment removed for export] *)
  Variable RR : shape_rel BSEGS.
  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile sigmask : word.   (* [comment removed for export] *)
  Variable abort : bool.
  Variable va : VaSize.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Hypothesis IMG : img_facts BSEGS AT_B ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Let E0 := AsSInit.E0 ph sp rdraw brk0 argv envp uid hw.
  Let SINV := AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw.
  Let argH := AsSInit.argH0 ph sp rdraw argv envp uid hw.
  Let inp := AsSInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abort va urnd.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Definition HOLES (h : nat) (E : env) (f : Fs.Fs) : TSet := T.

  (* [comment removed for export] *)
  Hypothesis SEGS_wx : wx_segs_nowrap BSEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull AT_B (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
  Hypothesis RES_len : res_len_ok BSEGS AT_B.
  Hypothesis RES_hull : Forall (fun iv => img_lo AT_B <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_B) (segments_reserved BSEGS).
  Hypothesis HULL_ok : hull_ok AT_B.
  Hypothesis SHADOW_ok : shadow_ok AT_B.
  Hypothesis RES_tile : forall z, img_lo AT_B <= z < img_hi AT_B -> in_ivs z (segments_reserved BSEGS) = true.
  Hypothesis HULL_ne : img_lo AT_B < img_hi AT_B.

  (* [comment removed for export] *)
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound BSEGS IT.

  Definition hole_obl_f (ch : acs) : Prop :=
    forall E fx R M model, cs_ok BSEGS AT_B LIMIT_S SINV argH ISP_S fs E ch R M model -> fx_ok fx ->
      realizes BSEGS (GPS.cfgF BSEGS fx R (pc ch) M model) T.

  (* [comment removed for export] *)
  Hypothesis XN_sound : SIF.ext_stmt BSEGS RR AT_B NXS LIMIT_S XN_B SINV argH ISP_S fs fx_ok.

  Lemma XE_sound : SIF.emit_stmt BSEGS RR AT_B NXS LIMIT_S XE_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.
  Lemma XB_sound : SIF.ext2_stmt BSEGS RR AT_B NXS LIMIT_S XB_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.
  Lemma XA_sound : SIF.alt2_stmt BSEGS RR AT_B NXS LIMIT_S XA_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.

  (* [comment removed for export] *)
  Definition hole_oblR (ch : acs) : Prop :=
    forall E fx R M model, cs_ok BSEGS AT_B LIMIT_S SINV argH ISP_S fs E ch R M model -> fx_ok fx ->
      RR (GPS.cfgF BSEGS fx R (pc ch) M model) T.

  (* [comment removed for export] *)
  Definition table_ok (HS : nat -> option acs) : Prop := forall h ch, HS h = Some ch -> hole_oblR ch.

  Lemma table_holes_stmt : forall HS, table_ok HS -> SIF.holes_stmt BSEGS RR AT_B LIMIT_S HS SINV argH ISP_S fs fx_ok HOLES.
  Proof. intros HS HT h ch Hh E fx R M model HC HF. unfold HOLES. exact (HT h ch Hh E fx R M model HC HF). Qed.

  (* [comment removed for export] *)
  Definition shapeT (s : shape) : Prop := forall E f, t_eq (sd HOLES T E f s) T.





  (* [comment removed for export] *)
  Lemma subT_sound : forall s E f tr, subT s = true -> sd HOLES T E f s tr -> T tr.
  Proof.
    induction s as [|c|fd ps s IH|a IHs1 b IHs2|e z a IHs1 b IHs2|h|]; intros E f tr H X; cbn in H, X |- *; try discriminate.
    - unfold t_nil in X. subst tr. exact T_nil.
    - apply andb_prop in H as [Ha Hb]. unfold t_alt2 in X. destruct X as [X|X]; [eapply IHs1 | eapply IHs2]; eassumption.
    - apply andb_prop in H as [Ha Hb]. destruct (bv_unsigned (edenot E e) <=? z); [eapply IHs1 | eapply IHs2]; eassumption.
    - unfold HOLES in X. exact X.
  Qed.

  Lemma fullT_shapeT : forall s, fullT s = true -> shapeT s.
  Proof.
    induction s as [|c|fd ps s IH|a IHs1 b IHs2|e z a IHs1 b IHs2|h|]; intros H E f tr; cbn in H |- *; try discriminate.
    - apply orb_prop in H as [H|H]; apply andb_prop in H as [Ha Hb]; unfold t_alt2; split.
      + intros [X|X]; [apply (IHs1 Ha E f tr); exact X | eapply subT_sound; eassumption].
      + intros X. left. apply (IHs1 Ha E f tr). exact X.
      + intros [X|X]; [eapply subT_sound; eassumption | apply (IHs2 Hb E f tr); exact X].
      + intros X. right. apply (IHs2 Hb E f tr). exact X.
    - apply andb_prop in H as [Ha Hb]. destruct (bv_unsigned (edenot E e) <=? z); [apply (IHs1 Ha) | apply (IHs2 Hb)].
    - unfold HOLES. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma segment_sound : forall HS (p : plan) (cs : acs) (s : shape),
    table_ok HS -> SPS.splan_ok p = true -> shapeT s ->
    checkA BSEGS IT AT_B NXS LIMIT_S ISP_S XN_B XE_S XB_S XA_S AP.XT0 HS KC_S true BFUEL_S FUEL_S None cs p = COk s ->
    hole_oblR cs.
  Proof.
    intros HS p cs s HT Hp Hs CERT E fx R M model HC HF.
    eapply (sr_conseq BSEGS RR).
    - eapply (SPS.check_sound BSEGS RR IT IT_ok AT_B NXS LIMIT_S HS XN_B XE_S XB_S XA_S AP.XT0 KC_S SINV argH fs fx_ok HOLES T
                SEGS_wx SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok ISP_S); try eassumption; try (apply table_holes_stmt; exact HT).
      + reflexivity.                                                   (* [comment removed for export] *)
      + exact (AsSInit.argH0_high ph sp rdraw argv envp uid hw Hsp Hva).
      + exact (AsSInit.argH0_agree ph sp rdraw argv envp uid hw).
      + exact (AsSInit.SINV0_frame ph sp rdraw brk0 argv envp uid hw).
      + exact (AsSInit.SINV0_agree ph sp rdraw brk0 argv envp uid hw).
      + intros; reflexivity.                                           (* [comment removed for export] *)
      + intros; exact T_nil.                                           (* [comment removed for export] *)
      + intros; reflexivity.                                           (* [comment removed for export] *)
      + apply AzNodesSound.RUN_sound_fx.
      + exact XE_sound.
      + exact XB_sound.
      + exact XA_sound.
    - apply Hs.
  Qed.

  Lemma segment_ok : forall HS (p : plan) (cs : acs),
    table_ok HS -> SPS.splan_ok p = true -> cert_okB IT HS cs p = true -> hole_oblR cs.
  Proof.
    intros HS p cs HT Hp. unfold cert_okB, chkB.
    pose proof (segment_sound HS p cs) as SS.
    generalize dependent SS.
    generalize (checkA BSEGS IT AT_B NXS LIMIT_S ISP_S XN_B XE_S XB_S XA_S AP.XT0 HS KC_S true BFUEL_S FUEL_S None cs p).
    intros r SS HC. destruct r as [s|code wh ecs]; [|discriminate HC].
    apply (SS s HT Hp); [apply fullT_shapeT; exact HC | reflexivity].
  Qed.

End Startup.



End BoStartupSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartup OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtIStrncpyI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtSums.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartup.AsRtSums OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtIStrncpyI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma both_fill_spec_imemset : fill_spec BSEGS 0x809a8 256.
Proof using.
  intros mem0 s c n regs ret Hn Hnw Hok Hc Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x809a8 : word) with both_imemset_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (both_imemset mem0 s c n (seg_rom BSEGS) regs ret Hn Hnw Hok (fun _ _ => Hc) Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ imemset_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.

Lemma both_fill_spec_memset : fill_spec BSEGS 0xfc38c (2 ^ 64).
Proof using.
  intros mem0 s c n regs ret Hn Hnw Hok Hc Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0xfc38c : word) with both_memset_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (both_memset mem0 s c ret n (seg_rom BSEGS) regs Hn Hnw Hok Hret H10 H11 H12 H1) as (r & RUN & A10 & AG).
  exists r. split; [exact RUN | split; [exact (kept_of_agree _ _ _ ms_clob_cs AG) | exact A10]].
Qed.

Lemma both_copy_spec_imemcpy : copy_spec BSEGS 0x8092c.
Proof using.
  intros mem0 dst src n bs regs ret Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x8092c : word) with both_imemcpy_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (both_imemcpy mem0 dst src n bs (seg_rom BSEGS) regs ret (CPYH _ _ _ _ _ _ Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd) Hret H1 H10 H11 H12)
    as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ imemcpy_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold imemcpy_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.

Lemma both_copy_spec_memcpy : copy_spec BSEGS 0xfbf88.
Proof using.
  intros mem0 dst src n bs regs ret Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0xfbf88 : word) with both_memcpy_entry by (apply bv_eq; vm_compute; reflexivity).
  assert (HOK : AsRtMemcpyBase.mcH BSEGS mem0 dst src n bs) by (pose proof (u64_range dst); split; try assumption; lia).
  destruct (both_memcpy mem0 dst src n bs (seg_rom BSEGS) regs ret HOK Hret H1 H10 H11 H12) as (r & RUN & K).
  exists r. split; [exact RUN | split; [exact (kept_of_keeps _ _ K) | rewrite (K 10%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact H10]].
Qed.

Lemma both_miz_spec : miz_spec BSEGS 0x80ed8.
Proof using.
  intros mem beg sp N regs ret HN Hnw Hsp Hok Hdisj Hz Hret H1 H2 H10 H11.
  replace (Z_to_bv 64 0x80ed8 : word) with both_mem_is_zero_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (both_mem_is_zero mem beg sp N (seg_rom BSEGS) regs ret HN Hnw Hsp Hok Hdisj Hz Hret H1 H2 H10 H11) as (r & RUN & AG & A10 & _).
  exists r. split; [exact RUN | split; [exact (kept_of_agree _ _ _ memisz_clob_cs AG) | exact A10]].
Qed.

Lemma both_istrncpy_spec : istrncpy_spec BSEGS 0x80dd4 0x11aae.
Proof using.
  intros mem0 dst regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x80dd4 : word) with both_istrncpy_entry by (apply bv_eq; vm_compute; reflexivity).
  change SEALED_BYTES with strncpy_sealed_bytes. change 0x11aae%Z with both_sealed_src in *.
  destruct (both_istrncpy_sealed mem0 dst (seg_rom BSEGS) regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ istrncpy_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold istrncpy_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.
End FPGen1.
End BoRtSums.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSums OSSVerify.Proofs.glaze.binary_reflection.lib.AzSStartX OSSVerify.Proofs.glaze.binary_reflection.lib.AzSExt OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_ed07c_ed9d0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoStartupXN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSums OSSVerify.Proofs.glaze.binary_reflection.lib.AzSStartX OSSVerify.Proofs.glaze.binary_reflection.lib.AzSExt.
Import BoRtSums.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_ed07c_ed9d0 Bo_code_eda0c_edd44.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma hull_okP_B : APSX.hull_okP AT_B.
Proof. unfold APSX.hull_okP. vm_compute. repeat split; try reflexivity; try discriminate. Qed.

Lemma hull_ok_B : APS.hull_ok AT_B.
Proof. exact both_S_hull_ok. Qed.

Lemma segs_wr_B : APSX.segs_wr_ok BSEGS.
Proof.
  intros seg Hin Hw. rewrite BoImages.both_segs_eq in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hw; try discriminate Hw; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint noblob (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => noblob x && noblob y
  | EExt _ _ _ x => noblob x
  | EBlob _ _ _ _ => false
  end.
Lemma edenot_vals_agree : forall b E E' e,
  (forall n, (n < b)%nat -> ev E n = ev E' n) -> expr_vars_lt b e = true -> noblob e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e Hv. induction e; cbn [expr_vars_lt noblob edenot]; intros H1 H2;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end; try reflexivity; try discriminate.
  - apply Hv. apply Nat.ltb_lt. assumption.
  - rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
Qed.

Lemma total_arg_bytes_nonneg : forall l, 0 <= total_arg_bytes l.
Proof. induction l as [|x t IH]; [cbn; lia|]. change (total_arg_bytes (x :: t)) with (Z.of_nat (length x) + 1 + total_arg_bytes t). lia. Qed.
Lemma total_arg_bytes_hd : forall l, (0 < length l)%nat -> Z.of_nat (length (nth 0 l [])) + 1 <= total_arg_bytes l.
Proof.
  intros [|x t] H; [cbn in H; lia|]. cbn [nth]. change (total_arg_bytes (x :: t)) with (Z.of_nat (length x) + 1 + total_arg_bytes t).
  pose proof (total_arg_bytes_nonneg t). lia.
Qed.

Section XN.
  (* [comment removed for export] *)
  Variable RR : shape_rel BSEGS.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Hypothesis IMG : img_facts BSEGS AT_B ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Let E0 := AsSInit.E0 ph sp rdraw brk0 argv envp uid hw.
  Let SINV := AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw.
  Let argH := AsSInit.argH0 ph sp rdraw argv envp uid hw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.

  (* [comment removed for export] *)
  Let ISP_vars := AsSInit.e_sp0_vars.
  Let argH_high := AsSInit.argH0_high ph sp rdraw argv envp uid hw Hsp Hva.
  Let argH_agree := AsSInit.argH0_agree ph sp rdraw argv envp uid hw.
  Let SINV_frame := AsSInit.SINV0_frame ph sp rdraw brk0 argv envp uid hw.
  Let SINV_agree := AsSInit.SINV0_agree ph sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Lemma SINV_vals : forall E M e, SINV E M -> expr_vars_lt NXS e = true -> noblob e = true -> edenot E e = edenot E0 e.
  Proof. intros E M e [H1 _] Hv Hb. exact (edenot_vals_agree NXS E E0 e H1 Hv Hb). Qed.

  Lemma SINV_u : forall E M e, SINV E M -> expr_vars_lt NXS e = true -> noblob e = true -> uE E e = uE E0 e.
  Proof. intros E M e HS Hv Hb. unfold uE. rewrite (SINV_vals E M e HS Hv Hb). reflexivity. Qed.

  Lemma SINV_isp : forall E M, SINV E M -> bv_unsigned (edenot E ISP_S) <= bv_unsigned sp.
  Proof.
    intros E M HS. unfold ISP_S. rewrite (SINV_vals E M e_sp0 HS eq_refl eq_refl). unfold E0.
    rewrite (AsSInit.edenot_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit). lia.
  Qed.

  Lemma SINV_envp : forall E M, SINV E M ->
    uE E e_envp = bv_unsigned sp + 8 * Z.of_nat (length argv) + 16
    /\ ev E V_ENVC = Z_to_bv 64 (Z.of_nat (length envp))
    /\ uE E e_str0 = bv_unsigned sp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184.
  Proof.
    intros E M HS. repeat split.
    - rewrite (SINV_u E M e_envp HS eq_refl eq_refl). exact (AsSInit.u_e_envp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
    - destruct HS as [H1 _]. rewrite (H1 V_ENVC) by (unfold V_ENVC, NXS; lia). reflexivity.
    - rewrite (SINV_u E M e_str0 HS eq_refl eq_refl). exact (AsSInit.u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
  Qed.

  (* [comment removed for export] *)
  Lemma SINV_envarr : forall E M (a : word), SINV E M ->
    bv_unsigned sp + 8 * Z.of_nat (length argv) + 16 <= bv_unsigned a
      < bv_unsigned sp + 8 * Z.of_nat (length argv) + 16 + 8 * Z.of_nat (length envp) + 8 ->
    M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    intros E M a HS Ha. destruct HS as [H1 H2]. apply H2. unfold AsSInit.argH0.
    pose proof (SINV_u E M e_sp0 (conj H1 H2) eq_refl eq_refl) as U. rewrite U. unfold E0.
    rewrite (AsSInit.u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit), Z.eqb_refl. cbn [andb].
    apply orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma L0_fits : L0 + 1 <= 8 * W.
  Proof.
    pose proof (AsSInit.W_range ph sp rdraw argv envp uid hw Hva Hve) as WR. cbv zeta in WR. destruct WR as (W0 & W8 & _).
    pose proof (AsSInit.length_bsb_eq ph sp rdraw argv envp uid hw) as LB.
    pose proof (total_arg_bytes_hd argv (AsSInit.Hav0 ph sp rdraw argv envp uid hw Hva)) as HD.
    pose proof (total_arg_bytes_nonneg envp) as TE. pose proof (total_arg_bytes_nonneg argv) as TA.
    unfold W, bsb, argc, envc, L0. rewrite W8. rewrite LB. unfold AsSInit.stack_image_size. cbv zeta.
    set (len := 8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160 + total_arg_bytes argv + total_arg_bytes envp).
    assert (0 <= (8 - len mod 8) mod 8) by (apply Z.mod_pos_bound; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV_str0 : forall E M (a : word), SINV E M ->
    bv_unsigned sp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 <= bv_unsigned a
      <= bv_unsigned sp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 + Z.of_nat (length (nth 0 argv [])) ->
    M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Proof.
    intros E M a HS Ha. pose proof L0_fits as LF. unfold L0, W, bsb, argc, envc in LF.
    destruct HS as [H1 H2]. apply H2. unfold AsSInit.argH0.
    pose proof (SINV_u E M e_sp0 (conj H1 H2) eq_refl eq_refl) as U. rewrite U. unfold E0.
    rewrite (AsSInit.u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit), Z.eqb_refl. cbn [andb].
    apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Let N1 := SIF.node1_stmtN BSEGS RR AT_B NXS LIMIT_S SINV argH ISP_S fs AzSymStepR.fx_ok SIF.always.

  Lemma hook27 : N1 (fun cs => Some cs).
  Proof.
    red. intros cs cs' E fx R M model T HT HC HF _ Hn K. injection Hn as <-.
    apply (K E fx R M model); [split; apply APS.env_agree_refl | exact HC | exact HF | reflexivity].
  Qed.

  Lemma hook210 : forall args, N1 (fun cs => node_nameword NXS cs args).
  Proof. intros args. exact (AzSExt.node_nameword_sound BSEGS RR AT_B NXS LIMIT_S SINV argH fs AzSymStepR.fx_ok ISP_S ISP_vars argH_agree SINV_agree args). Qed.

  Lemma hook200 : N1 (fun cs => summary_fill AT_B NXS cs (x_imemset AT_B) 256).
  Proof. exact (APSX.summary_fill_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (x_imemset AT_B) 256 (fun fx => @BoRtSums.both_fill_spec_imemset fx)). Qed.
  Lemma hook201 : N1 (fun cs => summary_fill AT_B NXS cs (x_memset AT_B) two64).
  Proof. exact (APSX.summary_fill_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (x_memset AT_B) two64 (fun fx => @BoRtSums.both_fill_spec_memset fx)). Qed.
  Lemma hook202 : N1 (fun cs => summary_copy BSEGS AT_B NXS cs (x_imemcpy AT_B)).
  Proof. exact (APSX.summary_copy_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok segs_wr_B (x_imemcpy AT_B) (fun fx => @BoRtSums.both_copy_spec_imemcpy fx)). Qed.
  Lemma hook203 : N1 (fun cs => summary_copy BSEGS AT_B NXS cs (x_memcpy AT_B)).
  Proof. exact (APSX.summary_copy_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok segs_wr_B (x_memcpy AT_B) (fun fx => @BoRtSums.both_copy_spec_memcpy fx)). Qed.
  Lemma hook204 : N1 (fun cs => summary_miz AT_B NXS cs).
  Proof. exact (APSX.summary_miz_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (fun fx => @BoRtSums.both_miz_spec fx)). Qed.
  Lemma hook205 : N1 (fun cs => summary_istrncpy AT_B NXS cs).
  Proof. exact (APSX.summary_istrncpy_stmtN BSEGS RR AT_B NXS LIMIT_S both_S_wx both_S_in_hull hull_okP_B SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (fun fx => @BoRtSums.both_istrncpy_spec fx)). Qed.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.   Proof. exact (proj1 Hsp). Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.   Proof. exact (proj1 (proj2 Hsp)). Qed.

  Lemma hook206 : N1 (node_envscan AT_B).
  Proof.
    apply SIF.node1_stmt_N.
    eapply (SX.node_envscan_stmt BSEGS RR AT_B NXS LIMIT_S SINV argH fs both_S_wx both_S_in_hull hull_ok_B ISP_S SINV_frame AzSymStepR.fx_ok W_ed2e0 W_ed2e4 W_ed2e8).
    - vm_compute. repeat split; try reflexivity; try discriminate.
    - exact F_ed2e0. - exact F_ed2e4. - exact F_ed2e8.
    - vm_compute. repeat split; reflexivity.
    - exact D_ed2e0. - exact D_ed2e4. - exact D_ed2e8.
    - exact Hva. - exact Hve. - exact sp_lo. - exact sp_hi.
    - exact SINV_isp. - exact SINV_envp. - exact SINV_envarr.
  Qed.

  Lemma hook207 : N1 (node_pnscan AT_B NXS).
  Proof.
    apply SIF.node1_stmt_N.
    eapply (SX.node_pnscan_stmt BSEGS RR AT_B NXS LIMIT_S SINV argH fs both_S_wx both_S_in_hull hull_ok_B ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree AzSymStepR.fx_ok W_ed39c W_ed3a0 W_ed3a4 W_ed3a8 W_ed3ac).
    - vm_compute. repeat split; try reflexivity; try discriminate.
    - exact F_ed39c. - exact F_ed3a0. - exact F_ed3a4. - exact F_ed3a8. - exact F_ed3ac.
    - vm_compute. repeat split; reflexivity.
    - exact D_ed39c. - exact D_ed3a0. - exact D_ed3a4. - exact D_ed3a8. - exact D_ed3ac.
    - exact Hva. - exact Hve. - exact sp_lo. - exact sp_hi.
    - exact SINV_isp. - exact SINV_envp. - exact SINV_str0.
  Qed.

  Lemma hook208 : forall args, N1 (fun cs => node_layout cs args).
  Proof. intros args. apply SIF.node1_stmt_N. exact (SX.node_layout_stmt BSEGS RR AT_B NXS LIMIT_S SINV argH fs ISP_S AzSymStepR.fx_ok args). Qed.

  (* [comment removed for export] *)
  Lemma XN_B_cases : forall id args cs r, XN_B id args cs = Some r ->
    (id = 210 \/ id = 200 \/ id = 201 \/ id = 202 \/ id = 203 \/ id = 204 \/ id = 205 \/ id = 206 \/ id = 207 \/ id = 208 \/ id = 27)%nat.
  Proof.
    intros id args cs r H. unfold XN_B in H.
    do 211 (destruct id as [|id]; [first [discriminate H | lia] |]).
    discriminate H.
  Qed.

  Theorem XN_B_sound : SIF.ext_stmt BSEGS RR AT_B NXS LIMIT_S XN_B SINV argH ISP_S fs AzSymStepR.fx_ok.
  Proof.
    intros id args cs cs' E fx R M model T HT HC HF Hpre Hn K.
    destruct (XN_B_cases id args cs cs' Hn) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
    - exact (hook210 args cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook200 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook201 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook202 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook203 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook204 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook205 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook206 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook207 cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook208 args cs cs' E fx R M model T HT HC HF Hpre Hn K).
    - exact (hook27 cs cs' E fx R M model T HT HC HF Hpre Hn K).
  Qed.
End XN.
End BoStartupXN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymStepR AzSymExec3 AzSymExec3B AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS AzSIface AzSSound AzNodesSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.BoImages BoStartupSound BoStartupXN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs BoStartupTabsOk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoCertM2. Import BoCertM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCertM2 BoCertS2a BoCertS2b BoCertS2c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ok_s1_planP : SPS.splan_ok s1_planP = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q4 : SPS.splan_ok s1_q4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q5 : SPS.splan_ok s1_q5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q7 : SPS.splan_ok s1_q7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q11 : SPS.splan_ok s1_q11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q11b : SPS.splan_ok s1_q11b = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_planT : SPS.splan_ok s1_planT = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_planTb : SPS.splan_ok s1_planTb = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q17 : SPS.splan_ok s1_q17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q18r : SPS.splan_ok s1_q18r = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s1_q18g : SPS.splan_ok s1_q18g = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s2a : SPS.splan_ok s2a_plan = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s2b : SPS.splan_ok s2b_plan = true. Proof. vm_compute. reflexivity. Qed.
Lemma ok_s2c : SPS.splan_ok s2c_plan = true. Proof. vm_compute. reflexivity. Qed.

Section StartupB.
  (* [comment removed for export] *)
  Variable RR : shape_rel BSEGS.
  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Hypothesis IMG : img_facts BSEGS AT_B ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  (* [comment removed for export] *)
  Let XN_sound : SIF.ext_stmt BSEGS RR AT_B NXS LIMIT_S XN_B (AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw)
                   (AsSInit.argH0 ph sp rdraw argv envp uid hw) ISP_S fs AzSymStepR.fx_ok
    := BoStartupXN.XN_B_sound RR ph sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit.

  Let HOBL := hole_oblR RR ph sp rdraw brk0 argv envp fs uid hw T.
  Let TOK := table_ok RR ph sp rdraw brk0 argv envp fs uid hw T.

  (* [comment removed for export] *)
  Let SEG (IT : itab) (IT_ok : itab_sound BSEGS IT) :=
    segment_ok RR ph sp rdraw brk0 argv envp fs uid hw Hsp Hva T T_nil
      both_S_wx both_S_in_hull both_S_res_len both_S_res_hull both_S_hull_ok both_S_shadow_ok both_S_res_tile both_S_hull_ne
      IT IT_ok XN_sound.

  Lemma tab1_ok : forall h c, HOBL c -> TOK (tab1 h c).
  Proof. intros h c Hc h' ch E. unfold tab1 in E. destruct (Nat.eqb h' h); [injection E as <-; exact Hc | discriminate]. Qed.

  (* [comment removed for export] *)
  Hypothesis H1 : HOBL HS_1.
  Hypothesis H2 : HOBL HS_2.

  Lemma T1_2_ok : TOK T1_2.
  Proof. intros h ch E. unfold T1_2 in E. destruct h as [|[|[|h]]]; try discriminate; injection E as <-; assumption. Qed.
  Lemma ob_951 : HOBL HS_951.   Proof. exact (SEG IT2c IT2c_ok _ _ _ T1_2_ok ok_s2c cert_S2c). Qed.
  Lemma ob_950 : HOBL HS_950.   Proof. exact (SEG IT2b IT2b_ok _ _ _ (tab1_ok _ _ ob_951) ok_s2b cert_S2b). Qed.
  Lemma ob_0 : HOBL HS_0.       Proof. exact (SEG IT2a IT2a_ok _ _ _ (tab1_ok _ _ ob_950) ok_s2a cert_S2a). Qed.
  (* [comment removed for export] *)
  Lemma ob_917J : HOBL HS_917J. Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_0) ok_s1_q18r cert_5c). Qed.
  Lemma ob_918J : HOBL HS_918J. Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_0) ok_s1_q18g cert_5d). Qed.
  Lemma T5b_ok : forall h917 h918, HOBL h917 -> HOBL h918 -> TOK (T5b h917 h918).
  Proof.
    intros h917 h918 O7 O8 h ch E. unfold T5b in E.
    destruct (Nat.eqb h 0); [injection E as <-; exact ob_0|].
    destruct (Nat.eqb h 917); [injection E as <-; exact O7|].
    destruct (Nat.eqb h 918); [injection E as <-; exact O8| discriminate E].
  Qed.
  Lemma ob_916J : HOBL HS_916J. Proof. exact (SEG IT1 IT1_ok _ _ _ (T5b_ok _ _ ob_917J ob_918J) ok_s1_q17 cert_5b). Qed.
  (* [comment removed for export] *)
  Lemma ob_915 : HOBL HS_915.   Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_916J) ok_s1_planTb cert_5a2). Qed.
  Lemma T916J_ok : TOK T916J.
  Proof.
    intros h ch E. unfold T916J in E.
    destruct (Nat.eqb h 915); [injection E as <-; exact ob_915|].
    exact (tab1_ok _ _ ob_916J h ch E).
  Qed.
  Lemma ob_11J : HOBL HS_11J.   Proof. exact (SEG IT1 IT1_ok _ _ _ T916J_ok ok_s1_planT cert_5a). Qed.
  (* [comment removed for export] *)
  Lemma T11_13b_ok : TOK T11_13b.
  Proof.
    intros h ch E. unfold T11_13b in E.
    do 11 (destruct h as [|h]; [discriminate|]).
    destruct h as [|[|[|h]]]; try discriminate; injection E as <-; exact ob_11J.
  Qed.
  Lemma ob_904 : HOBL HS_904.   Proof. exact (SEG IT1 IT1_ok _ _ _ T11_13b_ok ok_s1_q11b cert_4b). Qed.
  Lemma T11_13_ok : TOK T11_13.
  Proof.
    intros h ch E. unfold T11_13 in E.
    destruct (Nat.eqb h 904); [injection E as <-; exact ob_904|].
    exact (T11_13b_ok h ch E).
  Qed.
  Lemma ob_903 : HOBL HS_903.   Proof. exact (SEG IT1 IT1_ok _ _ _ T11_13_ok ok_s1_q11 cert_4). Qed.
  Lemma ob_902 : HOBL HS_902.   Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_903) ok_s1_q7 cert_3). Qed.
  Lemma ob_901 : HOBL HS_901.   Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_902) ok_s1_q5 cert_2). Qed.
  Lemma ob_900 : HOBL HS_900.   Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_901) ok_s1_q4 cert_1b). Qed.
  Lemma ob_init : HOBL both_init_S. Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_900) ok_s1_planP cert_1a). Qed.

End StartupB.


