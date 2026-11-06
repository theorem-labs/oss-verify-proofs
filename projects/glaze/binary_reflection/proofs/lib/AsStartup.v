(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsCertM1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_1a : cert_okS IT1 T900 asan_init_S s1_planP = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_1b : cert_okS IT1 T901 HS_900 s1_q4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_4 : cert_okS IT1 T11_13 HS_903 s1_q11 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5a : cert_okS IT1 T916J HS_11J s1_planT = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma cert_5a2 : cert_okS IT1 T916Jb HS_915 s1_planTb = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End AsCertM1.
Module AsCertS2a.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2a : cert_okS IT2a T950 HS_0 s2a_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End AsCertS2a.
Module AsCertS2b.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2b : cert_okS IT2b T951 HS_950 s2b_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End AsCertS2b.
Module AsCertS2c.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_S2c : cert_okS IT2c T1_2 HS_951 s2c_plan = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End AsCertS2c.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsStartupTabsOk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
Open Scope Z_scope.
Lemma IT1_ok : itab_sound ASEGS IT1.   Proof. exact (APS.mk_itab_ranges_sound ASEGS s1_plan_ranges). Qed.
Lemma IT2a_ok : itab_sound ASEGS IT2a. Proof. exact (APS.mk_itab_ranges_sound ASEGS s2a_plan_ranges). Qed.
Lemma IT2b_ok : itab_sound ASEGS IT2b. Proof. exact (APS.mk_itab_ranges_sound ASEGS s2b_plan_ranges). Qed.
Lemma IT2c_ok : itab_sound ASEGS IT2c. Proof. exact (APS.mk_itab_ranges_sound ASEGS s2c_plan_ranges). Qed.
End AsStartupTabsOk.
Require Stdlib.NArith.NArith Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsStartupSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section Startup.
  (* [comment removed for export] *)
  Variable RR : shape_rel ASEGS.
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
  Hypothesis IMG : img_facts ASEGS AT_A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
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
  Hypothesis SEGS_wx : wx_segs_nowrap ASEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull AT_A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
  Hypothesis RES_len : res_len_ok ASEGS AT_A.
  Hypothesis RES_hull : Forall (fun iv => img_lo AT_A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_A) (segments_reserved ASEGS).
  Hypothesis HULL_ok : hull_ok AT_A.
  Hypothesis SHADOW_ok : shadow_ok AT_A.
  Hypothesis RES_tile : forall z, img_lo AT_A <= z < img_hi AT_A -> in_ivs z (segments_reserved ASEGS) = true.
  Hypothesis HULL_ne : img_lo AT_A < img_hi AT_A.

  (* [comment removed for export] *)
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound ASEGS IT.

  Definition hole_obl_f (ch : acs) : Prop :=
    forall E fx R M model, cs_ok ASEGS AT_A LIMIT_S SINV argH ISP_S fs E ch R M model -> fx_ok fx ->
      realizes ASEGS (GPS.cfgF ASEGS fx R (pc ch) M model) T.

  (* [comment removed for export] *)
  Hypothesis XN_sound : SIF.ext_stmt ASEGS RR AT_A NXS LIMIT_S XN_S SINV argH ISP_S fs fx_ok.

  Lemma XE_sound : SIF.emit_stmt ASEGS RR AT_A NXS LIMIT_S XE_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.
  Lemma XB_sound : SIF.ext2_stmt ASEGS RR AT_A NXS LIMIT_S XB_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.
  Lemma XA_sound : SIF.alt2_stmt ASEGS RR AT_A NXS LIMIT_S XA_S SINV argH ISP_S fs fx_ok.
  Proof. red. intros. discriminate. Qed.

  (* [comment removed for export] *)
  Definition hole_oblR (ch : acs) : Prop :=
    forall E fx R M model, cs_ok ASEGS AT_A LIMIT_S SINV argH ISP_S fs E ch R M model -> fx_ok fx ->
      RR (GPS.cfgF ASEGS fx R (pc ch) M model) T.

  (* [comment removed for export] *)
  Definition table_ok (HS : nat -> option acs) : Prop := forall h ch, HS h = Some ch -> hole_oblR ch.

  Lemma table_holes_stmt : forall HS, table_ok HS -> SIF.holes_stmt ASEGS RR AT_A LIMIT_S HS SINV argH ISP_S fs fx_ok HOLES.
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
    checkA ASEGS IT AT_A NXS LIMIT_S ISP_S XN_S XE_S XB_S XA_S AP.XT0 HS KC_S true BFUEL_S FUEL_S None cs p = COk s ->
    hole_oblR cs.
  Proof.
    intros HS p cs s HT Hp Hs CERT E fx R M model HC HF.
    eapply (sr_conseq ASEGS RR).
    - eapply (SPS.check_sound ASEGS RR IT IT_ok AT_A NXS LIMIT_S HS XN_S XE_S XB_S XA_S AP.XT0 KC_S SINV argH fs fx_ok HOLES T
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
    table_ok HS -> SPS.splan_ok p = true -> cert_okS IT HS cs p = true -> hole_oblR cs.
  Proof.
    intros HS p cs HT Hp. unfold cert_okS, chkS.
    pose proof (segment_sound HS p cs) as SS.
    generalize dependent SS.
    generalize (checkA ASEGS IT AT_A NXS LIMIT_S ISP_S XN_S XE_S XB_S XA_S AP.XT0 HS KC_S true BFUEL_S FUEL_S None cs p).
    intros r SS HC. destruct r as [s|code wh ecs]; [|discriminate HC].
    apply (SS s HT Hp); [apply fullT_shapeT; exact HC | reflexivity].
  Qed.

End Startup.



End AsStartupSound.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtSums.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (AX2.ridx r) APC.caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop :=
  forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
    0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    bv_unsigned c < cmax ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = s.

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition miz_spec (entry : Z) : Prop :=
  forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
    0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
    (forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.

(* [comment removed for export] *)
Definition SEALED_BYTES : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]%Z
  ++ repeat (Z_to_bv 8 0) 4087.

(* [comment removed for export] *)
Definition istrncpy_spec (entry src : Z) : Prop :=
  forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
    (forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
    store_ok SEGS mem0 dst 4095%nat = true ->
    bv_unsigned dst + 4095 < 2 ^ 64 ->
    (bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clob_in_caller_saved Hin :=
  cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|]); destruct Hin.

Lemma kept_of_agree : forall (l : list reg) regs regs',
  (forall r, In r l -> In (AX2.ridx r) APC.caller_saved) ->
  regs_agree (fun r => In r l) regs regs' -> kept_ok regs regs'.
Proof using. intros l regs regs' Hl AG r Hr0 Hn. apply AG. intros Hin. apply Hn. apply Hl. exact Hin. Qed.

Lemma imemset_clob_cs : forall r, In r imemset_clob -> In (AX2.ridx r) APC.caller_saved.
Proof using. intros r Hin. unfold imemset_clob in Hin. clob_in_caller_saved Hin. Qed.
Lemma imemcpy_clob_cs : forall r, In r imemcpy_clob -> In (AX2.ridx r) APC.caller_saved.
Proof using. intros r Hin. unfold imemcpy_clob in Hin. clob_in_caller_saved Hin. Qed.
Lemma memisz_clob_cs : forall r, In r memisz_clob -> In (AX2.ridx r) APC.caller_saved.
Proof using. intros r Hin. unfold memisz_clob in Hin. clob_in_caller_saved Hin. Qed.
Lemma istrncpy_clob_cs : forall r, In r istrncpy_clob -> In (AX2.ridx r) APC.caller_saved.
Proof using. intros r Hin. unfold istrncpy_clob in Hin. clob_in_caller_saved Hin. Qed.
Lemma ms_clob_cs : forall r, In r ms_clob -> In (AX2.ridx r) APC.caller_saved.
Proof using. intros r Hin. unfold ms_clob in Hin. clob_in_caller_saved Hin. Qed.

(* [comment removed for export] *)
Lemma kept_of_keeps : forall regs regs', keeps regs regs' -> kept_ok regs regs'.
Proof using.
  intros regs regs' K r Hr0 Hn.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  remember (AX2.ridx r) as n eqn:En.
  assert (Hn32 : (n < 32)%nat) by (rewrite En; (lazymatch goal with |- ?G => let G' := eval unfold AX2.ridx in G in change_no_check G' end); lia).
  assert (E : r = Z_to_bv 5 (Z.of_nat n)).
  { rewrite En; (lazymatch goal with |- ?G => let G' := eval unfold AX2.ridx in G in change_no_check G' end). rewrite Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  apply K. rewrite E. clear En.
  (lazymatch goal with |- ?G => let G' := eval unfold callee_kept in G in change_no_check G' end).
  do 32 (destruct n as [|n];
    [ first [ solve [(lazymatch goal with |- ?G => let G' := eval cbn [In Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])]
            | solve [exfalso; apply Hn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto]
            | solve [exfalso; apply Hr0; rewrite E; apply bv_eq; vm_compute; reflexivity] ]
    |]).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_fill_spec_imemset : fill_spec ASEGS 0x7ff38 256.
Proof using.
  intros mem0 s c n regs ret Hn Hnw Hok Hc Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x7ff38 : word) with asan_imemset_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (asan_imemset mem0 s c n (seg_rom ASEGS) regs ret Hn Hnw Hok (fun _ _ => Hc) Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ imemset_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.

Lemma asan_fill_spec_memset : fill_spec ASEGS 0xf56e4 (2 ^ 64).
Proof using.
  intros mem0 s c n regs ret Hn Hnw Hok Hc Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0xf56e4 : word) with asan_memset_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (asan_memset mem0 s c ret n (seg_rom ASEGS) regs Hn Hnw Hok Hret H10 H11 H12 H1) as (r & RUN & A10 & AG).
  exists r. split; [exact RUN | split; [exact (kept_of_agree _ _ _ ms_clob_cs AG) | exact A10]].
Qed.

Lemma asan_copy_spec_imemcpy : copy_spec ASEGS 0x7febc.
Proof using.
  intros mem0 dst src n bs regs ret Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x7febc : word) with asan_imemcpy_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (asan_imemcpy mem0 dst src n bs (seg_rom ASEGS) regs ret (CPYH _ _ _ _ _ _ Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd) Hret H1 H10 H11 H12)
    as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ imemcpy_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold imemcpy_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.

Lemma asan_copy_spec_memcpy : copy_spec ASEGS 0xf52e0.
Proof using.
  intros mem0 dst src n bs regs ret Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0xf52e0 : word) with asan_memcpy_entry by (apply bv_eq; vm_compute; reflexivity).
  assert (HOK : AsRtMemcpyBase.mcH ASEGS mem0 dst src n bs) by (pose proof (u64_range dst); split; try assumption; lia).
  destruct (asan_memcpy mem0 dst src n bs (seg_rom ASEGS) regs ret HOK Hret H1 H10 H11 H12) as (r & RUN & K).
  exists r. split; [exact RUN | split; [exact (kept_of_keeps _ _ K) | rewrite (K 10%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact H10]].
Qed.

Lemma asan_miz_spec : miz_spec ASEGS 0x80468.
Proof using.
  intros mem beg sp N regs ret HN Hnw Hsp Hok Hdisj Hz Hret H1 H2 H10 H11.
  replace (Z_to_bv 64 0x80468 : word) with asan_mem_is_zero_entry by (apply bv_eq; vm_compute; reflexivity).
  destruct (asan_mem_is_zero mem beg sp N (seg_rom ASEGS) regs ret HN Hnw Hsp Hok Hdisj Hz Hret H1 H2 H10 H11) as (r & RUN & AG & A10 & _).
  exists r. split; [exact RUN | split; [exact (kept_of_agree _ _ _ memisz_clob_cs AG) | exact A10]].
Qed.

Lemma asan_istrncpy_spec : istrncpy_spec ASEGS 0x80364 0x11abe.
Proof using.
  intros mem0 dst regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  replace (Z_to_bv 64 0x80364 : word) with asan_istrncpy_entry by (apply bv_eq; vm_compute; reflexivity).
  change SEALED_BYTES with strncpy_sealed_bytes. change 0x11abe%Z with asan_sealed_src in *.
  destruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS) regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r. split; [exact RUN | split].
  - exact (kept_of_agree _ _ _ istrncpy_clob_cs AG).
  - rewrite (AG 10%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold istrncpy_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). exact H10.
Qed.

End FPGen1.
End AsRtSums.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSums OSSVerify.Proofs.glaze.binary_reflection.lib.AzSStartX OSSVerify.Proofs.glaze.binary_reflection.lib.AzSExt OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsStartupXN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSSums OSSVerify.Proofs.glaze.binary_reflection.lib.AzSStartX OSSVerify.Proofs.glaze.binary_reflection.lib.AzSExt.
Import AsRtSums.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma hull_okP_A : APSX.hull_okP AT_A.
Proof. unfold APSX.hull_okP. vm_compute. repeat split; try reflexivity; try discriminate. Qed.

Lemma hull_ok_A : APS.hull_ok AT_A.
Proof. exact asan_S_hull_ok. Qed.

Lemma segs_wr_A : APSX.segs_wr_ok ASEGS.
Proof.
  intros seg Hin Hw. rewrite AsImages.ASEGS_eq, AzImageAsan.asan_segs_eq in Hin.
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
  Variable RR : shape_rel ASEGS.
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
  Hypothesis IMG : img_facts ASEGS AT_A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
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
  Let N1 := SIF.node1_stmtN ASEGS RR AT_A NXS LIMIT_S SINV argH ISP_S fs AzSymStepR.fx_ok SIF.always.

  Lemma hook27 : N1 (fun cs => Some cs).
  Proof.
    red. intros cs cs' E fx R M model T HT HC HF _ Hn K. injection Hn as <-.
    apply (K E fx R M model); [split; apply APS.env_agree_refl | exact HC | exact HF | reflexivity].
  Qed.

  Lemma hook210 : forall args, N1 (fun cs => node_nameword NXS cs args).
  Proof. intros args. exact (AzSExt.node_nameword_sound ASEGS RR AT_A NXS LIMIT_S SINV argH fs AzSymStepR.fx_ok ISP_S ISP_vars argH_agree SINV_agree args). Qed.

  Lemma hook200 : N1 (fun cs => summary_fill AT_A NXS cs (x_imemset AT_A) 256).
  Proof. exact (APSX.summary_fill_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (x_imemset AT_A) 256 (fun fx => @AsRtSums.asan_fill_spec_imemset fx)). Qed.
  Lemma hook201 : N1 (fun cs => summary_fill AT_A NXS cs (x_memset AT_A) two64).
  Proof. exact (APSX.summary_fill_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (x_memset AT_A) two64 (fun fx => @AsRtSums.asan_fill_spec_memset fx)). Qed.
  Lemma hook202 : N1 (fun cs => summary_copy ASEGS AT_A NXS cs (x_imemcpy AT_A)).
  Proof. exact (APSX.summary_copy_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok segs_wr_A (x_imemcpy AT_A) (fun fx => @AsRtSums.asan_copy_spec_imemcpy fx)). Qed.
  Lemma hook203 : N1 (fun cs => summary_copy ASEGS AT_A NXS cs (x_memcpy AT_A)).
  Proof. exact (APSX.summary_copy_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok segs_wr_A (x_memcpy AT_A) (fun fx => @AsRtSums.asan_copy_spec_memcpy fx)). Qed.
  Lemma hook204 : N1 (fun cs => summary_miz AT_A NXS cs).
  Proof. exact (APSX.summary_miz_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (fun fx => @AsRtSums.asan_miz_spec fx)). Qed.
  Lemma hook205 : N1 (fun cs => summary_istrncpy AT_A NXS cs).
  Proof. exact (APSX.summary_istrncpy_stmtN ASEGS RR AT_A NXS LIMIT_S asan_S_wx asan_S_in_hull hull_okP_A SINV argH ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree fs AzSymStepR.fx_ok (fun fx => @AsRtSums.asan_istrncpy_spec fx)). Qed.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.   Proof. exact (proj1 Hsp). Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.   Proof. exact (proj1 (proj2 Hsp)). Qed.

  Lemma hook206 : N1 (node_envscan AT_A).
  Proof.
    apply SIF.node1_stmt_N.
    eapply (SX.node_envscan_stmt ASEGS RR AT_A NXS LIMIT_S SINV argH fs asan_S_wx asan_S_in_hull hull_ok_A ISP_S SINV_frame AzSymStepR.fx_ok W_e6630 W_e6634 W_e6638).
    - vm_compute. repeat split; try reflexivity; try discriminate.
    - exact F_e6630. - exact F_e6634. - exact F_e6638.
    - vm_compute. repeat split; reflexivity.
    - exact D_e6630. - exact D_e6634. - exact D_e6638.
    - exact Hva. - exact Hve. - exact sp_lo. - exact sp_hi.
    - exact SINV_isp. - exact SINV_envp. - exact SINV_envarr.
  Qed.

  Lemma hook207 : N1 (node_pnscan AT_A NXS).
  Proof.
    apply SIF.node1_stmt_N.
    eapply (SX.node_pnscan_stmt ASEGS RR AT_A NXS LIMIT_S SINV argH fs asan_S_wx asan_S_in_hull hull_ok_A ISP_S ISP_vars argH_high argH_agree SINV_frame SINV_agree AzSymStepR.fx_ok W_e66ec W_e66f0 W_e66f4 W_e66f8 W_e66fc).
    - vm_compute. repeat split; try reflexivity; try discriminate.
    - exact F_e66ec. - exact F_e66f0. - exact F_e66f4. - exact F_e66f8. - exact F_e66fc.
    - vm_compute. repeat split; reflexivity.
    - exact D_e66ec. - exact D_e66f0. - exact D_e66f4. - exact D_e66f8. - exact D_e66fc.
    - exact Hva. - exact Hve. - exact sp_lo. - exact sp_hi.
    - exact SINV_isp. - exact SINV_envp. - exact SINV_str0.
  Qed.

  Lemma hook208 : forall args, N1 (fun cs => node_layout cs args).
  Proof. intros args. apply SIF.node1_stmt_N. exact (SX.node_layout_stmt ASEGS RR AT_A NXS LIMIT_S SINV argH fs ISP_S AzSymStepR.fx_ok args). Qed.

  (* [comment removed for export] *)
  Lemma XN_S_cases : forall id args cs r, XN_S id args cs = Some r ->
    (id = 210 \/ id = 200 \/ id = 201 \/ id = 202 \/ id = 203 \/ id = 204 \/ id = 205 \/ id = 206 \/ id = 207 \/ id = 208 \/ id = 27)%nat.
  Proof.
    intros id args cs r H. unfold XN_S in H.
    do 211 (destruct id as [|id]; [first [discriminate H | lia] |]).
    discriminate H.
  Qed.

  Theorem XN_S_sound : SIF.ext_stmt ASEGS RR AT_A NXS LIMIT_S XN_S SINV argH ISP_S fs AzSymStepR.fx_ok.
  Proof.
    intros id args cs cs' E fx R M model T HT HC HF Hpre Hn K.
    destruct (XN_S_cases id args cs cs' Hn) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
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
End AsStartupXN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymStepR AzSymExec3 AzSymExec3B AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS AzSIface AzSSound AzNodesSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages AsStartupSound AsStartupXN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs AsStartupTabsOk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsCertM2. Import AsCertM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCertM2 AsCertS2a AsCertS2b AsCertS2c.
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

Section StartupA.
  (* [comment removed for export] *)
  Variable RR : shape_rel ASEGS.
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
  Hypothesis IMG : img_facts ASEGS AT_A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  (* [comment removed for export] *)
  Let XN_sound : SIF.ext_stmt ASEGS RR AT_A NXS LIMIT_S XN_S (AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw)
                   (AsSInit.argH0 ph sp rdraw argv envp uid hw) ISP_S fs AzSymStepR.fx_ok
    := AsStartupXN.XN_S_sound RR ph sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit.

  Let HOBL := hole_oblR RR ph sp rdraw brk0 argv envp fs uid hw T.
  Let TOK := table_ok RR ph sp rdraw brk0 argv envp fs uid hw T.

  (* [comment removed for export] *)
  Let SEG (IT : itab) (IT_ok : itab_sound ASEGS IT) :=
    segment_ok RR ph sp rdraw brk0 argv envp fs uid hw Hsp Hva T T_nil
      asan_S_wx asan_S_in_hull asan_S_res_len asan_S_res_hull asan_S_hull_ok asan_S_shadow_ok asan_S_res_tile asan_S_hull_ne
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
  Lemma ob_init : HOBL asan_init_S. Proof. exact (SEG IT1 IT1_ok _ _ _ (tab1_ok _ _ ob_900) ok_s1_planP cert_1a). Qed.

End StartupA.


