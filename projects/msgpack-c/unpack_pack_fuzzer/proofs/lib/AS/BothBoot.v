(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's whole ProcInput and kernel build, and the five start-up segments' certificates used at the run's own CONFIG_RSEQ value, each from the hand-off state the one before computes). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin BothStartup
  StartupPlanBoth StartupPlan2Both PlanRegen BothStartupCert BothStartupCertB BothStartupCertC BothStartupCertD BothStartupCert2.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Section Boot.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable ifs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  #[local] Notation INP := (AsanInit.inp argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation fs := (in_fs INP).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrdr : in_channel_reader INP = true.

  #[local] Notation SINV := (SINV0 BOTH BPH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  (** the run's CONFIG_RSEQ flag as the plans' 0 or 1: every certificate is used at it *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  Let RZr : 0 <= RZ <= 1 := rseq_z_range (kb_rseq kb).

  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM (HS_both2 RZ) SINV argH (fun _ => H) fs.

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a Ha. eapply argH0_high; eassumption. Qed.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS Ha. eapply argH0_high2; eassumption. Qed.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a Hag. eapply argH0_agree; exact Hag. Qed.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' H1 H2. eapply SINV0_frame; eassumption. Qed.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M H1 H2. eapply SINV0_agree; eassumption. Qed.

  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS BOTH LIM HSn SINV argH HH fs ->
      check BSEGS IT BOTH nx LIM RZ (XNS BSEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound BSEGS IT IT_ok BOTH nx Hnx LIM RZ HSn (XNS BSEGS BOTH nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
                (both_node_x_sound_all sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm
                   fs Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                (XNS_sound BSEGS BOTH nx LIM SINV argH fs AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  Ltac holes_by_cases := cbv beta; match goal with |- holes_only (?f RZ) = true => unfold f; destruct (Z.eqb RZ 1); vm_compute; reflexivity end.

  Lemma S2_sound : holes_stmt BSEGS BOTH LIM (HS_bothD RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothD RZ) 0%nat (HD RZ) (HS_bothD_one RZ)).
    apply (seg_sound (NXS2 RZ) (NXS2_ge RZ) IT2 IT2_ok (HS_both2 RZ) FUEL BFUEL KC0 startup2_plan_both_k (HD RZ) (shape2 RZ));
      [| exact (cert2 RZ RZr) | holes_by_cases].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS BOTH LIM (HS_bothC RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothC RZ) 12%nat (HC RZ) (HS_bothC_one RZ)).
    apply (seg_sound (NXD RZ) (NXD_ge RZ) ITD ITD_ok (HS_bothD RZ) FUEL BFUEL KC0 startup_plan_both_segC_k (HC RZ) (shapeD RZ));
      [exact S2_sound | exact (certD RZ RZr) | holes_by_cases].
  Qed.
  Lemma C_sound : holes_stmt BSEGS BOTH LIM (HS_bothB RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothB RZ) 11%nat (HB RZ) (HS_bothB_one RZ)).
    apply (seg_sound (NXC RZ) (NXC_ge RZ) ITC ITC_ok (HS_bothC RZ) FUEL BFUEL KC0 (planC RZ) (HB RZ) (shapeC RZ));
      [exact D_sound | exact (certC RZ RZr) | holes_by_cases].
  Qed.
  Lemma B_sound : holes_stmt BSEGS BOTH LIM (HS_bothA RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothA RZ) 10%nat (HA RZ) (HS_bothA_one RZ)).
    apply (seg_sound (NXB RZ) (NXB_ge RZ) ITB ITB_ok (HS_bothB RZ) FUEL BFUEL KC0 startup_plan_both_segA_k (HA RZ) (shapeB RZ));
      [exact C_sound | exact (certB RZ RZr) | holes_by_cases].
  Qed.

  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM INP)
              (sd HH t_nil E0a fs startup_shape).
  Proof.
    exact (both_startup sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau Hrdr
             IT0 IT0_ok (HS_bothA RZ) startup_plan_both_k startup_shape KC0 BFUEL FUEL (startup_cert RZ RZr) HH HH_agree HH_nil B_sound).
  Qed.

  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM INP)
              (H E0a fs).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
