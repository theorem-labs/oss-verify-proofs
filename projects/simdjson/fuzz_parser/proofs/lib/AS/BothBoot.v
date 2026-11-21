(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up proof takes the run's whole launch input and its CONFIG_RSEQ value, and chains the start-up certificates over the hand-off states computed in the build. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin BothStartup
  StartupPlanBoth BothStartupCert BothStartupCertB BothStartupCertC BothStartupCertD
  StartupPlan2Both BothStartupCert2 PlanRegen.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* A certificate is stated over its wrapper ([run0] .. [run2], each one [check] call) and is used
   where [check] itself is named: the wrapper is unfolded first (explicitly, and as the conversion
   order of the kernel), so that [check] is never reduced at a free CONFIG_RSEQ value. *)
Local Strategy expand [run0 runB runC runD run2].

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Section Boot.
  (* LPS 727298f3: the run's whole launch input, as AS/AsanInit.v's Section Init takes it; the
     start-up certificates are used at the run's own CONFIG_RSEQ value [RZ] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  #[local] Notation fs := (in_fs inp).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range _). Qed.

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM (HS_both2 RZ) SINV argH (fun _ => H) fs.

  Let AH := argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva.
  Let AH2 := argH0_high2 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
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

    Lemma xall_nx : forall x, x_stmt BSEGS BOTH nx LIM RZ SINV argH fs x.
    Proof.
      intros x. eapply both_node_x_sound_all;
        first [ exact (fun E M HH0 => HH0) | exact SF | exact SAn | exact Hnx | eassumption ].
    Qed.

    (* [comment removed for export] *)
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
                xall_nx
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                (XNS_sound BSEGS BOTH nx LIM SINV argH fs AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* a certificate as the check it states, its wrapper unfolded (fuzz_utf8's AsanBoot form) *)
  Local Ltac cert_r C := let Hc := fresh "Hc" in
    pose proof C as Hc; cbv delta [run0 runB runC runD run2] beta in Hc; exact Hc.

  (* the computed shapes have holes only, at both CONFIG_RSEQ values *)
  Lemma holes_root : holes_only (startup_shape RZ) = true.
  Proof. unfold startup_shape. destruct (Z.eqb RZ 1); vm_compute; reflexivity. Qed.
  Lemma holes_B : holes_only (startup_shapeB RZ) = true.
  Proof. unfold startup_shapeB. destruct (Z.eqb RZ 1); vm_compute; reflexivity. Qed.
  Lemma holes_C : holes_only (startup_shapeC RZ) = true.
  Proof. unfold startup_shapeC. destruct (Z.eqb RZ 1); vm_compute; reflexivity. Qed.
  Lemma holes_D : holes_only (startup_shapeD RZ) = true.
  Proof. unfold startup_shapeD. destruct (Z.eqb RZ 1); vm_compute; reflexivity. Qed.
  Lemma holes_2 : holes_only (startup2_shape RZ) = true.
  Proof. unfold startup2_shape. destruct (Z.eqb RZ 1); vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt BSEGS BOTH LIM (HS_bothD RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothD RZ) 0%nat (HS_D RZ) (HS_bothD_one RZ)).
    apply (seg_sound (nxt (HS_D RZ)) (NX_D_ge RZ) IT2 IT2_ok (HS_both2 RZ) FUEL BFUEL KC0 (startup2_plan_both_k RZ) (HS_D RZ) (startup2_shape RZ));
      [| cert_r (startup2_cert RZ RZ_range) | exact holes_2].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS BOTH LIM (HS_bothC RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothC RZ) 12%nat (HS_C RZ) (HS_bothC_one RZ)).
    apply (seg_sound (nxt (HS_C RZ)) (NX_C_ge RZ) ITD ITD_ok (HS_bothD RZ) FUEL BFUEL KC0 (startup_plan_both_segC_k RZ) (HS_C RZ) (startup_shapeD RZ));
      [exact S2_sound | cert_r (startup_certD RZ RZ_range) | exact holes_D].
  Qed.
  Lemma C_sound : holes_stmt BSEGS BOTH LIM (HS_bothB RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothB RZ) 11%nat (HS_B RZ) (HS_bothB_one RZ)).
    apply (seg_sound (nxt (HS_B RZ)) (NX_B_ge RZ) ITC ITC_ok (HS_bothC RZ) FUEL BFUEL KC0 (startup_plan_both_segB_k RZ) (HS_B RZ) (startup_shapeC RZ));
      [exact D_sound | cert_r (startup_certC RZ RZ_range) | exact holes_C].
  Qed.
  Lemma B_sound : holes_stmt BSEGS BOTH LIM (HS_bothA RZ) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS_bothA RZ) 10%nat (HS_A RZ) (HS_bothA_one RZ)).
    apply (seg_sound (nxt (HS_A RZ)) (NX_A_ge RZ) ITB ITB_ok (HS_bothB RZ) FUEL BFUEL KC0 (startup_plan_both_segA_k RZ) (HS_A RZ) (startup_shapeB RZ));
      [exact C_sound | cert_r (startup_certB RZ RZ_range) | exact holes_B].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp)
              (sd HH t_nil E0a fs (startup_shape RZ)).
  Proof.
    pose proof (startup_cert RZ RZ_range) as C0. cbv delta [run0] beta in C0.
    exact (both_startup sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau Hhw
             IT0 IT0_ok (HS_bothA RZ) (startup_plan_both_k RZ) (startup_shape RZ) KC0 BFUEL FUEL C0 HH HH_agree HH_nil B_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp)
              (H E0a fs).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; exact holes_root]. Qed.
End Boot.
