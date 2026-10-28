(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanNodesWJoin AsanStartup
  StartupPlanAsan StartupHSAsan AsanStartupCert AsanStartupCertB AsanStartupCertC AsanStartupCertD
  StartupPlan2Asan StartupHS2Asan AsanStartupCert2.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Section Boot.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.          (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS ASAN LIM HS_both2 SINV argH (fun _ => H) (fs_seed_tmp fs tmp).

  Let AH := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree BPH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame BPH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree BPH sp rdraw brk0 argv envp uid hw.

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

  (* [comment removed for export] *)
  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS ASAN LIM HSn SINV argH HH (fs_seed_tmp fs tmp) ->
      check BSEGS IT ASAN nx LIM (XNS BSEGS ASAN nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp) E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound BSEGS IT IT_ok ASAN nx Hnx LIM HSn (XNS BSEGS ASAN nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil (fs_seed_tmp fs tmp) KC
                (AsanNodesMmB.node_sys_sound BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp))
                (both_node_x_sound_all sp rdraw brk0 argv envp (fs_seed_tmp fs tmp) Hsp Hva Hve uid hw Hfit SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp))
                (XNS_sound BSEGS ASAN nx LIM SINV argH (fs_seed_tmp fs tmp) AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp) E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS ASAN LIM HSp SINV argH HH (fs_seed_tmp fs tmp).
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt BSEGS ASAN LIM HS_bothD SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    apply (seg_holes HS_bothD 0%nat HS_bothD_0); [intros [|h] ch Hh; cbn in Hh; [injection Hh as <-; split; reflexivity | discriminate Hh]|].
    apply (seg_sound NXS2 NXS2_ge IT2 IT2_ok HS_both2 FUEL BFUEL KC0 startup2_plan_both HS_bothD_0 startup2_shape); [| exact startup2_cert | reflexivity].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS ASAN LIM HS_bothC SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    apply (seg_holes HS_bothC 12%nat HS_bothC_12).
    { intros h ch Hh. unfold HS_bothC in Hh. do 12 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXD NXD_ge ITD ITD_ok HS_bothD FUEL BFUEL KC0 startup_plan_both_segC HS_bothC_12 startup_shapeD); [exact S2_sound | exact startup_certD | reflexivity].
  Qed.
  Lemma C_sound : holes_stmt BSEGS ASAN LIM HS_bothB SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    apply (seg_holes HS_bothB 11%nat HS_bothB_11).
    { intros h ch Hh. unfold HS_bothB in Hh. do 11 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXC NXC_ge ITC ITC_ok HS_bothC FUEL BFUEL KC0 startup_plan_both_segB HS_bothB_11 startup_shapeC); [exact D_sound | exact startup_certC | reflexivity].
  Qed.
  Lemma B_sound : holes_stmt BSEGS ASAN LIM HS_bothA SINV argH HH (fs_seed_tmp fs tmp).
  Proof.
    apply (seg_holes HS_bothA 10%nat HS_bothA_10).
    { intros h ch Hh. unfold HS_bothA in Hh. do 10 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXB NXB_ge ITB ITB_ok HS_bothB FUEL BFUEL KC0 startup_plan_both_segA HS_bothA_10 startup_shapeB); [exact C_sound | exact startup_certB | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS Asan.M.init_pc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp))
              (sd HH t_nil E0a (fs_seed_tmp fs tmp) startup_shape).
  Proof.
    exact (both_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
             IT0 IT0_ok HS_bothA startup_plan_both startup_shape KC0 BFUEL FUEL startup_cert HH HH_agree HH_nil B_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS Asan.M.init_pc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp))
              (H E0a (fs_seed_tmp fs tmp)).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
