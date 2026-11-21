(* TRIAL NOT-OFFICIAL: AS/AsanBoot = our text + 727298f3's own edits to theories/Common/AsanBoot.v, 3-way merged (proposal md5 bc2f641b); the old text is kept aside *)
(* TRIAL NOT-OFFICIAL: A1 split: Section Boot gains VSEGS + VSEGS_nx + VSEGS_res; asan_boot(_shape) over the run's list ASEGS ++ VSEGS; the node lemmas get the tail *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_asan.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.SpinAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AgentLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AsanAcct OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanAcctImages OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymExec3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymExec3Sound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymRun3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanCore OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanSound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanSound2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanPlanImages OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanInit OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesMmA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesMmB OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.SumsAsanClose OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesStartX OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanNodesStartXAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesWJoin OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartup OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupPlanAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCert OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCertB OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCertC OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCertD OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupPlan2Asan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHS2Asan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCert2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanRenum OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan727.
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
  Variable lim : Z.   (* [comment removed for export] *)
  Hypothesis Hlim : AsanInit.LIMIT <= lim.
  (* an earlier development run 727298f3: the launch *)
  Variable kb : KernelBuild.
  Variable efn : list byte.
  Variable sigdef : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  #[local] Notation APC := TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation SINV := (SINV0 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb efn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 mbase argv envp uid gid hw kb efn).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  (* an earlier development run 727298f3 A1: the run reads ASEGS ++ VSEGS (Run.run_segments; VSEGS = the vDSO pair) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.
  Hypothesis VSEGS_res : segments_reserved VSEGS = [].
  (* an earlier development run 727298f3: the main body takes the per-rseq hand-off states *)
  Hypothesis MAIN : holes_stmt ASEGS VSEGS ASAN LIM (HS727_2 RZK) SINV argH (fun _ => H) fs.

  Let AH := argH0_high APC sp rdraw argv envp Hsp Hva kb efn.
  Let AH2 := argH0_high2 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
               nof sigm abt urnd kb efn sigdef Hlau.
  Let AA := argH0_agree sp rdraw argv envp kb efn.
  Let SF := SINV0_frame APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  Let SA := SINV0_agree APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.

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
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound ASEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt ASEGS VSEGS ASAN LIM HSn SINV argH HH fs ->
      check ASEGS IT ASAN nx LIM RZK (XNS ASEGS ASAN nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
        srealizes (ASEGS ++ VSEGS) (cfg_of (ASEGS ++ VSEGS) R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound ASEGS VSEGS VSEGS_nx IT IT_ok ASAN nx Hnx LIM RZK HSn (XNS ASEGS ASAN nx LIM) XE0 XB0
                asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound ASEGS VSEGS VSEGS_nx ASAN nx LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound ASEGS VSEGS VSEGS_nx ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL ASEGS VSEGS VSEGS_nx ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL ASEGS VSEGS VSEGS_nx ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL ASEGS VSEGS VSEGS_nx ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound ASEGS VSEGS VSEGS_nx ASAN LIM SINV argH fs)
                (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit mbase fs stdin APC gid groups net kb
                   nof sigm abt urnd efn sigdef Hlaunch Hlau SINV (fun E M HH0 => HH0) SF nx Hnx SAn VSEGS VSEGS_nx)
                (node_join_sound ASEGS VSEGS ASAN nx LIM SINV argH fs)
                (XNS_sound ASEGS VSEGS ASAN nx LIM SINV argH fs AAn SAn asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
         srealizes (ASEGS ++ VSEGS) (cfg_of (ASEGS ++ VSEGS) R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt ASEGS VSEGS ASAN LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* an earlier development run 727298f3: a one-entry hand-off table *)
  Lemma one_entry : forall (h0 : nat) (st : acs) h ch,
    (if Nat.eqb h h0 then Some st else None) = Some ch -> h = h0 /\ ch = st.
  Proof. intros h0 st h ch Hh. destruct (Nat.eqb_spec h h0) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt ASEGS VSEGS ASAN LIM (HS727D RZK) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS727D RZK) 0%nat (HS727D_0 RZK)); [intros h ch Hh; exact (one_entry 0 _ h ch Hh)|].
    apply (seg_sound NXS2 NXS2_ge IT2 IT2_ok (HS727_2 RZK) FUEL BFUEL KC0 (plan727 RZK startup2_plan) (HS727D_0 RZK) (startup2_shape RZK));
      [| exact (startup2_cert (kb_rseq kb)) | destruct (kb_rseq kb); vm_compute; reflexivity].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt ASEGS VSEGS ASAN LIM (HS727C RZK) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS727C RZK) 12%nat (HS727C_12 RZK)); [intros h ch Hh; exact (one_entry 12 _ h ch Hh)|].
    apply (seg_sound NXD NXD_ge ITD ITD_ok (HS727D RZK) FUEL BFUEL KC0 (plan727 RZK startup_plan_segC) (HS727C_12 RZK) startup_shapeD);
      [exact S2_sound | exact (startup_certD (kb_rseq kb)) | reflexivity].
  Qed.
  Lemma C_sound : holes_stmt ASEGS VSEGS ASAN LIM (HS727B RZK) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS727B RZK) 11%nat (HS727B_11 RZK)); [intros h ch Hh; exact (one_entry 11 _ h ch Hh)|].
    apply (seg_sound NXC NXC_ge ITC ITC_ok (HS727C RZK) FUEL BFUEL KC0 (plan727 RZK startup_plan_segB) (HS727B_11 RZK) (startup_shapeC RZK));
      [exact D_sound | exact (startup_certC (kb_rseq kb)) | destruct (kb_rseq kb); vm_compute; reflexivity].
  Qed.
  Lemma B_sound : holes_stmt ASEGS VSEGS ASAN LIM (HS727A RZK) SINV argH HH fs.
  Proof.
    apply (seg_holes (HS727A RZK) 10%nat (HS727A_10 RZK)); [intros h ch Hh; exact (one_entry 10 _ h ch Hh)|].
    apply (seg_sound NXB NXB_ge ITB ITB_ok (HS727B RZK) FUEL BFUEL KC0 (plan727 RZK startup_plan_segA) (HS727A_10 RZK) startup_shapeB);
      [exact C_sound | exact (startup_certB (kb_rseq kb)) | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot_shape :
    srealizes (ASEGS ++ VSEGS) (init_config (ASEGS ++ VSEGS) APC APH sp brk0 mbase rdraw lim INP) (sd HH t_nil E0a fs startup_shape).
  Proof.
    exact (asan_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd lim Hlim kb efn sigdef
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau
             IT0 IT0_ok (HS727A RZK) (plan727 RZK startup_plan) startup_shape KC0 BFUEL FUEL (startup_cert (kb_rseq kb)) VSEGS VSEGS_nx VSEGS_res
             HH HH_agree HH_nil B_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot :
    srealizes (ASEGS ++ VSEGS) (init_config (ASEGS ++ VSEGS) APC APH sp brk0 mbase rdraw lim INP) (H E0a fs).
  Proof. eapply srz_conseq; [exact asan_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
