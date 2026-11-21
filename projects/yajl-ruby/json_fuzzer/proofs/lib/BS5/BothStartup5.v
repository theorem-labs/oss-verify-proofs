(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up takes the launch's whole ProcInput (kernel build kb, execfn and the rest), mmap base, recorded kernel, valid_launch and entry_launch_ok_va, with the launch's SINV0 and argH0; the stage-1 plan, b_check_sound (renamed from a_check_sound), the hole sets and the stage-2 certificates are taken at the CONFIG_RSEQ value of kb (RZK), one s2_sound replacing s2_sound_0 and s2_sound_1, so JS1Both and HS1Both are no longer imported; the join-counter floor KC0 is read from CertS1BothD, where the split certificate files define it; b_startup reads the kernel, launch and channel-reader conjuncts of valid_input (the reader seeds cs_ok's co_rdr); u_e_sp0 takes the launch's ph and entry address; node_mmapin_sound and node_mprotect_sound are applied to the section hypotheses they use; the S1 certificate is passed with XN0 unfolded and the S2 certificates are stated as check runs (CertS2Asan/CertS2Both), so their types meet the soundness lemma's premise argument by argument; the section's INP is unfolded before init_cfg_eq rewrites the launch configuration; a/b_startup's argH0 takes the kernel build). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit AsanNodesIface AsanNodesMmCs AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit CertRefl.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import BothAcctImages AsanPlanImagesB SumsBothClose AsanNodesStartXBoth BothMaxVA PlanS1Both CertS1Both PlanS2Both HS2Both CertS2Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ACFG : SpuriousCfg := alloc_only_cfg false.
Lemma ACFG_alloc_off : family_may_fail ACFG FamAlloc = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0x818b0.

(* [comment removed for export] *)
Lemma HS_MAIN_pc : forall hs, HS_MAIN hs -> pc hs = A_MAIN.
Proof.
  intros hs H. unfold HS_MAIN in H.
  repeat (destruct H as [H|H]; [subst hs; reflexivity|]). subst hs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma XE0_emit_stmt : forall SC nx0 LIMIT SINV argH FS0, emit_stmt BSEGS SC BOTH5 nx0 LIMIT XE0 SINV argH FS0.
Proof. intros SC nx0 LIMIT SINV argH FS0 id args cs fd ps cs' E R FULL model T _ H. discriminate H. Qed.
Lemma XB0_ext2_stmt : forall SC nx0 LIMIT SINV argH FS0, ext2_stmt BSEGS SC BOTH5 nx0 LIMIT XB0 SINV argH FS0.
Proof. intros SC nx0 LIMIT SINV argH FS0 id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma xsniff_vacuous : forall SC nx0 LIMIT rz SINV argH FS0, x_stmt BSEGS SC BOTH5 nx0 LIMIT rz SINV argH FS0 XSniff.
Proof.
  intros SC nx0 LIMIT rz SINV argH FS0 args cs cs' E R FULL model T _ _ H.
  cbn [node_x] in H. discriminate H.
Qed.

(* [comment removed for export] *)
Section XAll.
  Variable SC : SpuriousCfg.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable ifs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables rdr sgd sgt : bool.
  Let INP := AsanInit.inp argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hkernel : in_kernel INP = recorded_kernel (in_kernel INP).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation argHx := (argH0 sp rdraw argv envp kb execfn).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 BPH apc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argHx E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Variable nx0 : nat.
  Hypothesis NX0_le : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma nx0_S : nx0_sp_ok nx0.
  Proof. unfold nx0_sp_ok, NX0 in *. lia. Qed.
  Lemma argH0_agree_nx0 : forall E E' (a : word), env_agree nx0 E E' -> argHx E a = argHx E' a.
  Proof. reflexivity. Qed.
  Lemma argH0_high_x : forall E a, argHx E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  Theorem both_node_x_sound_all : forall x, x_stmt BSEGS SC BOTH5 nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV argHx FS0 x.
  Proof.
    pose proof argH0_high_x as AH.
    pose proof argH0_agree_nx0 as AA.
    pose proof nx0_S as NS.
    intros [ | | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (both_node_x_sound_XIMemcpy SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (both_node_x_sound_XMemset SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (both_node_x_sound_XMemcpy SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (both_node_x_sound_XMemIsZero SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (both_node_x_sound_XPopFree SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply xsniff_vacuous.
    - apply (both_node_x_sound_XMaxVA SC nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree NS FS0).
  Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables rdr sgd sgt : bool.
  Let INP := AsanInit.inp argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  (* start-up is proved for the default kernel only (rseq on, 29 auxv pairs) *)
  Hypothesis Hkernel : in_kernel INP = recorded_kernel (in_kernel INP).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* LPS 08b1429: the standard channels have a reader (Run.valid_input), which seeds cs_ok's co_rdr *)
  Hypothesis Hrdr : rdr = true.

  #[local] Notation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* the run's CONFIG_RSEQ value, 0 or 1: the start-up certificates are taken at it *)
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall hs, HS_MAIN hs -> hs_argv_ok RZK hs = true -> forall E R FULL model,
      cs_ok BSEGS BOTH5 LIM SINV argH fs E hs R FULL model ->
      realizes_cfg ACFG BSEGS (cfg_of BSEGS R A_MAIN FULL model) T.

  (* [comment removed for export] *)
  Definition HOLES_T (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Lemma HOLES_T_agree : forall nx0 h E E' fs', env_agree nx0 E E' -> HOLES_T h E fs' = HOLES_T h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES_T_nil : forall h E fs', HOLES_T h E fs' [].
  Proof. intros. exact T_nil. Qed.

  Lemma AH : forall E a, argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. first [eapply argH0_high; eassumption | eapply (argH0_high AsanUbsan.M.init_pc); eassumption]. Qed.
  Lemma SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  (* [comment removed for export] *)
  Lemma ASP : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof.
    intros E M a [HE _] Ha.
    set (Ez := Env (ev E) (eb E0a)).
    assert (Hag : env_agree NX0 E0a Ez) by (split; [intros n Hn; symmetry; exact (HE n Hn) | reflexivity]).
    assert (HU : uE E e_sp0 = bv_unsigned sp).
    { change (uE E e_sp0) with (uE Ez e_sp0). unfold uE.
      rewrite <- (edenot_agree' NX0 E0a Ez e_sp0 Hag (e_sp0_vars NX0 ltac:(unfold NX0; lia))).
      fold (uE E0a e_sp0).
      (* LPS 727298f3: u_e_sp0 rests on the launch's stack image (ph and the entry address) *)
      first [ eapply (u_e_sp0 BPH AsanUbsan.M.init_pc); first [eassumption | exact Hlau]
            | eapply u_e_sp0; first [eassumption | exact Hlau] ]. }
    rewrite HU. unfold argH0 in Ha.
    apply orb_prop in Ha as [Ha|Ha]; apply andb_prop in Ha as [Ha _]; apply Z.leb_le in Ha; lia.
  Qed.

  (* [comment removed for export] *)
  Section AnyRoot.
  Variable nx0 : nat.
  Hypothesis NX0_le : (NX0 <= nx0)%nat.
  Let NS : nx0_sp_ok nx0 := nx0_S nx0 NX0_le.
  Lemma AA : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Proof. reflexivity. Qed.
  Lemma SA : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn.
    rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.
  #[local] Notation XN := (A_Hooks5.XN5 BSEGS BOTH5 nx0).

  Lemma b_check_sound : forall (IT : itab) (HS : nat -> option acs),
    itab_sound BSEGS IT ->
    holes_stmt BSEGS ACFG BOTH5 LIM HS SINV argH HOLES_T fs ->
    forall fuel bfuel p cs s,
      check BSEGS IT BOTH5 nx0 LIM RZK XN XE0 XB0 HS CertS1BothD.KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok BSEGS BOTH5 LIM SINV argH fs E cs R FULL model ->
        realizes_cfg ACFG BSEGS (cfg_of BSEGS R (pc cs) FULL model) (sd HOLES_T t_nil E (m_fs model) s).
  Proof.
    intros IT HS IT_ok HH fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound BSEGS ACFG IT IT_ok BOTH5 nx0 LIM RZK HS XN XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA NS
              HOLES_T (HOLES_T_agree nx0) HOLES_T_nil fs CertS1BothD.KC0
              (AsanNodesMmB.node_sys_sound BSEGS ACFG ACFG_alloc_off BOTH5 nx0 LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AA SF SA ASP NS)
              (AsanNodesMmB.node_brk2_sound BSEGS ACFG ACFG_alloc_off BOTH5 nx0 LIM SINV argH fs both_in_hull both_hull_ok both_shadow_ok AH SF ASP)
              (node_mmapG_sound BSEGS ACFG ACFG_alloc_off BOTH5 nx0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok AH AA SF SA ASP NS both_res_cover)
              (ltac:(eapply (node_mmapin_sound BSEGS ACFG);
                       first [exact both_in_hull | exact both_res_len | exact both_res_hull | exact both_hull_ok
                             | exact both_shadow_ok | exact AH | exact SF | exact ASP | exact AA | exact SA | exact NS
                             | exact both_res_cover | exact both_wx | exact ACFG_alloc_off]))
              (ltac:(eapply (node_mprotect_sound BSEGS ACFG);
                       first [exact both_in_hull | exact both_res_len | exact both_res_hull | exact both_hull_ok
                             | exact both_shadow_ok | exact AH | exact SF | exact ASP | exact AA | exact SA | exact NS
                             | exact both_res_cover | exact both_wx | exact ACFG_alloc_off]))
              (AsanNodesMmB.node_exit_sound BSEGS ACFG BOTH5 LIM SINV argH fs)
              (ltac:(intros x; eapply both_node_x_sound_all; first [eassumption | exact (fun E M H => H) | exact SF | exact SA]))
              (node_join_sound BSEGS ACFG BOTH5 nx0 LIM SINV argH fs)
              (XN5_ext_stmt BSEGS ACFG BOTH5 nx0 LIM SINV argH fs AA SA NS)
              (XE0_emit_stmt ACFG nx0 LIM SINV argH fs) (XB0_ext2_stmt ACFG nx0 LIM SINV argH fs)
              HH fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.
  End AnyRoot.

  (* [comment removed for export] *)
  Fixpoint all_holes (s : shape) : bool :=
    match s with SHole _ => true | SAlt2 a b | SCase _ _ a b => all_holes a && all_holes b | _ => false end.
  Lemma all_holes_T : forall E fs' s, all_holes s = true -> t_eq (sd HOLES_T t_nil E fs' s) T.
  Proof.
    intros E fs'. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros Hs; cbn in Hs; try discriminate; cbn [sd].
    - apply andb_prop in Hs as [Ha Hb]. intros tr. unfold t_alt2.
      split; [intros [H|H]; [apply (IHa Ha) | apply (IHb Hb)]; exact H | intros H; left; apply (IHa Ha); exact H].
    - apply andb_prop in Hs as [Ha Hb]. destruct (bv_unsigned (edenot E e) <=? mid); [apply IHa | apply IHb]; assumption.
    - unfold HOLES_T. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma holes_s2a : holes_stmt BSEGS ACFG BOTH5 LIM (HS_s2a RZK) SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_s2a_main _ _ _ Hh) as HM.
    unfold HOLES_T. rewrite (HS_MAIN_pc ch HM). exact (MAIN ch HM (HS_s2a_argv _ _ _ Hh) E R FULL model HC).
  Qed.
  Lemma holes_s2b : holes_stmt BSEGS ACFG BOTH5 LIM (HS_s2b RZK) SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_s2b_main _ _ _ Hh) as HM.
    unfold HOLES_T. rewrite (HS_MAIN_pc ch HM). exact (MAIN ch HM (HS_s2b_argv _ _ _ Hh) E R FULL model HC).
  Qed.

  (* S2 from each of the run's S1 hand-off states *)
  Lemma s2_sound : forall h ch, HS_s1 RZK h = Some ch -> forall E R FULL model,
    cs_ok BSEGS BOTH5 LIM SINV argH fs E ch R FULL model ->
    realizes_cfg ACFG BSEGS (cfg_of BSEGS R (pc ch) FULL model) T.
  Proof.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_s1_start _ _ _ Hh) as Est. rewrite <- Est in HC |- *.
    assert (Hh01 : h = 0%nat \/ h = 1%nat) by (destruct h as [|[|h]]; [left; reflexivity | right; reflexivity | discriminate Hh]).
    destruct Hh01 as [-> | ->].
    - (* the certificate at the run's value, stated as the check run b_check_sound's premise names *)
      pose proof (s2_cert_a (kb_rseq kb)) as C.
      pose proof (b_check_sound N2 N2_ge IT2 (HS_s2a RZK) IT2_ok holes_s2a FUEL BFUEL s2_plan_k (s2_start RZK 0) s2_shape
                    C E R FULL model HC) as RZ.
      eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
    - (* the certificate at the run's value, stated as the check run b_check_sound's premise names *)
      pose proof (s2_cert_b (kb_rseq kb)) as C.
      pose proof (b_check_sound N2 N2_ge IT2 (HS_s2b RZK) IT2_ok holes_s2b FUEL BFUEL s2_plan_k (s2_start RZK 1) s2_shape
                    C E R FULL model HC) as RZ.
      eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma holes_s1 : holes_stmt BSEGS ACFG BOTH5 LIM (HS_s1 RZK) SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC. unfold HOLES_T. exact (s2_sound h ch Hh E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  Theorem b_startup_open :
    realizes_cfg ACFG BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM INP) T.
  Proof.
    pose proof both_img_facts as IMG.
    assert (Hapc : Z.of_N AsanUbsan.M.init_pc = a_entry BOTH5) by reflexivity.
    unfold INP. erewrite init_cfg_eq by eassumption.
    match goal with |- realizes_cfg _ _ (cfg_of _ ?R0 _ ?F0 ?m0) _ =>
      assert (HC : cs_ok BSEGS BOTH5 LIM SINV argH (in_fs INP) E0a (init_acs_of RZK BOTH5) R0 F0 m0)
        by (eapply init_cs_ok; eassumption) end.
    change (in_fs _) with (fs_seed_tmp ifs tmp) in HC. rewrite <- Hfs in HC.
    pose proof (s1_cert (kb_rseq kb)) as C1. unfold CertS1BothD.XN0 in C1.
    pose proof (b_check_sound NX0 (le_n NX0) IT1 (HS_s1 RZK) IT1_ok holes_s1 FUEL BFUEL (s1_plan_k RZK) (init_acs_of RZK BOTH5) s1_shape
                  C1 E0a _ _ _ HC) as RZ.
    eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
  Qed.
End Startup.

(* [comment removed for export] *)
Theorem b_startup : forall (en : ExecEntry) (inp : ProcInput) (T : TSet),
  valid_entry (mkImage BSEGS AsanUbsan.M.init_pc BPH) en inp -> valid_input inp ->
  T [] ->
  (forall hs, HS_MAIN hs -> hs_argv_ok (rseq_z (kb_rseq (in_kernel inp))) hs = true -> forall E R FULL model,
      cs_ok BSEGS BOTH5 AsanInit.LIMIT
            (SINV0 BPH AsanUbsan.M.init_pc (en_sp en) (en_draw en) (en_brk en) (en_mmap_base en)
                   (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
                   (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp)
                   (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp)
                   (in_channel_reader inp) (in_sigpipe_default inp) (in_sigpipe_terminal inp))
            (argH0 (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_kernel inp) (in_execfn inp))
            (in_fs inp) E hs R FULL model ->
      realizes_cfg ACFG BSEGS (cfg_of BSEGS R A_MAIN FULL model) T) ->
  realizes_cfg ACFG BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                             AsanInit.LIMIT inp) T.
Proof.
  intros [sp brk0 mbase rdraw] [argv envp ifs stdin uid gid groups net nofile sigmask hw abrt va urnd tmp kb execfn rdr sgd sgt]
    T HE HI HT MAIN.
  cbn [en_sp en_brk en_mmap_base en_draw in_argv in_envp in_fs in_image_fs in_tmp in_uid in_gid in_hwcap
       in_groups in_net in_nofile in_sigmask in_urandom in_kernel in_execfn in_channel_reader
       in_sigpipe_default in_sigpipe_terminal in_stdin in_va_size in_abort_terminal] in *.
  pose proof HI as HI'.
  pose proof (valid_input_channel_reader _ HI') as Hrdr. cbn [in_channel_reader] in Hrdr.
  destruct HI as (Hva & Hve & _ & _ & _ & [Huid _] & _ & _ & _ & Habrt & Hva48 & _ & Hlaunch & _ & _ & Hk). cbn [in_argv in_envp in_uid in_gid in_abort_terminal in_va_size] in *.
  subst abrt va.
  destruct HE as (Hsp & Hbrk & Hmb & Hfit0 & Hlau).
  assert (Hfit : entry_stack_fits sp argv envp) by exact Hfit0.
  eapply (b_startup_open sp rdraw brk0 mbase argv envp (fs_seed_tmp ifs tmp));
    first [reflexivity | eassumption].
Qed.
