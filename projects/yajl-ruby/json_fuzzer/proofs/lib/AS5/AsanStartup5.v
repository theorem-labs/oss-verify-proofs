(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit
  AsanNodesIface AsanNodesMmCs AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit CertRefl.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import
  AsanAcctImages AsanPlanImages5 SumsAsanClose AsanNodesStartXAsan AsanMaxVA
  A_Hooks5 PlanS1Asan JS1Asan HS1Asan CertS1Asan PlanS2Asan HS2Asan CertS2Asan.
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
Definition A_MAIN : Z := 0x81aa4.

(* [comment removed for export] *)
Lemma HS_MAIN_pc : forall hs, HS_MAIN hs -> pc hs = A_MAIN.
Proof. intros hs [-> | [-> | [-> | ->]]]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma XE0_emit_stmt : forall SC nx0 LIMIT SINV argH FS0, emit_stmt ASEGS SC ASAN5 nx0 LIMIT XE0 SINV argH FS0.
Proof. intros SC nx0 LIMIT SINV argH FS0 id args cs fd ps cs' E R FULL model T _ H. discriminate H. Qed.
Lemma XB0_ext2_stmt : forall SC nx0 LIMIT SINV argH FS0, ext2_stmt ASEGS SC ASAN5 nx0 LIMIT XB0 SINV argH FS0.
Proof. intros SC nx0 LIMIT SINV argH FS0 id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma xsniff_vacuous : forall SC nx0 LIMIT SINV argH FS0, x_stmt ASEGS SC ASAN5 nx0 LIMIT SINV argH FS0 XSniff.
Proof.
  intros SC nx0 LIMIT SINV argH FS0 args cs cs' E R FULL model T _ _ H.
  cbn [node_x] in H. discriminate H.
Qed.

(* [comment removed for export] *)
Section XAll.
  Variable SC : SpuriousCfg.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis NX0_le : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma nx0_S : nx0_sp_ok nx0.
  Proof. unfold nx0_sp_ok, NX0 in *. lia. Qed.
  Lemma argH0_agree_nx0 : forall E E' (a : word), env_agree nx0 E E' -> argH0 APH sp rdraw argv envp uid hw E a = argH0 APH sp rdraw argv envp uid hw E' a.
  Proof. intros E E' a Hag. apply (argH0_agree APH sp rdraw argv envp uid hw). eapply env_agree_le; [exact Hag | exact NX0_le]. Qed.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS SC ASAN5 nx0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 x.
  Proof.
    pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva) as AH.
    pose proof argH0_agree_nx0 as AA.
    pose proof nx0_S as NS.
    intros [ | | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (asan_node_x_sound_XIMemcpy SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (asan_node_x_sound_XMemset SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (asan_node_x_sound_XMemcpy SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (asan_node_x_sound_XMemIsZero SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (node_x_sound_XEnvScan_asan_gen SC sp rdraw brk0 hw argv envp FS0 Hsp Hva Hve uid Hfit SINV SINV_SINV0 SINV_frame nx0 NX0_le).
    - apply (node_x_sound_XPnScan_asan_gen SC sp rdraw brk0 hw argv envp FS0 Hsp Hva Hve uid Hfit SINV SINV_SINV0 SINV_frame nx0 NX0_le SINV_agree).
    - apply (node_x_sound_XLayout_asan_gen SC sp rdraw hw argv envp FS0 uid SINV nx0).
    - apply (asan_node_x_sound_XIStrncpy SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply (asan_node_x_sound_XPopFree SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
    - apply xsniff_vacuous.
    - apply (asan_node_x_sound_XMaxVA SC nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree NS FS0).
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
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall hs, HS_MAIN hs -> forall E R FULL model,
      cs_ok ASEGS ASAN5 LIM SINV argH fs E hs R FULL model ->
      realizes_cfg ACFG ASEGS (cfg_of ASEGS R A_MAIN FULL model) T.

  (* [comment removed for export] *)
  Definition HOLES_T (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Lemma HOLES_T_agree : forall nx0 h E E' fs', env_agree nx0 E E' -> HOLES_T h E fs' = HOLES_T h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES_T_nil : forall h E fs', HOLES_T h E fs' [].
  Proof. intros. exact T_nil. Qed.

  (* [comment removed for export] *)
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Lemma ASP : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof.
    intros E M a [HE _] Ha.
    set (Ez := Env (ev E) (eb E0a)).
    assert (Hag : env_agree NX0 E0a Ez) by (split; [intros n Hn; symmetry; exact (HE n Hn) | reflexivity]).
    assert (HU : uE E e_sp0 = bv_unsigned sp).
    { change (uE E e_sp0) with (uE Ez e_sp0). unfold uE.
      rewrite <- (edenot_agree' NX0 E0a Ez e_sp0 Hag (e_sp0_vars NX0 ltac:(unfold NX0; lia))).
      exact (u_e_sp0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit). }
    rewrite HU. unfold argH0 in Ha. pose proof (AsanInit.len_av APH sp rdraw argv envp uid hw Hva).
    apply orb_prop in Ha as [Ha|Ha]; apply andb_prop in Ha as [Ha _]; apply Z.leb_le in Ha; lia.
  Qed.

  (* [comment removed for export] *)
  Section AnyRoot.
  Variable nx0 : nat.
  Hypothesis NX0_le : (NX0 <= nx0)%nat.
  Let NS : nx0_sp_ok nx0 := nx0_S nx0 NX0_le.
  Let AA := argH0_agree_nx0 sp rdraw hw argv envp uid nx0 NX0_le.
  Lemma SA : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag. apply (SINV0_agree APH sp rdraw brk0 argv envp uid hw). eapply env_agree_le; [exact Hag | exact NX0_le]. Qed.
  #[local] Notation XN := (A_Hooks5.XN5 ASEGS ASAN5 nx0).

  Lemma a_check_sound : forall (IT : itab) (HS : nat -> option acs),
    itab_sound ASEGS IT ->
    holes_stmt ASEGS ACFG ASAN5 LIM HS SINV argH HOLES_T fs ->
    forall fuel bfuel p cs s,
      check ASEGS IT ASAN5 nx0 LIM XN XE0 XB0 HS CertS1Asan.KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok ASEGS ASAN5 LIM SINV argH fs E cs R FULL model ->
        realizes_cfg ACFG ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES_T t_nil E (m_fs model) s).
  Proof.
    intros IT HS IT_ok HH fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound ASEGS ACFG IT IT_ok ASAN5 nx0 LIM HS XN XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA NS
              HOLES_T (HOLES_T_agree nx0) HOLES_T_nil fs CertS1Asan.KC0
              (AsanNodesMmB.node_sys_sound ASEGS ACFG ASAN5 nx0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA ASP NS)
              (AsanNodesMmB.node_brk2_sound ASEGS ACFG ACFG_alloc_off ASAN5 nx0 LIM SINV argH fs asan_in_hull asan_hull_ok asan_shadow_ok AH SF ASP)
              (node_mmapG_sound ASEGS ACFG ACFG_alloc_off ASAN5 nx0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA ASP NS asan_res_cover)
              (node_mmapin_sound ASEGS ACFG ACFG_alloc_off ASAN5 nx0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH SF ASP)
              (node_mprotect_sound ASEGS ACFG ACFG_alloc_off ASAN5 nx0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH SF ASP)
              (AsanNodesMmB.node_exit_sound ASEGS ACFG ASAN5 LIM SINV argH fs)
              (asan_node_x_sound_all ACFG sp rdraw brk0 hw argv envp fs Hsp Hva Hve uid Hfit SINV (fun E M H => H) SF nx0 NX0_le SA)
              (node_join_sound ASEGS ACFG ASAN5 nx0 LIM SINV argH fs)
              (XN5_ext_stmt ASEGS ACFG ASAN5 nx0 LIM SINV argH fs AA SA NS)
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
  Lemma holes_s2a : holes_stmt ASEGS ACFG ASAN5 LIM HS_s2a SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Ech : ch = HS_s2_00 \/ ch = HS_s2_01) by (destruct h as [|[|h]]; [injection Hh as <-; left; reflexivity | injection Hh as <-; right; reflexivity | discriminate Hh]).
    assert (HM : HS_MAIN ch) by (unfold HS_MAIN; tauto).
    unfold HOLES_T. rewrite (HS_MAIN_pc ch HM). exact (MAIN ch HM E R FULL model HC).
  Qed.
  Lemma holes_s2b : holes_stmt ASEGS ACFG ASAN5 LIM HS_s2b SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Ech : ch = HS_s2_10 \/ ch = HS_s2_11) by (destruct h as [|[|h]]; [injection Hh as <-; left; reflexivity | injection Hh as <-; right; reflexivity | discriminate Hh]).
    assert (HM : HS_MAIN ch) by (unfold HS_MAIN; tauto).
    unfold HOLES_T. rewrite (HS_MAIN_pc ch HM). exact (MAIN ch HM E R FULL model HC).
  Qed.

  Lemma s2_sound_0 : forall E R FULL model,
    cs_ok ASEGS ASAN5 LIM SINV argH fs E HS_s1_0 R FULL model ->
    realizes_cfg ACFG ASEGS (cfg_of ASEGS R (pc HS_s1_0) FULL model) T.
  Proof.
    intros E R FULL model HC.
    pose proof (a_check_sound N2 N2_ge IT2 HS_s2a IT2_ok holes_s2a FUEL BFUEL s2_plan HS_s1_0 s2_shape s2_cert_0 E R FULL model HC) as RZ.
    eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
  Qed.
  Lemma s2_sound_1 : forall E R FULL model,
    cs_ok ASEGS ASAN5 LIM SINV argH fs E HS_s1_1 R FULL model ->
    realizes_cfg ACFG ASEGS (cfg_of ASEGS R (pc HS_s1_1) FULL model) T.
  Proof.
    intros E R FULL model HC.
    pose proof (a_check_sound N2 N2_ge IT2 HS_s2b IT2_ok holes_s2b FUEL BFUEL s2_plan HS_s1_1 s2_shape s2_cert_1 E R FULL model HC) as RZ.
    eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma holes_s1 : holes_stmt ASEGS ACFG ASAN5 LIM HS_s1 SINV argH HOLES_T fs.
  Proof.
    intros h ch Hh E R FULL model HC. unfold HOLES_T.
    destruct h as [|[|h]]; [injection Hh as <- | injection Hh as <- | discriminate Hh].
    - exact (s2_sound_0 E R FULL model HC).
    - exact (s2_sound_1 E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  Theorem a_startup_open :
    realizes_cfg ACFG ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                               (AsanInit.inp argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.
  Proof.
    rewrite (init_cfg_eq ASEGS ASAN5 APH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp Asan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN5 APH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask urnd tmp asan_img_facts Hsp Hbrk Hmb Hva Hve Hfit Huid) as HC.
    change (in_fs _) with (fs_seed_tmp ifs tmp) in HC. rewrite <- Hfs in HC.
    pose proof (a_check_sound NX0 (le_n NX0) IT1 HS_s1 IT1_ok holes_s1 FUEL BFUEL (s1_plan js_2 js_11) (init_acs_of ASAN5) s1_shape s1_cert E0a _ _ _ HC) as RZ.
    eapply rz_conseq_cfg; [exact RZ|]. apply all_holes_T. reflexivity.
  Qed.
End Startup.

(* [comment removed for export] *)
Theorem a_startup : forall (en : ExecEntry) (inp : ProcInput) (T : TSet),
  valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input inp -> T [] ->
  (forall hs, HS_MAIN hs -> forall E R FULL model,
      cs_ok ASEGS ASAN5 AsanInit.LIMIT
            (SINV0 APH (en_sp en) (en_draw en) (en_brk en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
            (argH0 APH (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
            (in_fs inp) E hs R FULL model ->
      realizes_cfg ACFG ASEGS (cfg_of ASEGS R A_MAIN FULL model) T) ->
  realizes_cfg ACFG ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                             AsanInit.LIMIT inp) T.
Proof.
  intros [sp brk0 mbase rdraw] [argv envp ifs stdin uid gid groups net nofile sigmask hw abrt va urnd tmp] T HE HI HT MAIN.
  cbn [en_sp en_brk en_mmap_base en_draw in_argv in_envp in_fs in_image_fs in_tmp in_uid in_hwcap] in *.
  pose proof HI as HI'.
  destruct HE as (Hsp & Hbrk & Hmb & Hfit0).
  destruct HI as (Hva & Hve & _ & _ & [Huid _] & _ & _ & _ & Habrt & Hva48 & _). cbn [in_argv in_envp in_uid in_gid in_abort_terminal in_va_size] in *.
  subst abrt va.
  assert (Hfit : entry_stack_fits sp argv envp) by exact Hfit0.
  exact (a_startup_open sp rdraw brk0 mbase argv envp (fs_seed_tmp ifs tmp) stdin ifs urnd tmp eq_refl uid gid hw groups net nofile sigmask Hsp Hbrk Hmb Hva Hve Hfit Huid T HT MAIN).
Qed.
