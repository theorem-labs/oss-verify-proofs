(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages As_code_startx AsSmearCode SumsAsanSpecs SumsAsanClose.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext_stmt SEGS SC A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @emit_stmt SEGS SC A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext2_stmt SEGS SC A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Lemma sd_holes_only : forall HOLES D E fs T s,
  (forall h, HOLES h E fs = T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HT. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros H; try discriminate.
  - apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2. specialize (IHa H1 tr). specialize (IHb H2 tr). tauto.
  - apply andb_prop in H as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - rewrite HT. intros tr. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 APH sp rdraw argv envp uid hw.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 x.
  Proof.
    intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - eapply (init_x_sound_envscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_137b8c W_137b90 W_137b94
                ltac:(cbn [x_envscan x_envscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_137b8c) (fetch_lit _ _ _ _ eq_refl F_137b90) (fetch_lit _ _ _ _ eq_refl F_137b94)
                ltac:(repeat split; reflexivity)
                D_137b8c D_137b90 D_137b94
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF).
    - eapply (init_x_sound_pnscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_137c48 W_137c4c W_137c50 W_137c54 W_137c58
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_137c48) (fetch_lit _ _ _ _ eq_refl F_137c4c) (fetch_lit _ _ _ _ eq_refl F_137c50)
                (fetch_lit _ _ _ _ eq_refl F_137c54) (fetch_lit _ _ _ _ eq_refl F_137c58)
                ltac:(repeat split; reflexivity)
                D_137c48 D_137c4c D_137c50 D_137c54 D_137c58
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA).
    - apply (init_x_sound_layout ASEGS ASAN_H APH sp rdraw argv envp FS0 uid hw SINV).
    - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - (* [comment removed for export] *)
      intros args cs cs' E R FULL model T _ _ H. discriminate H.
    - (* [comment removed for export] *)
      exact (x_sound_smear ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 asan_wx asan_in_hull asan_hull_ok SF asan_smear_x asan_smear_fwa).
  Qed.
End XAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition level_certified (KC0 BFUEL FUEL : nat) (HSs HSt : nat -> option acs) : Prop :=
  forall h ch, HSs h = Some ch ->
    exists (rs : list (Z * nat)) (p : plan) (s : shape),
      check ASEGS (mk_itab_ranges ASEGS rs) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSt KC0 BFUEL FUEL None ch p = COk s
      /\ holes_only s = true.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abterm : bool.
  Variable vasz : VaSize.
  Variable ur : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz ur).

  (* [comment removed for export] *)
  Variable RANGES : list (Z * nat).          (* [comment removed for export] *)
  Variables HS1 HSC HSA : nat -> option acs.   (* [comment removed for export] *)
  Variable plan1 : plan.
  Variable shape1 : shape.
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges ASEGS RANGES).
  Hypothesis cert1 : check ASEGS IT ASAN_H NX0 LIM XN0 XE0 XB0 HS1 KC0 BFUEL FUEL None hinit plan1 = COk shape1.
  Hypothesis shape1_holes : holes_only shape1 = true.
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : LEVEL HS1 HSC.
  Hypothesis cert3 : LEVEL HSC HSA.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Hypothesis HOLESA_sound : holes_stmt ASEGS ASAN_H LIM HSA SINV argH HOLES fs.   (* [comment removed for export] *)

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 APH sp rdraw argv envp uid hw.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  (* [comment removed for export] *)
  Let SP := SINV0_pg APH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV (fun E M H => H).

  (* [comment removed for export] *)
  Lemma asan_check_sound : forall RS HS,
    holes_stmt ASEGS ASAN_H LIM HS SINV argH HOLES fs ->
    forall fuel bfuel p cs s,
      check ASEGS (mk_itab_ranges ASEGS RS) ASAN_H NX0 LIM XN0 XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok ASEGS ASAN_H LIM SINV argH fs E cs R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound ASEGS (mk_itab_ranges ASEGS RS) (itab_ranges_ok RS) ASAN_H NX0 LIM HS XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH E_SP0 AA SF SA
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_H NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA AS E_SP0)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_H NX0 LIM SINV argH fs asan_in_hull asan_hull_ok asan_shadow_ok AH SF asan_res_len asan_res_cover AS)
              (node_mmap1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (node_mmapin1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mprotect1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mmapgaps_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_H LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit)
              (node_join_sound ASEGS ASAN_H NX0 LIM SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (asan_node_fillfz_sound NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA fs)   (* [comment removed for export] *)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma level_sound : forall HSs HSt, LEVEL HSs HSt ->
    holes_stmt ASEGS ASAN_H LIM HSt SINV argH HOLES fs -> holes_stmt ASEGS ASAN_H LIM HSs SINV argH HOLES fs.
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. destruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (asan_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESC_sound : holes_stmt ASEGS ASAN_H LIM HSC SINV argH HOLES fs.
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : holes_stmt ASEGS ASAN_H LIM HS1 SINV argH HOLES fs.
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP) (sd HOLES t_nil E0a fs shape1).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz ur
               AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz ur
                  IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
    pose proof (asan_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 hinit shape1 cert1 _ _ _ _ HC) as R.
    replace (m_fs (model0 ASEGS sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz ur)) with fs in R by reflexivity.
    exact R.
  Qed.

  Theorem as_startup_T :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP) T.
  Proof.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
