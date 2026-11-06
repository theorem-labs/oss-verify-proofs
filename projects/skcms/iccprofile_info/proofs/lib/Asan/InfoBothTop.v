(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ShapeAlg Spec ProofInfoPlan ProofInfoRows ProofInfoTop.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.   (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require BoLibFuzz.        (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  BothAsanPlanImages AsanInit AsanInitHW SpinAlgCfg AsanPlanSoundCfg MasterCfg AsanSpec AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth
  AsanMainCfgBoth AsanMainClosedCfgBoth AsanNodesNRCfg AsanNodesMmACfg AsanNodesMmBCfg AsanPlanSound2Cfg AsanNodesStartXInitCfg
  BothSumsAsanCloseCfg BothAsan_code_startx BothAsanNodesStartXAsan AsanNodesXLib DepotNodeBoth DepotNodeSoundBoth StartHooksBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoCfgBridge.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache.

Module ISpec := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec.
Module IPlan := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoPlan.
Module IRows := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoRows.
Module ITop := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoTop.

#[local] Abbreviation LIM := AsanInit.LIMIT.
#[local] Abbreviation TPC := AsanUbsan.M.init_pc.
#[local] Abbreviation SSEGS := Plain.M.loaded_segments.
#[local] Abbreviation SPC := Plain.M.init_pc.
#[local] Abbreviation SPH := Plain.M.phdrs.
#[local] Abbreviation FPS0 := (@eq PropExec.FPState PropExec.fx0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spec_bridge : forall argv fs tr, ISpec.spec argv fs tr <-> spec argv fs tr.
Proof. intros argv fs tr. exact (iff_refl _). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Top.
  (* [comment removed for export] *)
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLNB.abi_of INFO_BOTH).
  (* [comment removed for export] *)
  Variable XNs : nat -> list expr -> acs -> option acs.     (* [comment removed for export] *)
  Hypothesis XNs_ok : start_hooks_ok XNs.
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.                     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    APF.check ASEGS IT0 INFO_BOTH NX0 LIM XNs XE0 XB0 HS_asan KC0 BFUEL FUEL None (init_acs_hw INFO_BOTH) startup_plan
    = COk startup_shape.
  Hypothesis startup_all_holes : all_holes startup_shape = true.
  Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.

  Section Run.
    Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
      (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
      (urnd : InputStream).
    Hypothesis Hsp : valid_sp sp.
    Hypothesis Hbrk : valid_brk ASEGS brk0.
    Hypothesis Hva : valid_argv argv.
    Hypothesis Hve : valid_envp envp.
    Hypothesis Hfit : entry_stack_fits sp argv envp.
    Hypothesis Huid : valid_id uid.

    #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
    #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).

    Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
    Let AA := argH0_agree APH sp rdraw argv envp uid hw.
    Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
    Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
    Let ASP := argH0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.

    #[local] Ltac obl X :=
      exact (X ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok
               AH AA SF SA ASP asan_res_cover NX0_sp0).

    (* [comment removed for export] *)
    Lemma st_sys : forall y, APSC.sys_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 y.
    Proof. obl node_sys_cfg_OBL. Qed.
    Lemma st_brk2 : APSC.brk2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0.
    Proof. obl node_brk2_cfg_OBL. Qed.
    Lemma st_brku : APSC.brku_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0.
    Proof. obl node_brku_cfg_OBL. Qed.
    Lemma st_mmap2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 (node_mmap2 INFO_BOTH NX0 LIM).
    Proof. obl node_mmap2_cfg_OBL. Qed.
    Lemma st_mmapin : forall hole : bool, APSC.mm3_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 (node_mmapin INFO_BOTH LIM hole).
    Proof. obl node_mmapin_cfg_OBL. Qed.
    Lemma st_mprotect2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 (node_mprotect2 INFO_BOTH LIM).
    Proof. obl node_mprotect2_cfg_OBL. Qed.
    Lemma st_exit : APSC.exit_stmt_cfg ASEGS INFO_BOTH LIM SINV argH fs FPS0.
    Proof. obl node_exit_cfg_OBL. Qed.
    Lemma st_join : APSC.join_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0.
    Proof. exact (node_join_cfg_OBL ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0). Qed.

    (* [comment removed for export] *)
    Lemma st_x : forall x, APF.xnode_fo x = true -> APSC.x_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0 x.
    Proof.
      intros x Hx. destruct x; try discriminate Hx.
      - exact (asan_node_x_cfg_XIMemset NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XIMemcpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemset NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemcpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemIsZero NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - intros args. apply APSC.x_of_fp. intros FP _.
        eapply (@init_x_sound_envscan FP ASEGS INFO_BOTH APH asan_wx asan_in_hull W_8ea54 W_8ea58 W_8ea5c);
          first [ exact asan_Fe1 | exact asan_Fe2 | exact asan_Fe3 | exact D_8ea54 | exact D_8ea58 | exact D_8ea5c
                | (cbn [x_envscan x_envscan_k INFO_BOTH]; lia) | (repeat split; reflexivity) | eassumption
                | exact (fun E M (H : SINV E M) => H) | exact SF ].
      - intros args. apply APSC.x_of_fp. intros FP _.
        eapply (@init_x_sound_pnscan FP ASEGS INFO_BOTH APH asan_wx asan_in_hull asan_hull_ok W_8eb10 W_8eb14 W_8eb18 W_8eb1c W_8eb20);
          first [ exact asan_Fp0 | exact asan_Fp1 | exact asan_Fp2 | exact asan_Fp3 | exact asan_Fp4
                | exact D_8eb10 | exact D_8eb14 | exact D_8eb18 | exact D_8eb1c | exact D_8eb20
                | (cbn [x_pnscan x_pnscan_k INFO_BOTH]; lia) | (repeat split; reflexivity) | eassumption
                | exact (fun E M (H : SINV E M) => H) | exact SF | exact SA ].
      - intros args. apply APSC.x_of_fp. intros FP _. exact (@init_x_sound_layout FP ASEGS INFO_BOTH APH sp rdraw argv envp fs uid hw SINV).
      - exact (asan_node_x_cfg_XIStrncpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XPopFree NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
    Qed.

    (* [comment removed for export] *)
    Lemma st_run : APSC.run_block_stmt_cfg ASEGS IT0 INFO_BOTH NX0 LIM SINV argH fs KC0 FPS0.
    Proof.
      exact (APSC.run_block_stmt_cfg_all ASEGS IT0 IT0_ok INFO_BOTH NX0 LIM HS_asan XNs XE0 XB0
               asan_wx asan_in_hull asan_hull_ok SINV argH AH AA SF SA NX0_sp0 fs KC0 FPS0).
    Qed.
    Lemma st_xn : APSC.ext_stmt_cfg ASEGS INFO_BOTH NX0 LIM XNs SINV argH fs FPS0.
    Proof. exact (XNs_ok sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
    Lemma st_holes : APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM HS_asan SINV argH (HOLESM argv) fs FPS0.
    Proof.
      apply (main_holes_closed sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit LIB HS_asan HSA_noblob KCm BFUELm FUELm ITm ITm_ok
               TREE TREES FPS0).
      intros FP HFP. rewrite <- HFP. exact FPI_fx0.
    Qed.

    (* [comment removed for export] *)
    Theorem asan_startup_cfg :
      srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rdraw LIM
                                       (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
        (sd (HOLESM argv) t_nil (E0hw APH sp rdraw brk0 argv envp uid hw) fs startup_shape).
    Proof.
      rewrite (init_cfg_eq ASEGS INFO_BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd TPC eq_refl).
      pose proof (init_cs_ok_hw ASEGS INFO_BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd
                    asan_img_facts Hsp Hbrk Hva Hve Hfit Huid) as HC.
      exact (APSC.check_sound_cfg ASEGS IT0 INFO_BOTH NX0 LIM HS_asan XNs XE0 XB0 asan_in_hull asan_hull_ok asan_shadow_ok
               SINV argH AA SA NX0_sp0 (HOLESM argv) (HOLESM_agree argv) (HOLESM_nil argv)
               (fun h h' E fs' => eq_refl) (* [comment removed for export] *) fs KC0 FPS0
               st_run st_sys st_brk2 st_brku st_mmap2 st_mmapin st_mprotect2 st_exit st_x st_join st_xn
               (XE0_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0) (XB0_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPS0) st_holes
               FUEL BFUEL None startup_plan (init_acs_hw INFO_BOTH) startup_shape startup_cert PropExec.fx0 eq_refl
               _ _ _ _ t_nil HC I eq_refl).
    Qed.

    (* [comment removed for export] *)
    Theorem asan_realizes_spec_cfg :
      srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rdraw LIM
                                       (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
        (spec argv fs).
    Proof.
      eapply srz_cfg_conseq; [exact asan_startup_cfg|].
      apply sd_all_holes; [exact startup_all_holes | intros h; reflexivity].
    Qed.
  End Run.

  (* [comment removed for export] *)
  Definition asan_tgt_stmt : Prop :=
    forall en inp, valid_entry (mkImage ASEGS TPC APH) en inp -> valid_input inp ->
      match en with
      | mkEntry sp brk0 mbase rnd =>
          srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rnd target_alloc_limit inp) (spec (in_argv inp) (in_fs inp))
      end.

  Theorem info_both_tgt : asan_tgt_stmt.
  Proof.
    intros [sp brk0 mbase rnd] inp Hen Hv.
    pose proof (valid_input_va_size _ Hv) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as (Hsp & Hbrk & _ & Hfit).
    destruct Hv as (Hargv & Henvp & _ & _ & [Huid _] & _ & _ & _ & Hab & Hva & _).
    rewrite (init_config_inp _ _ _ _ _ _ _ _ inp Hab Hva).
    exact (asan_realizes_spec_cfg sp rnd brk0 mbase (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
             (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
             Hsp Hbrk Hargv Henvp Hfit Huid).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem info_both_scfg :
    strong_universal_error_free_T_scfg CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (info_both_tgt (mkEntry asp abrk amb arnd) inp Hent Hvalid) as HT. cbv beta iota in HT.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. destruct Hens as (Hrsp & Hrbrk & _ & Hrfit).
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    pose proof (ITop.info_ref_realizes rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs) as HS.
    unfold strong_equiv_error_free_scfg.
    exact (cfg_strong_equiv_ef SSEGS SPC SPH rsp rbrk rmb rrnd source_alloc_limit ASEGS TPC APH asp abrk amb arnd target_alloc_limit
             _ (spec (in_argv inp) (in_fs inp)) inp (info_realizes_src_real _ _ _ HS) HT
             (fun tr => spec_bridge (in_argv inp) (in_fs inp) tr)).
  Qed.

  (* [comment removed for export] *)
  Theorem info_both_budgets :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
               AsanUbsan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (info_both_tgt (mkEntry asp abrk amb arnd) inp Hent Hvalid) as HT. cbv beta iota in HT.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. destruct Hens as (Hrsp & Hrbrk & _ & Hrfit).
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    pose proof (ITop.info_ref_realizes_san rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs) as HS.
    unfold strong_equiv_error_free_budgets_scfg.
    exact (cfg_strong_equiv_ef SSEGS SPC SPH rsp rbrk rmb rrnd SanitizerBudgets.lim_source
             ASEGS TPC APH asp abrk amb arnd SanitizerBudgets.lim_target
             _ (spec (in_argv inp) (in_fs inp)) inp (info_realizes_src_real _ _ _ HS) HT
             (fun tr => spec_bridge (in_argv inp) (in_fs inp) tr)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma traces_entry_indep_cfg : forall inp, valid_input inp ->
    forall en1 en2,
      valid_entry (mkImage ASEGS TPC APH) en1 inp -> valid_entry (mkImage ASEGS TPC APH) en2 inp ->
      trace_equiv (bh_traces (run_scfg CFG (mkImage ASEGS TPC APH) target_alloc_limit en1 inp))
                  (bh_traces (run_scfg CFG (mkImage ASEGS TPC APH) target_alloc_limit en2 inp)).
  Proof.
    intros inp Hvalid [sp1 brk1 mb1 rnd1] [sp2 brk2 mb2 rnd2] He1 He2 tr.
    pose proof (info_both_tgt (mkEntry sp1 brk1 mb1 rnd1) inp He1 Hvalid) as R1. cbv beta iota in R1.
    pose proof (info_both_tgt (mkEntry sp2 brk2 mb2 rnd2) inp He2 Hvalid) as R2. cbv beta iota in R2.
    cbn.
    rewrite (srealizes_cfg_obs_iff ASEGS _ _ R1 tr).
    rewrite (srealizes_cfg_obs_iff ASEGS _ _ R2 tr).
    reflexivity.
  Qed.

  Lemma agree_s_self_cfg : forall inp, valid_input inp ->
    agree_s CFG (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) target_alloc_limit inp.
  Proof.
    intros inp Hinp.
    split; [| split; [| split]].
    - intros enX enY HX HY. exact (traces_entry_indep_cfg inp Hinp enX enY HX HY).
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem ca_iff_info_both : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _ en1 en2 H1 H2.
      exact (info_both_scfg en1 en2 (to_proc_input f) H1 H2 Hf).
    - intros _. exact Hacc.
  Qed.

  (* [comment removed for export] *)
  Theorem cb_iff_info_both : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _. split.
      + exact (IRows.agree_s_self SSEGS SPC SPH source_alloc_limit ITop.info_ref_realizes (to_proc_input f) Hf).
      + exact (agree_s_self_cfg (to_proc_input f) Hf).
    - intros _. exact Hacc.
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record both_certs : Type := BOTH_CERTS {
  ac_IT0 : itab;                                  (* [comment removed for export] *)
  ac_IT0_ok : itab_sound ASEGS ac_IT0;
  ac_HS : nat -> option acs;                      (* [comment removed for export] *)
  ac_plan : plan;                                 (* [comment removed for export] *)
  ac_shape : shape;                               (* [comment removed for export] *)
  ac_KC0 : nat; ac_BFUEL : nat; ac_FUEL : nat;
  ac_cert : APF.check ASEGS ac_IT0 INFO_BOTH NX0 LIM XNS XE0 XB0 ac_HS ac_KC0 ac_BFUEL ac_FUEL None (init_acs_hw INFO_BOTH) ac_plan
            = COk ac_shape;
  ac_all_holes : all_holes ac_shape = true;
  ac_noblob : forall h ch, ac_HS h = Some ch -> acs_noblob ch = true;
  ac_KCm : nat; ac_BFUELm : nat; ac_FUELm : nat;  (* [comment removed for export] *)
  ac_ITm : itab;                                  (* [comment removed for export] *)
  ac_ITm_ok : itab_sound ASEGS ac_ITm;
  ac_TREE : nat -> nat -> mtree;                  (* [comment removed for export] *)
  ac_TREES : forall h ch i, ac_HS h = Some ch -> (i < 6)%nat ->
               mtree_ok ac_KCm ac_BFUELm ac_FUELm ac_ITm 0 0 (HSA ac_HS h) (root_class i) (ac_TREE h i) = true
}.

Section Certs.
  Variable LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLNB.abi_of INFO_BOTH).   (* [comment removed for export] *)
  Variable C : both_certs.

  #[local] Ltac use X := exact (X LIB XNS XNS_ok (ac_IT0 C) (ac_IT0_ok C) (ac_HS C) (ac_plan C) (ac_shape C) (ac_KC0 C) (ac_BFUEL C)
                              (ac_FUEL C) (ac_cert C) (ac_all_holes C) (ac_noblob C) (ac_KCm C) (ac_BFUELm C) (ac_FUELm C)
                              (ac_ITm C) (ac_ITm_ok C) (ac_TREE C) (ac_TREES C)).

  (* [comment removed for export] *)
  Theorem info_both_tgt_C : asan_tgt_stmt.
  Proof. use info_both_tgt. Qed.

  (* [comment removed for export] *)
  Theorem info_both_top :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
               AsanUbsan.M.phdrs).
  Proof. use info_both_budgets. Qed.

  Theorem info_both_ca_iff_C : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) Cl.
  Proof. use ca_iff_info_both. Qed.

  Theorem info_both_cb_iff_C : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) Cl.
  Proof. use cb_iff_info_both. Qed.
End Certs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Closed.
  Variable C : both_certs.

  Theorem info_both_top_closed :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
               AsanUbsan.M.phdrs).
  Proof. exact (info_both_top BoLibFuzz.as_fuzz_closed C). Qed.

  Theorem info_both_ca_iff_closed : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) Cl.
  Proof. exact (info_both_ca_iff_C BoLibFuzz.as_fuzz_closed C). Qed.

  Theorem info_both_cb_iff_closed : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) Cl.
  Proof. exact (info_both_cb_iff_C BoLibFuzz.as_fuzz_closed C). Qed.
End Closed.
