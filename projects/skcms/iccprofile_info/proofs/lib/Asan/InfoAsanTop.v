(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the top checks the start-up and main certificates once per CONFIG_RSEQ layout and uses the launch's, reads the launch facts, channel reader and SIGPIPE disposition from valid_input, takes the kernel build at its recorded fields (pinned_kernel), and lifts the walks to the run's segments (RunSegsCfg); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ShapeAlg Spec ProofInfoPlan ProofInfoRows ProofInfoTop.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.   (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzz.        (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  AsanPlanImages AsanInit SpinAlgCfg AsanPlanSoundCfg MasterCfg AsanSpec AsanMainLib AsanMainDefs AsanMainTree
  AsanMainCfg AsanMainClosedCfg AsanNodesNRCfg AsanNodesMmACfg AsanNodesMmBCfg AsanPlanSound2Cfg AsanNodesStartXInitCfg
  SumsAsanCloseCfg Asan_code_startx AsanNodesStartXAsan AsanNodesXLib DepotNode DepotNodeSound StartHooks.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoCfgBridge.
Unset Nia Cache.  (* [comment removed for export] *)
Require OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.RunSegsCfg.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache.

Module ISpec := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec.
Module IPlan := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoPlan.
Module IRows := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoRows.
Module ITop := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoTop.

#[local] Abbreviation LIM := AsanInit.LIMIT.
#[local] Abbreviation TPC := Asan.M.init_pc.
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
  (* the ABI does not read the table's layout ([XLN.abi_of] is constant) *)
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLN.abi_of (INFO_ASAN_at 1)).
  (* LPS 727298f3: CONFIG_RSEQ is free in [Run.valid_input], so every certificate comes once per
     layout, [rsb] the launch's [kb_rseq] and [rseq_z rsb] the table's [a_rseq]: the start-up
     hooks, the start-up certificate and its hand-off states, and the main forest.  The launch
     reads them at its own bit (Section Run), so no premise fixes it. *)
  Variable XNs : Z -> nat -> list expr -> acs -> option acs.     (* [comment removed for export] *)
  Hypothesis XNs_ok : start_hooks_ok XNs.
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : bool -> nat -> option acs.                     (* [comment removed for export] *)
  Variable startup_plan : bool -> plan.
  Variable startup_shape : bool -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall rsb,
    APF.check ASEGS IT0 (INFO_ASAN_at (rseq_z rsb)) NX0 LIM (XNs (rseq_z rsb)) XE0 XB0 (HS_asan rsb) KC0 BFUEL FUEL None
      (init_acs_hw (INFO_ASAN_at (rseq_z rsb))) (startup_plan rsb)
    = COk (startup_shape rsb).
  Hypothesis startup_all_holes : forall rsb, all_holes (startup_shape rsb) = true.
  Hypothesis HSA_noblob : forall rsb h ch, HS_asan rsb h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : bool -> nat -> nat -> mtree.
  Hypothesis TREES : forall rsb h ch i, HS_asan rsb h = Some ch -> (i < 6)%nat ->
    mtree_ok (rseq_z rsb) KCm BFUELm FUELm ITm 0 0 (HSA (HS_asan rsb) h) (root_class i) (TREE rsb h i) = true.

  Section Run.
    Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
      (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
      (urnd : InputStream) (kern : KernelBuild) (execfn : list byte).
    Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
    Hypothesis Hsp : valid_sp sp.
    Hypothesis Hbrk : valid_brk ASEGS brk0.
    Hypothesis Hva : valid_argv argv.
    Hypothesis Hve : valid_envp envp.
    Hypothesis Hfit : entry_stack_fits sp argv envp.
    Hypothesis Huid : valid_id uid.
    Hypothesis Hmb : valid_mmap_base mbase.
    (** see [AsanInit.pinned_kernel]: [recorded_kernel]'s eight fields; CONFIG_RSEQ free *)
    Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
      = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))).
    Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
    Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
    (* LPS 727298f3: the launch's own CONFIG_RSEQ bit picks the table and the certificates. *)
    #[local] Notation rsb := (kb_rseq kern) (only parsing).
    #[local] Notation IA := (INFO_ASAN_at (rseq_z (kb_rseq kern))) (only parsing).

    #[local] Notation SINV := (SINV0 APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
    #[local] Notation argH := (argH0 sp rdraw argv envp kern execfn).

    (* [AsanInit.argH0_high] is discharged over the entry pc too, which it does not read. *)
    Let AH := argH0_high TPC sp rdraw argv envp kern execfn Hsp Hva.
    Let AA := argH0_agree sp rdraw argv envp kern execfn.
    Let SF := SINV0_frame APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default).
    Let SA := SINV0_agree APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default).
    Let ASP := argH0_sp APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn Hsp Hva Hve Hfit Hlau.

    #[local] Ltac obl X :=
      exact (X ASEGS IA NX0 LIM SINV argH fs FPS0 asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok
               AH AA SF SA ASP asan_res_cover NX0_sp0).

    (* [comment removed for export] *)
    Lemma st_sys : forall y, APSC.sys_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPS0 y.
    Proof. obl node_sys_cfg_OBL. Qed.
    Lemma st_brk2 : APSC.brk2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPS0.
    Proof. obl node_brk2_cfg_OBL. Qed.
    Lemma st_brku : APSC.brku_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPS0.
    Proof. obl node_brku_cfg_OBL. Qed.
    Lemma st_mmap2 : APSC.mm2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPS0 (node_mmap2 IA NX0 LIM).
    Proof. obl node_mmap2_cfg_OBL. Qed.
    Lemma st_mmapin : forall hole : bool, APSC.mm3_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPS0 (node_mmapin IA LIM hole).
    Proof. obl node_mmapin_cfg_OBL. Qed.
    Lemma st_mprotect2 : APSC.mm2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPS0 (node_mprotect2 IA LIM).
    Proof. obl node_mprotect2_cfg_OBL. Qed.
    Lemma st_exit : APSC.exit_stmt_cfg ASEGS IA LIM SINV argH fs FPS0.
    Proof. obl node_exit_cfg_OBL. Qed.
    Lemma st_join : APSC.join_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPS0.
    Proof. exact (node_join_cfg_OBL ASEGS IA NX0 LIM SINV argH fs FPS0). Qed.

    (* [comment removed for export] *)
    Lemma st_x : forall x, APF.xnode_fo x = true -> APSC.x_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPS0 x.
    Proof.
      intros x Hx. destruct x; try discriminate Hx.
      - exact (asan_node_x_cfg_XIMemset NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XIMemcpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemset NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemcpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XMemIsZero NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - intros args. apply APSC.x_of_fp. intros FP _.
        eapply (@init_x_sound_envscan FP ASEGS IA APH asan_wx asan_in_hull W_8dc24 W_8dc28 W_8dc2c);
          first [ exact asan_Fe1 | exact asan_Fe2 | exact asan_Fe3 | exact D_8dc24 | exact D_8dc28 | exact D_8dc2c
                | (cbn [x_envscan x_envscan_k INFO_ASAN_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption
                | exact (fun E M (H : SINV E M) => H) | exact SF ].
      - intros args. apply APSC.x_of_fp. intros FP _.
        eapply (@init_x_sound_pnscan FP ASEGS IA APH asan_wx asan_in_hull asan_hull_ok W_8dce0 W_8dce4 W_8dce8 W_8dcec W_8dcf0);
          first [ exact asan_Fp0 | exact asan_Fp1 | exact asan_Fp2 | exact asan_Fp3 | exact asan_Fp4
                | exact D_8dce0 | exact D_8dce4 | exact D_8dce8 | exact D_8dcec | exact D_8dcf0
                | (cbn [x_pnscan x_pnscan_k INFO_ASAN_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption
                | exact (fun E M (H : SINV E M) => H) | exact SF | exact SA ].
      - intros args. apply APSC.x_of_fp. intros FP _. exact (@init_x_sound_layout FP ASEGS IA sp rdraw argv envp fs kern execfn SINV).
      - exact (asan_node_x_cfg_XIStrncpy NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
      - exact (asan_node_x_cfg_XPopFree NX0 LIM SINV argH AH AA SF SA NX0_sp0 fs FPS0).
    Qed.

    (* [comment removed for export] *)
    Lemma st_run : APSC.run_block_stmt_cfg ASEGS IT0 IA NX0 LIM SINV argH fs KC0 FPS0.
    Proof.
      exact (APSC.run_block_stmt_cfg_all ASEGS IT0 IT0_ok IA NX0 LIM (HS_asan rsb) (XNs (rseq_z rsb)) XE0 XB0
               asan_wx asan_in_hull asan_hull_ok SINV argH AH AA SF SA NX0_sp0 fs KC0 FPS0).
    Qed.
    Lemma st_xn : APSC.ext_stmt_cfg ASEGS IA NX0 LIM (XNs (rseq_z rsb)) SINV argH fs FPS0.
    (* Hfit and Hlaunch are arguments of start_hooks_ok; both are this Section's own
       hypotheses, discharged from valid_entry/valid_input with kb_rseq FREE. *)
    Proof. exact (XNs_ok TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sigpipe_default Hsp Hva Hve Hfit Hkernel Hlaunch Hlau). Qed.
    Lemma st_holes : APSC.holes_stmt_cfg ASEGS IA LIM (HS_asan rsb) SINV argH (HOLESM argv) fs FPS0.
    Proof.
      first [ apply (main_holes_closed sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit LIB TPC mbase stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlaunch Hlau (HS_asan rsb) (HSA_noblob rsb) KCm BFUELm FUELm ITm ITm_ok (TREE rsb) (TREES rsb) FPS0)
            | apply (main_holes_closed sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit LIB TPC mbase stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlaunch Hmb Hlau (HS_asan rsb) (HSA_noblob rsb) KCm BFUELm FUELm ITm ITm_ok (TREE rsb) (TREES rsb) FPS0) ].
      intros FP HFP. rewrite <- HFP. exact FPI_fx0.
    Qed.

    (* [comment removed for export] *)
    Theorem asan_startup_cfg :
      srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rdraw LIM
                                       (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)))
        (sd (HOLESM argv) t_nil (E0hw sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) fs (startup_shape rsb)).
    Proof.
      rewrite (init_cfg_eq ASEGS IA APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn eq_refl).
      pose proof (init_cs_ok_hw ASEGS IA APH TPC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn
                    asan_img_facts eq_refl Hsp Hbrk Hmb Hva Hve Hfit Huid Hkernel Hlaunch Hlau eq_refl) as HC.
      exact (APSC.check_sound_cfg ASEGS IT0 IA NX0 LIM (HS_asan rsb) (XNs (rseq_z rsb)) XE0 XB0 asan_in_hull asan_hull_ok asan_shadow_ok
               SINV argH AA SA NX0_sp0 (HOLESM argv) (HOLESM_agree argv) (HOLESM_nil argv)
               (fun h h' E fs' => eq_refl) (* [comment removed for export] *) fs KC0 FPS0
               st_run st_sys st_brk2 st_brku st_mmap2 st_mmapin st_mprotect2 st_exit st_x st_join st_xn
               (XE0_cfg ASEGS IA NX0 LIM SINV argH fs FPS0) (XB0_cfg ASEGS IA NX0 LIM SINV argH fs FPS0) st_holes
               FUEL BFUEL None (startup_plan rsb) (init_acs_hw IA) (startup_shape rsb) (startup_cert rsb) PropExec.fx0 eq_refl
               _ _ _ _ t_nil HC I eq_refl).
    Qed.

    (* [comment removed for export] *)
    Theorem asan_realizes_spec_cfg :
      srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rdraw LIM
                                       (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)))
        (spec argv fs).
    Proof.
      eapply srz_cfg_conseq; [exact asan_startup_cfg|].
      apply sd_all_holes; [exact (startup_all_holes rsb) | intros h; reflexivity].
    Qed.
  End Run.

  (* [comment removed for export] *)
  Definition asan_tgt_stmt : Prop :=
    forall en inp, valid_entry (mkImage ASEGS TPC APH) en inp -> valid_input inp ->
      match en with
      | mkEntry sp brk0 mbase rnd =>
          srealizes_cfg ASEGS (init_config ASEGS TPC APH sp brk0 mbase rnd target_alloc_limit inp) (spec (in_argv inp) (in_fs inp))
      end.

  Theorem info_asan_tgt : asan_tgt_stmt.
  Proof.
    intros [sp brk0 mbase rnd] inp Hen Hv.
    pose proof (valid_input_va_size _ Hv) as Hsv48.
    pose proof (pinned_of_recorded (in_kernel inp) (valid_input_recorded_kernel inp Hv)) as Hkernel.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    (* [Run.valid_input] has SIXTEEN conjuncts at LPS 727298f3; the last is
       [in_kernel inp = recorded_kernel (in_kernel inp)], which [Hkernel] above already used.
       It leaves [in_sigpipe_default] free: [init_config_inp] hands the input's own value to
       [AsanInit]'s Section. *)
    destruct Hv as (Hargv & Henvp & _ & _ & _ & [Huid _] & _ & _ & _ & Hab & Hva & _ & Hlaunch & Hcr & Hst & _).
    rewrite (init_config_inp _ _ _ _ _ _ _ _ inp Hab Hva Hcr Hst).
    eapply (asan_realizes_spec_cfg sp rnd brk0 mbase (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
             (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
             (in_kernel inp) (in_execfn inp) (sigpipe_default := in_sigpipe_default inp)); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem info_asan_scfg :
    strong_universal_error_free_T_scfg CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (info_asan_tgt (mkEntry asp abrk amb arnd) inp Hent Hvalid) as HT. cbv beta iota in HT.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. destruct Hens as (Hrsp & Hrbrk & _ & Hrfit & Hrlau).
    (* LPS 727298f3: [realizes_spec_stmt] takes the launch, the channel reader and the entry's
       launch fact, as [Info/ProofInfoPlan.v]'s [info_ubsan_scfg] discharges them. *)
    pose proof (valid_input_launch _ Hvalid) as Hvl. pose proof (valid_input_channel_reader _ Hvalid) as Hcr.
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    pose proof (ITop.info_ref_realizes rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hvl Hcr Hrlau) as HS.
    unfold strong_equiv_error_free_scfg.
    exact (cfg_strong_equiv_ef SSEGS SPC SPH rsp rbrk rmb rrnd source_alloc_limit ASEGS TPC APH asp abrk amb arnd target_alloc_limit
             _ (spec (in_argv inp) (in_fs inp)) inp (info_realizes_src_real _ _ _ (RunSegsCfg.info_realizes_run_init SSEGS SPC SPH inp rsp rbrk rmb rrnd _ _ ltac:(reflexivity) HS))
             (RunSegsCfg.srealizes_cfg_run_init ASEGS TPC APH inp asp abrk amb arnd _ _ ltac:(reflexivity) HT)
             (fun tr => spec_bridge (in_argv inp) (in_fs inp) tr)).
  Qed.

  (* [comment removed for export] *)
  Theorem info_asan_budgets :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc
               Asan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (info_asan_tgt (mkEntry asp abrk amb arnd) inp Hent Hvalid) as HT. cbv beta iota in HT.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. destruct Hens as (Hrsp & Hrbrk & _ & Hrfit & Hrlau).
    pose proof (valid_input_launch _ Hvalid) as Hvl. pose proof (valid_input_channel_reader _ Hvalid) as Hcr.
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    pose proof (ITop.info_ref_realizes_san rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hvl Hcr Hrlau) as HS.
    unfold strong_equiv_error_free_budgets_scfg.
    exact (cfg_strong_equiv_ef SSEGS SPC SPH rsp rbrk rmb rrnd SanitizerBudgets.lim_source
             ASEGS TPC APH asp abrk amb arnd SanitizerBudgets.lim_target
             _ (spec (in_argv inp) (in_fs inp)) inp (info_realizes_src_real _ _ _ (RunSegsCfg.info_realizes_run_init SSEGS SPC SPH inp rsp rbrk rmb rrnd _ _ ltac:(reflexivity) HS))
             (RunSegsCfg.srealizes_cfg_run_init ASEGS TPC APH inp asp abrk amb arnd _ _ ltac:(reflexivity) HT)
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
    pose proof (info_asan_tgt (mkEntry sp1 brk1 mb1 rnd1) inp He1 Hvalid) as R1. cbv beta iota in R1.
    pose proof (info_asan_tgt (mkEntry sp2 brk2 mb2 rnd2) inp He2 Hvalid) as R2. cbv beta iota in R2.
    (* LPS 727298f3: the run is over [run_segments], as in [info_asan_scfg] above. *)
    pose proof (RunSegsCfg.srealizes_cfg_run_init ASEGS TPC APH inp sp1 brk1 mb1 rnd1 _ _ ltac:(reflexivity) R1) as R1'.
    pose proof (RunSegsCfg.srealizes_cfg_run_init ASEGS TPC APH inp sp2 brk2 mb2 rnd2 _ _ ltac:(reflexivity) R2) as R2'.
    first [ (cbn; rewrite (srealizes_cfg_obs_iff _ _ _ R1' tr), (srealizes_cfg_obs_iff _ _ _ R2' tr); reflexivity)
          | (unfold run_scfg; rewrite (srealizes_cfg_obs_iff _ _ _ R1' tr), (srealizes_cfg_obs_iff _ _ _ R2' tr); reflexivity) ].
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
  Theorem ca_iff_info_asan : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _ en1 en2 H1 H2.
      exact (info_asan_scfg en1 en2 (to_proc_input f) H1 H2 Hf).
    - intros _. exact Hacc.
  Qed.

  (* [comment removed for export] *)
  Theorem cb_iff_info_asan : forall (C : Image),
    (forall inp en, valid_input inp -> valid_entry C en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) C.
  Proof.
    intros C MX f Hf en Hen.
    pose proof (MX (to_proc_input f) en Hf Hen) as Hacc.
    split; [split | left; exact Hacc].
    - intros _. split.
      + exact (IRows.agree_s_self SSEGS SPC SPH source_alloc_limit eq_refl ITop.info_ref_realizes (to_proc_input f) Hf).
      + exact (agree_s_self_cfg (to_proc_input f) Hf).
    - intros _. exact Hacc.
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record asan_certs : Type := ASAN_CERTS {
  ac_IT0 : itab;                                  (* [comment removed for export] *)
  ac_IT0_ok : itab_sound ASEGS ac_IT0;
  ac_HS : bool -> nat -> option acs;                      (* [comment removed for export] *)
  ac_plan : bool -> plan;                                 (* [comment removed for export] *)
  ac_shape : bool -> shape;                               (* [comment removed for export] *)
  ac_KC0 : nat; ac_BFUEL : nat; ac_FUEL : nat;
  ac_cert : forall rsb, APF.check ASEGS ac_IT0 (INFO_ASAN_at (rseq_z rsb)) NX0 LIM (XNS (rseq_z rsb)) XE0 XB0 (ac_HS rsb) ac_KC0 ac_BFUEL ac_FUEL None
              (init_acs_hw (INFO_ASAN_at (rseq_z rsb))) (ac_plan rsb)
            = COk (ac_shape rsb);
  ac_all_holes : forall rsb, all_holes (ac_shape rsb) = true;
  ac_noblob : forall rsb h ch, ac_HS rsb h = Some ch -> acs_noblob ch = true;
  ac_KCm : nat; ac_BFUELm : nat; ac_FUELm : nat;  (* [comment removed for export] *)
  ac_ITm : itab;                                  (* [comment removed for export] *)
  ac_ITm_ok : itab_sound ASEGS ac_ITm;
  ac_TREE : bool -> nat -> nat -> mtree;                  (* [comment removed for export] *)
  ac_TREES : forall rsb h ch i, ac_HS rsb h = Some ch -> (i < 6)%nat ->
               mtree_ok (rseq_z rsb) ac_KCm ac_BFUELm ac_FUELm ac_ITm 0 0 (HSA (ac_HS rsb) h) (root_class i) (ac_TREE rsb h i) = true
}.

Section Certs.
  Variable LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLN.abi_of (INFO_ASAN_at 1)).   (* [comment removed for export] *)
  Variable C : asan_certs.

  #[local] Ltac use X := exact (X LIB XNS XNS_ok (ac_IT0 C) (ac_IT0_ok C) (ac_HS C) (ac_plan C) (ac_shape C) (ac_KC0 C) (ac_BFUEL C)
                              (ac_FUEL C) (ac_cert C) (ac_all_holes C) (ac_noblob C) (ac_KCm C) (ac_BFUELm C) (ac_FUELm C)
                              (ac_ITm C) (ac_ITm_ok C) (ac_TREE C) (ac_TREES C)).

  (* [comment removed for export] *)
  Theorem info_asan_tgt_C : asan_tgt_stmt.
  Proof. use info_asan_tgt. Qed.

  (* [comment removed for export] *)
  Theorem info_asan_top :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc
               Asan.M.phdrs).
  Proof. use info_asan_budgets. Qed.

  Theorem info_asan_ca_iff_C : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) Cl.
  Proof. use ca_iff_info_asan. Qed.

  Theorem info_asan_cb_iff_C : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) Cl.
  Proof. use cb_iff_info_asan. Qed.
End Certs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Closed.
  Variable C : asan_certs.

  Theorem info_asan_top_closed :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc
               Asan.M.phdrs).
  Proof. exact (info_asan_top AsLibFuzz.as_fuzz_closed C). Qed.

  Theorem info_asan_ca_iff_closed : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage ASEGS TPC APH) Cl.
  Proof. exact (info_asan_ca_iff_C AsLibFuzz.as_fuzz_closed C). Qed.

  Theorem info_asan_cb_iff_closed : forall (Cl : Image),
    (forall inp en, valid_input inp -> valid_entry Cl en inp ->
       must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en inp) ->
    classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                  (mkImage ASEGS TPC APH) (mkImage ASEGS TPC APH) Cl.
  Proof. exact (info_asan_cb_iff_C AsLibFuzz.as_fuzz_closed C). Qed.
End Closed.
