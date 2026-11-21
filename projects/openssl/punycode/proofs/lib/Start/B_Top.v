(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up is over the run's whole ProcInput with the mmap base, the image entry and the launch's premises; img_facts gains if_resx; the Section variables AsanInit's lemmas close over and never read are supplied from this image; the chain starts from init_acs_of at the run's CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit AsanNodesIface AsanNodesLibE AsanNodesMmA AsanNodesMmB.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_XAll B_HooksDefs B_Hooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation BPC0 := AsanUbsan.M.init_pc.
#[local] Notation LIM := AsanInit.LIMIT.

Lemma B_img_facts : img_facts B_SEGS B_T B_PH.
Proof.
  constructor.
  - exact B_t_if_ph.
  - exact B_t_if_hull.
  - exact B_t_if_top.
  - exact B_t_res_hull.
  - exact B_t_if_sizes.
  - exact B_t_if_rw.
  - exact B_t_shadow_ok.
  - (* [if_resx]: the table states [n_resx := 2; p_resx := 20] (Start/B_Atable.v) *)
    split; apply Nat.leb_le; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section B_Check.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable fs : Fs.Fs.
  Hypothesis IMG : img_facts B_SEGS B_T B_PH.
  Hypothesis Hapc : Z.of_N BPC0 = a_entry B_T.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk B_SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation ISP := (bv_unsigned sp).
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  (* as A_Top.v: the Section variables [argH0_high]'s statement never reads *)
  Proof. intros E a H. eapply argH0_high; try eassumption. all: first [exact B_SEGS | exact B_T | exact B_PH | exact BPC0 | exact LIM]. Qed.
  Let AA := argH0_agree sp rdraw inp.

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis S0 : forall E M, SINV E M -> SINV0 B_PH BPC0 sp rdraw brk0 mbase inp E M.
  Hypothesis SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Let SP : forall E M, SINV E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M H. pose proof (S0 E M H) as H0. eapply SINV0_pgsp; eassumption. Qed.

  (* [comment removed for export] *)
  Variable XN : nat -> list expr -> acs -> option acs.
  Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
  Variable XB : nat -> list expr -> acs -> option (acs * acs).
  Hypothesis XN_sound : ext_stmt B_SEGS B_T NX0 LIM XN SINV argH ISP fs.
  Hypothesis XE_sound : emit_stmt B_SEGS B_T NX0 LIM XE SINV argH ISP fs.
  Hypothesis XB_sound : ext2_stmt B_SEGS B_T NX0 LIM XB SINV argH ISP fs.
  (* [comment removed for export] *)
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound B_SEGS IT.
  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt B_SEGS B_T LIM HS SINV argH ISP HOLES fs.
  Variable KC : nat.

  Let X_sound : forall x, x_stmt B_SEGS B_T NX0 AsanInit.LIMIT SINV argH ISP fs x.
  Proof. intros x. eapply B_x_all_sinv; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma B_ob_sys : forall y, sys_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs y.
  Proof.
    apply (AsanNodesMmB.node_sys_sound B_SEGS B_T NX0 LIM SINV argH ISP fs);
      auto using B_t_in_hull, B_t_res_hull, B_t_hull_ok, B_t_shadow_ok, B_t_zone_ok, NX0_spw, B_t_res_len, B_t_res_cover, B_t_hull_ne.
  Qed.
  Lemma B_ob_brk2 : brk2_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs.
  Proof.
    apply (AsanNodesMmB.node_brk2_sound B_SEGS B_T NX0 LIM SINV argH ISP fs);
      auto using B_t_in_hull, B_t_res_hull, B_t_hull_ok, B_t_shadow_ok, B_t_zone_ok, NX0_spw, B_t_res_len, B_t_res_cover, B_t_hull_ne.
  Qed.
  Lemma B_ob_mmap2 : mm2_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs (node_mmap2 B_T NX0 LIM).
  Proof.
    apply (node_mmap2_sound_OBL B_SEGS B_T NX0 LIM SINV argH ISP fs);
      auto using B_t_in_hull, B_t_res_len, B_t_res_hull, B_t_hull_ok, B_t_shadow_ok, B_t_zone_ok, NX0_spw, B_t_res_cover, B_t_hull_ne.
  Qed.
  Lemma B_ob_mmapin : forall hole : bool, mm3_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs (node_mmapin B_T LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL B_SEGS B_T NX0 LIM SINV argH ISP fs);
      auto using B_t_in_hull, B_t_res_len, B_t_res_hull, B_t_hull_ok, B_t_shadow_ok, B_t_zone_ok, NX0_spw, B_t_res_cover, B_t_hull_ne.
  Qed.
  Lemma B_ob_mprotect2 : mm2_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs (node_mprotect2 B_T LIM).
  Proof.
    apply (node_mprotect2_sound_OBL B_SEGS B_T NX0 LIM SINV argH ISP fs);
      auto using B_t_in_hull, B_t_res_len, B_t_res_hull, B_t_hull_ok, B_t_shadow_ok, B_t_zone_ok, NX0_spw, B_t_res_cover, B_t_hull_ne.
  Qed.
  Lemma B_ob_exit : exit_stmt B_SEGS B_T LIM SINV argH ISP fs.
  Proof. apply (AsanNodesMmB.node_exit_sound B_SEGS B_T LIM SINV argH ISP fs). Qed.
  Lemma B_ob_join : join_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs.
  Proof. apply (node_join_sound B_SEGS B_T NX0 LIM SINV argH ISP fs). Qed.
  Lemma B_ob_joinx : joinx_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs.
  Proof. apply (node_joinx_sound B_SEGS B_T NX0 LIM SINV argH ISP fs); auto using NX0_spw. Qed.

  (* [comment removed for export] *)
  Theorem B_check_sound : forall FUEL BFUEL p cs s,
    check B_SEGS IT B_T NX0 LIM XN XE XB HS KC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok B_SEGS B_T LIM SINV argH ISP fs E cs R FULL model ->
      srealizes B_SEGS (cfg_of B_SEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound B_SEGS IT IT_ok B_T NX0 LIM HS XN XE XB
              B_t_segs_wx B_t_in_hull B_t_hull_ok B_t_shadow_ok B_t_zone_ok NX0_spw SINV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil fs KC
              B_ob_sys B_ob_brk2 B_ob_mmap2 B_ob_mmapin B_ob_mprotect2 B_ob_exit X_sound B_ob_join B_ob_joinx
              XN_sound XE_sound XB_sound HOLES_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End B_Check.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section B_Top.
  (* LPS 08b1429: the run's whole [ProcInput]; the hypotheses are [Run.valid_entry]'s and
     [Run.valid_input]'s, as AsanInit's Section states them. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk B_SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation SINV := (SINV0 B_PH BPC0 sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  (* as A/HandoffArgv.v:89: E0 takes sp, rdraw, brk0, inp - not mbase. *)
  #[local] Notation E0B := (E0 sp rdraw brk0 inp).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation fs := (in_fs inp).
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. eapply SINV0_frame; eassumption. Qed.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  (* as A_Top.v: [SINV0_agree] closes over AsanInit Section variables its statement never reads *)
  Proof.
    intros E E' M Hag HS. eapply SINV0_agree; try eassumption;
      try exact B_SEGS; try exact B_T; try exact B_PH; try exact BPC0; try exact LIM.
  Qed.
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; try eassumption. all: first [exact B_SEGS | exact B_T | exact B_PH | exact BPC0 | exact LIM]. Qed.
  Let AA := argH0_agree sp rdraw inp.

  (* [comment removed for export] *)
  Variable csm : acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis MAIN : holes_stmt B_SEGS B_T LIM (HS_one csm) SINV argH ISP HOLES fs.

  (* [init_acs_of] takes the run's CONFIG_RSEQ flag, read off the input here, never chosen *)
  Hypothesis CHAIN : chain B_SEGS B_T LIM B_XN0 B_XE0 B_XB0 (init_acs_of (rseq_z (kb_rseq (in_kernel inp))) B_T) csm.

  Theorem B_chain_startup :
    srealizes B_SEGS (init_config B_SEGS BPC0 B_PH sp brk0 mbase rdraw LIM inp) (HOLES 0%nat E0B fs).
  Proof.
    (* positional: AsanInit's Section order, segs A ph apc sp rdraw brk0 mbase inp LIM *)
    epose proof (init_cfg_eq B_SEGS B_T B_PH BPC0 sp rdraw brk0 mbase inp LIM) as EQ.
    repeat match type of EQ with ?P -> _ => specialize (EQ ltac:(first [exact eq_refl | exact B_img_facts | exact LIMIT_ok | eassumption])) end.
    rewrite EQ. clear EQ.
    epose proof (init_cs_ok B_SEGS B_T B_PH BPC0 sp rdraw brk0 mbase inp LIM) as HC.
    repeat match type of HC with ?P -> _ => specialize (HC ltac:(first [exact eq_refl | exact B_img_facts | exact LIMIT_ok | eassumption])) end.
    pose proof (chain_realizes B_SEGS B_T LIM SINV argH ISP fs B_XN0 B_XE0 B_XB0 HOLES) as CR.
    match type of HC with cs_ok _ _ _ _ _ _ _ ?E ?cs ?R ?FULL ?model =>
      specialize (fun CS => CR CS (init_acs_of (rseq_z (kb_rseq (in_kernel inp))) B_T) csm CHAIN MAIN E R FULL model HC) end.
    match type of HC with cs_ok _ _ _ _ _ _ _ _ _ _ _ ?model =>
      match goal with |- srealizes _ ?c (HOLES 0%nat ?e _) =>
        enough (Hg : srealizes B_SEGS c (HOLES 0%nat e (m_fs model)))
          by (rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) in Hg; exact Hg) end end.
    apply CR. clear CR.
    intros IT HIT HS HSs KC FUEL BFUEL p cs s Hchk E R FULL model HC'.
    pose proof (B_XN0_sound LIM SINV argH ISP fs AH AA SF SA) as XNs.
    pose proof (B_XE0_sound LIM SINV argH ISP fs) as XEs. pose proof (B_XB0_sound LIM SINV argH ISP fs) as XBs.
    pose proof B_img_facts as IMG0.
    assert (Hapc0 : Z.of_N BPC0 = a_entry B_T) by reflexivity.
    assert (S00 : forall E M, SINV E M -> SINV E M) by (intros ? ? H; exact H).
    eapply B_check_sound; eassumption.
  Qed.
End B_Top.
