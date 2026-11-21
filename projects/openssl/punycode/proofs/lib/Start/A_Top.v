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
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit AsanNodesIface AsanNodesLibE AsanNodesMmA AsanNodesMmB.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_XAll A_HooksDefs A_Hooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation APC0 := Asan.M.init_pc.
#[local] Notation LIM := AsanInit.LIMIT.

Lemma A_img_facts : img_facts A_SEGS A_T A_PH.
Proof.
  constructor.
  - exact A_t_if_ph.
  - exact A_t_if_hull.
  - exact A_t_if_top.
  - exact A_t_res_hull.
  - exact A_t_if_sizes.
  - exact A_t_if_rw.
  - exact A_t_shadow_ok.
  - (* [if_resx]: the table states [n_resx := 2; p_resx := 20] (Start/A_Atable.v) *)
    split; apply Nat.leb_le; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A_Check.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable fs : Fs.Fs.
  Hypothesis IMG : img_facts A_SEGS A_T A_PH.
  Hypothesis Hapc : Z.of_N APC0 = a_entry A_T.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk A_SEGS brk0.
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
  (* [argH0_high] closes over AsanInit's Section variables segs, A, ph, apc and LIM, which
     its statement never reads; [eassumption] leaves them, so they take this image's *)
  Proof. intros E a H. eapply argH0_high; try eassumption. all: first [exact A_SEGS | exact A_T | exact A_PH | exact APC0 | exact LIM]. Qed.
  Let AA := argH0_agree sp rdraw inp.

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis S0 : forall E M, SINV E M -> SINV0 A_PH APC0 sp rdraw brk0 mbase inp E M.
  Hypothesis SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Let SP : forall E M, SINV E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M H. pose proof (S0 E M H) as H0. eapply SINV0_pgsp; eassumption. Qed.

  (* [comment removed for export] *)
  Variable XN : nat -> list expr -> acs -> option acs.
  Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
  Variable XB : nat -> list expr -> acs -> option (acs * acs).
  Hypothesis XN_sound : ext_stmt A_SEGS A_T NX0 LIM XN SINV argH ISP fs.
  Hypothesis XE_sound : emit_stmt A_SEGS A_T NX0 LIM XE SINV argH ISP fs.
  Hypothesis XB_sound : ext2_stmt A_SEGS A_T NX0 LIM XB SINV argH ISP fs.
  (* [comment removed for export] *)
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound A_SEGS IT.
  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt A_SEGS A_T LIM HS SINV argH ISP HOLES fs.
  Variable KC : nat.

  Let X_sound : forall x, x_stmt A_SEGS A_T NX0 AsanInit.LIMIT SINV argH ISP fs x.
  Proof. intros x. eapply A_x_all_sinv; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma A_ob_sys : forall y, sys_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs y.
  Proof.
    apply (AsanNodesMmB.node_sys_sound A_SEGS A_T NX0 LIM SINV argH ISP fs);
      auto using A_t_in_hull, A_t_res_hull, A_t_hull_ok, A_t_shadow_ok, A_t_zone_ok, NX0_spw, A_t_res_len, A_t_res_cover, A_t_hull_ne.
  Qed.
  Lemma A_ob_brk2 : brk2_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs.
  Proof.
    apply (AsanNodesMmB.node_brk2_sound A_SEGS A_T NX0 LIM SINV argH ISP fs);
      auto using A_t_in_hull, A_t_res_hull, A_t_hull_ok, A_t_shadow_ok, A_t_zone_ok, NX0_spw, A_t_res_len, A_t_res_cover, A_t_hull_ne.
  Qed.
  Lemma A_ob_mmap2 : mm2_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs (node_mmap2 A_T NX0 LIM).
  Proof.
    apply (node_mmap2_sound_OBL A_SEGS A_T NX0 LIM SINV argH ISP fs);
      auto using A_t_in_hull, A_t_res_len, A_t_res_hull, A_t_hull_ok, A_t_shadow_ok, A_t_zone_ok, NX0_spw, A_t_res_cover, A_t_hull_ne.
  Qed.
  Lemma A_ob_mmapin : forall hole : bool, mm3_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs (node_mmapin A_T LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL A_SEGS A_T NX0 LIM SINV argH ISP fs);
      auto using A_t_in_hull, A_t_res_len, A_t_res_hull, A_t_hull_ok, A_t_shadow_ok, A_t_zone_ok, NX0_spw, A_t_res_cover, A_t_hull_ne.
  Qed.
  Lemma A_ob_mprotect2 : mm2_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs (node_mprotect2 A_T LIM).
  Proof.
    apply (node_mprotect2_sound_OBL A_SEGS A_T NX0 LIM SINV argH ISP fs);
      auto using A_t_in_hull, A_t_res_len, A_t_res_hull, A_t_hull_ok, A_t_shadow_ok, A_t_zone_ok, NX0_spw, A_t_res_cover, A_t_hull_ne.
  Qed.
  Lemma A_ob_exit : exit_stmt A_SEGS A_T LIM SINV argH ISP fs.
  Proof. apply (AsanNodesMmB.node_exit_sound A_SEGS A_T LIM SINV argH ISP fs). Qed.
  Lemma A_ob_join : join_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs.
  Proof. apply (node_join_sound A_SEGS A_T NX0 LIM SINV argH ISP fs). Qed.
  Lemma A_ob_joinx : joinx_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs.
  Proof. apply (node_joinx_sound A_SEGS A_T NX0 LIM SINV argH ISP fs); auto using NX0_spw. Qed.

  (* [comment removed for export] *)
  Theorem A_check_sound : forall FUEL BFUEL p cs s,
    check A_SEGS IT A_T NX0 LIM XN XE XB HS KC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok A_SEGS A_T LIM SINV argH ISP fs E cs R FULL model ->
      srealizes A_SEGS (cfg_of A_SEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound A_SEGS IT IT_ok A_T NX0 LIM HS XN XE XB
              A_t_segs_wx A_t_in_hull A_t_hull_ok A_t_shadow_ok A_t_zone_ok NX0_spw SINV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil fs KC
              A_ob_sys A_ob_brk2 A_ob_mmap2 A_ob_mmapin A_ob_mprotect2 A_ob_exit X_sound A_ob_join A_ob_joinx
              XN_sound XE_sound XB_sound HOLES_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End A_Check.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A_Top.
  (* LPS 08b1429: the run's whole [ProcInput]; the hypotheses are [Run.valid_entry]'s and
     [Run.valid_input]'s, as AsanInit's Section states them. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk A_SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation SINV := (SINV0 A_PH APC0 sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  (* as A/HandoffArgv.v:89: E0 takes sp, rdraw, brk0, inp - not mbase. *)
  #[local] Notation E0A := (E0 sp rdraw brk0 inp).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation fs := (in_fs inp).
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. eapply SINV0_frame; eassumption. Qed.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  (* [SINV0_agree] closes over AsanInit Section variables its statement never reads; [eapply]
     leaves them as goals, which take this image's terms *)
  Proof.
    intros E E' M Hag HS. eapply SINV0_agree; try eassumption;
      try exact A_SEGS; try exact A_T; try exact A_PH; try exact APC0; try exact LIM.
  Qed.
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; try eassumption. all: first [exact A_SEGS | exact A_T | exact A_PH | exact APC0 | exact LIM]. Qed.
  Let AA := argH0_agree sp rdraw inp.

  (* [comment removed for export] *)
  Variable csm : acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis MAIN : holes_stmt A_SEGS A_T LIM (HS_one csm) SINV argH ISP HOLES fs.

  (* [init_acs_of] takes the run's CONFIG_RSEQ flag, read off the input here, never chosen *)
  Hypothesis CHAIN : chain A_SEGS A_T LIM A_XN0 A_XE0 A_XB0 (init_acs_of (rseq_z (kb_rseq (in_kernel inp))) A_T) csm.

  Theorem A_chain_startup :
    srealizes A_SEGS (init_config A_SEGS APC0 A_PH sp brk0 mbase rdraw LIM inp) (HOLES 0%nat E0A fs).
  Proof.
    (* positional: AsanInit's Section order, segs A ph apc sp rdraw brk0 mbase inp LIM *)
    epose proof (init_cfg_eq A_SEGS A_T A_PH APC0 sp rdraw brk0 mbase inp LIM) as EQ.
    repeat match type of EQ with ?P -> _ => specialize (EQ ltac:(first [exact eq_refl | exact A_img_facts | exact LIMIT_ok | eassumption])) end.
    rewrite EQ. clear EQ.
    epose proof (init_cs_ok A_SEGS A_T A_PH APC0 sp rdraw brk0 mbase inp LIM) as HC.
    repeat match type of HC with ?P -> _ => specialize (HC ltac:(first [exact eq_refl | exact A_img_facts | exact LIMIT_ok | eassumption])) end.
    pose proof (chain_realizes A_SEGS A_T LIM SINV argH ISP fs A_XN0 A_XE0 A_XB0 HOLES) as CR.
    match type of HC with cs_ok _ _ _ _ _ _ _ ?E ?cs ?R ?FULL ?model =>
      specialize (fun CS => CR CS (init_acs_of (rseq_z (kb_rseq (in_kernel inp))) A_T) csm CHAIN MAIN E R FULL model HC) end.
    match type of HC with cs_ok _ _ _ _ _ _ _ _ _ _ _ ?model =>
      match goal with |- srealizes _ ?c (HOLES 0%nat ?e _) =>
        enough (Hg : srealizes A_SEGS c (HOLES 0%nat e (m_fs model)))
          by (rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) in Hg; exact Hg) end end.
    apply CR. clear CR.
    intros IT HIT HS HSs KC FUEL BFUEL p cs s Hchk E R FULL model HC'.
    pose proof (A_XN0_sound LIM SINV argH ISP fs AH AA SF SA) as XNs.
    pose proof (A_XE0_sound LIM SINV argH ISP fs) as XEs. pose proof (A_XB0_sound LIM SINV argH ISP fs) as XBs.
    pose proof A_img_facts as IMG0.
    assert (Hapc0 : Z.of_N APC0 = a_entry A_T) by reflexivity.
    assert (S00 : forall E M, SINV E M -> SINV E M) by (intros ? ? H; exact H).
    eapply A_check_sound; eassumption.
  Qed.
End A_Top.
