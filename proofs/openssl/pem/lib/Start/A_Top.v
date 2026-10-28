(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit AsanNodesIface AsanNodesLibE AsanNodesMmA AsanNodesMmB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_XAll A_Gsh A_HooksDefs A_Hooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation BPC0 := Asan.M.init_pc.
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
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A_Check.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation argH := (argH0 A_PH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  Let AH := argH0_high A_PH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree A_PH sp rdraw argv envp uid hw.

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis S0 : forall E M, SINV E M -> SINV0 A_PH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Let SP : forall E M, SINV E M -> uE E e_pgsp = pgdown ISP :=
    fun E M H => SINV0_pgsp A_PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (S0 E M H).

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

  Let X_sound := A_x_all_sinv sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SINV S0 SF SA.

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
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.      (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk A_SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation SINV := (SINV0 A_PH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 A_PH sp rdraw argv envp uid hw).
  #[local] Notation E0B := (E0 A_PH sp rdraw brk0 argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation inpB := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd).
  Let SF := SINV0_frame A_PH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree A_PH sp rdraw brk0 argv envp uid hw.
  Let AH := argH0_high A_PH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree A_PH sp rdraw argv envp uid hw.

  (* [comment removed for export] *)
  Lemma A_SB : forall E M, SINV E M -> forall k, k <> K_RND -> eb E k = A_BLOBS k.
  Proof.
    intros E M (_ & _ & H3) k Hk. rewrite H3. unfold E0. cbn [eb]. destruct (Nat.eqb_spec k K_RND) as [->|_]; [contradiction | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Variable csm : acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis MAIN : holes_stmt A_SEGS A_T LIM (HS_one csm) SINV argH ISP HOLES fs.

  (* [comment removed for export] *)
  Hypothesis CHAIN : chain A_SEGS A_T LIM A_XN0 A_XE0 A_XB0 (init_acs_of A_T) csm.

  Theorem A_chain_startup :
    srealizes A_SEGS (init_config A_SEGS BPC0 A_PH sp brk0 mbase rdraw LIM inpB) (HOLES 0%nat E0B fs).
  Proof.
    rewrite (init_cfg_eq A_SEGS A_T A_PH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd LIM BPC0 eq_refl).
    pose proof (init_cs_ok A_SEGS A_T A_PH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd LIM LIMIT_ok
                  A_img_facts Hsp Hbrk Hva Hve Hfit Huid) as HC.
    pose proof (chain_realizes A_SEGS A_T LIM SINV argH ISP fs A_XN0 A_XE0 A_XB0 HOLES) as CR.
    match type of HC with cs_ok _ _ _ _ _ _ _ ?E ?cs ?R ?FULL ?model =>
      specialize (fun CS => CR CS (init_acs_of A_T) csm CHAIN MAIN E R FULL model HC) end.
    match type of HC with cs_ok _ _ _ _ _ _ _ _ _ _ _ ?model =>
      replace fs with (m_fs model) at 2 by (exact (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC)) end.
    apply CR. clear CR.
    intros IT HIT HS HSs KC FUEL BFUEL p cs s Hchk E R FULL model HC'.
    exact (A_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SINV (fun E M H => H) SF SA
              A_XN0 A_XE0 A_XB0
              (A_XN0_sound LIM SINV argH ISP fs AH AA SF SA A_SB) (A_XE0_sound LIM SINV argH ISP fs) (A_XB0_sound LIM SINV argH ISP fs)
              IT HIT HS HOLES HOLES_agree HOLES_nil HSs KC FUEL BFUEL p cs s Hchk E R FULL model HC').
  Qed.
End A_Top.
