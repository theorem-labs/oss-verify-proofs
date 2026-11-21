(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the MainEntry, Boot1 and Piece sections restated over one ProcInput, entry pc and mmap base, with the launch hypotheses including the channel reader; the start-up and main-entry certificates take the run's CONFIG_RSEQ flag; every encoded CDefT statement written out in plain text; the munmap2 node obligation added to the soundness chain; section Let facts moved into the proofs, #[using] lists dropped and a few comments written out). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanCertDefs AsanPlanImages AsanInit
  AsanExtNodes AsanNoReplaceNode AsanExtNodesSound
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanStartup PlanCut.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMainEntry () : Init.string Init.list := ["OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shape"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "only_holes"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.sd"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_nil"; "has_hole_all"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_eq"; "OSSVerify.KrLib.ABoot.AxSymRun3.env_agree"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cs_ok"; "OSSVerify.KrLib.ABoot.AsanCertDefs.ASEGS"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ASAN"; "OSSVerify.KrLib.ABoot.AsanCertDefs.ALIMIT"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.ABoot.AsanInit.SINV0"; "OSSVerify.KrLib.ABoot.AsanPlanImages.APH"; "OSSVerify.KrLib.ABoot.AsanInit.argH0"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cfg_of"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pc"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_asan.M.init_pc"; "OSSVerify.KrLib.ABoot.AsanInit.LIMIT"; "OSSVerify.KrLib.ABoot.AsanInit.inp"; "OSSVerify.KrLib.ABoot.AsanInit.E0"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Piece.from_state"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.holes_stmt"; "OSSVerify.KrLib.ABoot.PlanCut.hs_tab"; "Corelib.Init.Datatypes.Some"].


(* [comment removed for export] *)
Fixpoint only_holes (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SNil => true
  | SAlt2 a b => only_holes a && only_holes b
  | SCase _ _ a b => only_holes a && only_holes b
  | _ => false
  end.

Lemma sd_only_holes : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,PE,$0.Pfs',$1.A3.R6.R2.R1.(4.$5.)P,(6.$7.(8.R4.)$9.)Ptr,(:.$5.)P,(;.L,$<.R8.$=.R5.R4.R6.R1.)A3.R8.R6.R5.R2.")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs' Hnil.
  induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h | ]; intros H tr X; cbn [only_holes] in H; try discriminate; cbn [sd] in X.
  - unfold t_nil in X. subst tr. apply Hnil.
  - apply andb_prop in H as [Ha Hb]. destruct X as [X|X]; [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - apply andb_prop in H as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - exact X.
Qed.

(* [comment removed for export] *)
Fixpoint has_hole_all (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b => has_hole_all a || has_hole_all b
  | SCase _ _ a b => has_hole_all a && has_hole_all b
  | _ => false
  end.

Lemma sd_has_hole_all : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,(6.$7.(>.R3.)$9.)Ptr,(:.$5.)P,A3.R6.R4.R3.R1.(;.L,$<.R8.$=.R5.R4.R6.R2.)")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs'.
  induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h | ]; intros H tr X; cbn [has_hole_all] in H; try discriminate; cbn [sd].
  - apply orb_prop in H as [H|H]; [left; exact (IHa H tr X) | right; exact (IHb H tr X)].
  - apply andb_prop in H as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - exact X.
Qed.

Lemma sd_main_eq : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,PE,$0.Pfs',$1.A3.R6.R2.R1.(4.$5.)P,(6.$7.(8.R4.)$9.)P,(6.$7.(>.R5.)$9.)(?.(;.L,$<.R8.$=.R5.R4.R6.)A2.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs' Hnil H1 H2 tr. split; [apply sd_only_holes; assumption | apply sd_has_hole_all; assumption].
Qed.

(** #108 (LPS 75d69e00): the three Sections below are restated over AsanInit's / AsanStartup's
    whole-input interface: the run is [apc sp rdraw brk0 mbase inp] with AsanStartup's hypotheses,
    the certificates carry the run's CONFIG_RSEQ flag [RZ := rseq_z (kb_rseq (in_kernel inp))], and
    every statement that was encoded (CDefT.buildp) over the old 16 loose variables is written out
    from its decode (cdeft_print.py) with those arities replaced; nothing is re-encoded.  The proofs
    follow AsanStartup.asan_startup's (the same node-soundness chain at [nx]). *)
Section MainEntry.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
  #[local] Notation SP0 := (bv_unsigned sp).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  (** the start-up certificate *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable HS0 : acs.
  Hypothesis HS_asan_only0 : forall h ch, HS_asan h = Some ch -> ch = HS0.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check RZ IT0 HS_asan startup_plan = COk startup_shape.
  Hypothesis startup_guard : spin_guarded startup_plan = true.
  Hypothesis startup_shape_holes : only_holes startup_shape = true.
  Hypothesis startup_shape_hole : has_hole_all startup_shape = true.

  (** the main-entry certificate, from the start-up's one hole state *)
  Variable NX1 : nat.
  Hypothesis HNX1 : (NX0 <= NX1)%nat.
  Variable IT1 : itab.
  Hypothesis IT1_ok : itab_sound ASEGS IT1.
  Variable HS_main : nat -> option acs.
  Variable mainentry_plan : plan.
  Variable mainentry_shape : shape.
  Hypothesis mainentry_cert : s2_check NX1 RZ IT1 HS_main HS0 mainentry_plan = COk mainentry_shape.
  Hypothesis mainentry_guard : spin_guarded mainentry_plan = true.
  Hypothesis mainentry_shape_holes : only_holes mainentry_shape = true.
  Hypothesis mainentry_shape_hole : has_hole_all mainentry_shape = true.

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].
  Hypothesis MAIN_sound : holes_stmt ASEGS ASAN ALIMIT HS_main SP0 SINV argH (fun _ => MAIN) fs.

  Lemma MAIN_agree1 : forall (h : nat) (E E' : env) (fs' : Fs.Fs),
    env_agree NX1 E E' -> (fun _ : nat => MAIN) h E fs' = (fun _ : nat => MAIN) h E' fs'.
  Proof. intros h E E' fs' Hag. apply MAIN_agree. exact (env_agree_le _ _ _ _ Hag HNX1). Qed.
  Lemma MAIN_nil1 : forall (h : nat) E fs', (fun _ : nat => MAIN) h E fs' [].
  Proof. intros. apply MAIN_nil. Qed.

  Theorem mainentry_sound : forall (E : env) (R : bvmap 5 (bv 64)) (FULL : bv 64 -> option (bv 8)) (model : Model),
    cs_ok ASEGS ASAN ALIMIT SP0 SINV argH fs E HS0 R FULL model ->
    srealizes ASEGS (cfg_of ASEGS R (pc HS0) FULL model) (sd (fun _ => MAIN) t_nil E (m_fs model) mainentry_shape).
  Proof.
    intros E R FULL model HC.
    pose proof asan_img_facts as IMG.
    pose proof (run_sp0_ok sp Hsp) as SP0_ok.
    assert (AH : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a)
      by (intros E' a H; eapply run_argH_high; [asan_close .. | exact H]).
    pose proof (argH0_agreeN NX1 sp rdraw inp) as AA1.
    assert (SF : forall E M M', (forall a, argH E a = true -> M' a = M a) ->
               (forall a : word, SP0 <= bv_unsigned a -> M a <> None -> M' a <> None) -> SINV E M -> SINV E M')
      by (intros E' M M' H1 H2; eapply SINV0_frame; asan_close).
    assert (SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M)
      by (intros E' E'' M H1; eapply SINV0_agree; exact H1).
    assert (SA1 : forall E E' M, env_agree NX1 E E' -> SINV E M -> SINV E' M)
      by (intros E' E'' M H1; apply SA; exact (env_agree_le _ _ _ _ H1 HNX1)).
    assert (SS : forall E M, SINV E M -> uE_sp0 E = SP0)
      by (intros E' M H; eapply run_SINV_sp; [asan_close .. | exact H]).
    assert (XS : forall x, x_stmt ASEGS ASAN NX1 ALIMIT RZ SP0 SINV argH fs x)
      by (eapply (asan_node_x_sound_allN NX1 HNX1); first [ exact (fun E M H => H) | asan_close | exact SF | exact SA ]).
    pose proof (check_sound ASEGS IT1 IT1_ok ASAN NX1 ALIMIT RZ HS_main (XN_A NX1) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA1 SF SA1
              (fun _ => MAIN) MAIN_agree1 MAIN_nil1 fs KC0) as C1.
    pose proof (C1
              (AsanNodesMmB.node_sys_sound ASEGS ASAN NX1 ALIMIT SINV argH fs SP0 AA1 SF SA1)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN NX1 ALIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mmapin_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mprotect2_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_munmap2_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 XS (asan_node_x_sound0_all NX1 ALIMIT RZ SINV argH SP0 SP0_ok AH AA1 SF SA1 fs)) as C3.
    pose proof (C3 (node_join_sound ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 (node_ext_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs AA1 SA1) (XE0_sound _ _ _ _ _ _ _ _)
                   (node_noreplace_sound_OBL ASEGS ASAN NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
                   MAIN_sound) as C5.
    exact (C5 FUEL BFUEL None mainentry_plan HS0 mainentry_shape mainentry_cert mainentry_guard E R FULL model t_nil HC I eq_refl).
  Qed.

  Theorem startup_holes_sound : holes_stmt ASEGS ASAN ALIMIT HS_asan SP0 SINV argH (fun _ => MAIN) fs.
  Proof.
    intros h ch Hh E R FULL model HC. rewrite (HS_asan_only0 h ch Hh) in HC |- *.
    apply (srz_conseq ASEGS _ _ _ (mainentry_sound E R FULL model HC)).
    apply sd_main_eq; [exact MAIN_nil | exact mainentry_shape_holes | exact mainentry_shape_hole].
  Qed.

  Theorem asan_boot_shape :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp)
      (sd (fun _ => MAIN) t_nil E0a fs startup_shape).
  Proof.
    (* [asan_startup]'s conclusion fixes the run, the holes and the shape; the certificate fixes the
       table, the instruction table and the plan, so it is closed first. *)
    eapply asan_startup.
    all: try exact startup_cert.
    all: first [ exact startup_holes_sound | exact startup_guard | exact IT0_ok
               | exact (fun h E E' fs' Hag => MAIN_agree E E' fs' Hag)
               | exact (fun h E fs' => MAIN_nil E fs') | asan_close ].
  Qed.

  Theorem asan_boot :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) (MAIN E0a fs).
  Proof.
    apply (srz_conseq ASEGS _ _ _ asan_boot_shape).
    apply sd_main_eq; [exact MAIN_nil | exact startup_shape_holes | exact startup_shape_hole].
  Qed.
End MainEntry.

(** the start-up alone, when [MAIN] is given at the start-up's holes directly *)
Section Boot1.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
  #[local] Notation SP0 := (bv_unsigned sp).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check RZ IT0 HS_asan startup_plan = COk startup_shape.
  Hypothesis startup_guard : spin_guarded startup_plan = true.
  Hypothesis startup_shape_holes : only_holes startup_shape = true.
  Hypothesis startup_shape_hole : has_hole_all startup_shape = true.

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].
  Hypothesis MAIN_sound : holes_stmt ASEGS ASAN ALIMIT HS_asan SP0 SINV argH (fun _ => MAIN) fs.

  Theorem asan_boot1 :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) (MAIN E0a fs).
  Proof.
    assert (S1 : srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp)
                   (sd (fun _ => MAIN) t_nil E0a fs startup_shape)).
    { eapply asan_startup.
      all: try exact startup_cert.
      all: first [ exact MAIN_sound | exact startup_guard | exact IT0_ok
                 | exact (fun h E E' fs' Hag => MAIN_agree E E' fs' Hag)
                 | exact (fun h E fs' => MAIN_nil E fs') | asan_close ]. }
    apply (srz_conseq ASEGS _ _ _ S1).
    apply sd_main_eq; [exact MAIN_nil | exact startup_shape_holes | exact startup_shape_hole].
  Qed.
End Boot1.

(** one certified piece, from a recorded state [cs0] *)
Section Piece.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation SP0 := (bv_unsigned sp).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].

  (** the realization a state [cs] carries: from any concrete configuration it covers, the run reaches [MAIN] *)
  Definition from_state (cs : acs) : Prop :=
    forall (E : env) (R : bvmap 5 (bv 64)) (FULL : bv 64 -> option (bv 8)) (model : Model),
      cs_ok ASEGS ASAN ALIMIT SP0 SINV argH fs E cs R FULL model ->
      srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (MAIN E (m_fs model)).

  Lemma hs_tab_holes : forall l : list (nat * acs),
    (forall h cs, In (h, cs) l -> from_state cs) ->
    holes_stmt ASEGS ASAN ALIMIT (hs_tab l) SP0 SINV argH (fun _ => MAIN) fs.
  Proof.
    intros l Hl. induction l as [|[h0 cs0] l IH]; intros h ch Hh E R FULL model HC; cbn [hs_tab] in Hh; [discriminate Hh|].
    destruct (Nat.eqb h h0) eqn:He.
    - injection Hh as <-. exact (Hl h0 cs0 (or_introl eq_refl) E R FULL model HC).
    - exact (IH (fun h' cs' Hin => Hl h' cs' (or_intror Hin)) h ch Hh E R FULL model HC).
  Qed.

  Lemma hs_const_holes : forall (HS : nat -> option acs) (cs0 : acs),
    (forall h ch, HS h = Some ch -> ch = cs0) -> from_state cs0 ->
    holes_stmt ASEGS ASAN ALIMIT HS SP0 SINV argH (fun _ => MAIN) fs.
  Proof. intros HS cs0 Honly H0 h ch Hh E R FULL model HC. rewrite (Honly h ch Hh) in HC |- *. exact (H0 E R FULL model HC). Qed.

  Variable nx : nat.
  Hypothesis Hnx : (NX0 <= nx)%nat.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound ASEGS IT.
  Variable HS : nat -> option acs.
  Variable cs0 : acs.
  Variable p : plan.
  Variable s : shape.
  Hypothesis cert : s2_check nx RZ IT HS cs0 p = COk s.
  Hypothesis cert_guard : spin_guarded p = true.
  Hypothesis s_holes : only_holes s = true.
  Hypothesis s_hole : has_hole_all s = true.
  Hypothesis HS_sound : holes_stmt ASEGS ASAN ALIMIT HS SP0 SINV argH (fun _ => MAIN) fs.

  Lemma MAIN_agreeP : forall (h : nat) (E E' : env) (fs' : Fs.Fs),
    env_agree nx E E' -> (fun _ : nat => MAIN) h E fs' = (fun _ : nat => MAIN) h E' fs'.
  Proof. intros h E E' fs' Hag. apply MAIN_agree. exact (env_agree_le _ _ _ _ Hag Hnx). Qed.
  Lemma MAIN_nilP : forall (h : nat) E fs', (fun _ : nat => MAIN) h E fs' [].
  Proof. intros. apply MAIN_nil. Qed.

  Theorem piece_shape_sound : forall (E : env) (R : bvmap 5 (bv 64)) (FULL : bv 64 -> option (bv 8)) (model : Model),
    cs_ok ASEGS ASAN ALIMIT SP0 SINV argH fs E cs0 R FULL model ->
    srealizes ASEGS (cfg_of ASEGS R (pc cs0) FULL model) (sd (fun _ => MAIN) t_nil E (m_fs model) s).
  Proof.
    intros E R FULL model HC.
    pose proof asan_img_facts as IMG.
    pose proof (run_sp0_ok sp Hsp) as SP0_ok.
    assert (AH : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a)
      by (intros E' a H; eapply run_argH_high; [asan_close .. | exact H]).
    pose proof (argH0_agreeN nx sp rdraw inp) as AA1.
    assert (SF : forall E M M', (forall a, argH E a = true -> M' a = M a) ->
               (forall a : word, SP0 <= bv_unsigned a -> M a <> None -> M' a <> None) -> SINV E M -> SINV E M')
      by (intros E' M M' H1 H2; eapply SINV0_frame; asan_close).
    assert (SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M)
      by (intros E' E'' M H1; eapply SINV0_agree; exact H1).
    assert (SA1 : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M)
      by (intros E' E'' M H1; apply SA; exact (env_agree_le _ _ _ _ H1 Hnx)).
    assert (SS : forall E M, SINV E M -> uE_sp0 E = SP0)
      by (intros E' M H; eapply run_SINV_sp; [asan_close .. | exact H]).
    assert (XS : forall x, x_stmt ASEGS ASAN nx ALIMIT RZ SP0 SINV argH fs x)
      by (eapply (asan_node_x_sound_allN nx Hnx); first [ exact (fun E M H => H) | asan_close | exact SF | exact SA ]).
    pose proof (check_sound ASEGS IT IT_ok ASAN nx ALIMIT RZ HS (XN_A nx) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA1 SF SA1
              (fun _ => MAIN) MAIN_agreeP MAIN_nilP fs KC0) as C1.
    pose proof (C1
              (AsanNodesMmB.node_sys_sound ASEGS ASAN nx ALIMIT SINV argH fs SP0 AA1 SF SA1)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN nx ALIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mmapin_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mprotect2_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_munmap2_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 XS (asan_node_x_sound0_all nx ALIMIT RZ SINV argH SP0 SP0_ok AH AA1 SF SA1 fs)) as C3.
    pose proof (C3 (node_join_sound ASEGS ASAN nx ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 (node_ext_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs AA1 SA1) (XE0_sound _ _ _ _ _ _ _ _)
                   (node_noreplace_sound_OBL ASEGS ASAN nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
                   HS_sound) as C5.
    exact (C5 FUEL BFUEL None p cs0 s cert cert_guard E R FULL model t_nil HC I eq_refl).
  Qed.

  Theorem piece_sound : from_state cs0.
  Proof.
    intros E R FULL model HC.
    apply (srz_conseq ASEGS _ _ _ (piece_shape_sound E R FULL model HC)).
    apply sd_main_eq; [exact MAIN_nil | exact s_holes | exact s_hole].
  Qed.
End Piece.
