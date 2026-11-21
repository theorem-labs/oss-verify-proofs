(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start over the launch input ProcInput, the CONFIG_RSEQ flag and the m_channel_reader fact). *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImagesB AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanSmearB AsanHeapSortB AsanStartupB.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec.
Local Instance topa_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImagesB AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanSmearB AsanHeapSortB AsanStartupB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => (holes_only a && holes_only b)%bool
  | SAlt2 a b => (holes_only a && holes_only b)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Lemma sd_holes_only : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (T : TSet) (s : shape),
  (forall h, t_eq (HOLES h E fs) T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HH. induction s as [| c | fd ps s' IH | a IHa b IHb | e mid a IHa b IHb | h | ];
    cbn [holes_only sd]; intros Hs; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. intros tr. unfold t_alt2. rewrite (IHa H1 tr), (IHb H2 tr). tauto.
  - apply andb_prop in Hs as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - exact (HH h).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* The reader premise: [cs_ok]'s [co_rdr] reads [State.m_channel_reader],
   which [init_model] takes from [in_channel_reader]; the left input
   ([mkProcInput]) pins it [true], the right one is the launch's own, so
   the caller takes it from [valid_input_either]. *)


(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StartupGen.
  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (** #108: the run's CONFIG_RSEQ flag is FREE ([Run.recorded_kernel]), so the hand-off tables, the plan
      (its join states) and the shape are per value of the plan's flag [r], and the certificate is one per
      build: [startup_cert b] is checked at [r = rseq_z b] ([AsanPlanCore.AUXSZ_of] ties [r] to the run).
      The case split on [b] happens where [startup_cert] is discharged, on closed goals. *)
  Variable HS_both : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both (rseq_z b)) KC0 BFUEL FUEL None
          (asan_b_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.

  (* [comment removed for export] *)
  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    holes_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT (HS_both (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 APH (AsanUbsan.M.init_pc) sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).

  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input_either inp ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (T (in_argv inp) (in_fs inp)).
  Proof using IT0_ok startup_cert Hshape T_nil T_holes.
    intros en inp Hve Hvi.
    destruct en as [sp brk0 mbase rdraw].
    (** the clauses of [Run.valid_input_either] this proof reads, by NAME, so an inserted conjunct does not move them *)
    assert (Hva : valid_argv (in_argv inp)) by (clear - Hvi; red in Hvi; tauto).
    assert (Hvenv : valid_envp (in_envp inp)) by (clear - Hvi; red in Hvi; tauto).
    assert (Hsv : in_va_size inp = Sv48) by (clear - Hvi; red in Hvi; tauto).
    assert (Hlaunch : valid_launch inp) by (clear - Hvi; red in Hvi; tauto).
    assert (Hrd : in_channel_reader inp = true) by (clear - Hvi; red in Hvi; tauto).
    assert (Huid : valid_id (in_uid inp)).
    { clear - Hvi. red in Hvi. repeat match goal with H : _ /\ _ |- _ => destruct H end.
      match goal with H : valid_creds _ |- _ => destruct H as [H _]; exact H end. }
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hve. destruct Hve as (Hsp & Hbrk & Hmb & _ & Hlau).
    cbn [en_sp en_brk en_mmap_base en_draw].
    (** the run's input IS AsanInit's [inp]: the Section takes the whole input, no bridge *)
    (* the statement names [target_alloc_limit]; [init_cfg_eq] is stated over [AsanInit.LIMIT], its
       definitional alias, and [rewrite] matches syntactically *)
    change target_alloc_limit with AsanInit.LIMIT.
    rewrite (init_cfg_eq ASEGS ASAN_B APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) by first [exact asan_img_facts | reflexivity | eassumption].
    pose proof (init_cs_ok ASEGS ASAN_B APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) as HC.
    (* NOT YET COMPILED.  Each Variable of [init_cs_ok] is passed explicitly, so these arms meet
       only the Section's Prop hypotheses; [eassumption] is still ambiguous between hypotheses
       whose statements unify, and [repeat] can stop one specialization short (the failure then
       surfaces where [HC] is used).  When this compiles: write the specializations out, or assert
       HC's final shape right after the [repeat]; keep [(split; cbn; lia)] (HRESX on the concrete
       table) LAST among the closers. *)
    repeat (specialize (HC ltac:(first [exact asan_img_facts | reflexivity | eassumption | (split; cbn; lia)]))).
    set (RZ := rseq_z (kb_rseq (in_kernel inp))).
    set (fs := in_fs inp) in *.
    set (SINV := SINV0 APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) in *.
    set (argH := argH0 sp rdraw inp) in *.
    set (HOLES := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => T (in_argv inp) fs').
    assert (AH : forall E a, argH E a = true -> CEIL <= bv_unsigned a)
      (* [argH0_high] also binds AsanInit's [apc : N], a bare goal no hypothesis pins: name it, and
         close the [argH0] goal FIRST so it fixes [sp]/[inp] before the two section facts *)
      by (intros E a H; eapply argH0_high with (apc := AsanUbsan.M.init_pc); [ | | exact H ]; [ exact Hsp | exact Hva ]).
    pose proof (argH0_agree sp rdraw inp) as AA.
    pose proof (SINV0_frame APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) as SF.
    pose proof (SINV0_agree APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) as SA.
    assert (HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') by (intros; reflexivity).
    assert (HOLES_nil : forall h E fs', HOLES h E fs' []) by (intros h E fs'; exact (T_nil (in_argv inp) fs')).
    pose proof (T_holes sp rdraw brk0 mbase inp Hsp Hva Hvenv Hlaunch Hlau) as HOLES_sound.
    assert (XALL : forall x, x_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT RZ SINV argH fs x)
      by (intros x; eapply asan_node_x_sound_all; first [exact (fun E M H => H) | eassumption]).
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 sp rdraw brk0 inp) fs (startup_shape RZ))).
    - exact (check_sound ASEGS IT0 IT0_ok ASAN_B NX0 AsanInit.LIMIT RZ (HS_both RZ) XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs)
              XALL
              (node_join_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None (startup_plan RZ) (asan_b_init RZ) (startup_shape RZ) (startup_cert (kb_rseq (in_kernel inp)))
              _ _ _ _ t_nil HC I eq_refl).
    - apply sd_holes_only; [intros h tr; reflexivity | exact (Hshape (kb_rseq (in_kernel inp)))].
    (* one [env] evar is left unconstrained by the applications above; any env closes it *)
    Unshelve. all: exact (E0 sp rdraw brk0 inp).
  Qed.
End StartupGen.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec.
Local Instance topa_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit AsanTablesA
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanSmearA AsanHeapSortA AsanStartup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => (holes_only a && holes_only b)%bool
  | SAlt2 a b => (holes_only a && holes_only b)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Lemma sd_holes_only : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (T : TSet) (s : shape),
  (forall h, t_eq (HOLES h E fs) T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HH. induction s as [| c | fd ps s' IH | a IHa b IHb | e mid a IHa b IHb | h | ];
    cbn [holes_only sd]; intros Hs; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. intros tr. unfold t_alt2. rewrite (IHa H1 tr), (IHb H2 tr). tauto.
  - apply andb_prop in Hs as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - exact (HH h).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StartupGen.
  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (** #108: the run's CONFIG_RSEQ flag is FREE ([Run.recorded_kernel]), so the hand-off tables, the plan
      (its join states) and the shape are per value of the plan's flag [r], and the certificate is one per
      build: [startup_cert b] is checked at [r = rseq_z b] ([AsanPlanCore.AUXSZ_of] ties [r] to the run).
      The case split on [b] happens where [startup_cert] is discharged, on closed goals. *)
  Variable HS_asan : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
          (asan_a_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.

  (* [comment removed for export] *)
  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT (HS_asan (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 APH (Asan.M.init_pc) sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).

  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input_either inp ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (T (in_argv inp) (in_fs inp)).
  Proof using IT0_ok startup_cert Hshape T_nil T_holes.
    intros en inp Hve Hvi.
    destruct en as [sp brk0 mbase rdraw].
    (** the clauses of [Run.valid_input_either] this proof reads, by NAME, so an inserted conjunct does not move them *)
    assert (Hva : valid_argv (in_argv inp)) by (clear - Hvi; red in Hvi; tauto).
    assert (Hvenv : valid_envp (in_envp inp)) by (clear - Hvi; red in Hvi; tauto).
    assert (Hsv : in_va_size inp = Sv48) by (clear - Hvi; red in Hvi; tauto).
    assert (Hlaunch : valid_launch inp) by (clear - Hvi; red in Hvi; tauto).
    assert (Hrd : in_channel_reader inp = true) by (clear - Hvi; red in Hvi; tauto).
    assert (Huid : valid_id (in_uid inp)).
    { clear - Hvi. red in Hvi. repeat match goal with H : _ /\ _ |- _ => destruct H end.
      match goal with H : valid_creds _ |- _ => destruct H as [H _]; exact H end. }
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hve. destruct Hve as (Hsp & Hbrk & Hmb & _ & Hlau).
    cbn [en_sp en_brk en_mmap_base en_draw].
    (** the run's input IS AsanInit's [inp]: the Section takes the whole input, no bridge *)
    (* the statement names [target_alloc_limit]; [init_cfg_eq] is stated over [AsanInit.LIMIT], its
       definitional alias, and [rewrite] matches syntactically *)
    change target_alloc_limit with AsanInit.LIMIT.
    rewrite (init_cfg_eq ASEGS ASAN_A APH Asan.M.init_pc sp rdraw brk0 mbase inp) by first [exact asan_img_facts | reflexivity | eassumption].
    pose proof (init_cs_ok ASEGS ASAN_A APH Asan.M.init_pc sp rdraw brk0 mbase inp) as HC.
    repeat (specialize (HC ltac:(first [exact asan_img_facts | reflexivity | eassumption | (split; cbn; lia)]))).
    set (RZ := rseq_z (kb_rseq (in_kernel inp))).
    set (fs := in_fs inp) in *.
    set (SINV := SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp) in *.
    set (argH := argH0 sp rdraw inp) in *.
    set (HOLES := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => T (in_argv inp) fs').
    assert (AH : forall E a, argH E a = true -> CEIL <= bv_unsigned a)
      (* [argH0_high] also binds AsanInit's [apc : N], a bare goal no hypothesis pins: name it, and
         close the [argH0] goal FIRST so it fixes [sp]/[inp] before the two section facts *)
      by (intros E a H; eapply argH0_high with (apc := Asan.M.init_pc); [ | | exact H ]; [ exact Hsp | exact Hva ]).
    pose proof (argH0_agree sp rdraw inp) as AA.
    pose proof (SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp) as SF.
    pose proof (SINV0_agree APH Asan.M.init_pc sp rdraw brk0 mbase inp) as SA.
    assert (HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') by (intros; reflexivity).
    assert (HOLES_nil : forall h E fs', HOLES h E fs' []) by (intros h E fs'; exact (T_nil (in_argv inp) fs')).
    pose proof (T_holes sp rdraw brk0 mbase inp Hsp Hva Hvenv Hlaunch Hlau) as HOLES_sound.
    assert (XALL : forall x, x_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT RZ SINV argH fs x)
      by (intros x; eapply asan_node_x_sound_all; first [exact (fun E M H => H) | eassumption]).
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 sp rdraw brk0 inp) fs (startup_shape RZ))).
    - exact (check_sound ASEGS IT0 IT0_ok ASAN_A NX0 AsanInit.LIMIT RZ (HS_asan RZ) XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs)
              XALL
              (node_join_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None (startup_plan RZ) (asan_a_init RZ) (startup_shape RZ) (startup_cert (kb_rseq (in_kernel inp)))
              _ _ _ _ t_nil HC I eq_refl).
    - apply sd_holes_only; [intros h tr; reflexivity | exact (Hshape (kb_rseq (in_kernel inp)))].
    (* one [env] evar is left unconstrained by the applications above; any env closes it *)
    Unshelve. all: exact (E0 sp rdraw brk0 inp).
  Qed.
End StartupGen.
