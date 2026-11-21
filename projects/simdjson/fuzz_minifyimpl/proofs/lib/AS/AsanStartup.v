(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up soundness is stated over the run's whole launch input and its CONFIG_RSEQ value (the checker takes rz), from the new launch start state (AsanInit.init_cs_ok). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma asan_maxva_code : forall i, (i < 45)%nat ->
  fetch_word ASEGS (Z_to_bv 64 (x_maxva ASAN + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva ASAN].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma asan_maxva_range : 0 < x_maxva ASAN /\ x_maxva ASAN + 180 < 2 ^ 64.
Proof. cbn [x_maxva ASAN]. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XAll.
  Variable LIM : Z.   (* this tree's two ASan builds run at two limits (AsanInit's [LIM]) *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (** the plan's CONFIG_RSEQ flag is the run's own *)
  Let RZ := rseq_z (kb_rseq (in_kernel inp)).

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN nx0 LIM RZ SINV (argH0 sp rdraw inp) FS0 x.
  Proof.
    assert (AH : forall E a, argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high; first [eassumption | exact asan_img_facts]).
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw inp). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XIMemcpy nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemset nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemcpy nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemIsZero nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XPopFree nx0 LIM RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva ASEGS ASAN nx0 LIM RZ SINV _ FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame asan_maxva_range asan_maxva_code).
  Qed.
End XAll.

Local Ltac asan_side :=
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_res_hull | exact asan_hull_ok
        | exact asan_shadow_ok | exact asan_hull_cov | exact asan_img_facts
        | exact (fun E M H => H) | apply le_n | eassumption ].

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variables brk0 mbase : word.
  (** the run's WHOLE input, as AsanInit's Section takes it *)
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  Hypothesis Hlaunch : valid_launch inp.             (* from valid_input *)
  Hypothesis Hrdr : in_channel_reader inp = true.    (* from valid_input *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.  (* valid_entry's fifth conjunct *)

  #[local] Notation apc := Asan.M.init_pc.
  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).
  Variable LIM : Z.                       (* [comment removed for export] *)
  Hypothesis LIM_ge : 2 ^ 33 <= LIM.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM RZ (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS_asan KC0 BFUEL FUEL None (asan_init RZ) startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN LIM HS_asan SINV argH HOLES fs.

  Lemma asan_apc : Z.of_N apc = a_entry ASAN.
  Proof. reflexivity. Qed.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw LIM inp)
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG. pose proof asan_apc as Hapc.
    assert (AH : forall E a, argH E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; exact (argH0_high apc sp rdraw inp Hsp Hva E a H)).
    assert (AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a)
      by (intros E M a HS H; exact (argH0_high2 APH apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E M a HS H)).
    pose proof (argH0_agree sp rdraw inp) as AA.
    pose proof (SINV0_frame APH apc sp rdraw brk0 mbase inp) as SF.
    pose proof (SINV0_agree APH apc sp rdraw brk0 mbase inp) as SA.
    erewrite (init_cfg_eq ASEGS ASAN APH LIM) by first [exact Hapc | eassumption | exact IMG].
    (* the configuration [init_cfg_eq] gives, named from the goal *)
    lazymatch goal with |- srealizes _ (cfg_of _ ?R0' _ ?FULL0' ?model0') _ =>
      assert (HC : cs_ok ASEGS ASAN LIM SINV argH fs E0a (asan_init RZ) R0' FULL0' model0')
        by (unfold asan_init; eapply init_cs_ok; first [exact IMG | exact Hapc | exact LIM_ge | eassumption | (split; cbn; lia)])
    end.
    assert (XALL : forall x, x_stmt ASEGS ASAN NX0 LIM RZ SINV argH fs x).
    { intros x. eapply asan_node_x_sound_all;
        first [exact (fun E M H => H) | exact SF | exact SA | exact (le_n NX0) | eassumption | exact IMG]. }
    pose proof (check_sound ASEGS IT0 IT0_ok ASAN NX0 (le_n NX0) LIM RZ HS_asan (XNS ASEGS ASAN NX0 LIM) XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              ltac:(eapply (AsanNodesMmB.node_sys_sound ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              ltac:(eapply (AsanNodesMmB.node_brk2_sound ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              ltac:(eapply (node_mmap2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              ltac:(eapply (node_mmapin_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              ltac:(eapply (node_mprotect2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
              XALL
              (node_join_sound ASEGS ASAN NX0 LIM SINV argH fs)
              ltac:(eapply (XNS_sound ASEGS ASAN NX0 LIM SINV argH fs); asan_side)
              (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (asan_init RZ) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
