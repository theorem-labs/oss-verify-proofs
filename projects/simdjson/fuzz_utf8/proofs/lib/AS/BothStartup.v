(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed AA, AH, AH2 and 18 more; added Hapc, Hlau, Hlaunch and 7 more; removed Hfit, abt, argv and 11 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
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
Lemma both_maxva_code : forall i, (i < 45)%nat ->
  fetch_word BSEGS (Z_to_bv 64 (x_maxva BOTH + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva BOTH].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma both_maxva_range : 0 < x_maxva BOTH /\ x_maxva BOTH + 180 < 2 ^ 64.
Proof. cbn [x_maxva BOTH]. lia. Qed.

(* [comment removed for export] *)
Section XAll.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Theorem both_node_x_sound_all : forall x,
    x_stmt BSEGS BOTH nx0 AsanInit.LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 x.
  Proof.
    assert (AH : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; exact (argH0_high apc sp rdraw inp Hsp Hva E a H)).
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a)
      by reflexivity.
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (node_x_sound_XEnvScan_asan_gen apc sp rdraw brk0 mbase inp FS0); assumption.
    - apply (node_x_sound_XPnScan_asan_gen apc sp rdraw brk0 mbase inp FS0); assumption.
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva BSEGS BOTH nx0 AsanInit.LIMIT _ SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
  Qed.
End XAll.

(* the image facts a launch of the ASan+UBSan image discharges by computation *)
Lemma both_apc : Z.of_N AsanUbsan.M.init_pc = a_entry BOTH.
Proof. vm_compute. reflexivity. Qed.
Lemma both_resx : (2 <= n_resx BOTH)%nat /\ (20 <= p_resx BOTH)%nat.
Proof. split; vm_compute; lia. Qed.

Local Ltac both_side :=
  first [ exact both_wx | exact both_in_hull | exact both_res_len | exact both_res_hull | exact both_hull_ok
        | exact both_shadow_ok | exact both_hull_cov | exact both_img_facts | exact both_apc | exact both_resx
        | exact (fun E M H => H) | apply le_n | eassumption ].

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  (** the run's WHOLE input (the model's [theories/Common/AsanInit.v] design) *)
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  (** the run's CONFIG_RSEQ flag as the plan's 0 or 1 *)
  Let RZ : Z := rseq_z (kb_rseq (in_kernel inp)).
  #[local] Notation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0b : itab.
  Hypothesis IT0b_ok : itab_sound BSEGS IT0b.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan_both : plan.
  Variable startup_shape_both : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert_both :
    check BSEGS IT0b BOTH NX0 LIM RZ (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None (both_init RZ) startup_plan_both = COk startup_shape_both.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS BOTH LIM HS_both SINV argH HOLES (in_fs inp).

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. exact (argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva E a H). Defined.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS H. exact (argH0_high2 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E M a HS H). Defined.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. reflexivity. Defined.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. exact (SINV0_frame BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp E M M' Hf HS). Defined.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag HS. exact (SINV0_agree BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp E E' M Hag HS). Defined.

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp)
              (sd HOLES t_nil E0a (in_fs inp) startup_shape_both).
  Proof.
    rewrite (init_cfg_eq BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp both_apc).
    pose proof (init_cs_ok BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp both_img_facts both_apc
                  Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau Hhw both_resx) as HC.
    pose proof (check_sound BSEGS IT0b IT0b_ok BOTH NX0 (le_n NX0) LIM RZ HS_both (XNS BSEGS BOTH NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil (in_fs inp) KC0
              ltac:(eapply (AsanNodesMmB.node_sys_sound BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              ltac:(eapply (AsanNodesMmB.node_brk2_sound BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              ltac:(eapply (node_mmap2_sound_OBL BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              ltac:(eapply (node_mmapin_sound_OBL BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              ltac:(eapply (node_mprotect2_sound_OBL BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH (in_fs inp))
              ltac:(eapply (both_node_x_sound_all AsanUbsan.M.init_pc sp rdraw brk0 mbase inp (in_fs inp)); both_side)
              (node_join_sound BSEGS BOTH NX0 LIM SINV argH (in_fs inp))
              ltac:(eapply (XNS_sound BSEGS BOTH NX0 LIM SINV argH (in_fs inp)); both_side)
              (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan_both (both_init RZ) startup_shape_both startup_cert_both
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
