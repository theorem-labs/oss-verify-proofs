(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the sections take the whole process input, entry pc and mmap base with the launch premises in place of argv, envp, uid, hwcap and the other input fields; x_stmt_XSniff_vacuous, the SINV_frame hypothesis and asan_startup written out in plain text from their encodings; the node statements and the startup certificate take the CONFIG_RSEQ flag; new lemmas run_sp0_ok, run_argH_high and run_SINV_sp and tactic asan_close; asan_node_x_sound_all is now the NX0 instance of asan_node_x_sound_allN; asan_startup's proof adds the munmap2 node and discharges init_cs_ok's vDSO-ledger premise by HRESX_BOTH; the proofs follow the bzip2 unit's copy of this file; the encoding table and its imports removed). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit
  AsanExtNodes AsanNoReplaceNode AsanExtNodesSound
  AsanNodesAux AsanNodesIface AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import SumsAsanClose AsanNodesStartXAsan Asan_code_startx.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(** #108 (LPS 75d69e00): the start-up layer on AsanInit's whole-input Section (apc sp rdraw brk0
    mbase inp, the launch hypotheses) and the plan's CONFIG_RSEQ flag [RZ := rseq_z (kb_rseq
    (in_kernel inp))] (UNIT: the flag as 0/1).  Shape from the bzip2/bzip2_compress_target
    unit's K/AS/AsanStartup.v (XAll: statement
    and proof shape); bzip2's Startup section is empty, so [asan_startup] is mbedtls' own proof with
    its old statement written out (it was encoded, CDefT.buildp) over the new arities, not re-encoded.
    mbedtls' own design kept (this port's ruling): the ceiling [bv_unsigned sp] in every statement,
    the three-clause [SINV_frame], [SINV_sp].  Certificates stay HYPOTHESES here
    ([startup_cert] over [s1_check RZ ..]); the split on [kb_rseq] happens where they are discharged,
    on closed goals (the settled shape TWO). *)

(** the empty emit table (unchanged) *)
Lemma XE0_sound : forall SEGS A nx0 LIMIT SP0 SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SP0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.

Definition XN_A_STMT (SP0 : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs) : Prop :=
  ext_stmt ASEGS BOTH NX0 ALIMIT (XN_A NX0) SP0 SINV argH FS0.
Definition XB_A_STMT (SP0 : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs) : Prop :=
  ext2_stmt ASEGS BOTH NX0 ALIMIT XB_A SP0 SINV argH FS0.

(* Was encoded (CDefT.buildp) over [x_stmt]'s old arity; written out from its decode with #108's [rz]. *)
Lemma x_stmt_XSniff_vacuous : forall (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT rz SP0 : Z)
    (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs),
  x_sniff A = 0 -> x_stmt SEGS A nx0 LIMIT rz SP0 SINV argH FS0 XSniff.
Proof.
  intros SEGS A nx0 LIMIT rz SP0 SINV argH FS0 H0 args cs cs' E R FULL model T HC Hpre Hn Hk.
  cbn [node_x] in Hn. rewrite H0 in Hn. cbn in Hn. discriminate Hn.
Qed.

(** close a closed AsanInit / StartXInit lemma's leftover Section hypotheses *)
Ltac asan_close := first [ eassumption | exact asan_img_facts | exact asan_wx | exact asan_in_hull
                         | exact asan_hull_ok | exact asan_hull_cov | exact asan_shadow_ok ].

(** the run's ceiling facts, from AsanInit (mbedtls' usp ceiling) *)
Section RunFacts.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  Lemma run_sp0_ok : APS.sp0_ok (bv_unsigned sp).
  Proof. unfold APS.sp0_ok. destruct Hsp as (H1 & H2 & _). split; assumption. Qed.

  Lemma run_argH_high : forall E (a : word), argH0 sp rdraw inp E a = true -> bv_unsigned sp <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; [asan_close .. | exact H]. Qed.

  Lemma run_SINV_sp : forall E M, SINV0 APH apc sp rdraw brk0 mbase inp E M -> APS.uE_sp0 E = bv_unsigned sp.
  Proof. intros E M H. eapply SINV0_sp; [asan_close .. | exact H]. Qed.
End RunFacts.

Section XAllN.
  Variable nx : nat.
  Hypothesis Hnx : (NX0 <= nx)%nat.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) ->
    (forall a : word, bv_unsigned sp <= bv_unsigned a -> M a <> None -> M' a <> None) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let RZ := rseq_z (kb_rseq (in_kernel inp)).
  Let SP0 := bv_unsigned sp.

  Lemma argH0_agreeN : forall E E' (a : word), env_agree nx E E' -> argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a.
  Proof. intros. reflexivity. Qed.
  Lemma SINV_agreeN : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag. apply SINV_agree. exact (env_agree_le _ _ _ _ Hag Hnx). Qed.

  Theorem asan_node_x_sound_allN : forall x,
    x_stmt ASEGS BOTH nx ALIMIT RZ SP0 SINV (argH0 sp rdraw inp) FS0 x.
  Proof.
    pose proof (run_sp0_ok sp Hsp) as SP0_ok.
    assert (AH : forall E (a : word), argH0 sp rdraw inp E a = true -> SP0 <= bv_unsigned a)
      by (intros E a H; eapply run_argH_high; [asan_close .. | exact H]).
    pose proof argH0_agreeN as AA. pose proof SINV_agreeN as SA.
    intros [ | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (asan_node_x_sound_XIMemcpy nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (asan_node_x_sound_XMemset nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (asan_node_x_sound_XMemcpy nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (asan_node_x_sound_XMemIsZero nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - eapply x_sound_envscan with (SEGS := ASEGS) (A := BOTH) (nx0 := nx) (LIMIT := ALIMIT) (rz := RZ)
        (SP0 := SP0) (SINV := SINV) (argH := argH0 sp rdraw inp) (FS0 := FS0)
        (ph := APH) (inp := inp) (mbase := mbase) (entry := Z_to_bv 64 (Z.of_N apc)) (sp := sp) (brk := brk0) (rdraw := rdraw)
        (we1 := W_dd408) (we2 := W_dd40c) (we3 := W_dd410)
        (Fe1 := fetch_lit _ _ _ _ eq_refl F_dd408) (Fe2 := fetch_lit _ _ _ _ eq_refl F_dd40c)
        (Fe3 := fetch_lit _ _ _ _ eq_refl F_dd410) (De1 := D_dd408) (De2 := D_dd40c) (De3 := D_dd410);
        first [ asan_close | exact SP0_ok | reflexivity | (cbn [x_envscan x_envscan_k BOTH]; lia)
              | (repeat split; reflexivity) | (eapply sp_lo; asan_close) | (eapply sp_hi; asan_close)
              | (intros E M HS; eapply run_SINV_sp; [asan_close .. | exact (SINV_SINV0 E M HS)])
              | (eapply SINV0_vals; asan_close) | (eapply SINV0_envp; asan_close) | (eapply SINV0_str0; asan_close) ].
    - eapply x_sound_pnscan with (SEGS := ASEGS) (A := BOTH) (nx0 := nx) (LIMIT := ALIMIT) (rz := RZ)
        (SP0 := SP0) (SINV := SINV) (argH := argH0 sp rdraw inp) (FS0 := FS0)
        (ph := APH) (inp := inp) (mbase := mbase) (entry := Z_to_bv 64 (Z.of_N apc)) (sp := sp) (brk := brk0) (rdraw := rdraw)
        (wp0 := W_dd4c4) (wp1 := W_dd4c8) (wp2 := W_dd4cc) (wp3 := W_dd4d0) (wp4 := W_dd4d4)
        (Fp0 := fetch_lit _ _ _ _ eq_refl F_dd4c4) (Fp1 := fetch_lit _ _ _ _ eq_refl F_dd4c8)
        (Fp2 := fetch_lit _ _ _ _ eq_refl F_dd4cc) (Fp3 := fetch_lit _ _ _ _ eq_refl F_dd4d0)
        (Fp4 := fetch_lit _ _ _ _ eq_refl F_dd4d4)
        (Dp0 := D_dd4c4) (Dp1 := D_dd4c8) (Dp2 := D_dd4cc) (Dp3 := D_dd4d0) (Dp4 := D_dd4d4);
        first [ asan_close | exact SP0_ok | exact AH | exact AA | exact SA | reflexivity
              | (cbn [x_pnscan x_pnscan_k BOTH]; lia) | (repeat split; reflexivity)
              | (eapply sp_lo; asan_close) | (eapply sp_hi; asan_close)
              | (intros E M HS; eapply run_SINV_sp; [asan_close .. | exact (SINV_SINV0 E M HS)])
              | (eapply SINV0_vals; asan_close) | (eapply SINV0_envp; asan_close) | (eapply SINV0_str0; asan_close) ].
    - apply x_sound_layout.
    - exact (asan_node_x_sound_XIStrncpy nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (asan_node_x_sound_XPopFree nx ALIMIT RZ SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply x_stmt_XSniff_vacuous. reflexivity.
  Qed.
End XAllN.

(** at [nx := NX0] *)
Definition asan_node_x_sound_all apc sp rdraw brk0 mbase inp FS0 :=
  asan_node_x_sound_allN NX0 (le_n _) apc sp rdraw brk0 mbase inp FS0.

Section Startup.
  (** the run: the whole input *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
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

  (** the certificate, as a hypothesis (discharged per [kb_rseq] on closed goals) *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check RZ IT0 HS_asan startup_plan = COk startup_shape.
  Hypothesis startup_guard : spin_guarded startup_plan = true.

  (** the holes *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS BOTH ALIMIT HS_asan SP0 SINV argH HOLES fs.

  (* Was an encoded statement (CDefT.buildp) over AsanInit's old 15-argument [inp]; written out from
     its decode (cdeft_print.py), not re-encoded, over the new arities: [init_config]'s entry pc is
     [apc], the input is [inp] whole, [E0 sp rdraw brk0 inp], the file system [in_fs inp]. *)
  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp)
      (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    pose proof (run_sp0_ok sp Hsp) as SP0_ok.
    assert (AH : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a)
      by (intros E a H; eapply run_argH_high; [asan_close .. | exact H]).
    pose proof (argH0_agree sp rdraw inp) as AA.
    assert (SF : forall E M M', (forall a, argH E a = true -> M' a = M a) ->
               (forall a : word, SP0 <= bv_unsigned a -> M a <> None -> M' a <> None) -> SINV E M -> SINV E M')
      by (intros E M M' H1 H2; eapply SINV0_frame; asan_close).
    assert (SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M)
      by (intros E E' M H1; eapply SINV0_agree; exact H1).
    assert (SS : forall E M, SINV E M -> uE_sp0 E = SP0)
      by (intros E M H; eapply run_SINV_sp; [asan_close .. | exact H]).
    pose proof (init_cfg_eq ASEGS BOTH APH apc sp rdraw brk0 mbase inp) as Ecfg.
    repeat (specialize (Ecfg ltac:(asan_close))).
    rewrite Ecfg.
    pose proof (init_cs_ok ASEGS BOTH APH apc sp rdraw brk0 mbase inp) as HC.
    repeat (specialize (HC ltac:(asan_close))).
    pose proof (node_ext_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs AA SA) as XN_sound.
    pose proof (node_noreplace_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS) as XB_sound.
    assert (XS : forall x, x_stmt ASEGS BOTH NX0 ALIMIT RZ SP0 SINV argH fs x)
      by (eapply asan_node_x_sound_all; first [ exact (fun E M H => H) | asan_close | exact SF | exact SA ]).
    pose proof (check_sound ASEGS IT0 IT0_ok BOTH NX0 ALIMIT RZ HS_asan (XN_A NX0) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0) as C1.
    pose proof (C1
              (AsanNodesMmB.node_sys_sound ASEGS BOTH NX0 ALIMIT SINV argH fs SP0 AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS BOTH NX0 ALIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (node_mmapin_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (node_mprotect2_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (node_munmap2_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (AsanNodesMmB.node_exit_sound ASEGS BOTH ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 XS (asan_node_x_sound0_all NX0 ALIMIT RZ SINV argH SP0 SP0_ok AH AA SF SA fs)) as C3.
    pose proof (C3 (node_join_sound ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 XN_sound (XE0_sound _ _ _ _ _ _ _ _) XB_sound HOLES_sound) as C5.
    pose proof (C5 FUEL BFUEL None startup_plan (both_init RZ) startup_shape) as C6.
    pose proof (C6 startup_cert startup_guard) as C7.
    exact (C7 _ _ _ _ t_nil (HC HRESX_BOTH) I eq_refl).
  Qed.
End Startup.
