(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed SINV, argH, argv and 8 more; added Hapc, Hbrk, Hhw and 21 more; internal commit ids in comments replaced by public commits or removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK
  AsanInitK Pm9DefsK Pm9PlanImagesK AsanNodesStartXK Pm9AsanNodesStartXAsanK Pm9SumsAsanCloseK.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.

Section XAll.
Variable scfg : SpuriousCfg.
  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva Hve Hfit;
            SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw;
            x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH fs x.
       NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order, so
            [SINV0]/[argH0] are instantiated at every place [AsanInitK] abstracts them
            over; and [x_stmt] takes the run's CONFIG_RSEQ flag [RZ] after [LIMIT]
            (AsanPlanSoundK).  [ifs] is the input's filesystem, [fs]
            the plan's FS0. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* Only the hypotheses a proof reads enter its arity, so consumers call
     [asan_X_ALL] by [eapply ...; eassumption], never positionally. *)
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).

  Theorem asan_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 AsanInitK.LIMIT RZ SINV argH fs x.
  Proof.
    pose proof (argH0_high sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc Hsp Hva) as AH.
    pose proof (argH0_agree sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf) as AA.
    pose proof (SINV0_frame APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc) as SF.
    pose proof (SINV0_agree APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc) as SA.
    pose proof e_sp0_init as EI.
    intros [ | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; eassumption.
    - eapply asan_node_x_sound_XIMemcpy; eassumption.
    - eapply asan_node_x_sound_XMemset; eassumption.
    - eapply asan_node_x_sound_XMemcpy; eassumption.
    - eapply asan_node_x_sound_XMemIsZero; eassumption.
    - eapply node_x_sound_XEnvScan_asan; eassumption.
    - eapply node_x_sound_XPnScan_asan; eassumption.
    - apply x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; eassumption.
    - eapply asan_node_x_sound_XPopFree; eassumption.
    -   intros args cs cs' E R FULL model T HC HE H. cbn [node_x] in H. discriminate H.
  Qed.
End XAll.
