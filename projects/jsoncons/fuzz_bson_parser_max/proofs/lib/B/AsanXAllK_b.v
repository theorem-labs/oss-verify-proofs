(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed SINV, argH, asan_X_ALL; added Hlau, Hlaunch, Hrz and 15 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanXAllK.v, lines 23-39, 45-66. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK
  AsanInitK. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanNodesStartXK. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import AsanNodesStartXAsanK_b SumsAsanCloseK_b.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.

Section XAll.
Variable scfg : SpuriousCfg.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable rz : Z.              (* [comment removed for export] *)
  Variable fs : Fs.Fs.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     fifteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as the already-migrated [HandoffBridgeK.v:619-629]. *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  (* [Run.valid_input]'s exec-name conjunct and [Run.valid_entry]'s launch
     conjunct: [AsanNodesStartXAsanK]'s two scan nodes read the stack image the
     launch wrote, so they are premises here too. *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* [rz] stays this Section's free variable -- [SumsAsanCloseK]'s providers are
     uniform in it -- but [XPnScan] reads [e_str0 rz], so for the scan nodes it
     must be the flag the run's own kernel build carries.  This equation is what
     a caller discharges with [eq_refl]; it is not a restriction a proof could
     avoid, since a wrong flag puts the strings at the wrong address. *)
  Hypothesis Hrz : rz = rseq_z (kb_rseq (in_kernel INP)).

  #[local] Notation SINV :=
    (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH :=
    (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).

  Theorem asan_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 AsanInitK.LIMIT rz SINV argH fs x.
  Proof.
    rewrite Hrz.
    pose proof (argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva) as AH.
    pose proof (argH0_agree sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) as AA.
    pose proof (SINV0_frame APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc) as SF.
    pose proof (SINV0_agree APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc) as SA.
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
    - (* [comment removed for export] *) intros args cs cs' E R FULL model T HC HE H. cbn [node_x] in H. discriminate H.
  Qed.
End XAll.
