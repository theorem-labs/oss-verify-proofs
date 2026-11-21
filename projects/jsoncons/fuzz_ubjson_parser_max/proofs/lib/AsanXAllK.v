(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: asan_X_ALL now takes launch-record variables (stdin, groups, kernel build, execfn, mbase, rz), valid_launch and entry_launch_ok_va hypotheses, and rebuilds SINV/argH over AsanInitK.inp with an rseq-dependent rz argument; the launch input takes its SIGPIPE disposition as a variable sdf; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanXAllK.v, lines 29-39, 45, 50-51, 57-66. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK
AsanInitK Ja0DefsK Ja0PlanImagesK AsanNodesStartXK AsanNodesStartXAsanK SumsAsanCloseK.
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
Variable rz : Z.
Variable fs : Fs.Fs.
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
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
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
- intros args cs cs' E R FULL model T HC HE H. cbn [node_x] in H. discriminate H.
Qed.
End XAll.
