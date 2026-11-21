(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: threads launch-record variables (gid, groups, kb, execfn, apc, mbase) and Hlaunch/Hlau hypotheses through the node_x_sound_XEnvScan/XPnScan/XLayout asan theorems, now stated as plain x_stmt with an rseq RZ argument, replacing encoded TCodec statements; the launch input takes its SIGPIPE disposition as a variable sdf; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanNodesStartXAsanKB0.v, lines 39-47, 60-68, 73-77, 86-89, 99-102, 107-116. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.
Section AsanInstance.
Variable scfg : SpuriousCfg.
Variable sp brk0 mbase : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
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
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Variable uid : word.
Variable hw : word.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Notation INP :=
(AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
#[local] Notation ARGH :=
(argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation SINV0A :=
(SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
Section AnySINV.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0A E M.
Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XEnvScan.
Proof.
eapply (init_x_sound_envscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
(ltac:(oW' 0x114cb0%Z)) (ltac:(oW' 0x114cb4%Z)) (ltac:(oW' 0x114cb8%Z))
ltac:(cbn [x_envscan x_envscan_k ASAN0]; lia)
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114cb0%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114cb4%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114cb8%Z)))
ltac:(repeat split; reflexivity)
(ltac:(oD' 0x114cb0%Z)) (ltac:(oD' 0x114cb4%Z)) (ltac:(oD' 0x114cb8%Z))
sp rdraw brk0 mbase argv envp fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc FS0
Hsp Hva Hve uid hw Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame).
Qed.
Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XPnScan.
Proof.
eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
(ltac:(oW' 0x114d6c%Z)) (ltac:(oW' 0x114d70%Z)) (ltac:(oW' 0x114d74%Z)) (ltac:(oW' 0x114d78%Z)) (ltac:(oW' 0x114d7c%Z))
ltac:(cbn [x_pnscan x_pnscan_k ASAN0]; lia)
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114d6c%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114d70%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114d74%Z)))
(fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114d78%Z))) (fetch_lit _ _ _ _ eq_refl (ltac:(oF' 0x114d7c%Z)))
ltac:(repeat split; reflexivity)
(ltac:(oD' 0x114d6c%Z)) (ltac:(oD' 0x114d70%Z)) (ltac:(oD' 0x114d74%Z)) (ltac:(oD' 0x114d78%Z)) (ltac:(oD' 0x114d7c%Z))
sp rdraw brk0 mbase argv envp fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc FS0
Hsp Hva Hve uid hw Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame SINV_agree).
Qed.
Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XLayout.
Proof. apply x_sound_layout. Qed.
End AnySINV.
Theorem node_x_sound_XEnvScan_asan :
x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV0A ARGH FS0 XEnvScan.
Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.
Theorem node_x_sound_XPnScan_asan :
x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV0A ARGH FS0 XPnScan.
Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.
Theorem node_x_sound_XLayout_asan :
x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV0A ARGH FS0 XLayout.
Proof. apply x_sound_layout. Qed.
End AsanInstance.
