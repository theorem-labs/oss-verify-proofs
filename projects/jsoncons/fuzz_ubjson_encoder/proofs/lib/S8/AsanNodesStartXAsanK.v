(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanNodesStartXAsanK.v, lines 33-46, 55-67, 72-76, 85-88, 98-101, 107-115. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ea0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Asan_code_startxK.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
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
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     fifteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as the already-migrated [HandoffBridgeK.v:619-629]; [mbase] and [stdin]
     this Section already had. *)
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

  (* the launch this instance runs under, and its CONFIG_RSEQ flag: [x_stmt]
     carries the flag since the auxv's size decides where the strings sit, and
     [XPnScan] reads [e_str0] of it, so it is the run's own flag and not a free
     parameter.  [Hlaunch]/[Hlau] are [AsanNodesStartXInitK]'s premises. *)
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
                W_119900 W_119904 W_119908
                ltac:(cbn [x_envscan x_envscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_119900) (fetch_lit _ _ _ _ eq_refl F_119904) (fetch_lit _ _ _ _ eq_refl F_119908)
                ltac:(repeat split; reflexivity)
                D_119900 D_119904 D_119908
                sp rdraw brk0 mbase argv envp fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc FS0
                Hsp Hva Hve uid hw Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
                W_1199bc W_1199c0 W_1199c4 W_1199c8 W_1199cc
                ltac:(cbn [x_pnscan x_pnscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1199bc) (fetch_lit _ _ _ _ eq_refl F_1199c0) (fetch_lit _ _ _ _ eq_refl F_1199c4)
                (fetch_lit _ _ _ _ eq_refl F_1199c8) (fetch_lit _ _ _ _ eq_refl F_1199cc)
                ltac:(repeat split; reflexivity)
                D_1199bc D_1199c0 D_1199c4 D_1199c8 D_1199cc
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
