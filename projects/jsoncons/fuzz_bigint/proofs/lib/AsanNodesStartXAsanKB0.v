(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the start-up node instances take the full launch input with its launch facts (valid_launch, entry_launch_ok_va) and the run's CONFIG_RSEQ flag. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Bo0PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK Asan_code_startxKB0.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Section AsanInstance.
Variable scfg : SpuriousCfg.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     sixteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as [HandoffBridgeK.v:614-624]; [mbase] and [stdin] are declared earlier
     in this Section. *)
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variables abrt sdf : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable apc : N.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  (* the launch this instance runs under, and its CONFIG_RSEQ flag: [x_stmt]
     carries the flag since the auxv's size decides where the strings sit, and
     [XPnScan] reads [e_str0] of it, so it is the run's own flag and not a free
     parameter.  [Hlaunch]/[Hlau] are [AsanNodesStartXInitK]'s premises. *)
  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
  #[local] Notation ARGH :=
    (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation SINV0A :=
    (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn apc).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0A E M.
    Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
                W_bd694 W_bd698 W_bd69c
                ltac:(cbn [x_envscan x_envscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bd694) (fetch_lit _ _ _ _ eq_refl F_bd698) (fetch_lit _ _ _ _ eq_refl F_bd69c)
                ltac:(repeat split; reflexivity)
                D_bd694 D_bd698 D_bd69c
                sp rdraw brk0 mbase argv envp fs stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc FS0
                Hsp Hva Hve uid hw Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
                W_bd750 W_bd754 W_bd758 W_bd75c W_bd760
                ltac:(cbn [x_pnscan x_pnscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bd750) (fetch_lit _ _ _ _ eq_refl F_bd754) (fetch_lit _ _ _ _ eq_refl F_bd758)
                (fetch_lit _ _ _ _ eq_refl F_bd75c) (fetch_lit _ _ _ _ eq_refl F_bd760)
                ltac:(repeat split; reflexivity)
                D_bd750 D_bd754 D_bd758 D_bd75c D_bd760
                sp rdraw brk0 mbase argv envp fs stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc FS0
                Hsp Hva Hve uid hw Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV ARGH FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
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
