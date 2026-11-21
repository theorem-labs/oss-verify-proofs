(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed SINV_SINV0, SINV_frame, argv and 15 more; added Hapc, Hbrk, Hhw and 24 more; removed FS0; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8AsanNodesStartXAsanK.v, lines 21-59, 64-89. *)
(* [comment removed for export] *)
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
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4PlanImagesK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK Pm4_code_140000_141000.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Section AsanInstance.
Variable scfg : SpuriousCfg.
  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 mbase rdraw argv envp fs stdin FS0 uid hw, with Hsp Hva Hve Hfit;
            SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw;
            x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 x.
       NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the
            input's filesystem, [fs] the plan's FS0, which was [FS0] here); [x_stmt]
            takes the run's CONFIG_RSEQ flag [RZ] after [LIMIT] (AsanPlanSoundK at
            an earlier revision).  [AsanNodesStartXInitK]'s lemmas are generalised over only the
            variables and hypotheses their proofs read, so they are called by [eapply]
            with the image facts offered by [ximg], never positionally. *)
  Variable rz : Z.
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
  #[local] Notation SINVI := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).

  Local Ltac ximg :=
    solve [ eassumption | exact Asan0_wx_nowrap | exact asan0_in_hull | exact asan0_hull_ok | exact asan0_img_facts
          | cbn [x_envscan x_envscan_k x_pnscan x_pnscan_k ASAN0]; lia
          | exact (fetch_lit _ _ _ _ eq_refl F_140f18) | exact (fetch_lit _ _ _ _ eq_refl F_140f1c) | exact (fetch_lit _ _ _ _ eq_refl F_140f20)
          | exact (fetch_lit _ _ _ _ eq_refl F_140fd4) | exact (fetch_lit _ _ _ _ eq_refl F_140fd8) | exact (fetch_lit _ _ _ _ eq_refl F_140fdc)
          | exact (fetch_lit _ _ _ _ eq_refl F_140fe0) | exact (fetch_lit _ _ _ _ eq_refl F_140fe4)
          | exact D_140f18 | exact D_140f1c | exact D_140f20
          | exact D_140fd4 | exact D_140fd8 | exact D_140fdc | exact D_140fe0 | exact D_140fe4
          | repeat split; reflexivity ].

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINVI E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV argH fs XEnvScan.
    Proof. eapply (init_x_sound_envscan ASEGS0 scfg ASAN0 APH0); ximg. Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV argH fs XPnScan.
    Proof. eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0); ximg. Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINV argH fs XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Local Ltac sinv0 :=
    solve [ eassumption | exact (fun E M H => H)
          | exact (SINV0_frame APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc)
          | exact (SINV0_agree APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc) ].

  Theorem node_x_sound_XEnvScan_asan : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINVI argH fs XEnvScan.
  Proof. eapply node_x_sound_XEnvScan_asan_gen; sinv0. Qed.

  Theorem node_x_sound_XPnScan_asan : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINVI argH fs XPnScan.
  Proof. eapply node_x_sound_XPnScan_asan_gen; sinv0. Qed.

  Theorem node_x_sound_XLayout_asan : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT RZ SINVI argH fs XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
