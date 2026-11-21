(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the closed start-up takes the full launch input that AsanInitK's start state reads with the launch facts (valid_launch, entry_launch_ok_va), the run's CONFIG_RSEQ flag (rz, tied to the kernel build by Hrz) and the image's entry pc. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
  AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK As0PlanImagesK AsanInitK
  AsanNodesExtraDefsK AsanNodesExtraK As0StartupK AsanXAllK AsanAddrIsInMemWalkK AsanMaxVAWalkK.
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Lemma as0_AIMW : aim_spec ASEGS0 AIM_ASAN0.
Proof. exact asan_addrisinmem. Qed.

Lemma as0_maxva_entry_eq : Z_to_bv 64 X_MAXVA_ASAN0 = asan_maxva_entry.
Proof. apply bv_eq. reflexivity. Qed.

Lemma as0_SMEARW : forall (mem rom : word -> option byte) regs (x : word),
    getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
    exists regs',
      msteps ASEGS0 (mkst regs (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 0) mem rom) (mkst regs' (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 180) mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
      /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
      /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.
Proof.
  intros mem rom regs x Hx Hr. rewrite as0_maxva_entry_eq. rewrite at_0. exact (asan_smearva mem rom regs x Hx Hr).
Qed.

Section Closed.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0] discharge all
     sixteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as [HandoffBridgeK.v:614-624]. *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variables abrt sdf : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable apc : N.
  (* the run's CONFIG_RSEQ flag as 0 or 1: [AsanPlanK]'s slot 6 ([AsanPlanK.v:34])
     and [APSK.x_stmt]'s, since the auxv's size decides where the strings sit.
     Free here, as in [As0StartupK]'s [Section Stage]; a certificate is checked
     at one literal value, and that join is not closed in this file. *)
  Variable rz : Z.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  (* [Run.valid_entry_va]'s fifth conjunct ([727298f3:theories/LinuxProcessSem/Run.v:3750],
     [valid_entry_sv48] :3767) and a conjunct of [Run.valid_input_either] (:4703): both are in the
     published binder of this unit's top, so they are not new
     assumptions. *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* [XPnScan] reads [e_str0 rz], so at the [x_stmt] boundary the flag must be
     the one the run's own kernel build carries.  A caller discharges this with
     [eq_refl]; it does not close the free-[rz]-to-certificate-literal join. *)
  Hypothesis Hrz : rz = rseq_z (kb_rseq (in_kernel INP)).

  #[local] Notation SINV :=
    (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn apc).
  #[local] Notation argH :=
    (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Lemma as0_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM rz SINV argH fs x.
  Proof.
    exact (asan_X_ALL scfg sp brk0 rdraw argv envp uid hw rz fs
             mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc
             Hsp Hva Hve Hfit Hlaunch Hlau Hrz).
  Qed.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.

  (* [comment removed for export] *)
  Theorem as0_stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM rz XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
  Proof.
    exact (stage_hole scfg Halloc as0_AIMW as0_SMEARW sp brk0 rdraw argv envp uid hw fs
             mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc rz
             Hsp Hva IT0 IT0_ok HS T T_nil HS_sound as0_X_ALL KC0 BFUEL FUEL).
  Qed.
End Closed.

(* [comment removed for export] *)
Section ClosedStartup.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variables abrt sdf : bool. Variable ur : InputStream.
  (* The kernel build, the exec file name and [sdf] above are the three places of
     [State.mkProcInput_full] this cone leaves free; see [AsanInitK.inp]. *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  (* the run's CONFIG_RSEQ flag, free as in [Section Closed] above *)
  Variable rz : Z.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  (* the launch premises, as in [Section Closed] *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrz : rz = rseq_z (kb_rseq (in_kernel INP)).

  (* [apc] is the image's ELF entry, the literal [Asan.M.init_pc], exactly as
     [As0StartupK]'s [Section Startup] instantiates it. *)
  #[local] Notation SINV :=
    (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn Asan.M.init_pc).
  #[local] Notation argH :=
    (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert :
    check ASEGS0 IT0 ASAN0 NX0 LIM rz XN0 XE0 XB0 HS KC0 BFUEL FUEL None (asan0_init rz) startup_plan = COk startup_shape.
  Hypothesis startup_ho : hole_only startup_shape = true.

  Theorem as0_startup_hole_c :
    srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw LIM INP)
              (T fs).
  Proof.
    eapply (as0_startup_hole scfg Halloc as0_AIMW as0_SMEARW); try eassumption;
      (* [Hapc]: the image's ELF entry, by computation *)
      try reflexivity.
    exact (as0_X_ALL scfg sp brk0 rdraw argv envp uid hw fs
             mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn Asan.M.init_pc rz
             Hsp Hva Hve Hfit Hlaunch Hlau Hrz).
  Qed.
End ClosedStartup.
