(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed BFUEL, FUEL, HS and 35 more; added Hapc, Hlau, Hlaunch and 8 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9StartupClosedK.v, lines 38-51, 61-64, 69-72, 82-86, 91, 98-108. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
  AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK Pm5PlanImagesK AsanInitK
  AsanNodesExtraDefsK AsanNodesExtraK Pm5StartupK Pm5AsanXAllK Pm5AsanAddrIsInMemWalkK Pm5AsanMaxVAWalkK.
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

(* THE SECTIONS' PARAMETERS, old beside new.
     OLD  sp brk0 rdraw argv envp uid hw fs (+ the input's remaining fields in
          ClosedStartup), SINV0/argH0 at their eight/seven-place closures.
     NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the
          input's filesystem, [fs] the plan's FS0); the checker and [x_stmt] read the
          run's CONFIG_RSEQ flag [RZ] (AsanPlanK / AsanPlanSoundK at an earlier revision).
     Pm5StartupK's and Pm5AsanXAllK's Section lemmas are generalised over only what
     their proofs read, so they are called here by [eapply ...; eassumption]. *)
Section Closed.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
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

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation LIM := AsanInitK.LIMIT.
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).

  Lemma as0_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM RZ SINV argH fs x.
  Proof. eapply asan_X_ALL; eassumption. Qed.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.

  (* STATEMENT CHANGED, old beside new: the checker reads the launch's flag.
       OLD  check ASEGS0 IT0 ASAN0 NX0 LIM XN0 ... cs0 p = COk s
       NEW  check ASEGS0 IT0 ASAN0 NX0 LIM RZ XN0 ... cs0 p = COk s *)
  Theorem as0_stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM RZ XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
  Proof.
    exact (stage_hole scfg Halloc as0_AIMW as0_SMEARW sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc fs
             Hsp Hva RZ IT0 IT0_ok HS T T_nil HS_sound as0_X_ALL KC0 BFUEL FUEL).
  Qed.

  Hypothesis Hseed : fs_seed_tmp ifs tmp0 = fs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert :
    check ASEGS0 IT0 ASAN0 NX0 LIM RZ XN0 XE0 XB0 HS KC0 BFUEL FUEL None (asan0_init RZ) startup_plan = COk startup_shape.
  Hypothesis startup_ho : hole_only startup_shape = true.

  (* STATEMENT CHANGED, old beside new, as [Pm5StartupK.as0_startup_hole]:
       OLD  init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM (inp ... tmp0)
       NEW  init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM INP, over [apc]/[Hapc]. *)
  Theorem as0_startup_hole_c :
    srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM INP) (T fs).
  Proof.
    pose proof as0_AIMW. pose proof as0_SMEARW. pose proof as0_X_ALL.
    eapply as0_startup_hole; eassumption.
  Qed.
End Closed.

(* [comment removed for export] *)
