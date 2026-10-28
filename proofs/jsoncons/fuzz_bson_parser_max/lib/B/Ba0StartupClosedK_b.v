(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
  AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanInitK
  AsanNodesExtraDefsK AsanNodesExtraK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0StartupK_b AsanXAllK_b AsanAddrIsInMemWalkK_b AsanMaxVAWalkK_b.
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
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Lemma as0_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
  Proof. exact (asan_X_ALL scfg sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit). Qed.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.

  (* [comment removed for export] *)
  Theorem as0_stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
  Proof.
    exact (stage_hole scfg Halloc as0_AIMW as0_SMEARW sp brk0 rdraw argv envp uid hw fs Hsp Hva IT0 IT0_ok HS T T_nil HS_sound as0_X_ALL KC0 BFUEL FUEL).
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
  Variable abrt : bool. Variable ur : InputStream.  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
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
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None asan0_init startup_plan = COk startup_shape.
  Hypothesis startup_ho : hole_only startup_shape = true.

  Theorem as0_startup_hole_c :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (T fs).
  Proof.
    eapply (as0_startup_hole scfg Halloc as0_AIMW as0_SMEARW); try eassumption.
    exact (as0_X_ALL scfg sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit).
  Qed.
End ClosedStartup.
