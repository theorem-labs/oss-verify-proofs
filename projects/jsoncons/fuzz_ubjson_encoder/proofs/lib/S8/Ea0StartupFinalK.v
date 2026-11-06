(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK
  Ea0DefsK Ea0PlanImagesK Ea0StartupK Ea0StartupClosedK Ea0HSK_0 Ea0HSK_1 Ea0HSK_201 Ea0HSK_202 Ea0MainTableK Ea0ResK Ea0CertK_root Ea0CertK_201 Ea0CertK_202.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.

Lemma IT0_ok : itab_sound ASEGS0 IT0.
Proof. apply APSK.mk_itab_ranges_sound. Qed.

Section Final.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
  Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
  Variables nofile sigmask : word. Variable abrt : bool. Variable ur : InputStream.
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS_as0 SINV argH (HOLES T) fs.

  Lemma J202_sound : holes_stmt ASEGS0 scfg ASAN0 LIM JS_as0_201 SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_201 in Hh.
    destruct (Nat.eqb_spec h 202) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit IT0 IT0_ok HS_as0 T T_nil HS_sound KC0 BFUEL FUEL
             planK_202 HS_202 shape_202 cert_202 eq_refl E R FULL model HC).
  Qed.

  Lemma J201_sound : holes_stmt ASEGS0 scfg ASAN0 LIM JS_as0_root SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_root in Hh.
    destruct (Nat.eqb_spec h 201) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit IT0 IT0_ok JS_as0_201 T T_nil J202_sound KC0 BFUEL FUEL
             planK_201 HS_201 shape_201 cert_201 eq_refl E R FULL model HC).
  Qed.

  Theorem as0_startup_closed :
    srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (T fs).
  Proof.
    exact (as0_startup_hole_c scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur
             Hsp Hbrk Hva Hve Hfit Huid Hhw IT0 IT0_ok JS_as0_root T T_nil J201_sound KC0 BFUEL FUEL
             planK_root shape_root cert_root eq_refl).
  Qed.
End Final.
