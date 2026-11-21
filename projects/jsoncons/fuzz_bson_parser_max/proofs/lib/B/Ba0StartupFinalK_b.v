(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed HS_sound, Hsp, J201_sound and 4 more; added Hlau, Hlaunch, INP and 4 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0StartupFinalK.v, lines 27-31, 36-39, 46-49, 54-58, 63-72. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
  From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b Ba0StartupK_b Ba0StartupClosedK_b Ba0ResK_b Ba0CertK_root_b Ba0CertK_201_b Ba0CertK_202_b.
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
  Variables nofile sigmask : word. Variable abrt : bool. Variable ur : InputStream.  (* [comment removed for export] *)
  (* The kernel build and the exec file name are the two places of
     [State.mkProcInput_full] this cone leaves free; see [AsanInitK.inp]. *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0. Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
  #[local] Notation INP := (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  (* ported premises, as in [Ba0StartupClosedK_b] *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the run's own CONFIG_RSEQ flag, 0 or 1, at which every certificate is used *)
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf AsanUbsan.M.init_pc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation LIM := AsanInitK.LIMIT.
  (* [comment removed for export] *)
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (HS_as0 RZ) SINV argH (HOLES T) fs.

  (* [comment removed for export] *)
  Lemma J202_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (JS_as0_201 RZ) SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_201 in Hh.
    destruct (Nat.eqb_spec h 202) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf AsanUbsan.M.init_pc RZ
             Hsp Hva Hve Hfit Hlaunch Hlau eq_refl IT0 IT0_ok (HS_as0 RZ) T T_nil HS_sound KC0 BFUEL FUEL
             planK_202_k (HS_202 RZ) shape_202 (cert_202 RZ (rseq_z_range _)) eq_refl E R FULL model HC).
  Qed.
  (* [comment removed for export] *)
  Lemma J201_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (JS_as0_root RZ) SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_root in Hh.
    destruct (Nat.eqb_spec h 201) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    exact (as0_stage_hole scfg Halloc sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf AsanUbsan.M.init_pc RZ
             Hsp Hva Hve Hfit Hlaunch Hlau eq_refl IT0 IT0_ok (JS_as0_201 RZ) T T_nil J202_sound KC0 BFUEL FUEL
             planK_201_k (HS_201 RZ) shape_201 (cert_201 RZ (rseq_z_range _)) eq_refl E R FULL model HC).
  Qed.

  Theorem as0_startup_closed :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM INP) (T fs).
  Proof.
    exact (as0_startup_hole_c scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf RZ
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau eq_refl IT0 IT0_ok (JS_as0_root RZ) T T_nil J201_sound KC0 BFUEL FUEL
             planK_root_k shape_root (cert_root RZ (rseq_z_range _)) eq_refl).
  Qed.
End Final.
