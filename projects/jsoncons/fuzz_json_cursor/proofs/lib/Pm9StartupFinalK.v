(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the rseq-dependent auxv, the launch input's kernel build): changed HS_sound, Hsp, Huid and 13 more; added B, Hapc, Hbrk and 26 more. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK
  Pm9DefsK Pm9PlanImagesK Pm9StartupK Pm9StartupClosedK Pm9HSK_0 Pm9HSK_1 Pm9HSK_201 Pm9HSK_202 Pm9MainTableK Pm9ResK Pm9CertK_root Pm9CertK_201 Pm9CertK_202.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.

Lemma IT0_ok : itab_sound ASEGS0 IT0.
Proof. apply APSK.mk_itab_ranges_sound. Qed.

(* THE SECTION'S PARAMETERS AND THE CERTIFICATES, old beside new.
     OLD  sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask
          abrt ifs urnd tmp0 (fs the plan's), Hseed; one certificate per stage:
          cert_root/_201/_202 : check ... LIM XN0 ... = COk shape_*.
     NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the
          input's filesystem, [fs] the plan's FS0); the plan is certified once PER
          CONFIG_RSEQ FLAG ([cert_* : forall b, check ... (rseq_z b) ... = COk (shape_* b)],
          an earlier port's Pm9CertK_* interface), and this file takes the certificate
          at the launch's own flag [B].  So the hand-off table [HS_as0 B] is the run's. *)
Section Final.
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
  Hypothesis Hseed : fs_seed_tmp ifs tmp0 = fs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation LIM := AsanInitK.LIMIT.
  (* the launch's CONFIG_RSEQ flag; [rseq_z B] is the [RZ] Pm9StartupK/ClosedK read *)
  #[local] Notation B := (kb_rseq (in_kernel INP)).

  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (HS_as0 B) SINV argH (HOLES T) fs.

  (* PROOF BODY ONLY; the three statements above are byte-identical to the pre-repair text.
     [vm_compute; reflexivity] runs the VM in the tactic and leaves a cast the kernel
     re-verifies at [Qed], so the fold over the whole pre-computed [shape_* b] literal is
     done twice.  [vm_cast_no_check] hands the kernel the VM reduction once; it is the
     idiom this unit already uses on the SAME literals at Pm9CertK_202.v:26-27 (and the
     _201 / _root twins).  Measured: a build round. *)
  Lemma ho_202 : forall b, hole_only (shape_202 b) = true.   Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma ho_201 : forall b, hole_only (shape_201 b) = true.   Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma ho_root : forall b, hole_only (shape_root b) = true. Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma J202_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (JS_as0_201 B) SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_201 in Hh.
    destruct (Nat.eqb_spec h 202) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    pose proof IT0_ok. pose proof (cert_202 B) as C. pose proof (ho_202 B) as HO.
    unfold HOLES. eapply as0_stage_hole with (HS := HS_as0 B); eassumption.
  Qed.

  Lemma J201_sound : holes_stmt ASEGS0 scfg ASAN0 LIM (JS_as0_root B) SINV argH (HOLES T) fs.
  Proof.
    intros h c Hh E R FULL model HC. unfold JS_as0_root in Hh.
    destruct (Nat.eqb_spec h 201) as [->|_]; [|discriminate Hh]. injection Hh as <-.
    pose proof IT0_ok. pose proof J202_sound. pose proof (cert_201 B) as C. pose proof (ho_201 B) as HO.
    unfold HOLES. eapply as0_stage_hole with (HS := JS_as0_201 B); eassumption.
  Qed.

  (* STATEMENT CHANGED, old beside new, as [Pm9StartupClosedK.as0_startup_hole_c]:
       OLD  init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM (inp ... tmp0)
       NEW  init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM INP, over [apc]/[Hapc]. *)
  Theorem as0_startup_closed :
    srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM INP) (T fs).
  Proof.
    pose proof IT0_ok. pose proof J201_sound. pose proof (cert_root B) as C. pose proof (ho_root B) as HO.
    eapply as0_startup_hole_c with (HS := JS_as0_root B); eassumption.
  Qed.
End Final.
