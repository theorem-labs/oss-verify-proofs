(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the chain at LIMITH taken from MainBridgeBoth.v's both_main_bootL with the start-up certificates at the run's CONFIG_RSEQ value (startup_cert_h to startup2_cert_h) and the main entry's facts justified in the computed states (main_justified); both_main_boot_h over the launch's ProcInput with its kernel build, exec file name and SIGPIPE disposition; both_boot_R reads valid_input_either's 15 conjuncts and the 20-field ProcInput at the recorded kernel). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.zstd_frame_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothStartup StartupHS2Both BothBoot
  BothCertDefs BothStartupCertH BothStartupCertHB BothStartupCertHC BothStartupCertHD BothStartupCertH2
  RegsEqv0 SrzEqv MainExport MainFactsBoth MainEntryBoth MainBridgeBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section BridgeH.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable hw : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  (* the kernel build, the exec file name and the SIGPIPE disposition: the launch's own (LPS 727298f3) *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINH : forall ms mo,
    bmain_atL source_alloc_limit (mkEntry sp brk0 mbase rdraw) INP ms mo ->
    srealizes bsegs (mkCfg ms mo) T.

  (* both_main_bootL's premises are dispatched by their form; a certificate is matched by its itab *)
  Theorem both_main_boot_h :
    srealizes bsegs (init_config bsegs AsanUbsan.M.init_pc b_phdrs sp brk0 mbase rdraw source_alloc_limit INP) T.
  Proof.
    eapply both_main_bootL with (sp := sp) (brk0 := brk0) (mbase := mbase) (rdraw := rdraw) (argv := argv) (envp := envp)
      (fs := fs) (stdin := stdin) (uid := uid) (gid := gid) (groups := groups) (net := net) (nof := nof)
      (sigm := sigm) (hw := hw) (abt := abt) (urnd := urnd) (kb := kb) (execfn := execfn) (sdef := sdef)
      (LIM := AsanInit.LIMITH).
    all: lazymatch goal with
         | |- check _ IT0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact (startup_cert_h RZ (rseq_z_range (kb_rseq kb)))
         | |- check _ ITB _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact (startup_certB_h RZ (rseq_z_range (kb_rseq kb)))
         | |- check _ ITC _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact (startup_certC_h RZ (rseq_z_range (kb_rseq kb)))
         | |- check _ ITD _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact (startup_certD_h RZ (rseq_z_range (kb_rseq kb)))
         | |- check _ IT2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact (startup2_cert_h RZ (rseq_z_range (kb_rseq kb)))
         | |- _ => first [ exact (main_justified _ (rseq_z_range (kb_rseq kb))) | exact AsanInit.LIMITH_ge
                         | exact T_nil | exact MAINH | eassumption ]
         end.
  Qed.
End BridgeH.

(* [comment removed for export] *)
Theorem both_boot_R : forall en inp (T : TSet),
  valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> T [] ->
  (forall ms mo, bmain_atL source_alloc_limit en inp ms mo -> srealizes bsegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes bsegs (init_config bsegs b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof.
  intros [sp brk0 mbase rdraw] inp T Hv Hi Tnil MAINH.
  (* valid_input_either's conjuncts by shape (LPS 727298f3: 15 of them) *)
  pose proof Hi as (Hva & Hve & Hfs & _ & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _ & Hlaunch & Hrdr & Hspt & Hkern).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vasz urnd tmp kb execfn chrd sdef spt].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz, Hrdr, Hspt. cbn [in_kernel] in Hkern. subst vasz chrd spt.
  (* the input is AsanInit's launch input at the recorded kernel build: AsanInit's input seeds the
     run's /tmp into its file system and declares none, which is the same run (by conversion, as
     at main) *)
  rewrite Hkern in MAINH, Hlaunch, Hlau |- *.
  apply SpinAlg.realizes_of_srealizes.
  eapply both_main_boot_h with (sp := sp) (brk0 := brk0) (mbase := mbase) (rdraw := rdraw) (argv := argv) (envp := envp)
    (fs := fs_seed_tmp ifs tmp) (stdin := stdin) (uid := uid) (gid := gid) (groups := groups) (net := net) (nof := nof)
    (sigm := sigm) (hw := hw) (abt := abt) (urnd := urnd) (kb := kb) (execfn := execfn) (sdef := sdef);
    first [ exact Tnil | exact MAINH | eassumption ].
Qed.

Corollary both_boot_R_valid : forall en inp (T : TSet),
  valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input inp -> T [] ->
  (forall ms mo, bmain_atL source_alloc_limit en inp ms mo -> srealizes bsegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes bsegs (init_config bsegs b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof. intros en inp T Hv Hi. apply (both_boot_R en inp T Hv (valid_input_either_of_valid_input inp Hi)). Qed.
