(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.zstd_frame_info.images Require Import Asan.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanStartup StartupHS2Asan AsanBoot
  AsanCertDefs AsanStartupCertH AsanStartupCertHB AsanStartupCertHC AsanStartupCertHD AsanStartupCertH2
  RegsEqv0 SrzEqv MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
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
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINH : forall ms mo,
    amain_atL source_alloc_limit (mkEntry sp brk0 mbase rdraw) (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd) ms mo ->
    srealizes asegs (mkCfg ms mo) T.

  #[using="Hsp Hbrk Hva Hve Hfit Huid Hhw T_nil MAINH"] Theorem asan_main_boot_h :
    srealizes asegs (init_config asegs Asan.M.init_pc a_phdrs sp brk0 mbase rdraw source_alloc_limit
                               (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd)) T.
  Proof.
    exact (asan_main_bootL sp brk0 mbase rdraw argv envp fs stdin uid gid groups net nof sigm hw abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw
             AsanInit.LIMITH AsanInit.LIMITH_ge T T_nil MAINH startup_cert_h startup_certB_h startup_certC_h startup_certD_h startup2_cert_h).
  Qed.
End BridgeH.

(* [comment removed for export] *)
Theorem asan_boot_R : forall en inp (T : TSet),
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> T [] ->
  (forall ms mo, amain_atL source_alloc_limit en inp ms mo -> srealizes asegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes asegs (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof.
  intros [sp brk0 mbase rdraw] inp T Hv Hi Tnil MAINH.
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit).
  pose proof Hi as (Hva & Hve & Hfs & Hrel & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & Hur).
  destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vasz urnd tmp].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  apply SpinAlg.realizes_of_srealizes.
  exact (asan_main_boot_h sp brk0 mbase rdraw argv envp (fs_seed_tmp ifs tmp) stdin uid gid groups net nof sigm hw abt urnd
           Hsp Hbrk Hva Hve Hfit Huid Hhw T Tnil MAINH).
Qed.

Corollary asan_boot_R_valid : forall en inp (T : TSet),
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input inp -> T [] ->
  (forall ms mo, amain_atL source_alloc_limit en inp ms mo -> srealizes asegs (mkCfg ms mo) T) ->
  ShapeAlg.realizes asegs (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T.
Proof. intros en inp T Hv Hi. apply (asan_boot_R en inp T Hv (valid_input_either_of_valid_input inp Hi)). Qed.
