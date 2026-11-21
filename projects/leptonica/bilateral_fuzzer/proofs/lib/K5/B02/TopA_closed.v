(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up for each CONFIG_RSEQ value; walks over the binary's own segments lifted to the run's segment list; recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanPlanImages.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanTablesA AsanStartup StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations. Import AX2. Import AP.
From OSSVerify.leptonica.bilateral_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s.

(* LPS 08b1429: the run premise [TopA_s3s] leaves open, RUNSEG, the lift of an srealizes walk from the
   image's segments to the run's ([Run.run_segments]).  LPS 75d69e00: the kernel premise
   [topA_kernel_pin : forall inp, valid_input inp -> in_kernel inp = default_kernel] is GONE.  It was
   REFUTED at this revision ([Run.recorded_kernel], Run.v:4575-4581, passes [kb_rseq] through, so a
   valid input with [kb_rseq = false] has [in_kernel inp <> default_kernel]); the start-up now takes
   the kernel of record from [Run.valid_input_recorded_kernel] and the certificate at the run's flag. *)
Definition topA_runseg_lift : Prop :=
  forall en inp T,
  valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input inp ->
  srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                               target_alloc_limit inp) T ->
  srealizes (run_segments ASEGS inp (en_sp en) (en_mmap_base en))
            (init_config (run_segments ASEGS inp (en_sp en) (en_mmap_base en)) AsanUbsan.M.init_pc APH
                         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.

Theorem s3s_of_conetop : topA_runseg_lift ->
  (rt_contracts RTA -> rt_gaps RTA -> fuzz_one_cps RTA LIB_A) ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. intros RUNSEG CONE. exact (s3s_B02_of_cone RUNSEG (CONE rta_rc rta_gaps)). Qed.
