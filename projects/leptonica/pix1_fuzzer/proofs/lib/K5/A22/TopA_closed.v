(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run-segment premise topA_runseg_lift of s3s_of_conetop, lifting the walk from the image's segments to run_segments; imports). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import AsanPlanImages.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import AsanTablesA AsanStartup StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations. Import AX2. Import AP.
From OSSVerify.leptonica.pix1_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s.

(* LPS 08b1429: the run premise [TopA_s3s] leaves open, RUNSEG, the lift of an srealizes walk from the
   image's segments to the run's ([Run.run_segments]).  LPS 75d69e00: the kernel premise
   [topA_kernel_pin : forall inp, valid_input inp -> in_kernel inp = default_kernel] is GONE.  It was
   REFUTED at this revision ([Run.recorded_kernel], Run.v:4575-4581, passes [kb_rseq] through, so a
   valid input with [kb_rseq = false] has [in_kernel inp <> default_kernel]); the start-up now takes
   the kernel of record from [Run.valid_input_recorded_kernel] and the certificate at the run's flag. *)
Definition topA_runseg_lift : Prop :=
  forall en inp T,
  valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input inp ->
  srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                               target_alloc_limit inp) T ->
  srealizes (run_segments ASEGS inp (en_sp en) (en_mmap_base en))
            (init_config (run_segments ASEGS inp (en_sp en) (en_mmap_base en)) Asan.M.init_pc APH
                         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.

Theorem s3s_of_conetop : topA_runseg_lift ->
  (rt_contracts RTA -> rt_gaps RTA -> fuzz_one_cps RTA LIB_A) ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. intros RUNSEG CONE. exact (s3s_A22_of_cone RUNSEG (CONE rta_rc rta_gaps)). Qed.
