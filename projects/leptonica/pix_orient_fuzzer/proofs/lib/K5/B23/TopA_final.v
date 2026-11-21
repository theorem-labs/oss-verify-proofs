(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (s3s_closed over the run-segments lift topA_runseg_lift, which TopA.v proves, and without the kernel premise topA_kernel_pin, false at LPS 75d69e00; its recorded proof replaced by a plain proof in the form of leptonica/kernel_fuzzer's TopA_final.v, with this tree's cone arguments; the Rocq imports of that proof, SpinAlg among them for srealizes). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanPlanImages.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanTablesA AsanStartup StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations. Import AX2. Import AP.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s RT_fk_iface RT_fk_proof RT23_iface RT23b_iface RT_stackmalloc347 RT_stackfree7 RT_strchr23 RT_sscanf23 RT_facts_lo Po_rot90_defs Po_top Po_fuzz Po_fuzz_adapt.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_final () := "C69OSSVerify5KrLib2K53B23;RT_facts_lo;rta_live_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237Po_fuzz:po_fuzz_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=Po_fuzz_adapt=po_fuzz_adaptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238TopA_s3s?s3s_B02_of_coneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Po_top?po_cone_of_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_gaps_proof6rta_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_gaps_proof8rta_gapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_fk_proof@rta_fk_contractsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_3FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_4FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_strchr23;rta_strchrFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_sscanf23>rta_sscanf_ddFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_7FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_stackfree7Arta_stack_free_7FC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23:TopA_final?rta_art_live_loC1?~~~~~~~~~~~~~~~".

Lemma rta_art_live_lo : art_live_lo RTA.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_final ()) [] "g0000o"). Qed.

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

(* THE ENCODED PROOF IS GONE: this file's [KReplay] replay applied the cone lemma WITH the kernel
   premise, which no longer exists, so the encoded term cannot typecheck.  The STATEMENT is this
   file's own, minus that premise; the PROOF is written out in the form the eight sibling trees
   state this same proof in (e.g. kernel_fuzzer K5/A17/TopA_final.v), with this tree's own cone
   arguments.  Nothing is re-encoded. *)
Theorem s3s_closed : topA_runseg_lift -> S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros RUNSEG.
  exact (s3s_B02_of_cone RUNSEG
           (po_cone_of_open RTA rta_rc rta_gaps rta_fk_contracts rta_stack_malloc_3F rta_stack_malloc_4F
                            rta_strchrF rta_sscanf_ddF rta_stack_malloc_7F rta_stack_free_7F rta_art_live_lo
                            (po_fuzz_ok RTA) (po_fuzz_adapt RTA))).
Qed.
