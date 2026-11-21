(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off states checked over the join and hand-off tables computed in the build at each CONFIG_RSEQ value, hs_tab_ok_1 and hs_tab_ok_0, in place of the recorded checks of four recorded states; HS_asan_ok and startup_shape_holes over the CONFIG_RSEQ flag; s3s_A over the launch's ProcInput through s3s_A_of and the start-up certificate, with the run-segments lift RUNSEG as a section hypothesis; imports SpinAlg for srealizes; the recorded proofs replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanPlanImages.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupCoGen.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanTablesA AsanStartup StartupPlanAsan StartupGenAsan StartupGenAsan0 StartupGenAsan1 StartupHSAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations. Import AX2. Import AP.

(* every computed hand-off state passes the main program's boolean test, at each CONFIG_RSEQ value *)
Lemma hs_tab_ok_1 : forallb (fun e => hs_all_ok (snd (fst e))) (go_H startup_tabs_1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_tab_ok_0 : forallb (fun e => hs_all_ok (snd (fst e))) (go_H startup_tabs_0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HS_asan_ok : forall b h ch, HS_asan b h = Some ch -> hs_all_ok ch = true.
Proof.
  intros b h ch. unfold HS_asan, startup_tabs.
  destruct b; apply gc_get_forallb; [exact hs_tab_ok_1 | exact hs_tab_ok_0].
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : forall b, holes_only (startup_shape b) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Section RunPremises.
(* RUNSEG: the run-segments lift.  There is no kernel premise: the start-up takes the kernel of
   record from [Run.valid_input] ([Run.valid_input_recorded_kernel]) and the certificate at the
   run's own [kb_rseq].  KERNEL WAS [forall inp, valid_input inp -> in_kernel inp = default_kernel],
   REFUTED at LPS 75d69e00 by any valid input with [kb_rseq = false] ([Run.recorded_kernel] passes
   [kb_rseq] through, Run.v:4575-4581). *)
Hypothesis RUNSEG : forall en inp T,
  valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input inp ->
  srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                               target_alloc_limit inp) T ->
  srealizes (run_segments ASEGS inp (en_sp en) (en_mmap_base en))
            (init_config (run_segments ASEGS inp (en_sp en) (en_mmap_base en)) AsanUbsan.M.init_pc APH
                         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.

Theorem s3s_A : fuzz_one_cps RTA LIB_A -> rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros FZ RC IOC.
  exact (s3s_A_of IT0 IT0_ok HS_asan startup_plan_r startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok FZ RC IOC RUNSEG).
Qed.


(* [comment removed for export] *)
Theorem s3s_A_rc : fuzz_one_cps RTA LIB_A -> rt_contracts RTA ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. intros FZ RC. exact (s3s_A FZ RC rta_io). Qed.


(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec.
Theorem s3s_B02_of_cone : fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros FZ. exact (s3s_A_rc FZ (rta_contracts (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
                   (rta_free (drain_ok fixed_commit_ok ((fun MN AN p HOK => item_sec_ok p MN AN HOK) munmap_ok madvise_ok)) fixed_commit_ok))).
Qed.

End RunPremises.
