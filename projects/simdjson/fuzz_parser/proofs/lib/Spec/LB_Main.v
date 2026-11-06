(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe Stdio Malloc HarnessP Adapter Driver PState ProgP KInv KStep StepB
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Init LB_Alloc LB_PCaps LB_Hist LB_Amb LB_PStdio LB_PTarget Gap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma prog_with_Q : forall rs argv, mspecL LBUDGET (Qamb []) (prog_with rs argv) (fun _ _ _ => False).
Proof.
  intros rs argv. unfold prog_with, main_exit.
  eapply mspecL_seq; [apply (startup_L LBUDGET (Qamb [])); [apply Qamb_minv| apply Qamb_fds| apply Qamb_live]|]. intros _.
  eapply mspecL_bind.
  - apply (main_model_L LBUDGET io raw_malloc raw_free rs alloc_init run alloc_count Qamb Qamb (fun X s mo H => H) malokA).
    + intros X n Hn. apply malloc_Qamb. exact Hn.
    + intros X p n. apply free_Qamb.
    + intros X p n. apply free_Qamb.
    + intros X Y s mo HP. apply Qamb_perm. exact HP.
    + intros X d. cbn [io io_diag io_S]. apply (s_diag_L LBUDGET (Qamb X) (Qamb_live X)).
    + intros X bm. unfold alloc_init, target_alloc_init. apply mspecL_ret. intros s mo H; exact H.
    + intros X. unfold alloc_count, target_alloc_count. apply mspecL_ret. intros s mo H; exact H.
    + exact run_Q.
    + intros X s mo H. exact (Qamb_minv _ _ _ H).
    + intros X s mo mo' H. exact (Qamb_fds _ _ _ _ H).
    + intros X s mo H. exact (Qamb_live _ _ _ H).
    + exact OK_firstQ.
    + exact OK_growQ.
  - intros code. cbn beta.
    eapply mspecL_seq with (R := fun s mo => exists X, Qamb X s mo).
    + apply mspecL_exI. intros X. eapply mspecL_post; [apply client_exit_Q|]. intros a s mo H. exists X. exact H.
    + intros _. apply (exit_model_L' LBUDGET io Qamb).
      intros X. cbn [io io_exit io_S]. apply (stdout_exit_flush_L LBUDGET (Qamb X) (Qamb_live X) (Qamb_so X)).
Qed.

(* [comment removed for export] *)
Theorem live_bound_nf : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^31 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  tlive LBUDGET (ProgP.prog segs rs inp en) (mo0 segs lim en inp) /\ tnf (ProgP.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil Hfloor Hresv Hlim Hve Hvi.
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((HspL & HspH & _) & Hbrk & _ & _).
  unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
  apply (mspecL_program LBUDGET (Qamb []) (prog_with rs (argv_Z (in_argv inp))) (fun _ _ _ => False)).
  - apply prog_with_Q.
  - unfold Qamb.      (* [comment removed for export] *)
    apply QI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hfloor| exact Hresv| exact Hlim| exact PambP_nonneg| exact PambP_ok| exact PHI_PambP_budget].
  - intros [].
Qed.

Theorem never_forced : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^31 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  tnf (ProgP.prog segs rs inp en) (mo0 segs lim en inp).
Proof. intros. eapply live_bound_nf; eauto. Qed.
