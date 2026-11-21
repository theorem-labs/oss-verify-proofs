(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe Stdio Malloc Adapter Driver PState Prog KInv KStep StepB
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Init LB_Alloc LB_PCaps LB_Hist LB_Proph LB_PStdio LB_PTarget Gap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import TopLevel ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import CMonad CLogic ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require DriverC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma OK_firstQ : malokA [] 65536.
Proof.
  intros P HPc HP8. apply (malok_of P HPc HP8); [lia| intros _; unfold LRX; rewrite zcount_nil; lia| unfold n63X; rewrite zcount_nil; lia| unfold R63X, RHOLD, W; cbn; lia].
Qed.

Lemma OK_growQ : forall b k, (k <= 9)%nat -> malokA [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk P HPc HP8. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Hq.
  assert (Hp : 2 ^ Z.of_nat k <= 512). { change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  apply (malok_of P HPc HP8); [lia| | |].
  - intros _. rewrite LRX_cons. unfold LRX. rewrite zcount_nil. destruct (_ && _); lia.
  - rewrite n63X_cons. unfold n63X. rewrite zcount_nil. destruct (_ <=? _); lia.
  - rewrite R63X_cons. unfold R63X. cbn [map zsum fold_right]. rewrite ?zsum_nil.
    pose proof (bigb_le (65536 * 2 ^ Z.of_nat k) (2^25) ltac:(lia)). unfold RHOLD, W. lia.
Qed.

Section FM.
Variable FM : flush_model.


Lemma prog_withC_Q : forall rs argv, cspecL LBUDGET (Qamb []) (prog_withC FM rs argv) (fun _ _ _ => False).
Proof.
  intros rs argv. unfold prog_withC.
  eapply cspecL_seq; [apply cspecL_lift; apply (startup_L LBUDGET (Qamb [])); [apply Qamb_minv| apply Qamb_fds| apply Qamb_live]|]. intros _.
  eapply cspecL_bind.
  - apply (main_modelC_L LBUDGET io raw_malloc raw_free rs alloc_init alloc_count Qamb Qrun Qamb_Qrun malokA).
    + intros X n Hn. apply malloc_Qamb. exact Hn.
    + intros X p n. apply free_Qamb.
    + intros X p n. apply free_Qrun.
    + intros X Y s mo HP. apply Qamb_perm. exact HP.
    + intros X d. cbn [io io_diag io_S]. apply (s_diag_L LBUDGET (Qamb X) (Qamb_live X)).
    + intros X bm. unfold alloc_init, target_alloc_init. apply mspecL_ret. intros s mo H; exact H.
    + intros X. unfold alloc_count, target_alloc_count. apply mspecL_ret. intros s mo H; exact H.
    + intros X s mo H. exact (Qamb_minv _ _ _ H).
    + intros X s mo mo' H. exact (Qamb_fds _ _ _ _ H).
    + intros X s mo H. exact (Qamb_live _ _ _ H).
    + exact OK_firstQ.
    + exact OK_growQ.
    + exact (runC_Q FM).
  - intros code. cbn beta. unfold DriverC.exit_model. apply cspecL_lift. apply (exit_model_L' LBUDGET io Qrun).
    intros X. cbn [io io_exit io_S]. apply (stdout_exit_flush_L LBUDGET (Qrun X) (Qrun_live X) (Qrun_so X)).
Qed.

Theorem live_bound_nf_D : forall D segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 -> (* + (APPENDED), as row 2 LB_Main *)
  tlive LBUDGET (progD FM D segs rs inp en) (mo0 segs lim en inp) /\ tnf (progD FM D segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros D segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil Hfloor Hresv Hlim Hve Hvi Hlow.
  (* the launch facts LB_Init QI_init takes: the channel reader (valid_input_either's
     13th conjunct) and mmap_base_min <= mbase (valid_mmap_base, valid_entry's third conjunct). *)
  assert (Hrd : in_channel_reader inp = true)
    by (destruct Hvi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hvi) in Hve. destruct Hve as ((HspL & HspH & _) & Hbrk & (Hmb & _) & _).
  unfold progD, progD_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp].
  apply (mspecL_program LBUDGET (Qamb []) (prog_withD FM D rs (argv_Z (in_argv inp))) (fun _ _ _ => False)).
  - unfold prog_withD. apply cspecL_RES. apply prog_withC_Q.
  - unfold Qamb. apply QI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hfloor| exact Hresv| exact Hlim| exact Pamb_nonneg| exact Pamb_ok| exact PHI_Pamb| exact Hrd| exact Hlow| exact Hmb].
  - intros [].
Qed.

Theorem never_forced_D : forall D segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 -> (* + (APPENDED) *)
  tnf (progD FM D segs rs inp en) (mo0 segs lim en inp).
Proof. intros. eapply live_bound_nf_D; eauto. Qed.
End FM.
