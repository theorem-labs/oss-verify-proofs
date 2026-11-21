(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Image CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe MSafeP CMonad CLogic STree Malloc Stdio PState Client Harness HarnessC Adapter AdapterC Driver DriverC Prog ProgC
  KInv KLink KEv KEvP TargetSafeC ModelInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section DriverSpecC.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> MC St Z.
Variable alloc_count : Monad.M St Z.
Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspec (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspec (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspec (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspec (own X) alloc_count (fun _ => own X).
Hypothesis Hrun : forall X cfg payload, zlength payload <= MAX_INPUT -> cspecP (own X) (run cfg payload) (fun _ => own X).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.

Local Ltac liftP := apply cspecP_lift, mspec_mspecP.

Lemma main_model_specC : forall X argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
  cspecP (own X) (DriverC.main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv)
         (fun _ s mo => exists X', own X' s mo).
Proof.
  intros X argv Hargv. unfold DriverC.main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= ARG_MAX_LEN).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength, ARG_MAX_LEN; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply cspecP_if; intros _.
  { liftP. eapply mspec_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspec_ret. intros s mo Ho. exists X; exact Ho. }
  eapply cspecP_bind; [liftP; eapply (read_all_spec io drv_malloc drv_free read_stage own); eauto|].
  intros [|buf content]; cbn beta iota; [apply cspecP_ret; intros s mo H; exact H|].
  apply cspecP_pure. intros Hlen.
  apply cspecP_if; intros _.
  { liftP. eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
  apply cspecP_if; intros _.
  { liftP. eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
  eapply cspecP_seq; [liftP; apply Hinit|]. intros _.
  eapply cspecP_seq; [apply Hrun; pose proof (zlength_skipn_le (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content); lia|]. intros status.
  eapply cspecP_seq with (R := own (buf :: X)).
  { liftP. destruct (Z.testbit _ 15); [|apply mspec_ret; intros s mo H; exact H].
    eapply mspec_seq; [apply Hcount|]. intros n. apply mspec_ret. intros s mo H; exact H. }
  intros status'. eapply cspecP_seq; [liftP; apply Hdf|]. intros _. apply cspecP_ret. intros s mo Ho. exists X. exact Ho.
Qed.

Lemma exit_model_specC : forall code,
  cspecP (fun s mo => exists X, own X s mo) (DriverC.exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold DriverC.exit_model. apply cspecP_lift.
  eapply (exit_model_spec io own); eauto.
Qed.
End DriverSpecC.


Lemma client_pre_nonneg : Forall (fun n => 0 <= n) Client.CLIENT_PRE.
Proof. unfold Client.CLIENT_PRE, Client.STATE_SIZE. repeat constructor; lia. Qed.
Lemma client_opt_nonneg : Forall (fun n => 0 <= n) Client.CLIENT_OPT.
Proof. unfold Client.CLIENT_OPT, Client.WINDOW_SIZE. repeat constructor; lia. Qed.

Lemma runC_GI : forall X cfg payload, cspecP (GI X) (runC cfg payload) (fun _ => GI X).
Proof.
  intros X cfg payload. unfold runC, fuzz_oneC.
  apply (target_run_spec raw_malloc raw_free (io_emit io) GI Client.CLIENT_PRE Client.CLIENT_OPT).
  - apply raw_malloc_GI. - apply raw_free_GI.
  - intros X' v. apply s_emit_GI.
  - exact client_pre_nonneg. - exact client_opt_nonneg.
Qed.

Theorem prog_withC_GIP : forall rs argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
  cspecP (GI []) (prog_withC rs argv) (fun _ _ _ => False).
Proof.
  intros rs argv Hargv. unfold prog_withC.
  eapply cspecP_seq; [apply cspecP_lift, mspec_mspecP; apply startup_GI|]. intros _.
  eapply cspecP_bind.
  - eapply (main_model_specC io raw_malloc raw_free rs alloc_init runC alloc_count GI);
      first [ exact Hargv | apply raw_malloc_GI | apply raw_free_GI | apply GI_perm
            | (intros; apply s_diag_GI; assumption) | apply stdout_exit_flush_GI
            | apply alloc_init_GI | apply alloc_count_GI | (intros; apply runC_GI) | apply GI_minv | apply GI_fds ].
  - intros code. eapply (exit_model_specC io GI); first [apply stdout_exit_flush_GI | apply GI_minv | apply GI_fds].
Qed.

Corollary prog_withD_GIP : forall D rs argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
  mspecP (GI []) (prog_withD D rs argv) (fun _ _ _ => False).
Proof. intros D rs argv Hargv. unfold prog_withD. apply cspecP_RES. apply prog_withC_GIP. exact Hargv. Qed.
