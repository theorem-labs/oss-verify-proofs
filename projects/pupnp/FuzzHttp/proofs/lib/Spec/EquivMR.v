(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepK JLedger MBound EquivK EquivAlloc.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require MI_Joint6.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import TSim MSim.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Definition Wb (k : nat) : Z := BB * Z.of_nat k.
Definition Wm (k : nat) : Z := BM * Z.of_nat k.
Definition Wp (k : nat) : Z := BP * Z.of_nat k.

Lemma PHM_weaken k cs : PHM (S k) cs -> PHM k cs.
Proof. unfold PHM. apply VI_mono. unfold CM. lia. Qed.

Lemma PK_weaken_k zd k mo : PK zd (Wb (S k)) (Wm (S k)) (Wp (S k)) mo -> PK zd (Wb k) (Wm k) (Wp k) mo.
Proof. intros P. eapply PK_weaken; [exact P| | |]; unfold Wb, Wm, Wp, BB, BM, BP; lia. Qed.

Lemma KL_with_fds : forall L pbrk mo fds, KL L pbrk mo -> minv (with_fds fds mo) -> m_halted (with_fds fds mo) = None ->
  KL L pbrk (with_fds fds mo).
Proof. intros L pbrk mo fds K MI HH. destruct K. constructor; rewrite ?m_vmmaps_with_fds; auto. Qed.

Lemma KL_with_tid : forall L pbrk mo t, KL L pbrk mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> KL L pbrk (with_tid t mo).
Proof.
  intros L pbrk mo t K Ht. destruct K. constructor; rewrite ?m_vmmaps_with_tid; auto.
  { unfold minv in *. rewrite m_fds_with_tid, m_fs_with_tid, m_tid_with_tid.
    destruct kl_minv as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [assumption|]). split; [| destruct mo; exact A8].
    intros t' E. injection E as <-. exact Ht. }
  all: try (rewrite m_halted_with_tid; assumption).
Qed.

Lemma KL_init : forall r brk mb sp lim inp pbrk,
  (forall e, In e r -> ehi e <= bv_unsigned brk) ->
  0 < bv_unsigned brk -> bv_unsigned brk mod PGSZ = 0 -> bv_unsigned brk + 4 * PGSZ <= bv_unsigned sp - stack_max_size ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  KL (led_init (map wwZ r) (bv_unsigned sp - stack_max_size)) pbrk (init_model r brk mb sp lim inp).
Proof.
  intros r brk mb sp lim inp pbrk TOP B0 BAL BC SPW.
  constructor; rewrite ?m_vmmaps_init_model; cbn [vm_maps vm_reserved vm_noaccess vm_start_brk vm_brk vm_init_sp alloc_top ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_ceil led_init].
  - apply minv_init. exact SPW.
  - reflexivity.
  - apply m_halted_init_model.
  - split; [intros e []| constructor].
  - reflexivity.
  - exact TOP.
  - lia.
  - intros b l [].
  - intros b l k [].
  - cbn. constructor.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros b l [].
  - intros e [].
Qed.

Lemma Wsucc k : Wb (S k) = BB + Wb k /\ Wm (S k) = BM + Wm k /\ Wp (S k) = BP + Wp k.
Proof. unfold Wb, Wm, Wp. rewrite Nat2Z.inj_succ. lia. Qed.
