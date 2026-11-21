(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; the channel-reader fact; the launch's input, mmap base and entry draw). *)
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
Proof. intros L pbrk mo fds K MI HH. destruct K. constructor; rewrite ?m_vmmaps_with_fds; auto. all: try exact kl_vdso. Qed.

Lemma KL_with_tid : forall L pbrk mo t, KL L pbrk mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> KL L pbrk (with_tid t mo).
Proof.
  intros L pbrk mo t K Ht. destruct K. constructor; rewrite ?m_vmmaps_with_tid; auto.
  { apply minv_with_tid; assumption. }
  all: try (rewrite m_halted_with_tid; assumption).
  all: try exact kl_vdso.
Qed.

(* The launch's reserved ledger is the image's entries followed by the vDSO pair, which sits within
   twenty-one pages below min(mmap base, stack floor); [MB] and [BC] keep the pair above the brk area. *)
Lemma KL_init : forall r brk mb sp lim inp pbrk,
  (forall e, In e r -> ehi e <= bv_unsigned brk) ->
  0 < bv_unsigned brk -> bv_unsigned brk mod PGSZ = 0 -> bv_unsigned brk + 32 * PGSZ <= bv_unsigned sp - stack_max_size ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  bv_unsigned brk + 32 * PGSZ <= bv_unsigned mb ->
  in_channel_reader inp = true ->
  KL (led_init (map wwZ r) (bv_unsigned sp - stack_max_size)) pbrk (init_model r brk mb sp lim inp).
Proof.
  intros r brk mb sp lim inp pbrk TOP B0 BAL BC SPW MB CR.
  assert (XB : 0 <= Z.min (bv_unsigned mb) (bv_unsigned sp - stack_max_size) < two_pow_64).
  { pose proof (Z.min_spec (bv_unsigned mb) (bv_unsigned sp - stack_max_size)) as MS.
    pose proof (bv_unsigned_in_range 64 mb) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
    unfold two_pow_64, PGSZ in *. lia. }
  constructor; rewrite ?m_vmmaps_init_model; cbn [vm_maps vm_reserved vm_noaccess vm_start_brk vm_brk vm_init_sp alloc_top ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_ceil led_init].
  - apply minv_init; [exact SPW| exact CR].
  - reflexivity.
  - apply m_halted_init_model.
  - split; [intros e []| constructor].
  - unfold init_reserved. rewrite map_app. eexists. reflexivity.
  - intros [a n] He. unfold init_reserved in He. apply in_app_or in He as [He|He]; [left; exact (TOP _ He)| right].
    pose proof (vdso_entry_lo _ _ a n XB He) as D. pose proof (Z.min_spec (bv_unsigned mb) (bv_unsigned sp - stack_max_size)) as MS.
    unfold elo; cbn [fst]. unfold PGSZ in *. lia.
  - unfold PGSZ in *. lia.
  - intros b l [].
  - intros b l k [].
  - cbn. constructor.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros b l [].
  - intros e [].
  - intros b l k [].
  - unfold vdso_in_resv. exists r. rewrite vm_reserved_init_model, m_kernel_init_model. split; [reflexivity|].
    intros e He. rewrite m_vmmaps_init_model. cbn [vm_start_brk]. exact (TOP e He).
Qed.

Lemma Wsucc k : Wb (S k) = BB + Wb k /\ Wm (S k) = BM + Wm k /\ Wp (S k) = BP + Wp k.
Proof. unfold Wb, Wm, Wp. rewrite Nat2Z.inj_succ. lia. Qed.
