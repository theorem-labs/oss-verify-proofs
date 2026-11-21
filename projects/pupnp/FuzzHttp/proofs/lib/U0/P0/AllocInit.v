(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; the 27- or 29-pair auxv; the channel-reader fact; the launch's input, mmap base and entry draw). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame ITree Nodes Decode Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KRemapDef KStep KStepK KStepC.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require EquivMR.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocHINV MallocFacts_A Malloc_iface MallocTree MallocRep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP. From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink. From OSSVerify.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import AllocInst.
Import ListNotations.
Local Open Scope Z_scope.

Definition s_init {HCEIL : HasCeiling} : PState := ps_init (reservedZ rsegs) alloc_ceiling.

Theorem P0_rheap_init {HGW : HasGuard} {HCEIL : HasCeiling} : forall (m : word -> option byte) (auxv : word),
  (forall a : word, 0x5bb18 <= bv_unsigned a < 0x5bec8 -> m a = None) ->
  rw_cells rsegs m 0x5baa8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m 0x5bab0 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                            C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  rw_cells rsegs m 0x2a150 [C8 (Z_to_bv 64 0x5ba88)] ->
  rw_cells rsegs m 0x5ba88 [C8 guard_word] ->
  rw_cells rsegs m 0x5c2f8 [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  AllocIF.RHEAP rsegs AI_P0 s_init [] m /\ rw_cells rsegs m RAUXV_CELL [C8 auxv].
Proof. exact RHEAP_init_proof. Qed.

Theorem P0_link_init {HGW : HasGuard} {HCEIL : HasCeiling} : forall brk0 mbase sp lim inp,
  valid_brk rsegs brk0 ->
  valid_sp sp ->
  valid_mmap_base mbase ->
  in_channel_reader inp = true ->
  alloc_ceiling = bv_unsigned sp - 8388608 ->
  LINK rsegs AI_P0 s_init [] (init_model (segments_reserved rsegs) brk0 mbase sp lim inp).
Proof.
  intros brk0 mbase sp lim inp (VB1 & VB2 & VB3) (SP1 & SP2 & _) (VM1 & _ & _) CR CEIL.
  unfold mmap_base_min in VM1.
  assert (RT : reserved_top (segments_reserved rsegs) = 0x5d000) by (vm_compute; reflexivity).
  rewrite RT in VB1, VB2. unfold brk_aslr_max in VB2. unfold page_size in VB3.
  unfold sp_window_lo in SP1. unfold sp_window_hi in SP2.
  cbn [LINK AI_P0]. unfold P0_LINK, OWN. cbn [map]. split; [| split; [constructor| exact I]].
  exists (led_init (reservedZ rsegs) alloc_ceiling). split; [| split; [| intros x []]].
  { unfold s_init, ps_init. cbn [ps_m]. apply c2_init. apply alloc_ceiling_le_max. }
  unfold s_init, ps_init. cbn [ps_brk]. change (reservedZ rsegs) with (map wwZ (segments_reserved rsegs)). rewrite CEIL. change 8388608 with stack_max_size.
  apply EquivMR.KL_init.
  - intros e He. unfold ehi.
    assert (E : segments_reserved rsegs = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3000); (Z_to_bv 64 0x13000, Z_to_bv 64 0x17000);
                                         (Z_to_bv 64 0x2a000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x2b000, Z_to_bv 64 0x32000)])
      by (vm_compute; reflexivity).
    rewrite E in He. destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite ?unsigned_lit by lia; lia.
  - lia.
  - unfold PGSZ. exact VB3.
  - unfold PGSZ, stack_max_size. lia.
  - unfold sp_window_lo, sp_window_hi. lia.
  - unfold PGSZ. lia.
  - exact CR.
Qed.

(* LPS 727298f3: the model at the start is [with_vdso (vdso_run_init ..) (init_model ..)]; [with_vdso]
   rebuilds only the vDSO run field of the VM state, so every accessor KL / minv / OWN read is unchanged. *)
Lemma m_tid_wvdso : forall v mo, m_tid (with_vdso v mo) = m_tid mo.
Proof. reflexivity. Qed.
Lemma m_halted_wvdso : forall v mo, m_halted (with_vdso v mo) = m_halted mo.
Proof. reflexivity. Qed.
Lemma m_fds_wvdso : forall v mo, m_fds (with_vdso v mo) = m_fds mo.
Proof. reflexivity. Qed.
Lemma m_fs_wvdso : forall v mo, m_fs (with_vdso v mo) = m_fs mo.
Proof. reflexivity. Qed.
Lemma minv_wvdso : forall v mo, minv mo -> minv (with_vdso v mo).
Proof. intros v mo H. exact H. Qed.
Lemma KL_wvdso : forall L pb mo v, KL L pb mo -> KL L pb (with_vdso v mo).
Proof. intros L pb mo v H. destruct H. constructor; assumption. Qed.
Lemma OWN_wvdso : forall X G s mo v, OWN X G s mo -> G s (with_vdso v mo) -> OWN X G s (with_vdso v mo).
Proof.
  intros X G s mo v [(L & HC & HK & HI) [ND _]] HG'. split; [| split; [exact ND| exact HG']].
  exists L. split; [exact HC|]. split; [exact (KL_wvdso L (ps_brk s) mo v HK)| exact HI].
Qed.

Theorem P0_link_init_vdso {HGW : HasGuard} {HCEIL : HasCeiling} : forall v brk0 mbase sp lim inp,
  valid_brk rsegs brk0 -> valid_sp sp -> valid_mmap_base mbase -> in_channel_reader inp = true ->
  alloc_ceiling = bv_unsigned sp - 8388608 ->
  LINK rsegs AI_P0 s_init [] (with_vdso v (init_model (segments_reserved rsegs) brk0 mbase sp lim inp)).
Proof.
  intros v brk0 mbase sp lim inp VB VS VM CR CEIL.
  pose proof (P0_link_init brk0 mbase sp lim inp VB VS VM CR CEIL) as L0.
  cbn [LINK AI_P0] in L0 |- *. unfold P0_LINK in L0 |- *.
  apply OWN_wvdso; [exact L0| exact I].
Qed.

(* LPS 727298f3: the environment fact over the launch's auxv pair list ([RMallocTree.rauxv_ok]). *)
Theorem P0_renv_init {HGW : HasGuard} {HCEIL : HasCeiling} : forall (m : word -> option byte) (B av rnd : Z)
    (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw efn : word),
  rw_cells rsegs m RAUXV_CELL [C8 (wz av)] ->
  bytes_at rsegs m av (u64s (auxv_list la ph entry uid gid hw rnd efn)) ->
  bytes_at rsegs m (rnd + 8) (le8 secret_word) ->
  alloc_ceiling <= B -> B <= av -> av + 464 <= 2^64 -> B <= rnd + 8 -> rnd + 16 <= 2^64 -> 0 <= rnd < 2^64 ->
  RENV rsegs AI_P0 m B.
Proof.
  intros. cbn [RENV AI_P0]. exists av, rnd, la, ph, entry, uid, gid, hw, efn. repeat (split; [assumption|]). assumption.
Qed.
