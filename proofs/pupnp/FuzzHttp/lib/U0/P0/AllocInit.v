(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling RunWord.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KRemapDef KStep KStepK KStepC.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require EquivMR.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocHINV MallocFacts_A Malloc_iface MallocTree MallocRep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import AllocInst.
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
  alloc_ceiling = bv_unsigned sp - 8388608 ->
  LINK rsegs AI_P0 s_init [] (init_model (segments_reserved rsegs) brk0 mbase sp lim inp).
Proof.
  intros brk0 mbase sp lim inp (VB1 & VB2 & VB3) (SP1 & SP2 & _) CEIL.
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
Qed.

Theorem P0_renv_init {HGW : HasGuard} {HCEIL : HasCeiling} : forall (m : word -> option byte) (B av x3 x4 x5 hw x6 x11 x12 x23 rnd : Z),
  rw_cells rsegs m RAUXV_CELL [C8 (wz av)] ->
  bytes_at rsegs m av (u64s (auxv_list x3 x4 x5 hw x6 x11 x12 x23 rnd)) ->
  bytes_at rsegs m (rnd + 8) (le8 secret_word) ->
  alloc_ceiling <= B -> B <= av -> av + 160 <= 2^64 -> B <= rnd + 8 -> rnd + 16 <= 2^64 ->
  0 <= x3 < 2^64 -> 0 <= x4 < 2^64 -> 0 <= x5 < 2^64 -> 0 <= hw < 2^64 -> 0 <= x6 < 2^64 ->
  0 <= x11 < 2^64 -> 0 <= x12 < 2^64 -> 0 <= x23 < 2^64 -> 0 <= rnd < 2^64 ->
  RENV rsegs AI_P0 m B.
Proof.
  intros. cbn [RENV AI_P0]. exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. repeat (split; [assumption|]). assumption.
Qed.
