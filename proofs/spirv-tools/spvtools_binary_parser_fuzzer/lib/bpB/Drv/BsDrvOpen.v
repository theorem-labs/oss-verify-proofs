(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BReach BeapCeil BFrame BFileSim BRefNodes BazyRestrict BazySR BazyFdNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsDrvRun.
Import BPropExec.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section DrvOpen.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  Section Openat.
    Variables (s : as_St H) (msF : machine_state) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (mo : Model) (w : bv 32).
    Hypothesis HF : fetch_word asegs pc = Some w.
    Hypothesis HE : is_ecall w = true.
    Hypothesis HV : as_VIS H s msF = mkst regs pc mem rom.
    Hypothesis HA : as_AKREL H s (mkCfg msF mo).
    Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
    Hypothesis H10 : getr regs 10 = AT_FDCWD.
    Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

    Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem rom.

    Theorem drv_openat_toolong : forall bs K,
      rdn asegs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
      (forall msF' mo', as_VIS H s msF' = post (errno_ret ENAMETOOLONG) -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) K.
    Proof.
      intros bs K Hrd Hnz Hc.
      apply (drv_lazy H DL s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
      eapply (rz_openat_toolong_lazy asegs L S Zr msF regs pc mem mo w HF HE OK RS H17 H10 Hfl bs K Hrd Hnz).
      intros msF' mo' OK' SB' RS' HS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
      exact (Hc msF' mo' HV' HA' SB').
    Qed.

    Theorem drv_openat_empty : forall K,
      path_at_lazy asegs regs mem [] ->
      (forall msF' mo', as_VIS H s msF' = post (errno_ret ENOENT) -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) K.
    Proof.
      intros K Hp Hc.
      apply (drv_lazy H DL s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
      eapply (rz_openat_empty_lazy asegs L S Zr msF regs pc mem mo w HF HE OK RS H17 H10 Hfl K Hp).
      intros msF' mo' OK' SB' RS' HS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
      exact (Hc msF' mo' HV' HA' SB').
    Qed.

    Theorem drv_openat_absent : forall p K,
      path_at_lazy asegs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
      fs_lookup (m_fs mo) p = None ->
      (forall msF' mo', as_VIS H s msF' = post (errno_ret ENOENT) -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) K.
    Proof.
      intros p K Hp Hne Hsl Hnd Hfs Hc.
      apply (drv_lazy H DL s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
      eapply (rz_openat_absent_lazy asegs L S Zr msF regs pc mem mo w HF HE OK RS H17 H10 Hfl p K Hp Hne Hsl Hnd Hfs).
      intros msF' mo' OK' SB' RS' HS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
      exact (Hc msF' mo' HV' HA' SB').
    Qed.

    Hypothesis Hfree : fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None.

    Theorem drv_openat_dot : forall p KA KB,
      path_at_lazy asegs regs mem p -> path_is_dirref p = true ->
      (forall e msF' mo', In e openat_errnos ->
         as_VIS H s msF' = post (errno_ret e) -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         realizes asegs (mkCfg msF' mo') KA) ->
      (forall msF' mo',
         as_VIS H s msF' = post (alloc_fd (m_fds mo)) -> as_AKREL H s (mkCfg msF' mo') ->
         same_but_materialized (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) FdDir) mo) mo' ->
         realizes asegs (mkCfg msF' mo') KB) ->
      realizes asegs (mkCfg msF mo) (t_alt2 KA KB).
    Proof.
      intros p KA KB Hp Hdr HAc HBc.
      apply (drv_lazy H DL s msF mo regs pc mem _ HV HA). intros L S Zr OK RS BACK.
      eapply (rz_openat_dot_lazy asegs L S Zr msF regs pc mem mo w HF HE OK RS H17 H10 Hfl Hfree p KA KB Hp Hdr).
      - intros e msF' mo' He OK' SB' RS' HS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
        exact (HAc e msF' mo' He HV' HA' SB').
      - intros msF' mo' OK' SB' RS' HS'.
        destruct (BACK msF' mo' _ OK' (same_vm_trans _ _ _ (same_vm_with_fds _ _) (same_vm_sb _ _ SB')) RS') as [HV' HA'].
        exact (HBc msF' mo' HV' HA' SB').
    Qed.

    Theorem drv_openat_file : forall p d KA KB,
      path_at_lazy asegs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
      fs_lookup (m_fs mo) p = Some d ->
      (forall e msF' mo', In e openat_errnos ->
         as_VIS H s msF' = post (errno_ret e) -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         realizes asegs (mkCfg msF' mo') KA) ->
      (forall msF' mo',
         as_VIS H s msF' = post (alloc_fd (m_fds mo)) -> as_AKREL H s (mkCfg msF' mo') ->
         same_but_materialized (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (FdFile p (Z_to_bv 64 0))) mo) mo' ->
         realizes asegs (mkCfg msF' mo') KB) ->
      realizes asegs (mkCfg msF mo) (t_alt2 KA KB).
    Proof.
      intros p d KA KB Hp Hne Hsl Hnd Hfs HAc HBc.
      apply (drv_lazy H DL s msF mo regs pc mem _ HV HA). intros L S Zr OK RS BACK.
      eapply (rz_openat_file_lazy asegs L S Zr msF regs pc mem mo w HF HE OK RS H17 H10 Hfl Hfree p d KA KB Hp Hne Hsl Hnd Hfs).
      - intros e msF' mo' He OK' SB' RS' HS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
        exact (HAc e msF' mo' He HV' HA' SB').
      - intros msF' mo' OK' SB' RS' HS'.
        destruct (BACK msF' mo' _ OK' (same_vm_trans _ _ _ (same_vm_with_fds _ _) (same_vm_sb _ _ SB')) RS') as [HV' HA'].
        exact (HBc msF' mo' HV' HA' SB').
    Qed.
  End Openat.

  Theorem drv_read_dir : forall s msF regs (pc : word) mem mo w fd (cnt : Z) K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 63 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some FdDir ->
    getr regs 12 = Z_to_bv 64 cnt -> (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
    (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
    store_ok asegs mem (getr regs 11) (Z.to_nat cnt) = true ->
    (forall msF', as_VIS H s msF' = mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom ->
       as_AKREL H s (mkCfg msF' mo) ->
       realizes asegs (mkCfg msF' mo) K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd cnt K HF HE HV HA H17 H10 Hfd32 Hlk H12 Hc1 Hc2 Htask Hso Hc.
    apply (drv_lazy H DL s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
    eapply (rz_read_dir_mapped_lazy asegs L S Zr msF regs pc mem mo w fd cnt K HF HE OK RS H17 H10 Hfd32 Hlk H12 Hc1 Hc2 Htask Hso).
    intros msF' OK' RS' HS'. destruct (BACK msF' mo _ OK' (same_vm_refl _) RS') as [HV' HA'].
    exact (Hc msF' HV' HA').
  Qed.
End DrvOpen.
