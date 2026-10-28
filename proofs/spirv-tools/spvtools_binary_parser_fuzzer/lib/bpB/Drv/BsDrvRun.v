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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BReach BegsEquivM BainEqv BeapCeil BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BLibKnowFrame BSymAux BazyRestrict BazySR BazyFdNodes BazySym.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsLazyRun BsPrintfFirst.
Import BPropExec.
Import ListNotations.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Drv.
  Context {fx : DFP}.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  Definition same_vm (mo mo' : Model) : Prop := m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo.

  Lemma same_vm_refl : forall mo, same_vm mo mo.
  Proof. intros mo. split; reflexivity. Qed.
  Lemma same_vm_trans : forall a b c, same_vm a b -> same_vm b c -> same_vm a c.
  Proof. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.
  Lemma same_vm_sb : forall mo mo', same_but_materialized mo mo' -> same_vm mo mo'.
  Proof.
    intros mo mo' SB. destruct (same_but_materialized_fields _ _ SB) as (_ & A & B & _). split; [exact A | exact B].
  Qed.
  Lemma same_vm_with_fds : forall f mo, same_vm mo (with_fds f mo).
  Proof. intros f [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

  Lemma drv_lazy : forall s msF mo R pc M (T : TSet),
    as_VIS H s msF = mkst R pc M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall L S Zr,
       lzok asegs L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R pc M rom ->
       (forall msF' mo' ms', lzok asegs L S Zr (mkCfg msF' mo') -> same_vm mo mo' -> restrict L S msF' = ms' ->
          as_VIS H s msF' = ms' /\ as_AKREL H s (mkCfg msF' mo')) ->
       realizes asegs (mkCfg msF mo) T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros s msF mo R pc M T HV HA HK.
    destruct (adl_lazy H DL s) as (L & S & Zr & HVIS & HLZ & HTR).
    apply (HK L S Zr); [apply HLZ; exact HA | rewrite <- HVIS; exact HV |].
    intros msF' mo' ms' OK' [SV1 SV2] RS'. split; [rewrite HVIS; exact RS'|].
    exact (HTR msF mo msF' mo' HA OK' SV1 SV2).
  Qed.

  Theorem drv_run_lf : forall s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T,
    sym_exec asegs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok asegs E M kn ->
    scs_denot asegs M E scs -> scs_denot asegs M E scs2 ->
    as_VIS H s msF = mkst R (Z_to_bv 64 pc) M rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok asegs E M' kn' ->
       M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
       as_VIS H s msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros s fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R msF mo T Hex Hc HR HK Hsc Hsc2 HV HA Hcont.
    apply (drv_lazy s msF mo R _ M T HV HA). intros L S Zr OK RS BACK.
    eapply (rz_run_lf_lazy asegs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T Hex Hc HR HK Hsc Hsc2 OK RS).
    intros R' M' msF' mo' HR' HK' EQ LF OK' SB HS RS'.
    destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB) RS') as [HV' HA'].
    exact (Hcont R' M' msF' mo' HR' HK' EQ LF HV' HA' SB).
  Qed.

  Theorem drv_close : forall s msF regs (pc : word) mem mo w fd e K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 57 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some e ->
    (forall msF', as_VIS H s msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom ->
       as_AKREL H s (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
       realizes asegs (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd e K HF HE HV HA H17 H10 Hfd32 Hlk Hc.
    apply (drv_lazy s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
    eapply (rz_close_lazy asegs L S Zr msF regs pc mem mo w fd e K HF HE OK RS H17 H10 Hfd32 Hlk).
    intros msF' OK' RS' HS'. destruct (BACK msF' _ _ OK' (same_vm_with_fds _ _) RS') as [HV' HA'].
    exact (Hc msF' HV' HA').
  Qed.

  Theorem drv_read_file : forall s msF regs (pc : word) mem mo w fd p off data (cnt : Z) K,
    fetch_word asegs pc = Some w -> is_ecall w = true ->
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 17 = Z_to_bv 64 63 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
    fs_lookup (m_fs mo) p = Some data ->
    getr regs 12 = Z_to_bv 64 cnt ->
    (1 <= cnt)%Z -> (cnt <= MAX_RW_COUNT)%Z -> (cnt < 2 ^ 64)%Z ->
    (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
    store_ok asegs mem (getr regs 11) (Z.to_nat cnt) = true ->
    let bs := file_read data off (getr regs 12) in
    let mo1 := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo in
    (forall msF' mo',
       as_VIS H s msF' = mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) rom ->
       as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo1 mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF regs pc mem mo w fd p off data cnt K HF HE HV HA H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso bs mo1 Hc.
    apply (drv_lazy s msF mo regs pc mem K HV HA). intros L S Zr OK RS BACK.
    eapply (rz_read_file_lazy asegs L S Zr msF regs pc mem mo w fd p off data cnt K HF HE OK RS H17 H10 Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Htask Hso).
    intros msF' mo' OK' SB' RS' HS'.
    destruct (BACK msF' mo' _ OK' (same_vm_trans _ _ _ (same_vm_with_fds _ _) (same_vm_sb _ _ SB')) RS') as [HV' HA'].
    exact (Hc msF' mo' HV' HA' SB').
  Qed.
End Drv.
