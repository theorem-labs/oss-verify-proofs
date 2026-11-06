(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach HeapCeil Frame FileSim RefNodes
  LazyRestrict LazySR LazyFdNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import MState Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsDrvRun.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~03asr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~k2h0asan_driver_laws37Corelib7Numbers7BinNumsp84Npos35stdpp9bitvectorbdefinitionsr82bv37Corelib4Init9Datatypesta4Someta6option37Corelib4Init5Logichg22eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshhcafetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hm15asegsta4boolta4truehhc8is_ecall3h5LinuxProcessSemanticsfLinuxProcessSem3Runhrf5mkCfg08as_AKRELhg21I69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ig34getrr82BVr84BvWfr87Z_to_bv4h5LinuxProcessSemanticsfLinuxProcessSem3Sys4Uapiilc8AT_FDCWDp81Z5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openipdh2open_ignored_flags46Stdlib6ZArith6BinInt1Ziu85ldiffr8bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Statejh77FdEntryjh75m_fdsta4Nonejh78alloc_fdjh79fd_lookup" s.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section DrvOpen.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jd$0").
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : ltac2:(zQ "10!o4@1$0?1H").

  Let rom := seg_rom asegs.

  Section Openat.
    Variables (s : as_St H) (msF : machine_state) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (mo : Model) (w : bv 32).
    Hypothesis HF : ltac2:(zQ "70!r1!t5!v2!v9!hh6!hl3!hpc@3$4@1$3@1$1@1$0#i0@2$5$6?2pc@2$2@1$1@1$0#i0?1w").
    Hypothesis HE : ltac2:(zQ "40!hq5!hqc!hh6!hr3@3$2$0@1$3?1w$1").
    Hypothesis HV : as_VIS H s msF = mkst regs pc mem rom.
    Hypothesis HA : ltac2:(zQ "20!hub!hv4@3$1?1H?1s@2$0?3msF?2mo").
    Hypothesis H17 : ltac2:(zQ "80!r1!hve!hh6!ije!ik6!ikb!il2!t5@3$2@1$7@1$0#k0@2$3?4regs@3$4@1$0#5+h1Kv$1@2$5@1$0#5+h1@2$6@1$0#k0+j8").
    Hypothesis H10 : ltac2:(zQ "80!r1!hve!hh6!iod!ije!ik6!ikb!t5@3$2@1$7@1$0#k0@2$4?4regs@3$5@1$0#5+aKv$1@2$6@1$0#5+a$3").
    Hypothesis Hfl : ltac2:(zQ "a0!r1!hve!hh6!ip9!it1!ije!jg0!ik6!ikb!jg9@3$2$3@2$6@2$9@1$0#k0@2$5?4regs@3$7@1$0#5+cKv$1@2$8@1$0#5+c$4Z").

    Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem rom.

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
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

    Hypothesis Hfree : ltac2:(zQ "70!jk5!jl0!jl9!v9!hh6!jm0!jmc@3$4@1$3$0@2$6@1$1?2mo@1$5@1$1?2mo@1$2$0").

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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
