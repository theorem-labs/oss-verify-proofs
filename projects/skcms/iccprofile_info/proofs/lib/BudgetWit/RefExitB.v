(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Info/RefExit.v: the exit walk restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, ref_exit_mid_flush_b and ref_exit_flush_b take the channel-reader premise (m_channel_reader) of the stdio write. *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefExitBase Ref_code_1293c_12d58 Ref_code_161c8_17084 Ref_code_12a40_1e480 Ref_code_1dbe0_1e5bc.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefExit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs. Import RefExit_run1. Import RefExit_run2. Import RefExit_run3. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefStdioWrite.RefStdioWrite_run1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefStdioWrite.RefStdioWrite_run2. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefStdioWrite Ref_code_161c8_17084.
From Stdlib Require Import Zify.

Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.
Import RefExit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.BudgetWit Require Import Rzb AgentNodesB NodesB LibWritevB RefNodesB RefStdioWriteB.

Section WithFP1. Context {FP : PropExec.FPState}.

Lemma ref_exit_mid_clean_b :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  file_clean mem1 0x20790 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  rzb RSEGS (mkCfg (mkst regs1 (0x16a14 : word) mem1 (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs1 mem1 model sp code wp2 rp2 wp1 rp1 EM F1 Hh Hlazy.
  destruct EM as [Esp Es0 Era Esplo Esphi Esok Efe Efs Efa Ecomp Eg1 Eg2 Edso Eglob Eerr].
  destruct (w2 regs1 mem1 (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 mem1 sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2; store_ok_peel; exact Esok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  eapply rzb_exit_at; [exact F_16868 | exact E_16868 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Lemma ref_exit_mid_flush_b :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  stdout_pending mem1 wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  (* LPS #38 (in 727298f3): [ref_stdio_write_b] asks for the reader, in the slot right after
     [fd_lookup], as [Info.RefExit.ref_exit_mid_flush] does *)
  m_channel_reader model = true ->
  rzb RSEGS (mkCfg (mkst regs1 (0x16a14 : word) mem1 (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending EM SP Hh Hlazy Hfd Hcr.
  destruct EM as [Esp Es0 Era Esplo Esphi Esok Efe Efs Efa Ecomp Eg1 Eg2 Edso Eglob Eerr]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  destruct (w2 regs1 mem1 (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 (mem_w2 mem1 sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2; store_ok_peel; exact Esok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  replace (Z_to_bv 64 0x18e88) with (0x18e88 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 mem1 sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write_b regs3 mem3 model (bv_unsigned sp - 32) 0x20790 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x18e88 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | subst mem3; unfold mem_w3a, mem_w2; sok_stack Esok
    | lia | lia
    | split; subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve
    | split; subst mem3; unfold mem_w3a, mem_w2; rdn_solve
    | lia | exact Hfd | exact Hcr | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rzb_exit_at; [exact F_16868 | exact E_16868 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

Lemma ref_exit_w1 :
  forall regs mem rom (sp tp code : word) (tid : Z) (wp2 rp2 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  exists regs1 mem1,
    msteps RSEGS (mkst regs (0x16a60 : word) mem rom) (mkst regs1 (0x16a14 : word) mem1 rom)
    /\ exit_mid regs1 mem1 sp code wp2 rp2
    /\ (forall (a : word) n bs, rdn RSEGS mem a n = Some bs ->
          (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
          (bv_unsigned a + Z.of_nat n <= bv_unsigned sp - 56 \/ bv_unsigned sp <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x50a30 \/ 0x50a48 <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x50c50 \/ 0x50c54 <= bv_unsigned a)%Z ->
          rdn RSEGS mem1 a n = Some bs).
Proof.
  intros regs mem rom sp tp code tid wp2 rp2 EC.
  pose proof EC as EC0. destruct EC0.
  destruct ec_ax as [AXE | AXO].
  - destruct (w1e regs mem rom sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption; try (destruct ec_glob as (Gnl & _); exact Gnl).
    exists regs1, (mem_w1e mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid).
    split; [exact RUN1|]. split.
    + destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      constructor; try assumption; unfold mem_w1e;
        first [ store_ok_peel; exact ec_sok
              | rdn_solve
              | repeat split; zaddr_goal; rdn_solve ].
    + intros a n bs H Hnw D1 D2 D3. unfold mem_w1e. repeat rdn_peel1; first [exact H | zsimp; lia].
  - destruct (w1x regs mem rom sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption; try (destruct ec_glob as (Gnl & _); exact Gnl).
    exists regs1, (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid).
    split; [exact RUN1|]. split.
    + destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      constructor; try assumption; unfold mem_w1x;
        first [ store_ok_peel; exact ec_sok
              | rdn_solve
              | repeat split; zaddr_goal; rdn_solve ].
    + intros a n bs H Hnw D1 D2 D3. unfold mem_w1x. repeat rdn_peel1; first [exact H | zsimp; lia].
Qed.

Theorem ref_exit_clean_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x20790 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  rzb RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct (ref_exit_w1 regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC) as (regs1 & mem1 & RUN1 & EM & FR).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  pose proof (ec_splo _ _ _ _ _ _ _ _ EC) as SPlo. pose proof (ec_sphi _ _ _ _ _ _ _ _ EC) as SPhi.
  eapply (ref_exit_mid_clean_b regs1 mem1 model sp code wp2 rp2 wp1 rp1 EM); [|exact Hh | exact Hlazy].
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  repeat split; (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
Qed.

Theorem ref_exit_flush_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  rzb RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hcr.
  destruct (ref_exit_w1 regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC) as (regs1 & mem1 & RUN1 & EM & FR).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  pose proof (ec_splo _ _ _ _ _ _ _ _ EC) as SPlo. pose proof (ec_sphi _ _ _ _ _ _ _ _ EC) as SPhi.
  eapply (ref_exit_mid_flush_b regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending EM);
    [|exact Hh | exact Hlazy | exact Hfd | exact Hcr].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  constructor; try assumption;
    try (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]);
    try (split; (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia])).
Qed.

Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hcr)].
  - eapply rzb_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean_b; eassumption.
  - eapply ref_exit_flush_b; eassumption.
Qed.

Corollary ref_exit_Z_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x16a60) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x16a60) with (0x16a60 : word) by (apply bv_eq; reflexivity).
  apply ref_exit_b; assumption.
Qed.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
