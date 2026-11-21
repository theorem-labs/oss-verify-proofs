(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader premise of the exit writes). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from S0Exit.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Lia.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0ExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes Spec LibWritev S0StdioDefs S0StdioWrite.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec S0_code_1337c_1378c S0_code_1ed68_1f620 S0_code_20620_216f4 S0_code_216f4_226f4 S0_code_26728_26f04 S0_code_atexit          .
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSum.
Import WalkHideSum.OptIn.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0Exit.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase.
Import ListNotations.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase.
Import ListNotations.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit.S7Exit_run2.
Import ListNotations.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit.S7Exit_run1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit.S7Exit_run2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit.S7Exit_run3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioWrite.S7StdioWrite_run1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioWrite.S7StdioWrite_run2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioWrite.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import S0Exit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.BudgetWit Require Import RefNodesB Rzb S0StdioWriteB.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Module S7Exit_run1.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run1.
Module S7Exit_run2.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run2.
Module S7Exit_run3.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run3.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Theorem ref_fini_clean_b :
  forall regs mem model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  S0Exit.fini_pre regs mem sp code wp2 rp2 ->
  file_clean mem 0x2a498 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x1f6b0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp code wp2 rp2 wp1 rp1 FP F1 Hh Hlazy.
  destruct FP as [Fsp Fs0 Fra Fsplo Fsphi Fsok Ffe Ffs Ffa Fcomp Fg1 Fg2 Fdso Fglob Ferr].
  (* [comment removed for export] *)
  cps_destruct (w2 regs mem (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  cps_destruct Fglob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct Ferr as (F2l & F2wp & F2wb & F2rp & F2re).
  cps_destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  cps_destruct (w3a regs2 (mem_w2 mem sp code (getr regs 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2; store_ok_peel; exact Fsok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr|zaddr F0l|zaddr F0wp|zaddr F0wb|zaddr F0rp|zaddr F0re]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply RefNodesB.rzb_exit_at; [exact F_1f414 | exact E_1f414 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
Theorem ref_fini_flush_b :
  forall regs mem model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  S0Exit.fini_pre regs mem sp code wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x1f6b0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending FP SP Hh Hlazy Hfd Hrdr.
  destruct FP as [Fsp Fs0 Fra Fsplo Fsphi Fsok Ffe Ffs Ffa Fcomp Fg1 Fg2 Fdso Fglob Ferr].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  cps_destruct (w2 regs mem (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  cps_destruct Fglob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct (w3b1 regs2 (mem_w2 mem sp code (getr regs 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2; store_ok_peel; exact Fsok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr|zaddr F0l|zaddr F0wp|zaddr F0wb|zaddr F0rp|zaddr F0re]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x21b5c) with (0x21b5c : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 mem sp code (getr regs 9)) sp code).
  eapply (S0StdioWriteB.ref_stdio_write_b regs3 mem3 model (bv_unsigned sp - 32) 0x2a498 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x21b5c : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2; sok_stack Fsok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2; rdn_solve
    | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
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
    cps_destruct Ferr as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
    cps_destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply RefNodesB.rzb_exit_at; [exact F_1f414 | exact E_1f414 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
Theorem ref_exit_clean_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x2a498 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x1f6fc : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  cps_destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  cps_destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  (* [comment removed for export] *)
  destruct ec_ax as [(Alk & Ahd) | (Alk & Asl & Ahd & Anx & Af0 & Aa0 & Acb)].
  - cps_destruct (w1e regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_clean_b regs1 _ model sp code wp2 rp2 wp1 rp1); [ fini_pre_of mem_w1e | | exact Hh | exact Hlazy ].
    repeat split; unfold mem_w1e; zaddr_goal; rdn_solve.
  - cps_destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_clean_b regs1 _ model sp code wp2 rp2 wp1 rp1); [ fini_pre_of mem_w1o | | exact Hh | exact Hlazy ].
    repeat split; unfold mem_w1o; zaddr_goal; rdn_solve.
Qed.
Theorem ref_exit_flush_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x1f6fc : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  cps_destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  (* [comment removed for export] *)
  destruct ec_ax as [(Alk & Ahd) | (Alk & Asl & Ahd & Anx & Af0 & Aa0 & Acb)].
  - cps_destruct (w1e regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_flush_b regs1 _ model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending);
      [ fini_pre_of mem_w1e | stdout_pending_of mem_w1e RANGE LEN PMAX BYTES | exact Hh | exact Hlazy | exact Hfd | exact Hrdr ].
  - cps_destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_flush_b regs1 _ model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending);
      [ fini_pre_of mem_w1o | stdout_pending_of mem_w1o RANGE LEN PMAX BYTES | exact Hh | exact Hlazy | exact Hfd | exact Hrdr ].
Qed.
Theorem ref_exit_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x1f6fc : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (intros regs mem model code pending; cps_intros (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES)).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply Rzb.rzb_conseq; [ | apply S0Exit.t_emit_nil_exit ].
    eapply ref_exit_clean_b; eassumption.
  - eapply ref_exit_flush_b; eassumption.
Qed.
Corollary ref_exit_Z_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x1f6fc) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x1f6fc) with (0x1f6fc : word) by (apply bv_eq; reflexivity).
  apply ref_exit_b; assumption.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
