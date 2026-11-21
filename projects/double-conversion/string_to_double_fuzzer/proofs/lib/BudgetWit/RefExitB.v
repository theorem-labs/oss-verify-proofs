(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RefExit.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reader fact of the output channels). *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic RefExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs RefStdioWrite.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec Ref_code_323a8_33000 Ref_code_95000_96000 Ref_code_9b000_9c000 Ref_code_a7000_a8000 Ref_code_drv      .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefExit.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioDefs RefExit_run1 RefExit_run2 RefExit_run3 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.RefStdioWrite_run1 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.RefStdioWrite_run2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.
Import ListNotations.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BudgetWit Require Import RefNodesB RefStdioWriteB Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_4.
Context {fx : PropExec.FPState}.
#[using="Type"] Theorem ref_exit_clean_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xb2d90 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply RefNodesB.rzb_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
#[using="Type"] Theorem ref_exit_flush_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->   (* LPS 727298f3: as RefExit.v *)
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (w3b1 regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x9b620) with (0x9b620 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (RefStdioWriteB.ref_stdio_write_b regs3 mem3 model (bv_unsigned sp - 32) 0xb2d90 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9b620 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; rdn_solve
    | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply RefNodesB.rzb_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
#[using="Type"] Theorem ref_exit_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply Rzb.rzb_conseq; [ | apply RefExit.t_emit_nil_exit ].
    eapply ref_exit_clean_b; eassumption.
  - eapply ref_exit_flush_b; eassumption.
Qed.
#[using="Type"] Corollary ref_exit_Z_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  Rzb.rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x96094) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x96094) with (0x96094 : word) by (apply bv_eq; reflexivity).
  apply ref_exit_b; assumption.
Qed.
End FPW_4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
