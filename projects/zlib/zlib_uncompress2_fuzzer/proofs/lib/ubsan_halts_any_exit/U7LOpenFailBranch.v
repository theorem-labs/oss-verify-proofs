(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec U7Startup U7MainEntry U7OpenFail_defs U7OpenFail U7PilotOOM_defs U7LPilotOOM.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section Branch.
  (* over the launch input (argv = [a0s; path] by Hav), the ruled VLAUNCH + LOK and the
     launch's channel reader, as S0OpenFail / S0PilotOOM; the file system is the launch's (in_fs inp). *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Local Notation envv := (in_envp inp) (only parsing).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hcr : in_channel_reader inp = true.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs0 mem0.

  Theorem open_err_branch_cannot_open :
    U7LPilotOOM.open_err_branch sp0 a0s path inp rdraw tid mem0 brk mbase (t_die (msg_cannot_open path) (in_fs inp)).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    eapply U7OpenFail.ref_open_fail_errno; try eassumption.
    apply openat_errnos_range. exact He.
  Qed.
End Branch.

Corollary cannot_open_branch : forall (sp0 : word) (a0s : list byte) (inp : ProcInput) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word),
  in_argv inp = [a0s; dot_path] -> valid_argv [a0s; dot_path] -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp -> in_channel_reader inp = true ->
  valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 inp mbase rdraw tid regs0 mem0 ->
  open_err_branch sp0 a0s dot_path inp rdraw tid mem0 brk mbase (t_die (msg_cannot_open dot_path) (in_fs inp)).
Proof.
  intros sp0 a0s inp rdraw tid regs0 mem0 brk mbase Hav Hva Hve Hvl Hlau Hcr Hvsp Htid ME.
  eapply open_err_branch_cannot_open; eassumption.
Qed.
