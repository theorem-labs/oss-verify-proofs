(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from PStartupRT.v: p_startup_rt restated over BudgetWit.Rzb.rzb, with its released proof. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: p_startup_rt_b takes the launch premises and the vDSO run state, and discharges the vdso_image premise of rzb_mkst_of_mkR, as PStartupRT.v does there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import Amb ShapeAlg PStartup RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState PropExec Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb RealizesEqvB PStartupB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Local Notation psegs := Plain.M.loaded_segments (only parsing).
Local Notation ppc := Plain.M.init_pc (only parsing).
Local Notation pph := Plain.M.phdrs (only parsing).

Theorem p_startup_rt_b : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_brk psegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     p_main_entry sp inp mbase rnd tid regs mem ->
     rzb psegs
       (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (0x1214c : word)
                 (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
              (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved psegs) brk mbase sp lim inp)))) K) ->
  rzb psegs (init_config psegs ppc pph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  apply p_startup_b; [exact Hsp | exact Hbrk | exact Hva | exact Hve | exact Hvl | exact Hlau |].
  intros tid regs mem Htid ME. apply rzb_mkst_of_mkR; [reflexivity |]. exact (HK tid regs mem Htid ME).
Qed.
