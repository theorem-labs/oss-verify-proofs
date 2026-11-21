(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: u_startup_rt gains the valid_launch and entry_launch_ok_va premises, takes u_main_entry over the whole ProcInput and the mmap base, and starts its continuation from the model with the vDSO run state. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import Amb ShapeAlg UStartup RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState PropExec Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Local Notation usegs := Ubsan.M.loaded_segments (only parsing).
Local Notation upc := Ubsan.M.init_pc (only parsing).
Local Notation uph := Ubsan.M.phdrs (only parsing).

Theorem u_startup_rt : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_brk usegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     u_main_entry sp inp mbase rnd tid regs mem ->
     realizes usegs
       (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty (0x1316c : word)
                 (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom usegs))
              (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved usegs) brk mbase sp lim inp)))) K) ->
  realizes usegs (init_config usegs upc uph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  apply u_startup; [exact Hsp | exact Hbrk | exact Hva | exact Hve | exact Hvl | exact Hlau |].
  intros tid regs mem Htid ME. apply realizes_mkst_of_mkR; [reflexivity |]. exact (HK tid regs mem Htid ME).
Qed.
