(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecFP LeptExecX DitherLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac ex_runA nx rounds fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch goal with
      | |- context [@mkst ?fxk regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (ex_auto segs rounds fuel stops true scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (SS ?pc' ?sr' ?log' ?kn' ?nx', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; try (exb_sc1 HK regs)
              | let ST := fresh "ST" in
                pose proof (ex_st_auto segs rounds fuel stops scr pc sr [] kn nx pc' sr' log' kn nx' scs scr' E base rom
                              (@mkst fxk regs (Z_to_bv 64 pc) base rom) fxk
                              ltac:(vm_cast_no_check (eq_refl (SS pc' sr' log' kn nx', scs, scr'))) HK Hsc
                              (ex_st_open segs E base rom fxk regs pc sr HR)) as ST;
                destruct ST as (R' & HR' & _ & Hms); clear Hsc ]
          end
      end
    end
  end.
