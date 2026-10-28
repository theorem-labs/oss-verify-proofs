(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptArith LeptExec LeptExecX.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Definition PC_pixRotateOrth : Z := 0x97094.

Section RotOrth.
Context {fx : FPState}.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ro_q1 : forall regs m (pixs : Z), (1 <= pixs < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x97094 : word) m rom) (mkst regs' (0x9713c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixs Hp H10 H11.
    replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
    replace (0x9713c : word) with (Z_to_bv 64 0x9713c) by (apply bv_eq; reflexivity).
    ex_entry regs [pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixs]) m [KRange (EVar 32) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 40%nat [0x9713c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma ro_q2 : forall regs m (pixs : Z), (1 <= pixs < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x97094 : word) m rom) (mkst regs' (0x98a70 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixs Hp H10 H11.
    replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
    replace (0x98a70 : word) with (Z_to_bv 64 0x98a70) by (apply bv_eq; reflexivity).
    ex_entry regs [pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixs]) m [KRange (EVar 32) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 40%nat [0x98a70%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma ro_q3 : forall regs m (pixs : Z), (1 <= pixs < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 3 ->
    exists regs',
      msteps SEGS (mkst regs (0x97094 : word) m rom) (mkst regs' (0x9713c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 (-1)
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixs Hp H10 H11.
    replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
    replace (0x9713c : word) with (Z_to_bv 64 0x9713c) by (apply bv_eq; reflexivity).
    ex_entry regs [pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixs]) m [KRange (EVar 32) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 40%nat [0x9713c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'); try (apply bv_eq; reflexivity). ex_agree HR HR'.
  Qed.
End RotOrth.
