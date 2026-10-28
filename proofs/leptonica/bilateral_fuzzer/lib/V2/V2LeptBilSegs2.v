(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib LeptExec LeptExecW LeptExecFP LeptExecX LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition bc_cptr : Z := 0x12088.
Definition bc_chalf : Z := 0x125b8.
Definition bc_fzero : Z := 0xffffffff00000000.

(* [comment removed for export] *)
Definition HPL : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition VPL : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition pass_fp (fr fr' : bvmap 5 word) : Prop := forall r : reg, ~ In (ridx r) [12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r.

Definition bc_fsc (fr : bvmap 5 word) : Prop :=
  reg_get fr 8 = Z_to_bv 64 p_lo_d /\ reg_get fr 9 = Z_to_bv 64 p_hi_d /\ reg_get fr 18 = Z_to_bv 64 bc_fzero.

Definition rd_bytes (M : word -> option byte) (lo n : Z) : Prop :=
  forall p, (lo <= p < lo + n)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b].

Definition img_none (M : word -> option byte) (lo n : Z) : Prop :=
  forall j, (lo <= j < lo + n)%Z -> M (Z_to_bv 64 j) = None.
Definition sbox (x : Z) : Z := bv_unsigned (fpv_box FMT_S x).
