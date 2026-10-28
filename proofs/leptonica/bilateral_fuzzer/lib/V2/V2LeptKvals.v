From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition kvals (m : word -> option byte) (h w : Z) (rows : Z -> Z) (f : Z -> Z -> Z) : Prop :=
  forall i j, 0 <= i < h -> 0 <= j < w ->
    rdn SEGS m (Z_to_bv 64 (rows i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (f i j)) /\ FB fmt_single 1 (f i j).
