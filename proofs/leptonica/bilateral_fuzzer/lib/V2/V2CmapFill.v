(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require CmapFill.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocVL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition CMAP_CLOB : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%nat.
Section CF.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables cmap dp nc arr nalloc : Z.
Variable bs : list byte.
#[local] Notation data := (dp - 3)%Z (only parsing).
Hypothesis Hcmap : (1 <= cmap /\ cmap + 24 <= 2 ^ 64)%Z.
Hypothesis Hnc : (1 <= nc <= 256)%Z.
Hypothesis Hnal : (nc <= nalloc <= 256)%Z.
Hypothesis Harr : (1 <= arr /\ arr + 4 * nalloc <= 2 ^ 64)%Z.
Hypothesis Hdat : (3 <= dp /\ dp - 3 + 4 * nc <= 2 ^ 64)%Z.
Hypothesis Carr : rdn SEGS M (Z_to_bv 64 cmap) 8 = Some (Z_to_le_bytes 8 arr).
Hypothesis Cnal : rdn SEGS M (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 nalloc).
Hypothesis Cn0 : rdn SEGS M (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 0).
Hypothesis Dbs : rdn SEGS M (Z_to_bv 64 (dp - 3)) (Z.to_nat (4 * nc)) = Some bs.
Hypothesis SOKa : store_ok SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * nalloc)) = true.
Hypothesis SOKc : store_ok SEGS M (Z_to_bv 64 cmap) 24 = true.
Hypothesis A_ca : (cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap)%Z.
Hypothesis A_cd : (cmap + 24 <= dp - 3 \/ dp - 3 + 4 * nc <= cmap)%Z.
Hypothesis A_ad : (arr + 4 * nalloc <= dp - 3 \/ dp - 3 + 4 * nc <= arr)%Z.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@CmapFill.lez8). Qed.

End CF.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x1ea98 0x1e9bc 19 18 0 8 [(23%nat, 0%Z); (9%nat, 4%Z); (22%nat, 4%Z)] CMAP_CLOB).
Proof. rl_tail (@CmapFill.cmapfill_contract fx v2_reloc v2_code_vl). Qed.

End VPORT.
