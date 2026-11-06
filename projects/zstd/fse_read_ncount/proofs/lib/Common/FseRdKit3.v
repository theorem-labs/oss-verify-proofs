(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Lemma slliw3_neg : forall d, - 2^28 <= d <= 0 -> bv_swrap 32 ((d mod 18446744073709551616) ≪ 3) = 8 * d.
Proof.
intros d Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0060=17177375443.428180754167.329784459402.238717662456.450379622024.367851517017.200000100200300400:00>SSSSS2Hd1NS2Hd".
rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. apply swrap32_eqm; [lia|].
change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
destruct (Z.eq_dec d 0) as [->|N]; [reflexivity|].
assert (E : d mod 2^64 = d + 2^64) by (symmetry; apply (Z.mod_unique_pos d (2^64) (-1) (d + 2^64)); lia).
rewrite E. replace ((d + 2^64) * 8 - 8 * d) with (2^35 * 2^32) by lia. apply Z.mod_mul. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sub_mod64_word : forall a b, Z_to_bv 64 (a - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply Z_to_bv_eqm. change 18446744073709551616 with (2^64).
Local Ltac2 Set LiaHints.tbl := fun () => "0010=11608269853.2000001S".
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma subw_mod64 : forall a b, - 2^31 <= a - b < 2^31 -> bv_swrap 32 (a - b mod 18446744073709551616) = a - b.
Proof.
intros a b H. Local Ltac2 Set LiaHints.tbl := fun () => "0040=11607912823.338717875063.341193234805.358928363066.3000001002005006SSS1HS".
apply swrap32_eqm; [lia|]. change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
rewrite (Z.mod_eq b (2^64)) by lia. replace (a - (b - 2^64 * (b / 2^64)) - (a - b)) with ((2^32 * (b / 2^64)) * 2^32) by lia.
apply Z.mod_mul. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
