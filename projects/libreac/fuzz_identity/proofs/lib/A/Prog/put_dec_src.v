(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_identity_fw_str.v, with its module names changed; 42 of its 73 lines of code are new or changed and 499 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require IdentSpec put_dec_c put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import put_dec_rev.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.IdentSpec(DEC, dg).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec(ds_lsb).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
Lemma pd_src_rev : forall (m : word -> option byte) (H : word -> bool) (T : Z) (L : list byte) (j : nat),
garr8 SEGS (mrestrict H m) T (map bv_unsigned L) -> (j < length L)%nat ->
val_mem SEGS (mrestrict H m) (T + Z.of_nat (length L) - 1 - Z.of_nat j) 1
  (bv_unsigned (nth j (rev L) (Z_to_bv 8 0))).
Proof.
intros m Hm T L j HG Hj.
rewrite rev_nth by exact Hj.
assert (Hi : (length L - S j < length L)%nat) by (clear - Hj; lia).
destruct (HG (length L - S j)%nat) as [HV _]; [rewrite length_map; exact Hi|].
replace (T + Z.of_nat (length L) - 1 - Z.of_nat j) with (T + Z.of_nat (length L - S j)) by (clear - Hj; lia).
replace (bv_unsigned (nth (length L - S j) L (Z_to_bv 8 0)))
  with (nth (length L - S j) (map bv_unsigned L) 0); [exact HV|].
transitivity (nth (length L - S j) (map bv_unsigned L) (bv_unsigned (Z_to_bv 8 0))).
- apply nth_indep. rewrite length_map. exact Hi.
- apply map_nth.
Qed.
Lemma pd_dec_bytes : forall v mn, 0 <= v < 2 ^ 32 -> 0 <= mn <= 10 ->
rev (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat mn - length (ds_lsb 10 v))) = DEC v mn
/\ Z.of_nat (length (ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat mn - length (ds_lsb 10 v)))) = dec_len v mn.
Proof.
intros v mn Hv Hmn.
destruct (pd_dec_rev v mn Hv Hmn) as [HD HL].
split; [symmetry; exact HD|].
rewrite HL, length_app, repeat_length. clear - Hmn. lia.
Qed.
Lemma pd_garr8_of_rev : forall (m : word -> option byte) (H : word -> bool) (q : Z) (L : list byte),
(forall j, (j < length L)%nat -> val_mem SEGS (mrestrict H m) (q + Z.of_nat j) 1 (bv_unsigned (nth j L (Z_to_bv 8 0)))) ->
garr8 SEGS (mrestrict H m) q (map bv_unsigned L).
Proof.
intros m Hm q L HV. unfold garr8. intros j Hj. rewrite length_map in Hj.
assert (E : nth j (map bv_unsigned L) 0 = bv_unsigned (nth j L (Z_to_bv 8 0))).
{ transitivity (nth j (map bv_unsigned L) (bv_unsigned (Z_to_bv 8 0))).
  - apply nth_indep. rewrite length_map. exact Hj.
  - apply map_nth. }
rewrite E. split; [exact (HV j Hj)|].
pose proof (bv_unsigned_in_range _ (nth j L (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.
End d.
End b.
