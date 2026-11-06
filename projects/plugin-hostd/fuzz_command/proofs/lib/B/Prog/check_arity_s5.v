(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the last two steps of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86958 .. the jal to check_round_trip at 0x86970), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the symbolic state at a point inside the function) and lib/A/Prog/check_refusal_s1.v (cr_entry): the symbolic state at 0x86958 and 0x86964 with the one frame word the step loads, and the transport of the cut's facts to a state that keeps the frame, the live blocks and the program's statics. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_Krefusal_s1.v, with its module paths and module names changed; 250 of its 280 lines of code are new or changed and 181 lines of the source are left out. *)
(* B twin of lib/A/Prog/check_arity_s5.v (a working branch 9c6410fb32e): the shadow of each row's
   syntax string is visible and addressable (ca_shadow_vis, ca_syn_addressable), from the image's zero-shadow ranges
   and constant shadow cells (lib/B/YF0m.v). Pure relocation (the strings move by + 0x40, their shadow patterns are
   unchanged). No code is walked here, so no UBSan trap site is in this file's range. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ca_vis_b (sa : Z) : bool :=
existsb (fun r => (SHADOW_OFF + fst r / 8 <=? sa) && (sa <? SHADOW_OFF + (fst r + snd r) / 8)
                  && (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) Tfib_zero_shadow
|| ((0 <? sa) && existsb (fun p => fst p =? sa) ca_cells).

Lemma ca_cells_range : Forall (fun p => 0 <= snd p < 256) ca_cells.
Proof.
apply Forall_forall. intros p Hp.
assert (Hb : forallb (fun q => (0 <=? snd q) && (snd q <? 256)) ca_cells = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. pose proof (Hb p Hp) as H.
apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma ca_sh_val_0 : forall g, (g < length (ca_syn_sh 0))%nat ->
nth g (ca_syn_sh 0) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 0) 0 = Z.of_nat (length (ca_syn_bytes 0)) /\ 0 < nth g (ca_syn_sh 0) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|[|[|[|[|g]]]]]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_1 : forall g, (g < length (ca_syn_sh 1))%nat ->
nth g (ca_syn_sh 1) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 1) 0 = Z.of_nat (length (ca_syn_bytes 1)) /\ 0 < nth g (ca_syn_sh 1) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_2 : forall g, (g < length (ca_syn_sh 2))%nat ->
nth g (ca_syn_sh 2) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 2) 0 = Z.of_nat (length (ca_syn_bytes 2)) /\ 0 < nth g (ca_syn_sh 2) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|g]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_3 : forall g, (g < length (ca_syn_sh 3))%nat ->
nth g (ca_syn_sh 3) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 3) 0 = Z.of_nat (length (ca_syn_bytes 3)) /\ 0 < nth g (ca_syn_sh 3) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|g]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_4 : forall g, (g < length (ca_syn_sh 4))%nat ->
nth g (ca_syn_sh 4) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 4) 0 = Z.of_nat (length (ca_syn_bytes 4)) /\ 0 < nth g (ca_syn_sh 4) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|g]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_5 : forall g, (g < length (ca_syn_sh 5))%nat ->
nth g (ca_syn_sh 5) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 5) 0 = Z.of_nat (length (ca_syn_bytes 5)) /\ 0 < nth g (ca_syn_sh 5) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|g]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_6 : forall g, (g < length (ca_syn_sh 6))%nat ->
nth g (ca_syn_sh 6) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 6) 0 = Z.of_nat (length (ca_syn_bytes 6)) /\ 0 < nth g (ca_syn_sh 6) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|g]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_7 : forall g, (g < length (ca_syn_sh 7))%nat ->
nth g (ca_syn_sh 7) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 7) 0 = Z.of_nat (length (ca_syn_bytes 7)) /\ 0 < nth g (ca_syn_sh 7) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|[|g]]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_8 : forall g, (g < length (ca_syn_sh 8))%nat ->
nth g (ca_syn_sh 8) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 8) 0 = Z.of_nat (length (ca_syn_bytes 8)) /\ 0 < nth g (ca_syn_sh 8) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|[|[|[|[|[|[|[|g]]]]]]]]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_9 : forall g, (g < length (ca_syn_sh 9))%nat ->
nth g (ca_syn_sh 9) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 9) 0 = Z.of_nat (length (ca_syn_bytes 9)) /\ 0 < nth g (ca_syn_sh 9) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|g]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_10 : forall g, (g < length (ca_syn_sh 10))%nat ->
nth g (ca_syn_sh 10) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 10) 0 = Z.of_nat (length (ca_syn_bytes 10)) /\ 0 < nth g (ca_syn_sh 10) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|[|[|g]]]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_11 : forall g, (g < length (ca_syn_sh 11))%nat ->
nth g (ca_syn_sh 11) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 11) 0 = Z.of_nat (length (ca_syn_bytes 11)) /\ 0 < nth g (ca_syn_sh 11) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_12 : forall g, (g < length (ca_syn_sh 12))%nat ->
nth g (ca_syn_sh 12) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 12) 0 = Z.of_nat (length (ca_syn_bytes 12)) /\ 0 < nth g (ca_syn_sh 12) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|g]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_13 : forall g, (g < length (ca_syn_sh 13))%nat ->
nth g (ca_syn_sh 13) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 13) 0 = Z.of_nat (length (ca_syn_bytes 13)) /\ 0 < nth g (ca_syn_sh 13) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|g]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_14 : forall g, (g < length (ca_syn_sh 14))%nat ->
nth g (ca_syn_sh 14) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 14) 0 = Z.of_nat (length (ca_syn_bytes 14)) /\ 0 < nth g (ca_syn_sh 14) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|[|[|g]]]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_15 : forall g, (g < length (ca_syn_sh 15))%nat ->
nth g (ca_syn_sh 15) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 15) 0 = Z.of_nat (length (ca_syn_bytes 15)) /\ 0 < nth g (ca_syn_sh 15) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_16 : forall g, (g < length (ca_syn_sh 16))%nat ->
nth g (ca_syn_sh 16) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 16) 0 = Z.of_nat (length (ca_syn_bytes 16)) /\ 0 < nth g (ca_syn_sh 16) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_17 : forall g, (g < length (ca_syn_sh 17))%nat ->
nth g (ca_syn_sh 17) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 17) 0 = Z.of_nat (length (ca_syn_bytes 17)) /\ 0 < nth g (ca_syn_sh 17) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_18 : forall g, (g < length (ca_syn_sh 18))%nat ->
nth g (ca_syn_sh 18) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 18) 0 = Z.of_nat (length (ca_syn_bytes 18)) /\ 0 < nth g (ca_syn_sh 18) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|g]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_19 : forall g, (g < length (ca_syn_sh 19))%nat ->
nth g (ca_syn_sh 19) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 19) 0 = Z.of_nat (length (ca_syn_bytes 19)) /\ 0 < nth g (ca_syn_sh 19) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|g]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_20 : forall g, (g < length (ca_syn_sh 20))%nat ->
nth g (ca_syn_sh 20) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 20) 0 = Z.of_nat (length (ca_syn_bytes 20)) /\ 0 < nth g (ca_syn_sh 20) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|[|[|g]]]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val_21 : forall g, (g < length (ca_syn_sh 21))%nat ->
nth g (ca_syn_sh 21) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh 21) 0 = Z.of_nat (length (ca_syn_bytes 21)) /\ 0 < nth g (ca_syn_sh 21) 0 < 8).
Proof.
intros g Hg. cbn [ca_syn_sh ca_syn_bytes ca_syn_list nth length] in Hg.
destruct g as [|g]; [first [left; reflexivity | right; split; [reflexivity | vm_compute; split; reflexivity]] | exfalso; lia].
Qed.

Lemma ca_sh_val : forall k g, (k < 22)%nat -> (g < length (ca_syn_sh k))%nat ->
nth g (ca_syn_sh k) 0 = 0 \/
(8 * Z.of_nat g + nth g (ca_syn_sh k) 0 = Z.of_nat (length (ca_syn_bytes k)) /\ 0 < nth g (ca_syn_sh k) 0 < 8).
Proof.
intros k g Hk Hg.
destruct k as [|k]; [exact (ca_sh_val_0 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_1 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_2 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_3 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_4 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_5 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_6 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_7 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_8 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_9 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_10 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_11 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_12 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_13 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_14 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_15 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_16 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_17 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_18 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_19 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_20 g Hg)|].
destruct k as [|k]; [exact (ca_sh_val_21 g Hg)|].
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_shadow_vis : forall ly S (W : world SEGS) mem md sa,
AR SEGS B ly S W mem md -> ca_vis_b sa = true -> aview SEGS (w_H W) mem sa <> None.
Proof.
intros ly S W mem md sa HAR Hb. apply orb_true_iff in Hb. destruct Hb as [Hz | Hc].
- apply existsb_exists in Hz as (r & Hr & Hc).
  apply andb_true_iff in Hc as [Hc Hs8]. apply andb_true_iff in Hc as [Hc Hr8].
  apply andb_true_iff in Hc as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. apply Z.eqb_eq in Hr8. apply Z.eqb_eq in Hs8.
  pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md r HAR Hr) as HZ.
  assert (Hd : 0 <= sa - (SHADOW_OFF + fst r / 8) < snd r / 8).
  { split; [lia|]. assert (Hq : (fst r + snd r) / 8 = fst r / 8 + snd r / 8).
    { rewrite <- Z.div_add_l by lia. f_equal. rewrite (Z_div_exact_2 (fst r) 8) at 1 by (lia || exact Hr8). lia. }
    lia. }
  pose proof (HZ (sa - (SHADOW_OFF + fst r / 8)) Hd) as H.
  unfold shadow_of_addr in H. replace (SHADOW_OFF + fst r / 8 + (sa - (SHADOW_OFF + fst r / 8))) with sa in H by lia.
  rewrite H. discriminate.
- apply andb_true_iff in Hc as [Hpos Hc]. apply Z.ltb_lt in Hpos.
  apply existsb_exists in Hc as ([x y] & Hin & Hc). cbn [fst snd] in Hc. apply Z.eqb_eq in Hc. subst x.
  assert (Hy : 0 <= y < 256) by (pose proof ca_cells_range as HR; rewrite Forall_forall in HR; exact (HR _ Hin)).
  pose proof (ca_const_byte B HB ly S W mem md sa y HAR
    ltac:(apply in_or_app; right; apply ca_cells_in; [exact Hin | lia]) Hy) as HV.
  intros Hnone. unfold aview in Hnone. rewrite HV in Hnone. discriminate.
Qed.

Lemma ca_syn_addressable : forall k ly S (W : world SEGS) mem md, (k < 22)%nat ->
AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ca_syn_addr k) (Z.of_nat (length (ca_syn_bytes k))).
Proof.
intros k ly S W mem md Hk HAR x Hx.
destruct (ca_syn_bound k Hk) as (Hsa & Hsa8 & Hsb & Hsh).
assert (Hgl : (Z.to_nat ((x - ca_syn_addr k) / 8) < length (ca_syn_sh k))%nat).
{ pose proof (Z.div_le_mono 0 (x - ca_syn_addr k) 8 ltac:(lia) ltac:(lia)).
  assert ((x - ca_syn_addr k) / 8 < Z.of_nat (length (ca_syn_sh k))) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hd : x / 8 = ca_syn_addr k / 8 + Z.of_nat (Z.to_nat ((x - ca_syn_addr k) / 8))).
{ rewrite Z2Nat.id by (apply Z.div_pos; lia).
  rewrite <- Z.div_add_l by lia. f_equal. rewrite (Z_div_exact_2 (ca_syn_addr k) 8) at 2 by (lia || exact Hsa8). lia. }
pose proof (ca_synsh_mbyte B HB k ly S W mem md Hk HAR _ Hgl) as H.
exists (nth (Z.to_nat ((x - ca_syn_addr k) / 8)) (ca_syn_sh k) 0). split.
- unfold shadow_of_addr. rewrite Hd.
  replace (SHADOW_OFF + (ca_syn_addr k / 8 + Z.of_nat (Z.to_nat ((x - ca_syn_addr k) / 8))))
    with (SHADOW_OFF + ca_syn_addr k / 8 + Z.of_nat (Z.to_nat ((x - ca_syn_addr k) / 8))) by lia.
  unfold aview. rewrite H. cbn [option_map]. f_equal.
  pose proof (ca_syn_sh_range k) as HR. rewrite Forall_forall in HR.
  pose proof (HR _ (nth_In (ca_syn_sh k) 0 Hgl)) as Hv.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
- destruct (ca_sh_val k _ Hk Hgl) as [Hz | [Heq Hpos]]; [left; exact Hz|].
  right. split; [|lia].
  assert (Hmod : x mod 8 = x - 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
  assert (Ha8 : ca_syn_addr k = 8 * (ca_syn_addr k / 8)) by (apply Z_div_exact_2; [lia | exact Hsa8]).
  rewrite Hmod, Hd. lia.
Qed.

End e.
End f.
End d.
