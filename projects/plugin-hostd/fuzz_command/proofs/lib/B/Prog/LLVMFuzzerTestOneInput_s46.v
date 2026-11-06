(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the exit of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a04 = LO_K: B stores w.n on every word, so no code runs between the split loop's exits and the five checks), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s46.v without its run: the words' facts as the loop carries them (sw_found) give lt_words, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment statement from the next one's). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdPaLib CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the words of the line hold no NUL ---- *)
Lemma ae_words_nz_loc : forall D w, In w (Verbs.words (Verbs.line D)) -> ~ In (Z_to_bv 8 0) w.
Proof.
intros D w Hw Hin.
destruct (Verbs.words_acc_spec (fun b => bv_unsigned b <> 0) (Verbs.line D) [] (fun b H => False_ind _ H)
  (Verbs.line_nonul D) w Hw) as [_ Hb].
destruct (Hb _ Hin) as [Hz _]. apply Hz. reflexivity.
Qed.

(* a word found in the copy buffer is a C string where it starts *)
Lemma ae_str_of_found : forall (rd : reader) copy (C : list byte) pt (w : list byte),
  abytes_atR rd copy C -> copy <= pt ->
  (forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (pt - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t) ->
  ~ In (Z_to_bv 8 0) w -> astr_atR rd pt w.
Proof.
intros rd copy C pt w HC Hp HW Hn. split; [|exact Hn].
intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
pose proof (HW t ltac:(lia)) as Ht2.
destruct (nth_error (w ++ [Z_to_bv 8 0]) t) as [x|] eqn:Ex;
  [|apply nth_error_None in Ex; rewrite length_app in Ex; cbn [length] in Ex; lia].
try rewrite Ex in Ht2.
assert (Hj : (Z.to_nat (pt - copy) + t < length C)%nat) by (apply nth_error_Some; rewrite Ht2; discriminate).
pose proof (HC _ Hj) as Hr.
replace (nth (Z.to_nat (pt - copy) + t) C (Z_to_bv 8 0)) with x in Hr by (symmetry; apply nth_error_nth; exact Ht2).
replace (nth t (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with x by (symmetry; apply nth_error_nth; exact Ex).
replace (pt + Z.of_nat t) with (copy + Z.of_nat (Z.to_nat (pt - copy) + t)) by lia. exact Hr.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- 0x86a04: the split loop's exit facts are LT_K_stmt's words (lt_words) ---- *)
Lemma aw_seg_E : forall m, LT_K_stmt B MT m -> AW_E_stmt B MT m.
Proof.
intros m HK. unfold AW_E_stmt.
intros cx q ly S W regs mem md k acc text copy arr C wp Hm HFP0 HC HR HWS HWN Hlwp HCb HCl HARR HFD.
pose proof (q_L0_U cx q) as HL0.
destruct HWS as (HW0 & HW8 & HW16).
apply (aw_LT_K B MT m HK cx q ly S W regs mem md k acc text copy arr wp Hm HFP0 HC); [|exact HR].
unfold lt_words. change (StrFun.strnlen_res (Z.of_nat (length (q_D cx q))) (q_D cx q)) with (q_L0 cx q).
split; [exact HW0|]. split; [exact HW8|]. split; [exact HW16|]. split; [exact HWN|].
split; [exact Hlwp|]. split; [exact HARR|].
intros i pt w Hip Hiw. destruct (HFD i pt w Hip Hiw) as (P1 & P2 & P3).
rewrite Z2Nat.id in P2 by lia.
split; [exact P1|]. split; [lia|].
exact (ae_str_of_found (rdW W mem) copy C pt w HCb P1 P3 (ae_words_nz_loc (q_D cx q) w (nth_error_In _ _ Hiw))).
Qed.

End e.
End f.
End d.
