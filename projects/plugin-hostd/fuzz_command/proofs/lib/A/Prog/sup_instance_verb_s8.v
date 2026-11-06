(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the two segments of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command) through
   the strspn and strcspn wrappers (0x8b474 .. 0x8b498), after lib/A/Prog/sup_reply_code.v (a step through a
   runtime entry by PaArt.aj_art_at) and proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PSIV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_instance_verb.

Lemma siv_set_lit : PSIV.siv_set ++ [Z_to_bv 8 0] = RO_lit_21d60.
Proof. vm_compute. reflexivity. Qed.
Lemma siv_set_nz : ~ In (Z_to_bv 8 0) PSIV.siv_set.
Proof. unfold PSIV.siv_set. cbn [In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the separators " \t" (.str.5 at 0x21d60) as the wrappers' second string, and its readable word tail *)
Lemma siv_set_at : forall rd, cmd_ro_ok rd ->
astr_atR rd 0x21d60 PSIV.siv_set /\ (forall a, 0x21d62 < a < 0x21d62 - 0x21d62 mod 8 + 8 -> rd a <> None).
Proof.
intros rd [HB HT]. split.
- split; [|exact siv_set_nz]. rewrite siv_set_lit. clear HT. unfold cmd_ro_bytes in HB.
  repeat match type of HB with
  | abytes_atR _ 0x21d60 _ /\ _ => exact (proj1 HB)
  | _ /\ _ => apply proj2 in HB
  end.
- apply (HT 0x21d62). apply In_of_existsb. vm_compute. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the line's tail from its j-th byte, as a range a string entry may read: inside the line's live block *)
Lemma siv_line_rd :
forall lyc Sc (Wc : world SEGS) memT mdT (regsT : bvmap 5 word) pl line j stk,
AR SEGS B lyc Sc Wc memT mdT ->
(exists p k, In (p, k) (ablocks B lyc Sc) /\ p <= pl /\ pl + Z.of_nat (length line) + 1 <= p + k) ->
(j <= length line)%nat -> alloc_ceiling <= spZ regsT - stk ->
aread_ok SEGS stk Wc regsT memT (pl + Z.of_nat j) (astr_len (skipn j line) + 1).
Proof.
intros lyc Sc Wc memT mdT regsT pl line j stk HARc (p & k & Hpk & Hp1 & Hp2) Hj Hstk.
unfold astr_len. rewrite length_skipn.
apply (aread_ok_of_block SEGS B LAWS stk lyc Sc Wc regsT memT mdT p k); [exact HARc | exact Hpk | lia | lia | lia | exact Hstk].
Qed.

End e.
End f.
End d.
