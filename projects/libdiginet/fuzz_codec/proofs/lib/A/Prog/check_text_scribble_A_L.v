(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths changed; 53 of its 74 lines of code are new or changed and 301 lines of the source are left out. *)
(* The inlined owed_scribble_text loop of check_text_scribble at image A: the loop by induction on the output
   slots left, from the three segments of 0x838d0-0x83958, against the fixed interface cts_loop_goal. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A
check_text_scribble_A_LD check_text_scribble_A_LA check_text_scribble_A_LB check_text_scribble_A_LJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

(* every turn uses one output slot, so the loop head holds for as many turns as there are slots left *)
Lemma ctl_head_all :
forall fuel STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 Q,
ctl_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 ->
cts_pad_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q ->
ctl_head B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q.
Proof using TL LAWS ML.
induction fuel as [|fuel IH];
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 Q HPRE PAD.
- unfold ctl_head. intros EZ msZ mdZ o i pre HS HAT E417 E418 E419 Ho Hfuel Hi Hplen HMOD HWANT.
  exfalso. lia.
- assert (JOIN : ctl_join B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0
                   (Datatypes.S fuel) Q)
    by exact (ctl_join_holds B TL LAWS ML STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb
                S2 fpos SP1 E0 fuel Q HPRE PAD
                (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 Q
                   HPRE PAD)).
  exact (ctl_head_holds B TL LAWS ML STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb
           S2 fpos SP1 E0 (Datatypes.S fuel) Q HPRE JOIN
           (ctl_alt_holds B TL LAWS ML STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb
              S2 fpos SP1 E0 (Datatypes.S fuel) Q HPRE JOIN)).
Qed.

(* the loop of check_text_scribble at image A, against its fixed interface *)
Lemma cts_loop_holds :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q,
cts_loop_goal B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q.
Proof using TL LAWS ML.
unfold cts_loop_goal.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q
  HE H10 H11 H12 Hn Hstr Hoq Hoch Hdst Hdisj EE E32 Hfin2 Hfrs2 Eab HSP1 HSP1al PAD
  EZ msZ mdZ o i pre HS SHOKz AG E33 E38 E60 E61 E417 E418 E419 HJZ KT HIO Ho Hi Hplen HMOD HWANT
  HTXT HRAT.
assert (HPRE : ctl_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0).
{ red. split; [exact HE|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  split; [exact Hn|]. split; [exact Hstr|]. split; [exact Hoq|]. split; [exact Hoch|].
  split; [exact Hdst|]. split; [exact Hdisj|]. split; [exact EE|]. split; [exact E32|].
  split; [exact Hfin2|]. split; [exact Hfrs2|]. split; [exact Eab|]. split; [exact HSP1 | exact HSP1al]. }
exact (ctl_head_all (Z.to_nat (n - o)) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb
         S2 fpos SP1 E0 Q HPRE PAD EZ msZ mdZ o i pre HS
         (conj AG (conj E33 (conj E38 (conj E60 (conj E61 (conj HJZ (conj KT HIO)))))))
         E417 E418 E419 Ho (Nat.le_refl _) Hi Hplen HMOD HWANT).
Qed.
End d.
End b.
