(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbp.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the three triv rules follow the 04 rules and the journal lemmas, which no longer take a trace membership premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Definition ameter_triv : ameter_ops :=
{| mo_ok := fun _ _ => True; mo_le := fun _ _ _ => True; mo_malloc := fun _ => 0; mo_free := 0 |}.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma ameter_triv_laws : ameter_laws ameter_triv.
Proof. constructor; cbn; intros; first [exact I | lia]. Qed.
Lemma ameter_triv_fs_laws : ameter_fs_laws ameter_triv.
Proof. constructor; cbn; intros; exact I. Qed.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Theorem amalloc04_rule_triv : amalloc_realizes segs B -> amalloc04_rule segs B ameter_triv.
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch _.
eapply SRr_mono; [exact (aj_malloc_at04 segs B LAWS segs_low errno_low ML AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
exists ly2, S2, regs2, mem2, md2, res. repeat (split; [assumption|]). exact I.
Qed.
Theorem afree04_rule_triv : afree_realizes segs B -> afree04_rule segs B ameter_triv.
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch HFP _.
eapply SRr_mono; [exact (aj_free_at segs B LAWS segs_low errno_low ML AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch HFP)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6).
exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact I.
Qed.
Theorem afree_null04_rule_triv : afree_realizes segs B -> afree_null04_rule segs B ameter_triv.
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch _.
eapply SRr_mono; [exact (aj_free_null_at segs B LAWS segs_low errno_low ML AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6).
exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact I.
Qed.
End b.
