(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1dj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X0j0
X0hr X0hn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X19k X18c X188.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition PCP : mem -> Prop := ps_cells.

Lemma PCP_framed : PC_framed PCP.
Proof. unfold PC_framed, PCP. intros m m' W PS MU WM HD. exact (ps_cells_framed m m' W PS MU WM HD). Qed.

Lemma PCP_stmt : poison_stmt PCP.
Proof.
unfold poison_stmt. intros until shj. intros Ha Hn Hn0 HH Hend SH PS ST HLOH HLO HSP MI.
assert (HA : ps_args_ok a n) by (unfold ps_args_ok, kHighMemEnd; split; [split; [exact Ha| split; [exact Hn| exact Hn0]]| right; lia]).
pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4).
eapply evt_mono; [eapply (poison_small_spec ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc m a n 250 lo shj); try eassumption; lia |].
intros ms' PO. unfold poison_small_post in PO. destruct_exs PO. destruct PO as (E & MU & WM & MI' & RW & ST').
subst ms'. unfold poison_post.
do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact RW|]. split; [exact ST'|].
apply (PCP_framed m _ _ PS MU WM). unfold kHighShadowEnd in *. destruct ST as [HL0 _].
cbn [disjoint_from]. unfold img_hull_lo, img_hull_hi. lia.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition PCP : mem -> Prop := ps_cells.

Lemma PCP_framed : PC_framed PCP.
Proof. unfold PC_framed, PCP. intros m m' W PS MU WM HD. exact (ps_cells_framed m m' W PS MU WM HD). Qed.

Lemma PCP_stmt : poison_stmt PCP.
Proof.
unfold poison_stmt. intros until shj. intros Ha Hn Hn0 HH Hend SH PS ST HLOH HLO HSP MI.
assert (HA : ps_args_ok a n) by (unfold ps_args_ok, kHighMemEnd; split; [split; [exact Ha| split; [exact Hn| exact Hn0]]| right; lia]).
pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4).
eapply evt_mono; [eapply (poison_small_spec ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc m a n 250 lo shj); try eassumption; lia |].
intros ms' PO. unfold poison_small_post in PO. destruct_exs PO. destruct PO as (E & MU & WM & MI' & RW & ST').
subst ms'. unfold poison_post.
do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact RW|]. split; [exact ST'|].
apply (PCP_framed m _ _ PS MU WM). unfold kHighShadowEnd in *. destruct ST as [HL0 _].
cbn [disjoint_from]. unfold img_hull_lo, img_hull_hi. lia.
Qed.
