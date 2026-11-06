(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E QqRD QybZ Qqcs Qmth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qg4E QqRD QybZ Qqcs.Mq1 Qmth.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

End WithFP1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg4E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqRD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqRD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmth. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq1.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k) ->
to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
(1 <= length rest)%nat ->
to_wall ms rest k ->
to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wall_tail ms' rest k ->
to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

Lemma msteps_to_wall_tail : forall ms ms' rest k,
msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
intros ms ms' rest k H; induction H; [auto|].
intro Hw. eapply twt_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
(ms : machine_state) : Prop :=
match bufs with
| [] => to_wexit segs ms [] code
| buf :: rest =>
(1 <= length buf)%nat /\
to_wall_tail ms buf (to_wallexit rest code)
end.

Lemma twe_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hsvc Hstep Hw.
destruct bufs as [|buf rest].
- eapply tw_step; eauto.
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
- exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply msteps_to_wall_tail; eauto.
Qed.

End WithSegsCh.

Abbreviation wexit1 segs ms bufs code :=
(to_wallexit segs (Z_to_bv 64 1) bufs code ms).

End WithFP1.
