(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fy X0fg X0d7 X0jc.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X16j X161 X13s X19t.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_io : forall Σ m, ART_A Σ m -> io_consts m.
Proof.
intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ (_ /\ _) => destruct IC as [_ IC] end. destruct IC as [IR IO].
split; [exact IR|]. split; [exact IO|].
unfold io_acc. repeat (apply Forall_cons; [cbn [fst snd];
match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)) end;
[unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn [fst snd]; lia | cbn [fst snd]; lia]|]).
apply Forall_nil.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_io : forall Σ m, ART_A Σ m -> io_consts m.
Proof.
intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ (_ /\ _) => destruct IC as [_ IC] end. destruct IC as [IR IO].
split; [exact IR|]. split; [exact IO|].
unfold io_acc. repeat (apply Forall_cons; [cbn [fst snd];
match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)) end;
[unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn [fst snd]; lia | cbn [fst snd]; lia]|]).
apply Forall_nil.
Qed.
