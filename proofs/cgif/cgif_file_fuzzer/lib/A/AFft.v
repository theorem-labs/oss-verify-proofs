(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK0i YP09 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YK18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj YFfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFf2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Export AFkq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition enq_after_refill (k : chunk) (r : unit * astate) : itree astate (unit * astate) :=
match pc_chunks (cache (snd r) kBatchClass) with
| [] => ISpin 219184
| _ => IRet (tt, AFf2.S' (snd r) k (pc_chunks (cache (snd r) kBatchClass)))
end.
Lemma amreal_enqueue_nb : forall k X W c (Q : unit * astate -> world tfibsegs -> config -> Prop),
need_new_batch (st_qthread X) = true ->
amreal tfibsegs (refill_tree kBatchClass X) W c (fun r W1 c1 => amreal tfibsegs (enq_after_refill k r) W1 c1 Q) ->
amreal tfibsegs (enqueue k X) W c Q.
Proof.
intros k X W c Q HNB H.
unfold enqueue. unfold bind at 1. unfold get. cbn [ibind]. rewrite HNB.
apply amreal_bind_assoc'. unfold cache_alloc. apply amreal_bind_assoc'. cbn beta.
lazymatch goal with |- amreal _ (bind ?mi (fun a => bind (bind ?mr ?G) ?REST) X) _ _ _ =>
assert (HK : amreal tfibsegs (bind (refill_tree kBatchClass) (fun v => bind (G v) REST) X) W c Q)
end.
{ apply amreal_mbind. eapply amreal_mono; [|exact H]. intros [u X1] W1 c1 HH. cbn [fst snd]. revert HH.
unfold enq_after_refill. cbn [snd]. unfold bind, get_pc, get, ret, set_pc, modify. unfold bind, spin. cbn [ibind].
change (znth pclass0 kBatchClass (st_cache X1)) with (cache X1 kBatchClass).
destruct (pc_chunks (cache X1 kBatchClass)) as [|z l0]; cbn [ibind]; intros HH; exact HH. }
unfold refill_tree in HK. apply amreal_bind_assoc in HK. cbn beta in HK.
unfold bind at 1. unfold bind at 1 in HK.
eapply amreal_ibind_ext; [|exact HK]. intros [a s'] W1 c1 HH. cbn beta iota in HH |- *.
apply amreal_bind_assoc'. exact HH.
Qed.
End b.
