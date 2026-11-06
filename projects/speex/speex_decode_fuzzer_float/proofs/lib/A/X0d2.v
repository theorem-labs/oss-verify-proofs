(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3
X0hi X0il X0gx X0fy X0fg X0ci X0cp.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X17w X19m X183 X196 X17i X16j X161 X133 X13a.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13a.
Import ListNotations.
Open Scope Z_scope.

Lemma ds_rel : forall L (m : mem), consts_rep L m -> rel_cells m.
Proof.
intros L m HC. pose proof HC as (_ & MG & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ ?R => let X := fresh "X" in destruct IC as [X IC] end.
pose proof MG as (M1 & _ & M3 & _). unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached.
split; [exact M1|]. split; [match goal with H : rw_cells bsegs m 0xfc158 _ |- _ => exact H end | exact M3].
Qed.

Lemma ds_upd_prefix : forall {X} (f : X -> word) (l : list X) (ws : list word) (k : nat) (lst : X),
firstn (length l) ws = map f l -> (length l <= length ws)%nat -> (k < length l)%nat -> nth_error l (length l - 1) = Some lst ->
firstn (length l - 1) (upd ws k (f lst)) = map f (swap_remove k l).
Proof.
intros X f l ws k lst Hf Hlw Hk Hlst. apply nth_error_ext. intros j.
rewrite nth_error_firstn, nth_error_map.
pose proof (swap_remove_length k l Hk) as SL.
destruct (Nat.ltb_spec j (length l - 1)) as [Hj|Hj].
- destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
destruct (swap_remove_nth k l j y Hk Ey) as (Ny & _). cbn [option_map].
destruct (Nat.eqb_spec j k) as [->|Hne].
+ rewrite Hlst in Ny. injection Ny as <-. rewrite nth_error_upd_same by lia. reflexivity.
+ rewrite nth_error_upd_other by lia.
assert (E : nth_error (firstn (length l) ws) j = nth_error (map f l) j) by (rewrite Hf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Ny in E. destruct (Nat.ltb_spec j (length l)) as [_|X']; [exact E | lia].
- destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [pose proof (nth_error_lt _ _ _ Ey); lia | reflexivity].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma ds_rel : forall L (m : mem), consts_rep L m -> rel_cells m.
Proof.
intros L m HC. pose proof HC as (_ & MG & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ ?R => let X := fresh "X" in destruct IC as [X IC] end.
pose proof MG as (M1 & _ & M3 & _). unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached.
split; [exact M1|]. split; [match goal with H : rw_cells asegs m 0xf38d8 _ |- _ => exact H end | exact M3].
Qed.

Lemma ds_upd_prefix : forall {X} (f : X -> word) (l : list X) (ws : list word) (k : nat) (lst : X),
firstn (length l) ws = map f l -> (length l <= length ws)%nat -> (k < length l)%nat -> nth_error l (length l - 1) = Some lst ->
firstn (length l - 1) (upd ws k (f lst)) = map f (swap_remove k l).
Proof.
intros X f l ws k lst Hf Hlw Hk Hlst. apply nth_error_ext. intros j.
rewrite nth_error_firstn, nth_error_map.
pose proof (swap_remove_length k l Hk) as SL.
destruct (Nat.ltb_spec j (length l - 1)) as [Hj|Hj].
- destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
destruct (swap_remove_nth k l j y Hk Ey) as (Ny & _). cbn [option_map].
destruct (Nat.eqb_spec j k) as [->|Hne].
+ rewrite Hlst in Ny. injection Ny as <-. rewrite nth_error_upd_same by lia. reflexivity.
+ rewrite nth_error_upd_other by lia.
assert (E : nth_error (firstn (length l) ws) j = nth_error (map f l) j) by (rewrite Hf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Ny in E. destruct (Nat.ltb_spec j (length l)) as [_|X']; [exact E | lia].
- destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [pose proof (nth_error_lt _ _ _ Ey); lia | reflexivity].
Qed.
