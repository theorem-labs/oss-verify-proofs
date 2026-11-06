(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StepTac StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ax_block1 (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xe7cac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cb0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98a7c))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7dc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33fd4)).
Definition ax_block2 (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xe7cac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cb0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 2))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe7cc0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98a7c))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7dc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33fd4))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7cd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x55b78))
/\ rdn RSEGS mem (Z_to_bv 64 0xe7dd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb5f20)).
Definition ax_block (mem : word -> option byte) (reg : bool) : Prop := if reg then ax_block2 mem else ax_block1 mem.
Definition atexit_cells (mem : word -> option byte) (n : nat) : Prop :=
match n with
| O => rdn RSEGS mem (Z_to_bv 64 0xe7cac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) /\ rdn RSEGS mem (Z_to_bv 64 0xe7cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
| S O => rdn RSEGS mem (Z_to_bv 64 0xc6234) 1%nat = Some [Z_to_bv 8 0] /\ ax_block1 mem
| S (S _) => rdn RSEGS mem (Z_to_bv 64 0xc6234) 1%nat = Some [Z_to_bv 8 0] /\ ax_block2 mem
end.
Lemma atexit_cells_of_block mem reg :
rdn RSEGS mem (Z_to_bv 64 0xc6234) 1%nat = Some [Z_to_bv 8 0] -> ax_block mem reg -> atexit_cells mem (if reg then 2 else 1).
Proof. intros HC H. destruct reg; (split; [exact HC | exact H]). Qed.
Lemma atexit_cells_frame : forall (M M' : word -> option byte) (n : nat),
(forall a : Z, (0xe7ca8 <= a < 0xe7ec8)%Z \/ a = 0xc6234%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M n -> atexit_cells M' n.
Proof.
intros M M' n AG H.
assert (R : forall (a : Z) (k : nat) v, ((0xe7ca8 <= a)%Z /\ (a + Z.of_nat k <= 0xe7ec8)%Z) \/ (a = 0xc6234%Z /\ k = 1%nat) ->
rdn RSEGS M (Z_to_bv 64 a) k = v -> rdn RSEGS M' (Z_to_bv 64 a) k = v).
{ intros a k v Hk <-. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. lia. }
unfold atexit_cells, ax_block1, ax_block2 in *. destruct n as [|[|k]].
- destruct H as (H1 & H2). split; (apply R; [cbn; lia | assumption]).
- destruct H as (HC & H1 & H2 & H3 & H4 & H5 & H6). split; [apply R; [cbn; lia | exact HC]|].
repeat split; (apply R; [cbn; lia | assumption]).
- destruct H as (HC & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). split; [apply R; [cbn; lia | exact HC]|].
repeat split; (apply R; [cbn; lia | assumption]).
Qed.
