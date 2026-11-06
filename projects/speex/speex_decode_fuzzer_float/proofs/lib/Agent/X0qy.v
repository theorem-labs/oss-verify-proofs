(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw X0qx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <->
rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
split.
- intros [[[W1 W2] [B1 B2]] WR].
pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
destruct WR as (HA & HN & HW).
split; [split; [split; assumption|] | split; [split; assumption|]].
+ split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
+ split; [lia|]. split; [lia|]. intros i Hi.
replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
- intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
pose proof (cells_bytes_length cs1 W1) as L1.
split; [split; [split; assumption|] |].
+ split; [exact B1|]. rewrite L1. exact B2.
+ split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
* apply HW1. lia.
* replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Lemma rd_u64 : forall segs m A (w : word) rest a,
bytes_at segs m A (le8 w ++ rest) -> a = wa A -> ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
intros segs m A w rest a B ->.
assert (L : (0 + 8 <= length (le8 w ++ rest))%nat) by (rewrite length_app, length_le8; lia).
pose proof (bytes_at_ov_read segs m A (le8 w ++ rest) 0 8 B L) as R.
rewrite Z.add_0_r in R. rewrite R. f_equal; reflexivity.
Qed.

Ltac exact_evt H :=
lazymatch type of H with evt _ _ ?s1 =>
lazymatch goal with |- evt _ _ ?s2 =>
replace s2 with s1; [exact H|];
cbv delta [mkR]; repeat first [reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => lia | nat => lia end | |- _ => lia end | progress f_equal | lia]
end
end.

Definition auxv20 (phnum : Z) (uid hw rnd : word) : list word :=
[Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 phnum;
Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
Z_to_bv 64 25; rnd; z64; z64].

Lemma rd_u64s : forall segs mm A ws (i : nat) w a,
bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
intros segs mm A ws i w a B Hn ->.
first [ pose proof (u64s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E1 Hlen Eu Hlu | sf_fb; destruct (u64s_split _ _ _ Hn) as (pre & post & E1 & Hlen & Eu & Hlu) ].
rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
eapply rd_u64; [exact B|]. unfold wa. f_equal. lia.
Qed.
