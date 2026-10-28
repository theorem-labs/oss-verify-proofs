(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land9_range : forall x, 0 <= Z.land x 9 < 64.
Proof.
  intros x.
  assert (H : Z.land x 9 = Z.land (x mod 16) 9).
  { change 16 with (2 ^ 4). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. }
  rewrite H. pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as B. set (y := x mod 16) in *. clearbody y. clear H.
  assert (A : forall n, (n < 16)%nat -> 0 <= Z.land (Z.of_nat n) 9 < 64)
    by (intros n Hn; do 16 (destruct n as [|n]; [vm_compute; split; [intro X; discriminate X | reflexivity]|]); lia).
  rewrite <- (Z2Nat.id y) by lia. apply A. lia.
Qed.

Ltac nexit0 KX ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0xcd488%Z) _ _ _ _) => eapply KX; cycle 1; [ s2_close_memx | s2_errok_code ]
  end.
