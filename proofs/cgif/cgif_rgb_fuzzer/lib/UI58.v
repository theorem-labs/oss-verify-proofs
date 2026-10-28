(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI59 UI56 YI0x YL0e UI57.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_lh : sstate :=
mkSS L_LH sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 192 8 192
([mkChunk 8 (CVal 8 (SOff 42 0)); mkChunk 16 (CVal 8 (SOff 43 0)); mkChunk 24 (CVal 8 (SOff 44 0))]
++ obj_chunks_gen (lay_shift 32 LAY_FrameConfig) 45 [] ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 192) (2^63 - 192) 4);
(8%nat, mkAF 1 100000000 0); (9%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(18%nat, mkAF 1 16 0); (42%nat, mkAF 4096 CEIL_MAX 0);
(43%nat, mkAF 1 CEIL_MAX 0); (44%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition ss_lh_c : sstate := Eval vm_compute in ss_lh.
Lemma nth_lay_shift_snd : forall d lay j, snd (nth j (lay_shift d lay) (0, 8%N)) = snd (nth j lay (0, 8%N)).
Proof. intros d lay. induction lay as [|f lay IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
End a.
Ltac stack_word HS HU2 n Hn :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) ?v =>
replace (spv - dd) with (spv - 192 + (192 - dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (192 - dd) (SOff n 0) (spv - 192) v HS);
[ reflexivity | reflexivity | cbv; auto 60
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hn; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
| ]
end.
Ltac saved_ok_tac HS HU2 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 :=
unfold saved_ok;
split; [stack_word HS HU2 32%nat H32; apply u64_range'|];
split; [stack_word HS HU2 33%nat H33; apply u64_range'|];
split; [stack_word HS HU2 34%nat H34; apply u64_range'|];
split; [stack_word HS HU2 35%nat H35; apply u64_range'|];
split; [stack_word HS HU2 36%nat H36; apply u64_range'|];
split; [stack_word HS HU2 37%nat H37; apply u64_range'|];
split; [stack_word HS HU2 38%nat H38; apply u64_range'|];
split; [stack_word HS HU2 39%nat H39; apply u64_range'|];
split; [stack_word HS HU2 40%nat H40; apply u64_range'|];
stack_word HS HU2 41%nat H41; apply u64_range'.
